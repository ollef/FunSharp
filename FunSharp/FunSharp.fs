module FunSharp 
open FParsec
open System.Runtime.InteropServices
open System

type Ident = string

type Expr =
  | Var of Ident // x
  | Lit of int // n
  | Lam of Ident * Expr // \x. e
  | App of Expr * Expr // e e'
  | Anno of Expr * Type

and Type =
    | Int
    | Fun of Type * Type
    | UVar of int * Type option ref
    | TVar of Ident
    | Forall of Ident * Type

let rec apps e es =
    match es with
    | [] -> e
    | e'::es' -> apps (App (e, e')) es'

let token p = p .>> spaces

let pident : Parser<string, unit> =
    let isIdentifierFirstChar c = isLetter c || c = '_'
    let isIdentifierChar c = isLetter c || isDigit c || c = '_'

    token (many1Satisfy2L isIdentifierFirstChar isIdentifierChar "identifier")

let preserved s = token (pstring s)

let pexpr, pexprRef = createParserForwardedToRef<Expr, unit>()

let pvar = pident |>> Var 

let plit : Parser<Expr, unit> = token pint32 |>> Lit

let patomicExpr = pvar <|> plit <|> (preserved "(" >>. pexpr .>> preserved ")")

let plambda =
    pipe4
        (preserved "\\")
        pident
        (preserved ".")
        pexpr
        (fun _ x _ e -> Lam (x, e))

let papp = pipe2 pexpr pexpr (fun e1 e2 -> App (e1, e2))

do pexprRef := plambda <|> pipe2 patomicExpr (many patomicExpr) apps

let test p str =
    match run (spaces >>. p) str with
    | Success(result, _, _)   -> printfn "Success: %A" result
    | Failure(errorMsg, _, _) -> printfn "Failure: %s" errorMsg

exception ParseException of string

let optimisticParse p str =
    match run (spaces >>. p) str with
    | Success(result, _, _) -> result
    | Failure(errorMsg, _, _) -> raise (ParseException errorMsg)

exception EvalException of string

let rec subst v e expr =
    match expr with
    | Var v' -> if v = v' then e else expr
    | Lit _ -> expr
    | Lam (v', e') -> if v = v' then expr else Lam (v', subst v e e')
    | App (e1, e2) -> App (subst v e e1, subst v e e2)
    | Anno (e', t) -> Anno (subst v e e', t)

let rec evalSubst expr =
    match expr with
    | Var _ -> expr
    | Lit _ -> expr
    | Lam _ -> expr
    | App (e1, e2) ->
        match evalSubst e1 with
        | Lam (x, e1') -> evalSubst (subst x (evalSubst e2) e1')
        | e1' -> App (e1', evalSubst e2)
    | Anno (e, _) -> evalSubst e

let rec evalEnv (env : Map<Ident, Expr>) expr =
    printfn "%A %A" env expr
    match expr with
    | Var v ->
        match Map.tryFind v env with
        | None -> expr
        | Some e -> e
    | Lit _ -> expr
    | Lam (x, e) -> Lam (x, evalEnv (Map.remove x env) e)
    | App (e1, e2) ->
        match evalEnv env e1 with
        | Lam (x, e1') -> evalEnv (Map.add x (evalEnv env e2) env) e1'
        | e1' -> App (e1', evalEnv env e2)
    | Anno (e, _) -> evalEnv env e

let freshU = ref 0
let newUVar () = 
    let n = !freshU
    freshU := n + 1
    UVar (n, ref None)

let rec zonk typ =
    match typ with
    | Int -> typ
    | Fun (arg, res) -> Fun (zonk arg, zonk res)
    | UVar (_, r) ->
        match !r with
        | None -> typ
        | Some typ' ->
            let typ'' = zonk typ'
            r := Some typ''
            typ''
    | TVar v -> TVar v
    | Forall (v, t) -> Forall (v, zonk t)

let rec unificationVars typ =
    match typ with
    | Int -> Set.empty
    | Fun (arg, res) -> Set.union (unificationVars arg) (unificationVars res)
    | UVar (n, r) -> Set.singleton (n, r)
    | TVar _ -> Set.empty
    | Forall (_, t) -> unificationVars t

let rec occursCheck n typ =
    if Set.contains n (unificationVars typ)
    then failwith ("occurs check failed, " + string typ + "contains " + string n)
    else ()

let rec unify type1 type2 =
    let ztype1 = zonk type1
    let ztype2 = zonk type2
    match (ztype1, ztype2) with
    | _ when ztype1 = ztype2 -> ()
    | (Fun (arg1, res1), Fun (arg2, res2)) ->
        unify arg1 arg2
        unify res1 res2
    | (Forall (_, t1), Forall (_, t2)) -> unify t1 t2
    | (UVar (n, v1), _) ->
        occursCheck (n, v1) ztype2
        v1 := Some ztype2
    | (_, UVar (n, v2)) ->
        occursCheck (n, v2) ztype1
        v2 := Some ztype1
    | _ -> failwith ("Can't unify " + string ztype1 + " and " + string ztype2) 

type TypedExpr =
    | Var of Ident * Type // x
    | Lit of int // n
    | Lam of Ident * Type * TypedExpr // \x. e
    | App of TypedExpr * TypedExpr // e e'
    | TypeLam of Ident * TypedExpr // /\x. e
    | TypeApp of TypedExpr * Type // e [t]

let rec zonkExpr expr : TypedExpr =
    match expr with
    | TypedExpr.Var (v, t) -> Var (v, zonk t)
    | TypedExpr.Lit i -> Lit i
    | TypedExpr.Lam (x, t, body) -> Lam (x, zonk t, zonkExpr body)
    | TypedExpr.App (func, arg) -> App (zonkExpr func, zonkExpr arg)
    | TypedExpr.TypeLam (x, body) -> TypeLam (x, zonkExpr body)
    | TypedExpr.TypeApp (e, t) -> TypeApp (zonkExpr e, zonk t)

let rec typeSubst x subType typ =
    match typ with
    | Int -> typ
    | Fun (arg, res) -> Fun (typeSubst x subType arg, typeSubst x subType res)
    | UVar _ -> typ
    | TVar x' when x = x' -> subType
    | TVar _ -> typ
    | Forall (x', _) when x = x' -> typ
    | Forall (x', typ') -> Forall (x', typeSubst x subType typ')

let rec instantiate expr typ =
    match typ with
    | Forall (x, typ') ->
        let v = newUVar ()
        let (expr', typ') = instantiate expr (typeSubst x v typ')
        (TypeApp (expr', v), typ')
    | _ -> (expr, typ)

let rec check expr expectedType (env : Map<Ident, Type>) : TypedExpr =
    let (expr', exprType) = infer expr env
    unify exprType expectedType
    expr'

and infer expr (env : Map<Ident, Type>) : TypedExpr * Type =
    match expr with
    | Expr.Var v ->
        match Map.tryFind v env with
        | None -> failwith ("not in scope: " + v)
        | Some varType ->
            instantiate (Var (v, varType)) varType
    | Expr.Lit i -> (Lit i, Int)
    | Expr.Lam (x, body) ->
        let argType = newUVar ()
        let (body', resType) = infer body (Map.add x argType env)
        (Lam (x, zonk argType, body'), Fun (argType, resType))
    | Expr.App (func, arg) ->
        let argType = newUVar ()
        let retType = newUVar ()
        let func' = check func (Fun (argType, retType)) env
        let arg' = check arg argType env
        (App (func', arg'), zonk retType)
    | Expr.Anno (e, typ) ->
        let e' = check e typ env
        (e', typ)

let infer' expr =
    let (expr, typ) = infer expr Map.empty
    (zonkExpr expr, zonk typ)

let freshT = ref 0
let freshName () = 
    let i = !freshT
    freshT := i + 1
    "x" + string i

let rec foralls names typ =
    match names with
    | [] -> typ
    | name::names' -> Forall (name, foralls names' typ)

let rec typelams names expr =
    match names with
    | [] -> expr
    | name::names' -> TypeLam (name, typelams names' expr)

let rec freshNames n = List.init n (fun _ -> freshName ())

let generalise expr typ =
    let ztype = zonk typ
    let uvars = Set.toList (unificationVars ztype)
    let names = freshNames (List.length uvars)
    for ((_, r), name) in List.zip uvars names do
        r := Some (TVar name)
    let expr' = zonkExpr (typelams names expr)
    let typ' = zonk (foralls names typ)
    (expr', typ')

let expr1 = optimisticParse pexpr "123"
let test1 = infer expr1 Map.empty
let expr2 = optimisticParse pexpr "\\x. x"
let test2 = check expr2 (Fun (Int, Int)) Map.empty

let expr3 = optimisticParse pexpr "f 123"
let test3 = infer expr3 (Map.ofList [("f", Fun (Int, Int))])

let expr4 = optimisticParse pexpr "\\x. x"
let test4 = infer expr4 Map.empty

let expr5 = optimisticParse pexpr "(\\x. x) 123"
let test5 = infer' expr5

let expr6 = optimisticParse pexpr "\\f. \\x. f x"
let test6 =
    let (expr, typ) = infer expr6 Map.empty
    generalise expr typ

// // Fails occurs check
// let expr7 = optimisticParse pexpr "\\f. f f"
// let test7 =
//    let (expr, typ) = infer expr7 Map.empty
//    (expr, generalise typ)

let expr8 = optimisticParse pexpr "f 32"
let test8 =
    let (expr, typ) = infer expr8 (Map.add "f" (Forall ("a", Fun (TVar "a", TVar "a"))) Map.empty)
    generalise expr typ