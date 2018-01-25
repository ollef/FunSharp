module FunSharp

open FParsec
open System.Runtime.InteropServices

type Ident = string

type Expr =
  | Var of Ident // x
  | Lit of int // n
  | Lam of Ident * Expr // \x. e
  | App of Expr * Expr // e e'

let rec apps e es = match es with
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

let rec subst v e expr = match expr with
    | Var v' -> if v = v' then e else expr
    | Lit i -> expr
    | Lam (v', e') -> if v = v' then expr else Lam (v', subst v e e')
    | App (e1, e2) -> App (subst v e e1, subst v e e2)

let rec evalSubst expr =
    match expr with
    | Var _ -> expr
    | Lit _ -> expr
    | Lam _ -> expr
    | App (e1, e2) -> match evalSubst e1 with
        | Lam (x, e1') -> evalSubst (subst x (evalSubst e2) e1')
        | e1' -> App (e1', evalSubst e2)

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
