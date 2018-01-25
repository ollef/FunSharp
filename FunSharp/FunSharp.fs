module FunSharp

open FParsec

type Ident = string

type Expr =
  | Var of Ident // x
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

let patomicExpr = pvar <|> (preserved "(" >>. pexpr .>> preserved ")")

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

let foo = test pexpr "x"