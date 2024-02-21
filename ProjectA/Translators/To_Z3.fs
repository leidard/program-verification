module To_Z3

open PLAST
open AST
open V0AST
open To_IVL1
open ErrorInfo
open Microsoft.Z3


// This function converts an expression into a Z3 expression such that it can be solved by Z3
let rec expr_to_Z3_expr (e: expr, ctx: Context, id_types: Map<ident, ty>) : Expr =
    match e with
    | Boolean b -> if b then ctx.MkTrue() else ctx.MkFalse()

    | Integer i -> ctx.MkInt(i)

    | Ref i ->
        (match Map.find i id_types with
         | Int -> ctx.MkIntConst(i)
         | Bool -> ctx.MkBoolConst(i))

    | Unary(UMinus, e') -> ctx.MkUnaryMinus((expr_to_Z3_expr (e', ctx, id_types)) :?> ArithExpr)
    | Unary(Neg, e') -> ctx.MkNot((expr_to_Z3_expr (e', ctx, id_types)) :?> BoolExpr)

    | Binary(And, e1, e2, _) ->
        ctx.MkAnd(
            (expr_to_Z3_expr (e1, ctx, id_types)) :?> BoolExpr,
            (expr_to_Z3_expr (e2, ctx, id_types)) :?> BoolExpr
        )
    | Binary(Divide, e1, e2, _) ->
        ctx.MkDiv(
            (expr_to_Z3_expr (e1, ctx, id_types)) :?> ArithExpr,
            (expr_to_Z3_expr (e2, ctx, id_types)) :?> ArithExpr
        )
    | Binary(Eq, e1, e2, _) -> ctx.MkEq((expr_to_Z3_expr (e1, ctx, id_types)), (expr_to_Z3_expr (e2, ctx, id_types)))
    | Binary(Geq, e1, e2, _) ->
        ctx.MkGe(
            (expr_to_Z3_expr (e1, ctx, id_types)) :?> ArithExpr,
            (expr_to_Z3_expr (e2, ctx, id_types)) :?> ArithExpr
        )
    | Binary(Gt, e1, e2, _) ->
        ctx.MkGt(
            (expr_to_Z3_expr (e1, ctx, id_types)) :?> ArithExpr,
            (expr_to_Z3_expr (e2, ctx, id_types)) :?> ArithExpr
        )
    | Binary(Implies, e1, e2, _) ->
        ctx.MkImplies(
            (expr_to_Z3_expr (e1, ctx, id_types)) :?> BoolExpr,
            (expr_to_Z3_expr (e2, ctx, id_types)) :?> BoolExpr
        )
    | Binary(Leq, e1, e2, _) ->
        ctx.MkLe(
            (expr_to_Z3_expr (e1, ctx, id_types)) :?> ArithExpr,
            (expr_to_Z3_expr (e2, ctx, id_types)) :?> ArithExpr
        )
    | Binary(Lt, e1, e2, _) ->
        ctx.MkLt(
            (expr_to_Z3_expr (e1, ctx, id_types)) :?> ArithExpr,
            (expr_to_Z3_expr (e2, ctx, id_types)) :?> ArithExpr
        )
    | Binary(Minus, e1, e2, _) ->
        ctx.MkSub(
            (expr_to_Z3_expr (e1, ctx, id_types)) :?> ArithExpr,
            (expr_to_Z3_expr (e2, ctx, id_types)) :?> ArithExpr
        )
    | Binary(Neq, e1, e2, _) ->
        ctx.MkDistinct((expr_to_Z3_expr (e1, ctx, id_types)), (expr_to_Z3_expr (e2, ctx, id_types)))
    | Binary(Or, e1, e2, _) ->
        ctx.MkOr((expr_to_Z3_expr (e1, ctx, id_types)) :?> BoolExpr, (expr_to_Z3_expr (e2, ctx, id_types)) :?> BoolExpr)
    | Binary(Plus, e1, e2, _) ->
        ctx.MkAdd(
            (expr_to_Z3_expr (e1, ctx, id_types)) :?> ArithExpr,
            (expr_to_Z3_expr (e2, ctx, id_types)) :?> ArithExpr
        )
    | Binary(Times, e1, e2, _) ->
        ctx.MkMul(
            (expr_to_Z3_expr (e1, ctx, id_types)) :?> ArithExpr,
            (expr_to_Z3_expr (e2, ctx, id_types)) :?> ArithExpr
        )

    | Quantification(Exists, (x, Int), e') ->
        ctx.MkExists(boundConstants = [| ctx.MkIntConst(x) |], body = (expr_to_Z3_expr (e', ctx, id_types.Add(x, Int))))
    | Quantification(Exists, (x, Bool), e') ->
        ctx.MkExists(
            boundConstants = [| ctx.MkBoolConst(x) |],
            body = (expr_to_Z3_expr (e', ctx, id_types.Add(x, Bool)))
        )
    | Quantification(Forall, (x, Int), e') ->
        ctx.MkForall(boundConstants = [| ctx.MkIntConst(x) |], body = (expr_to_Z3_expr (e', ctx, id_types.Add(x, Int))))
    | Quantification(Forall, (x, Bool), e') ->
        ctx.MkForall(
            boundConstants = [| ctx.MkBoolConst(x) |],
            body = (expr_to_Z3_expr (e', ctx, id_types.Add(x, Bool)))
        )

    | _ -> raise (InnerError("Function calls not implemented yet"))


// Convertrs a PL expression into a Z3 expression, keeping the infos for error reporting
let pl_expr_to_Z3_expr ((i: info, e: expr), ctx: Context, id_types: Map<ident, ty>) : info * Expr =
    let z3Expr = expr_to_Z3_expr (e, ctx, id_types)

    (i, z3Expr)

// COnverts a list of PL expressions into a list of Z3 expressions
let To_Z3 (el: plExpr list, ctx: Context, varmap: Map<ident, ty>) : (info * Expr) list =

    List.map (fun (i, e) -> pl_expr_to_Z3_expr ((i, e), ctx, varmap)) el
