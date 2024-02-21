module Utils

open AST
open V1AST
open V0AST
open PLAST
open ErrorInfo
open System
open Prettyprint

exception InnerError of string

// Given a body this function returns a map that associates to each identifier(of a variable) its type
let rec build_var_type_map (b: body) =
    match b with
    | [] -> Map.empty
    | Var((x, typ), _) :: t -> (build_var_type_map t).Add(x, typ)
    | _ :: t -> (build_var_type_map t)

// Given a a body this function returns a list of identifiers(of variables) that are modified in the body
let rec modified_vars_in_body (b: body) =
    let rec modifies_vars_in_stmt (c: statement) =
        match c with
        | Var((x, t), Some(e)) -> []
        | Var((x, t), None) -> []
        | Assert(_, e) -> []
        | Assume e -> []
        | Assignment(x, e) -> [ x ]
        | If(e, c1, Some(c2)) -> (modified_vars_in_body (c1)) @ (modified_vars_in_body (c2))
        | If(e, c1, None) -> (modified_vars_in_body (c1))
        | While(_, _, b') -> modified_vars_in_body (b')
        | MethodAssignment(_) -> raise (InnerError("Method assignment encoding yet to be implemented")) in

    Set.toList (Set.ofList (List.concat (List.map modifies_vars_in_stmt b)))

// This function adds a suffix to every variable in the body that bounds it to the method with name "name"
let rec bound_var_to_method_on_expr (name: ident, e: expr) : expr =
    match e with
    | Ref x -> Ref(x + "_" + name)
    | Call(f, el) -> Call(f, (List.map (fun e' -> bound_var_to_method_on_expr (name, e')) el))
    | Unary(u, e') -> Unary(u, bound_var_to_method_on_expr (name, e'))
    | Binary(b, e1, e2, i) -> Binary(b, (bound_var_to_method_on_expr (name, e1)), (bound_var_to_method_on_expr (name, e2)), i)
    | Quantification(q, (x, t), e') -> Quantification(q, (x + "_" + name, t), (bound_var_to_method_on_expr (name, e')))
    | _ -> e

// This function does the same as the previous one but it also returns the info of the expression
let rec bound_var_to_method_on_expr_with_info (name: ident, (i: info, e: expr)) =
    (i, bound_var_to_method_on_expr (name, e))

// This function adds a suffix to every variable in the body that bounds it to the method with name "name"
let rec bound_vars_to_method_on_stmt (name: ident, c: v1Statement) : v1Statement =
    match c with
    | V1Var((x, t), Some(e: expr)) -> V1Var((x + "_" + name, t), Some(bound_var_to_method_on_expr (name, e)))
    | V1Var((x, t), None) -> V1Var((x + "_" + name, t), None)
    | V1Assert(n, e) -> V1Assert(n, bound_var_to_method_on_expr (name, e))
    | V1Assume e -> V1Assume(bound_var_to_method_on_expr (name, e))
    | V1Assignment(x, e) -> V1Assignment(x + "_" + name, (bound_var_to_method_on_expr (name, e)))
    | V1Choice(c1,c2) ->
        V1Choice(
            (List.map (fun c' -> bound_vars_to_method_on_stmt (name, c')) c1),
            (List.map (fun c' -> bound_vars_to_method_on_stmt (name, c')) c2)
        )
    | V1Havoc(v) -> V1Havoc(List.map (fun (x, t) -> (x + "_" + name, t)) v)

// This function bounds every variable in the body to the method with name "name"
let bound_vars_to_method_on_body (name: ident, b: v1Body) : v1Body =
    List.map (fun c -> bound_vars_to_method_on_stmt (name, c)) b

// This function adds a prefix to variables in an expression
let rec add_prefix_to_vars_in_expr(pref : string, e : expr) = 
        match e with 
        | Ref x -> Ref(pref + "_" + x)
        | Call(f, el) -> Call(f, (List.map (fun x -> add_prefix_to_vars_in_expr(pref, x)) el))
        | Unary(u, e') -> Unary(u, add_prefix_to_vars_in_expr (pref, e'))
        | Binary(b, e1, e2, i) -> Binary(b, (add_prefix_to_vars_in_expr (pref, e1)), (add_prefix_to_vars_in_expr (pref, e2)), i)
        | Quantification(q, (x, t), e') -> Quantification(q, ((pref + "_" + x), t), (add_prefix_to_vars_in_expr (pref, e')))
        | _ -> e

// This function adds a prefix to all variables in a list given as input
let add_prefix_to_varlist(pref, vl : var list) : var list = 
    List.map (fun (x, t) -> (pref + "_" + x, t)) vl

// This function adds a prefix to variables in  a body
let rec add_prefix_to_vars(pref : string, b : body option)  : body =
    let rec add_prefix_to_vars_in_stmt(stmt : statement) : statement =
        match stmt with 
        | Var((x, t), Some(e)) -> Var(((pref + "_" + x), t), Some(add_prefix_to_vars_in_expr(pref, e)))
        | Var((x, t), None) -> Var(((pref + "_" + x), t), None)
        | Assert(n, e) -> Assert(n, add_prefix_to_vars_in_expr (pref, e))
        | Assume e -> Assume(add_prefix_to_vars_in_expr (pref, e))
        | Assignment(x, e) -> Assignment((pref + "_" + x), (add_prefix_to_vars_in_expr (pref, e)))
        | If(e, b1, Some(b2)) -> If((add_prefix_to_vars_in_expr (pref, e)), (add_prefix_to_vars(pref, Some b1)), Some(add_prefix_to_vars(pref, Some b2)))
        | If(e, b1, None) -> If((add_prefix_to_vars_in_expr (pref, e)), (add_prefix_to_vars(pref, Some b1)), None)
        | While(e, invs, b') -> 
            While((add_prefix_to_vars_in_expr (pref, e)),
                   (List.map (fun spec -> 
                        match spec with
                        | Invariant(i, e) -> Invariant(i, add_prefix_to_vars_in_expr (pref, e))
                        | Variant(i, e) -> Variant(i, add_prefix_to_vars_in_expr (pref, e))
                    ) invs),
                   (add_prefix_to_vars(pref, Some b'))) 
        | MethodAssignment(id_list, m, args, inf) ->
            MethodAssignment(List.map (fun x -> pref + "_" + x) id_list, 
                            m,
                            (List.map (fun e -> add_prefix_to_vars_in_expr(pref, e)) args), inf)
    in 
    match b with 
        | None -> []
        | Some b -> List.map add_prefix_to_vars_in_stmt b

// This function takes as input an expression and a list of couples (x, e) and substitutes every occurrence of x with e in the expression given as input
let rec subst_idents_in_expr(e : expr, couples : (ident * expr) list) : expr = 
    match e with 
    | Ref x -> 
        //Console.WriteLine("Couples: {0}, trying to find {1}", couples, x)
        (match List.tryFind (fun (x', y') -> x' = x) couples with 
        | Some (x', y') -> y'
        | None -> Ref x)
    | Call(f, el) -> Call(f, (List.map (fun e' -> subst_idents_in_expr(e', couples)) el))
    | Unary(u, e') -> Unary(u, subst_idents_in_expr(e', couples))
    | Binary(b, e1, e2, i) -> Binary(b, (subst_idents_in_expr(e1, couples)), (subst_idents_in_expr(e2, couples)), i)
    | Quantification(q, (x, t), e') -> raise(InnerError("Quantification in the method assignment should not be possible"))
    | _ -> e

let rec denominators_in_expression(e : expr) : (expr * (info)) list = 
    match e with 
    | Binary(Divide, e1, e2, i) -> [Binary(Neq, e2, Integer "0", i), {i with error_type = Some(DivByZeroError(Some(string_of_expr_without_prefix(e2, "my_"))))}] @ (denominators_in_expression e1) @ (denominators_in_expression e2)
    | Binary(Implies, e1, e2, i) -> (denominators_in_expression e1) @ (List.map (fun (e', i') -> (Binary(Implies, e1, e', i')),i) (denominators_in_expression e2))
    | Binary(_, e1, e2, _) -> (denominators_in_expression e1) @ (denominators_in_expression e2)
    | Unary(_, e') -> denominators_in_expression e'
    | Call(_, el) -> List.concat (List.map denominators_in_expression el)
    | Quantification(q, (x, t), e') -> denominators_in_expression e'
    | _ -> []