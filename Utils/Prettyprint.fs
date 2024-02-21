module Prettyprint

open AST
open V1AST
open V0AST
open PLAST
open ErrorInfo
open System

exception InnerError of string


let string_of_error_type (e: verification_error) =
    match e with
    | AssertionError(Some(s)) -> $"assert {s} might not hold"
    | PreconditionError(Some(s)) -> $"requires {s} might not hold"
    | PostconditionError(Some(s)) -> $"ensures {s} might not hold"
    | InvariantEntryError(Some(s)) -> $"invariant {s} might not hold on entry"
    | InvariantHoldingError(Some(s)) -> $"invariant {s} might not be preserved"
    | WhileVariantError(Some(s)) -> $"decreases {s} might not hold"
    | MethodPreconditionError(Some(s)) -> $"requires {s} might not hold"
    | MethodVariantDecreasingError(_) -> $"method might not terminate. Variant might not be decreased"
    | MethodVariantGTZeroError(Some(s)) -> $"method might not terminate. {s} might not be >= 0"
    | DivByZeroError(Some s) -> $"Division by zero: {s} might be zero"
    | DivByZeroError(_) ->  "erorr div"
    | AssertionError(_) -> $"Erorr assert"
    | PreconditionError(_) -> $"error precond"
    | PostconditionError(_) -> $"erorr postcond"
    | InvariantEntryError(_) -> $"erorr inv entry"
    | InvariantHoldingError(_) -> $"erorr inv holding"
    | WhileVariantError(_) -> $"error while variant"
    | MethodVariantGTZeroError(_) -> $"error method var gt zero"

let string_of_info
    ({ method_name = m
       no_line = nol
       error_type = e }: info)
    =

    let s_err = 
        match e with
            | None -> ""
            | Some e' -> string_of_error_type (e')

    match m with
    | Some(m_name) -> $"Method {m_name}(), line {nol}: {s_err}"
    | None -> $"no_method, line {nol}: {s_err}"


let string_of_uop (u: uop) =
    match u with
    | UMinus -> "-"
    | Neg -> "!"

let string_of_bop (b: bop) =
    match b with
    | And -> " && "
    | Divide -> " / "
    | Eq -> " == "
    | Geq -> " >= "
    | Gt -> " > "
    | Implies -> " ==> "
    | Leq -> " <= "
    | Lt -> " < "
    | Minus -> " - "
    | Neq -> " != "
    | Or -> " || "
    | Plus -> " + "
    | Times -> " * "

let string_of_var ((id, t): var) =
    match t with
    | Int -> id + ": Int"
    | Bool -> id + ": Bool"

let string_of_var_without_pref((id : ident, t : ty), pref : string) : string = 
    let (|Prefix|_|) (p:string) (s:string) =
        if s.StartsWith(p) then
            Some(s.Substring(p.Length))
        else
            None
    in 
    match t with 
    | Int -> 
        match id with 
        | Prefix(pref) rest -> 
            rest + ": Int"
        | _ -> 
            id + ": Int"
    | Bool -> 
        match id with 
        | Prefix(pref) rest -> 
            rest + ": Bool"
        | _ -> 
            id + ": Bool"

let string_of_quantifier (q: quantifier) =
    match q with
    | Exists -> "exists"
    | Forall -> "forall"

//This functon is used to print the expression without the prefix in the variables
let rec string_of_expr_without_prefix(e : expr , pref : string) : string = 
    let (|Prefix|_|) (p:string) (s:string) =
        if s.StartsWith(p) then
            Some(s.Substring(p.Length))
        else
            None
    in 

    match e with 
    | Boolean true -> "true"
    | Boolean false -> "false"
    | Integer i -> i
    | Result -> "result??"
    | Ref x -> 
        match x with
        | Prefix(pref) rest -> rest
        | _ -> x

    | Call(x, el) -> x + "(" + (List.fold (+) "" (List.map (fun x -> string_of_expr_without_prefix(x, pref)) el)) + ")"
    | Unary(u, e) -> 
        match e with
            | Boolean _ -> (string_of_uop u) + (string_of_expr_without_prefix(e, pref))
            | Integer _ -> (string_of_uop u) + (string_of_expr_without_prefix(e, pref))
            | Ref x -> (string_of_uop u) + (string_of_expr_without_prefix(Ref x, pref))
            | _ -> (string_of_uop u) + "(" + (string_of_expr_without_prefix(e, pref)) + ")"
    | Binary(b, e1, e2, _) ->
        match b with 
            | Eq -> string_of_expr_without_prefix(e1, pref) + (string_of_bop b) + string_of_expr_without_prefix(e2, pref)
            | _ -> 
                match e1, e2 with 
                    | Ref x, Ref y -> (string_of_expr_without_prefix(Ref x, pref)) + (string_of_bop b) + (string_of_expr_without_prefix(Ref y, pref))

                    | Ref x, Boolean _ -> (string_of_expr_without_prefix(Ref x, pref)) + (string_of_bop b) + (string_of_expr_without_prefix(e2, pref))
                    | Ref x, Integer _ -> (string_of_expr_without_prefix(Ref x, pref)) + (string_of_bop b) + (string_of_expr_without_prefix(e2, pref))
                    | Ref x, _ -> (string_of_expr_without_prefix(Ref x, pref)) + (string_of_bop b) + "(" + (string_of_expr_without_prefix(e2, pref)) + ")"

                    | Boolean _, Ref y -> (string_of_expr_without_prefix(e1, pref)) + (string_of_bop b) + (string_of_expr_without_prefix(Ref y, pref))
                    | Integer _, Ref y -> (string_of_expr_without_prefix(e1, pref)) + (string_of_bop b) + (string_of_expr_without_prefix(Ref y, pref))
                    | _ , Ref y -> "(" + (string_of_expr_without_prefix(e1, pref)) + ")" + (string_of_bop b) + (string_of_expr_without_prefix(Ref y, pref))

                    | Integer _, Boolean _ -> (string_of_expr_without_prefix(e1, pref)) + (string_of_bop b) + (string_of_expr_without_prefix(e2, pref))
                    | Boolean _, Integer _ -> (string_of_expr_without_prefix(e1, pref)) + (string_of_bop b) + (string_of_expr_without_prefix(e2, pref))
                    | Integer _, Integer _ -> (string_of_expr_without_prefix(e1, pref)) + (string_of_bop b) + (string_of_expr_without_prefix(e2, pref))
                    | Boolean _, Boolean _ -> (string_of_expr_without_prefix(e1, pref)) + (string_of_bop b) + (string_of_expr_without_prefix(e2, pref))

                    | Integer _, _ -> (string_of_expr_without_prefix(e1, pref)) + (string_of_bop b) + "(" + (string_of_expr_without_prefix(e2, pref)) + ")"
                    | Boolean _, _ -> (string_of_expr_without_prefix(e1, pref)) + (string_of_bop b) + "(" + (string_of_expr_without_prefix(e2, pref)) + ")"

                    | _, Integer _ -> "(" + (string_of_expr_without_prefix(e1, pref)) + ")" + (string_of_bop b) + (string_of_expr_without_prefix(e2, pref)) 
                    | _, Boolean _ -> "(" + (string_of_expr_without_prefix(e1, pref)) + ")" + (string_of_bop b) + (string_of_expr_without_prefix(e2, pref))

                    | _ -> "(" + (string_of_expr_without_prefix(e1, pref)) + ")" + (string_of_bop b) + "(" + (string_of_expr_without_prefix(e2, pref)) + ")"
    
    | Quantification(q, v, e) -> (string_of_quantifier q) + " " + (string_of_var_without_pref(v, pref)) + " :: " + (string_of_expr_without_prefix(e, pref))  


let rec string_of_expr (e: expr) =

    match e with
    | Boolean true -> "true"
    | Boolean false -> "false"
    | Integer i -> i
    | Result -> "result??"
    | Ref x -> x
    | Call(x, el) -> x + "(" + (List.fold (+) "" (List.map string_of_expr el)) + ")"
    | Unary(u, e) -> 
        match e with
            | Boolean _ -> (string_of_uop u) + (string_of_expr e)
            | Integer _ -> (string_of_uop u) + (string_of_expr e)
            | Ref x -> (string_of_uop u) + x
            | _ -> (string_of_uop u) + "(" + (string_of_expr e) + ")"
    | Binary(b, e1, e2, _) -> 
        match b with 
            | Eq -> string_of_expr e1 + (string_of_bop b) + string_of_expr e2
            | _ -> 
                match e1, e2 with 
                    | Ref x, Ref y -> x + (string_of_bop b) + y

                    | Ref x, Boolean _ -> x + (string_of_bop b) + (string_of_expr e2)
                    | Ref x, Integer _ -> x + (string_of_bop b) + (string_of_expr e2)
                    | Ref x, _ -> x + (string_of_bop b) + "(" + (string_of_expr e2) + ")"

                    | Boolean _, Ref y -> (string_of_expr e1) + (string_of_bop b) + y
                    | Integer _, Ref y -> (string_of_expr e1) + (string_of_bop b) + y
                    | _ , Ref y -> "(" + (string_of_expr e1) + ")" + (string_of_bop b) + y

                    | Integer _, Boolean _ -> (string_of_expr e1) + (string_of_bop b) + (string_of_expr e2)
                    | Boolean _, Integer _ -> (string_of_expr e1) + (string_of_bop b) + (string_of_expr e2)
                    | Integer _, Integer _ -> (string_of_expr e1) + (string_of_bop b) + (string_of_expr e2)
                    | Boolean _, Boolean _ -> (string_of_expr e1) + (string_of_bop b) + (string_of_expr e2)

                    | Integer _, _ -> (string_of_expr e1) + (string_of_bop b) + "(" + (string_of_expr e2) + ")"
                    | Boolean _, _ -> (string_of_expr e1) + (string_of_bop b) + "(" + (string_of_expr e2) + ")"

                    | _, Integer _ -> "(" + (string_of_expr e1) + ")" + (string_of_bop b) + (string_of_expr e2)
                    | _, Boolean _ -> "(" + (string_of_expr e1) + ")" + (string_of_bop b) + (string_of_expr e2)

                    | _ -> "(" + (string_of_expr e1) + ")" + (string_of_bop b) + "(" + (string_of_expr e2) + ")"
    
    | Quantification(q, v, e) -> (string_of_quantifier q) + " " + (string_of_var v) + " :: " + (string_of_expr e)

let string_of_while_spec (w: while_spec) =
    match w with
    | Invariant(i, e) -> "invariant " + (string_of_expr e)
    | Variant(i, e) -> "decreases " + (string_of_expr e)

let rec string_of_micro_statement (c: statement) =
    match c with
    | Var(v, Some(e)) -> (string_of_var v) + " := " + (string_of_expr e)
    | Var(v, None) -> string_of_var v
    | Assert(inf, e) -> "assert " + string_of_expr e
    | Assume e -> "assume " + string_of_expr e
    | Assignment(i, e) -> i + " := " + (string_of_expr e)
    | If(be, c1, Some(c2)) ->
        "If("
        + (string_of_expr be)
        + "){\n"
        + (String.concat "\n" (List.map string_of_micro_statement c1))
        + "\n}\n"
        + "else{\n"
        + (String.concat "\n" (List.map string_of_micro_statement c2))
        + "\n}"
    | If(be, c1, None) ->
        "If("
        + (string_of_expr be)
        + "){\n"
        + (String.concat "\n" (List.map string_of_micro_statement c1))
        + "\n}\n"
    | While(be, invs, b) ->
        "While("
        + (string_of_expr be)
        + ")"
        + (String.concat "\n" (List.map string_of_while_spec invs))
        + "{\n"
        + (String.concat "\n" (List.map string_of_micro_statement b))
        + "\n}"
    | MethodAssignment(ass, m, par, _) ->
        let str_of_params = String.concat "," (List.map string_of_expr par)

        (String.concat ", " ass )
        + " := " 
        + m + "(" + str_of_params + ")"


let string_of_body (b) =
    String.concat "\n" (List.map (string_of_micro_statement) b)

let string_of_body_opt (bo: body option) =
    match bo with
    | Some b -> string_of_body b
    | None -> ""

let string_of_spec (s: spec) =
    match s with
    | Requires e -> "requires " + (string_of_expr e)
    | Ensures(i, e) -> "ensures " + (string_of_expr e)
    | Decreases(_, e) -> "decreases " + (string_of_expr e)
let string_of_method
    ({ name = i
       inputs = inp
       outputs = outs
       specifications = specs
       body = b })
    =
    "method "
    + i
    + "("
    + (String.concat "," (List.map string_of_var inp))
    + ") : "
    + (String.concat "," (List.map string_of_var outs))
    + (String.concat "\n" (List.map string_of_spec specs))
    + "\n{\n"
    + (string_of_body_opt b)
    + "\n}"

let string_of_document_item (di) =
    match di with
    | Method m -> string_of_method m
    | Function f -> raise (InnerError("Still have to implement printing for functions"))

let string_of_document (d: document) =
    String.concat "\n" (List.map string_of_document_item d)




// ----------------- Print functions for IVL1 -----------------
let rec string_of_IVL1_statement (c: v1Statement) =
    match c with
    | V1Var(v, Some(e)) -> (string_of_var v) + " := " + (string_of_expr e)
    | V1Var(v, None) -> string_of_var v
    | V1Assert(i, e) -> "assert " + string_of_expr e
    | V1Assume e -> "assume " + string_of_expr e
    | V1Assignment(i, e) -> i + " := " + (string_of_expr e)
    | V1Choice(c1, c2) ->
        "{"
        + (String.concat "\n" (List.map string_of_IVL1_statement c1))
        + "}"
        + "\n"
        + "[]"
        + "\n"
        + "{"
        + (String.concat "\n" (List.map string_of_IVL1_statement c2))
        + "}"
    | V1Havoc(vl) -> "havoc " + (String.concat ", " (List.map string_of_var vl))

let string_of_IVL1_body (b: v1Body) =
    String.concat "\n" (List.map string_of_IVL1_statement b)

let string_of_IVL1_method ({ V1name = i; V1body = b }: v1method) =

    "method " + i + "{\n" + (string_of_IVL1_body b) + "\n}"

let string_of_IVL1_document_item (di: v1_document_item) =
    match di with
    | V1Method m -> string_of_IVL1_method m
    | _ -> raise (InnerError("Functions in IVL1 not implemented yet"))

let string_of_IVL1_document (d: v1_document) =
    String.concat "\n" (List.map string_of_IVL1_document_item d)

// ----------------- Print functions for DSA -----------------

let rec string_of_dsa_statement (c: DSAStatement) =
    match c with
    | DSAVar(v, Some(e)) -> (string_of_var v) + " := " + (string_of_expr e)
    | DSAVar(v, None) -> string_of_var v
    | DSAAssert(i, e) -> "assert " + (string_of_expr e)
    | DSAAssume e -> "assume " + (string_of_expr e)
    | DSAAssignment(i, e) -> i + " := " + (string_of_expr e)
    | DSAChoice(c1, c2) ->
        "{"
        + (String.concat "\n" (List.map string_of_dsa_statement c1))
        + "}"
        + "\n"
        + "[]"
        + "\n"
        + "{"
        + (String.concat "\n" (List.map string_of_dsa_statement c2))
        + "}"

let string_of_dsa_body (b: DSABody) =
    String.concat "\n" (List.map string_of_dsa_statement b)

let string_of_dsa_method ({ DSAname = i; DSAbody = b }: DSAmethod) =

    "method " + i + "{\n" + (string_of_dsa_body b) + "\n}"

let string_of_dsa_document_item (di: DSA_document_item) =
    match di with
    | DSAMethod m -> string_of_dsa_method m
    | _ -> raise (InnerError("Still have to implement DSA functions"))

let string_of_dsa_document (d: DSA_document) =
    String.concat "\n" (List.map string_of_dsa_document_item d)


// ----------------- Print functions for IVL0 -----------------

let rec string_of_v0_statement (c: v0Statement) =
    match c with
    | V0Var(v, Some(e)) -> (string_of_var v) + " := " + (string_of_expr e)
    | V0Var(v, None) -> string_of_var v
    | V0Assert(i, e) -> "assert " + (string_of_expr e)
    | V0Assume e -> "assume " + (string_of_expr e)
    | V0Choice(c1, c2) ->
        "{"
        + (String.concat "\n" (List.map string_of_v0_statement c1))
        + "}"
        + "\n"
        + "[]"
        + "\n"
        + "{"
        + (String.concat "\n" (List.map string_of_v0_statement c2))
        + "}"

let string_of_v0_body (b: v0Body) =
    String.concat "\n" (List.map string_of_v0_statement b)

let string_of_v0_method ({ V0name = i; V0body = b }: v0method) =

    "method " + i + "{\n" + (string_of_v0_body b) + "\n}"

let string_of_v0_document_item (di: v0_document_item) =
    match di with
    | V0Method m -> string_of_v0_method m
    | _ -> raise (InnerError("Still have to implement IVL0 functions"))

let string_of_v0_document (d: v0_document) =
    String.concat "\n" (List.map string_of_v0_document_item d)


// ----------------- Print functions for PL -----------------
let string_of_plExpr ((i, e): plExpr) : string =
    $"{string_of_expr (e)}, errorinfo: {string_of_info (i)}"


let print_check_result (res: check_result) =
    match res with
    | True -> Console.WriteLine("Passed")
    | False(err_list) -> Console.WriteLine(String.concat "\n" (List.map (string_of_info) err_list))
