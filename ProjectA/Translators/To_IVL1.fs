module To_IVL1

open AST
open V1AST
open System
open ErrorInfo
open Prettyprint
open Utils

exception InnerError of string

// This function encodes ensures and requires into asserts and assumes
let spec_to_stmt (s: spec) =
    match s with
    | Requires e -> Assume e
    | Ensures(inf, e) -> Assert(inf, e)
    | _ -> raise (InnerError("there shouldn't be any decreases here"))

// This function takes a body in microAST and returns an encoded body in IVL1 AST
let rec micro_body_to_IVL1(b : body, type_map : Map<ident, ty>, method_name : ident, method_list : method list) : v1Body * Map<ident, ty> = 
    
    // This function encodes a statement in microviper into IVL1 
    let rec micro_stmt_to_ILV1 (cmd: statement, type_map: Map<ident, ty>, method_name: ident, methods_list : method list) : (v1Statement list) * Map<ident, ty> =

        // builds the info based on the method name, expression given as an InvariantEntryError
        let info_to_entry_error (i: info, e: expr) =
            { method_name = Some(method_name)
              no_line = i.no_line
              error_type = Some (InvariantEntryError(Some(string_of_expr_without_prefix(e, "my_")))) }

        // builds the info based on the method name, expression given as an InvariantHoldingError
        let info_to_holding_error (i: info, e: expr) =
            { method_name = Some(method_name)
              no_line = i.no_line
              error_type = Some(InvariantHoldingError(Some(string_of_expr_without_prefix(e, "my_")))) }


        // This function performs the encoding of a while statement
        let encode_while (e, invs: while_spec list, b') : v1Body * Map<ident, ty> =

            // List of modified variables in the while's body with their types
            let mod_vars = modified_vars_in_body (b') in
            let mod_vars = List.map (fun x -> (x, type_map.Item(x))) mod_vars in

            // List of invariants with info relative to entry error
            let invs_asserts_entry =
                List.map (fun spec ->
                    match spec with
                    | Invariant(i, e) -> V1Assert((info_to_entry_error (i, e)), e)
                    | Variant(i, e) -> raise(InnerError("Variants of while should be removed before"))) invs

            // List of invariants with info relative to holding error
            let invs_asserts_holding =
                List.map (fun spec ->
                    match spec with
                    | Invariant(i, e) -> V1Assert((info_to_holding_error (i, e)), e)
                    | Variant(i, e) -> raise(InnerError("Variants of while should be removed before"))) invs

            // List of invariants encoded into assumes
            let invs_assumes = 
                List.map (fun spec ->
                    match spec with
                    | Invariant(i, e) -> V1Assume e
                    | Variant(i, e) -> raise(InnerError("Variants of while should be removed before"))) invs

            // Final encoding of the whole while statement
            invs_asserts_entry
            @ [ V1Havoc(mod_vars) ]
            @ invs_assumes
            @ [ V1Choice(
                    [ V1Assume(e) ]
                    @ fst (micro_body_to_IVL1(b', type_map, method_name, methods_list))
                    @ invs_asserts_holding
                    @ [ V1Assume(AST.Boolean(false)) ],

                    [ V1Assume(Unary(Neg, e)) ]
                )], type_map

        in

        // This function encodes a method assignment into IVL1
        let encode_method_assignment(assigned : ident list, m : ident, params_given : expr list, met : method, inf : info) : v1Statement list = 

            // identificators of the inputs and outputs of the method
            let idents_of_met_inputs = List.map (fun (id, _) -> id) met.inputs in
            let idents_of_met_outputs = List.map (fun (id, _) -> id) met.outputs in

            // zip between the inputs of the method and the parameters given to the method
            let inputs_params_zip = List.zip idents_of_met_inputs params_given 
            
            // zip between the outputs of the method and the assigned variables to the method call
            let outputs_assigned_zip = List.zip idents_of_met_outputs (List.map (fun x -> Ref x) assigned)

            // preconditions and postconditions of the method
            let preconds_of_met = List.filter (fun s -> match s with | Requires _ -> true | _ -> false) met.specifications
            let postconds_of_met = List.filter (fun s -> match s with | Ensures _ -> true | _ -> false) met.specifications

            // Assertions encoding the preconditions of the method call
            let preconds_of_call = 
                List.map (fun p -> subst_idents_in_expr(p, inputs_params_zip)) (List.map (fun p -> match p with Ensures(_, e) -> e | Decreases(_, e) -> e | Requires e -> e) preconds_of_met)
                |> List.map (fun e -> V1Assert({inf with method_name = Some(method_name); error_type = Some(MethodPreconditionError(Some(string_of_expr_without_prefix (e, "my_"))))}, e))
            
            // variables to store values of the params before method call
            let old_vars = 
                List.map (fun (x, t) -> ("old_" + x, t)) met.inputs
            
            let old_vars_with_vals = List.zip old_vars params_given

            // Declarations of the variables to store values of the params before method call
            let old_vars_decls = List.map (fun ((x, t), e) -> V1Var((x, t), Some(e))) old_vars_with_vals

            // zip between the inputs of the method and the variables storing the values of the params before method call
            let inputs_oldInputs_zip = List.zip idents_of_met_inputs (List.map (fun (x, t) -> Ref x) old_vars) 

            // variables with types of assigned idents for method call
            let var_of_assigned = 
                List.map 
                    (fun v -> 
                        match type_map.TryFind v with
                            | Some t -> (v, t)
                            | None -> raise(InnerError("Error in the method assignment encoding"))
                    ) assigned

            // Assumes encoding the postconditions of the method call(with substituted idents)
            let postconds_of_call = 
                //Console.WriteLine("Postconds of met: {0}", postconds_of_met)
                List.map (fun p -> subst_idents_in_expr(p, inputs_oldInputs_zip)) (List.map (fun p -> match p with Ensures(_, e) -> e | Decreases(_, e) -> e| Requires e -> e) postconds_of_met)
                |> List.map (fun p -> subst_idents_in_expr(p, outputs_assigned_zip))
                |> List.map (fun e -> V1Assume(e))


            // Final encoding of method assignment
            preconds_of_call
            @ old_vars_decls
            @ [V1Havoc(var_of_assigned)]
            @ postconds_of_call

            
        // List of encodings of the statements
        match cmd with
        | Var((x, t), e) -> [ V1Var((x, t), e) ], type_map.Add(x, t)
        | Assert(i, e) -> [ V1Assert(i, e) ], type_map
        | Assume e -> [ V1Assume e ], type_map
        | Assignment(x, e) -> [ V1Assignment(x, e) ], type_map

        | If(e, b1, Some(b2)) ->
            [ V1Choice(
                [ V1Assume(e) ]
                @ fst (micro_body_to_IVL1(b1, type_map, method_name, methods_list)), 
                [ V1Assume(Unary(Neg, e)) ]
                @ fst (micro_body_to_IVL1(b2, type_map, method_name, methods_list))
            ) ], type_map
        | If(e, b1, None) ->
            [ V1Choice(
                [ V1Assume(e) ]
                @ fst (micro_body_to_IVL1(b1, type_map, method_name, methods_list)),
                []
            ) ], type_map

        | MethodAssignment(outs, m, inps, inf) -> 

            let met : method = List.find (fun m' -> m'.name = m) methods_list in
            encode_method_assignment (outs, m, inps, met, inf), type_map

        | While(e, invs, b') -> encode_while (e, invs, b')


    // Recursively encodes the statements in the body
    match b with 
    | [] -> [], type_map
    | h :: t -> 
        let (h', type_map') = micro_stmt_to_ILV1(h, type_map, method_name, method_list)
        let (t', type_map'') = micro_body_to_IVL1(t, type_map', method_name, method_list)
        h' @ t', type_map''


// This functions takes a method as input and updates the info of the asserts and ensures with the method name and relative expressions
let update_errors_info
    (({ name = name
        inputs = inp
        outputs = outs
        specifications = specs
        body = b }))
    : method =

    // Updates the info of the asserts in the body
    let rec update_body (bd: body) =
        match bd with
        | [] -> []
        | Assert({ method_name = mn
                   no_line = i
                   error_type = err },
                 e) :: t ->
            Assert(
                { method_name = Some(name)
                  no_line = i
                  error_type = Some(AssertionError(Some(string_of_expr e))) },
                e
            )
            :: (update_body t)
        | If(ex, c1, Some(c2)) :: t -> If(ex, update_body (c1), Some(update_body (c2))) :: (update_body t)
        | If(ex, c1, None) :: t -> If(ex, update_body (c1), None) :: (update_body t)
        | While(be, invs, b') :: t -> While(be, invs, update_body (b')) :: (update_body t)

        | c :: t -> c :: update_body (t)

    // Updates the info of the ensures in the specifications
    let rec update_specs (s: spec list) =
        match s with
        | [] -> []
        | (Ensures({ method_name = _
                     no_line = i
                     error_type = _ },
                   e)) :: t ->
            Ensures(
                { method_name = Some(name)
                  no_line = i
                  error_type = Some(PostconditionError(Some(string_of_expr e))) },
                e
            )
            :: (update_specs t)
        | h :: t -> h :: update_specs (t)


    let updt_body =
        (match b with
         | Some(b') -> Some(update_body (b'))
         | None -> None)

    let updt_specs = update_specs specs

    // returns the updated method
    { name = name
      inputs = inp
      outputs = outs
      specifications = updt_specs
      body = updt_body }


// This function encodes a method from microviper to IVL1
let micro_method_to_IVL1
    ({ name = n
       inputs = i
       outputs = o
       specifications = s
       body = b }, methods_list: method list)
    =

    // If the method is abstract we dont actually need to check it on Z3 so we keep track of that
    let is_abstract = match b with | None -> true | _ -> false

    let inputs_origs_zip = List.zip (List.map (fun (id, typ) -> $"my_{id}") i) (List.map (fun (id, _) -> Ref $"orig_my_{id}") i)

    // Convert the specifications into statements
    let rec body_with_spec (b: body , s': statement list) =
        (match s' with
            | [] -> b
            | Assume(e) :: [] -> Assume(e) :: b
            | Assert(n, e) :: [] -> b @ [ Assert(n, (subst_idents_in_expr(e, inputs_origs_zip))) ]
            | Assume(e) :: t -> body_with_spec ((Assume(e) :: b), t)
            | Assert(n, e) :: t -> body_with_spec(b @ [ Assert(n, (subst_idents_in_expr(e, inputs_origs_zip))) ], t)
            | _ -> raise (InnerError("Incorrect specs")))
        
    // This function encodes the variants into statements in microviper
    let rec add_variants_stmts_to_body(b : body, v : spec, counter : int) : body = 

        // For every recursive call to the method n we have to add the termination assertions
        let rec add_assertions_before_recursive_call(b : body, variant_name : string, e : expr) : body = 
            let idents_of_input = List.map (fun (id, _) -> id) i

            match b with 
            | [] -> []
            | MethodAssignment(assigned, n, params_call, info_call)::t -> 
                let input_params_zip = List.zip idents_of_input params_call
                let termination_assertion = Assert({info_call with method_name = Some n; error_type = Some(MethodVariantDecreasingError(None))}, Binary(Lt,subst_idents_in_expr(e, input_params_zip) , Ref variant_name, info_call))
                termination_assertion :: MethodAssignment(assigned, n, params_call, info_call) :: (add_assertions_before_recursive_call(t, variant_name, e))
            
            | If(b, c1, Some(c2))::t -> 
                If(b, 
                    (add_assertions_before_recursive_call(c1, variant_name, e)),
                    Some(add_assertions_before_recursive_call(c2, variant_name, e))
                )::(add_assertions_before_recursive_call(t, variant_name, e))
            
            | If(b, c1, None)::t -> 
                If(b, 
                    (add_assertions_before_recursive_call(c1, variant_name, e)),
                    None
                )::(add_assertions_before_recursive_call(t, variant_name, e))
            | While(cond, invs, bod)::t -> 
                While(
                    cond, invs,
                    (add_assertions_before_recursive_call(bod, variant_name, e))
                )::(add_assertions_before_recursive_call(t, variant_name, e))

            | h :: t -> 
                h :: (add_assertions_before_recursive_call(t, variant_name, e))

        // For every decreases we construct a variant variable and add the assertions before every recursive call
        match v with 
            | Decreases(i, e) -> 
                let new_inf = {i with method_name = Some n; error_type = Some(MethodVariantGTZeroError(Some(string_of_expr_without_prefix(e, "my_"))))}
                [Var(($"variant_{counter}", Int), Some(add_prefix_to_vars_in_expr("my", e))) ; Assert(new_inf, Binary(Geq, Ref $"variant_{counter}", Integer "0", new_inf))]
                @ add_assertions_before_recursive_call(b, $"variant_{counter}", e)
            | _ -> raise (InnerError("Incorrect specs to add variants"))    
    
    // This function adds the variants encodings into the body
    let rec body_with_variants(b : body, s : spec list, counter : int) =
        match s with
        | [] -> b
        | Decreases(inf, e) :: t -> 
            body_with_variants(add_variants_stmts_to_body(b, Decreases(inf, e), counter), t, counter + 1)
        | h :: t -> body_with_variants (b, t, counter)
    
    // This function adds the loop variants into the body of the method
    let rec body_with_while_variants(b : body, counter : int) : body * int = 
        let rec add_while_variants_statements_to_body(b : body, specs : while_spec list, counter : int ) : body * int  = 
            match specs with
                | [] -> b, counter
                | Invariant(_, _):: t-> add_while_variants_statements_to_body(b, t, counter)
                | Variant(inf, e)::t ->
                    let new_inf = {inf with method_name = Some n; error_type = Some(WhileVariantError(Some(string_of_expr_without_prefix(e, "my_"))))}
                    let new_body, new_counter = add_while_variants_statements_to_body(b, t, counter + 1)
                    
                    [Var(($"while_variant_{counter}", Int), Some e); Assert(new_inf, Binary(Geq, Ref $"while_variant_{counter}", Integer "0", new_inf))]
                    @ new_body
                    @ [Assert(new_inf, Binary(Lt, e, Ref $"while_variant_{counter}", new_inf))], counter + 1
            
        
        match b with
            | [] -> [], counter
            | While(cond, specs, bod) :: rest -> 
                let spec_wo_variants = List.filter (fun x -> match x with | Variant(_, _) -> false | _ -> true) specs
                let new_body, new_counter = add_while_variants_statements_to_body(bod, specs, counter)
                let new_body', new_counter' = body_with_while_variants(new_body, new_counter)
                let new_rest, final_counter = body_with_while_variants(rest, new_counter')
               
                While(
                    cond, 
                    spec_wo_variants, 
                    new_body'
                )::new_rest , final_counter
            
            | If(cond, c1, Some(c2)) :: rest ->
                let new_c1, new_counter = body_with_while_variants(c1, counter)
                let new_c2, final_counter = body_with_while_variants(c2, new_counter)
                let new_rest, final_counter' = body_with_while_variants(rest, final_counter)
                If(cond, new_c1, Some(new_c2))::new_rest, final_counter'
            
            | If(cond, c1, None) :: rest ->
                let new_c1, new_counter = body_with_while_variants(c1, counter)
                let new_rest, final_counter' = body_with_while_variants(rest, new_counter)
                If(cond, new_c1, None)::new_rest, final_counter'
            
            | h :: t -> 
                let new_t, new_counter = body_with_while_variants(t, counter)
                h :: new_t, new_counter

    
    // Adds the assertions for Division by zero error
    let rec body_with_divbyzero_checks(b : body) : body = 
        let build_assertions(e : expr) = 
            let denominators = denominators_in_expression e
            let assertions = 
                List.map (fun (ex, i) -> Assert(
                    {i with method_name = Some n}, 
                     ex)) denominators
                in

                assertions

        let rec add_divbyzero_checks_to_stmt(stmt : statement) : statement list = 
            match stmt with 
            | Var((id, typ), Some e) -> 
                
                build_assertions(e) @ [Var((id, typ), Some e)]

            | Assert(i, e) -> 
                
                build_assertions(e) @ [Assert(i, e)]
            
            | Assume(e) -> 
                
                build_assertions(e) @ [Assume(e)]
            
            | Assignment(i, e) -> 
                build_assertions(e) @ [Assignment(i, e)]
            
            |MethodAssignment(ids, m, el, i) -> 
                List.concat (List.map build_assertions el) @ [MethodAssignment(ids, m, el, i)]

            | If(e, b1, Some(b2)) ->
                build_assertions(e) @ [If(e, add_divbyzero_checks_to_body(b1), Some(add_divbyzero_checks_to_body(b2)))]

            | If(e, b1, None) -> 
                build_assertions(e) @ [If(e, add_divbyzero_checks_to_body(b1), None)]

            | While(e, invs, b') -> 
                let spec_assertions = 
                    List.concat 
                        (List.map 
                            (fun sp -> match sp with Invariant(i, e) -> build_assertions e | Variant(i, e) -> build_assertions e) 
                            invs)

                build_assertions(e) @ spec_assertions @ [While(e, invs, add_divbyzero_checks_to_body(b'))]
                
            | _ -> [stmt]
        
        and add_divbyzero_checks_to_body(b : body) : body = 
            match b with 
            | [] -> []
            | h :: t -> add_divbyzero_checks_to_stmt(h) @ add_divbyzero_checks_to_body(t)
        
        add_divbyzero_checks_to_body(b)


    // Add the inputs and outputs declaratoins to the body
    let rec body_with_inputs_outputs(io : var list, b : body) : body =
        match io with
        | [] -> b
        | (id, typ) :: t -> (Var((id, typ), None)) :: (body_with_inputs_outputs(t, b))
    
    // Add the declarations of the original inputs to the body (to enables input re-assignments)
    let rec body_with_orig_inputs_declared(b : body) : body = 
        let orig_input_decls = 
            List.concat (List.map (fun (id, typ) -> [Var(($"orig_my_{id}", typ), Some(Ref($"my_{id}")))]) i)
        
        orig_input_decls @ b


    // List of encoded ensures and requires
    let spec_stmts = List.map spec_to_stmt (List.filter (fun x -> match x with Decreases(_, _) -> false | _ -> true) s) in

    let postcond =
        List.filter
            (fun c ->
                match c with
                | Assert _ -> true
                | _ -> false)
            spec_stmts

    let postcond =
        let inf_prova =
            { method_name = None
              no_line = 999
              error_type = Some(PostconditionError(Some("impossibile")))

            }

        // if there are no postconditions we add a true postcondition (sould always be verifies, that's the reason for the impossibile error)
        match postcond with
        | [] -> [ Assert(inf_prova, AST.Boolean(true)) ]
        | l -> l


    let precond =
        List.filter
            (fun c ->
                match c with
                | Assume _ -> true
                | _ -> false)
            spec_stmts

    let precond =
        match precond with
        | [] -> [ Assume(AST.Boolean(true)) ]
        | l -> l

    let b' = 
        match b with 
            | Some(b'') -> b'' 
            | None -> []


    // Preparation for the body before encoding it into IVL1
    let b' =
        b'
        |> (fun x -> add_prefix_to_vars("my", Some x))  // add prefix to variables (used in the encoding of the method assignment)
        |> (fun x -> body_with_variants(x, s, 0)) // add the variants to the body
        |> (fun x -> fst(body_with_while_variants(x, 0)))
        |> (fun x -> body_with_spec(x, add_prefix_to_vars("my", Some (precond @ postcond)))) // add the specifications to the body 
        |> (fun x -> body_with_orig_inputs_declared(x))
        |> (fun x -> body_with_inputs_outputs((add_prefix_to_varlist("my", i@o)), x))
        |> body_with_divbyzero_checks // add the divbyzero checks to the body
       


    let varsmap = build_var_type_map b' in  // build a map from variables to types

    // After we encode the method to IVL1 we need to add the bound variables to the method
    let b' =
        b' |> (fun b -> let b, _ = micro_body_to_IVL1 (b, varsmap, n, methods_list) in b)
        |> (fun b -> bound_vars_to_method_on_body(n, b)) in

    { V1name = n; V1body = b' ; is_abstract = is_abstract}

// Function that encodes a document from microviper to IVL1
let micro_to_IVL1 (doc: document) =

    let methods_list = 
        doc |> List.filter (fun d -> match d with | Method(_) -> true | _ -> false)
            |> List.map (fun d -> match d with | Method(m) -> m | _ -> raise (InnerError("functions yet to be implemented")))      

    let doc_item_to_IVL1(di : document_item) : v1_document_item = 
        match di with   
        | Method(m) -> 
            let m' = m |> update_errors_info

            V1Method(micro_method_to_IVL1(m', methods_list))

        | _ -> raise (InnerError("functions yet to be implemented"))
    in 
    
    List.map doc_item_to_IVL1 doc
