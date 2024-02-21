module To_IVL0

open AST
open V1AST
open V0AST
open System
open ErrorInfo

exception InnerError of string


// ------------------ IVL1 -> DSA ------------------


// update the vars ids in an expression, according to the varsMap, to translate them from IVL1 into DSA
let rec update_vars_in_expression
    (
        idAssign: ident option,
        e: expr,
        varsMap: Map<string, int>
    ) : expr * Map<string, int> =
    match e with
    | Ref id ->
        let count =
            if Map.containsKey id varsMap then
                Map.find id varsMap
            else
                0

        let varsMap' = Map.add id count varsMap

        (Ref($"{id}_{count}"), varsMap')


    | Call(id, exprl) ->
        let res = List.map (fun e -> update_vars_in_expression (idAssign, e, varsMap)) exprl
        let exprs, varMaps = List.unzip res
        (Call($"{id}_{(Map.find id varsMap)}", exprs), varMaps.Head)
    | Unary(op, e) ->
        let e', varsMap' = update_vars_in_expression (idAssign, e, varsMap)
        Unary(op, e'), varsMap'
    | Binary(op, e1, e2, i) ->
        let e1', varsMap1 = update_vars_in_expression (idAssign, e1, varsMap)
        let e2', varsMap2 = update_vars_in_expression (idAssign, e2, varsMap1)
        Binary(op, e1', e2', i), varsMap2
    | Quantification(q, (id, t), e) ->
        let e', varsMap' = update_vars_in_expression (idAssign, e, varsMap)
        Quantification(q, (($"{id}_{(Map.find id varsMap')}"), t), e'), varsMap'
    | _ -> e, varsMap


// given an id and a sequence, returns -if present- the value associated to that id in the sequence
let find_value_by_id (idToFind: 'a) (sequence: ('a * int) list) : int option =
    match List.tryFind (fun (id, _) -> id = idToFind) sequence with
    | Some(_, value) -> Some value
    | None -> None


// add the assignements needed in the first branch of the choice to align the variables counter in the branches
let rec add_assignments_to_choice_branch1 (c1Seq, c2Seq, c1StmtList) =
    match c1Seq, c2Seq with
    | _, (id2, c2Value) :: rest2 ->
        match find_value_by_id id2 c1Seq with
        | Some c1Value when c2Value > c1Value ->
            let c1Stmt = DSAAssignment($"{id2}_{c2Value}", Ref($"{id2}_{c1Value}"))
            add_assignments_to_choice_branch1 (c1Seq, rest2, c1Stmt :: c1StmtList)

        | Some c1Value when c2Value <= c1Value -> add_assignments_to_choice_branch1 (c1Seq, rest2, c1StmtList)

        | _ ->
            let c1Stmt = DSAAssignment($"{id2}_{c2Value}", Ref($"{id2}_{0}"))

            add_assignments_to_choice_branch1 (
                c1Seq,
                rest2,
                if (c2Value <> 0) then c1Stmt :: c1StmtList else c1StmtList
            )
    | _ -> (c1StmtList)

// add the assignements needed in the second branch of the choice to align the variables counter in the branches
let rec add_assignments_to_choice_branch2 (c1Seq, c2Seq, c2StmtList) =
    match c1Seq, c2Seq with
    | (id1, c1Value) :: rest1, _ ->
        match find_value_by_id id1 c2Seq with
        | Some c2Value when c2Value < c1Value ->
            let c2Stmt = DSAAssignment($"{id1}_{c1Value}", Ref($"{id1}_{c2Value}"))
            add_assignments_to_choice_branch2 (rest1, c2Seq, c2Stmt :: c2StmtList)

        | Some c2Value when c2Value >= c1Value -> add_assignments_to_choice_branch2 (rest1, c2Seq, c2StmtList)

        | _ ->
            let c2Stmt = DSAAssignment($"{id1}_{c1Value}", Ref($"{id1}_{0}"))

            add_assignments_to_choice_branch2 (
                rest1,
                c2Seq,
                if (c1Value <> 0) then c2Stmt :: c2StmtList else c2StmtList
            )
    | _ -> (c2StmtList)



// fixes the choice branches
// i.e., the case in which we have a branch with a higher counter than the other.
// e.g., if c1 has x1 and c2 has reached x4, then we need to add to c1 the assignment x4=x1)
let rec fix_choice_branches (c1VarsMap, c2VarsMap) =
    let c1Seq = Map.toSeq c1VarsMap |> List.ofSeq // convert maps into seq to iterate over them
    let c2Seq = Map.toSeq c2VarsMap |> List.ofSeq

    let c1StmtList = add_assignments_to_choice_branch1 (c1Seq, c2Seq, [])
    let c2StmtList = add_assignments_to_choice_branch2 (c1Seq, c2Seq, [])

    (c1VarsMap, c2VarsMap, c1StmtList, c2StmtList)


// translates a IVL1 statement into a DSA statement
let rec IVL1_stmt_to_DSA (cmd: v1Statement, varsMap: Map<string, int>) : DSAStatement list * Map<string, int> =
    match cmd with
    | V1Var((id, t), Some(e)) ->

        let (e, varsMap) = update_vars_in_expression (Some(id), e, varsMap)

        let count =
            if Map.containsKey id varsMap then
                Map.find id varsMap + 1
            else
                0

        let varsMap' = Map.add id count varsMap


        ([ DSAVar(($"{id}_{count}", t), Some(e)) ], varsMap')

    | V1Var((id, t), None) ->
        let count =
            if Map.containsKey id varsMap then
                Map.find id varsMap
            else
                0

        ([ DSAVar(($"{id}_{count}", t), None) ], varsMap)


    | V1Havoc(idlist) ->
        let rec handle_havocs idlist varsMap =
            match idlist with
            | [] -> [], varsMap
            | (x, typ) :: rest ->
                let count =
                    if Map.containsKey x varsMap then
                        Map.find x varsMap + 1
                    else
                        0

                let varsMap' = Map.add x count varsMap
                let newDSAVar = DSAVar(($"{x}_{count}", typ), None)

                let (DSAVars, finalVarsMap) = handle_havocs rest varsMap'

                (newDSAVar :: DSAVars, finalVarsMap)

        let (DSAVars, updatedVarsMap) = handle_havocs idlist varsMap

        (DSAVars, updatedVarsMap)

    | V1Assert(i, e) -> let (e', _) = update_vars_in_expression (None, e, varsMap) in [ DSAAssert(i, e') ], varsMap
    | V1Assume e -> let (e', _) = update_vars_in_expression (None, e, varsMap) in [ DSAAssume(e') ], varsMap
    | V1Assignment(i, e) ->

        let (e', varsMap') = update_vars_in_expression (Some(i), e, varsMap)

        let count =
            if Map.containsKey i varsMap' then
                Map.find i varsMap' + 1
            else
                0

        let varsMap' = Map.add i count varsMap

        ([ DSAAssignment($"{i}_{count}", e') ], varsMap')


    | V1Choice(c1, c2) ->
        let rec choice_stmts_to_DSA stmts varsMap (acc: DSAStatement list) =
            match stmts with
            | [] -> List.rev acc, varsMap
            | stmt :: rest ->
                let DSAStmt, varsMap' = IVL1_stmt_to_DSA(stmt, varsMap)
                choice_stmts_to_DSA rest varsMap' (DSAStmt @ acc)

        let c1', c1VarsMap = choice_stmts_to_DSA c1 varsMap []
        let c2', c2VarsMap = choice_stmts_to_DSA c2 varsMap []

        // lists of assignments to append to the list of the assignment in each choice branch
        let c1VarsMap', c2VarsMap', c1AdditionalStmts, c2AdditionalStmts =
            fix_choice_branches (c1VarsMap, c2VarsMap)

        let c1DSAStmts = c1' @ c1AdditionalStmts
        let c2DSAStmts = c2' @ c2AdditionalStmts

        let ids =
            List.distinct ((c1VarsMap' |> Map.keys |> List.ofSeq) @ (c2VarsMap' |> Map.keys |> List.ofSeq))

        // given the id of the variable, find the highest counter
        let find_highest_counter (id: string) =
            match c1VarsMap'.TryFind(id), c2VarsMap'.TryFind(id) with
            | Some(value1), Some(value2) -> max value1 value2
            | Some(value1), None -> value1
            | None, Some(value2) -> value2
            | _ -> 0

        let varsMap' =
            ids
            |> List.map (fun id -> (id, find_highest_counter id))
            |> List.fold (fun acc (id, value) -> Map.add id value acc) Map.empty


        ([ DSAChoice(c1DSAStmts, c2DSAStmts) ], varsMap')

// given a DSA body, returns a list of all the ids of the vars declared in it
let rec extract_var_declarations_from_dsa_body (body: list<DSAStatement>) : list<ident> =
    match body with
    | [] -> []
    | DSAVar((name, _), _) :: rest -> name :: extract_var_declarations_from_dsa_body rest
    | DSAChoice(c1, c2) :: rest -> extract_var_declarations_from_dsa_body c1 @ extract_var_declarations_from_dsa_body c2 @ extract_var_declarations_from_dsa_body rest
    | _ :: rest -> extract_var_declarations_from_dsa_body rest

// given a DSA expression, returns a list of all the ids of the vars present in it (with duplicates)
let rec extract_var_ids_from_expression (exp: expr) : list<ident> =
    match exp with
    | Ref id -> [ id ]
    | Call(id, exps) -> id :: List.concat (List.map (fun e -> extract_var_ids_from_expression e) exps)
    | Unary(_, exp) -> extract_var_ids_from_expression exp
    | Binary(_, exp1, exp2, i) -> (extract_var_ids_from_expression exp1) @ (extract_var_ids_from_expression exp2)
    | Quantification(_, (id, _), exp) -> id :: (extract_var_ids_from_expression exp)
    | _ -> []

// given a DSA body, returns a list of all the vars present in it (with duplicates)
let rec extract_var_ids_from_dsa_body (body: list<DSAStatement>) : list<ident> =
    match body with //assert and assume cases are not needed
    | [] -> []
    | DSAVar((id, _), _) :: rest -> id :: extract_var_ids_from_dsa_body rest
    | DSAAssignment(id, exp) :: rest ->
        [ id ]
        @ (extract_var_ids_from_expression exp)
        @ (extract_var_ids_from_dsa_body rest)
    | DSAChoice(c1, c2) :: rest ->
        extract_var_ids_from_dsa_body c1
        @ extract_var_ids_from_dsa_body c2
        @ extract_var_ids_from_dsa_body rest
    | _ :: rest -> extract_var_ids_from_dsa_body rest


// given a list of var declarations, it inserts them right after the already present var declarations in the body
let rec insert_missing_vars_declarations_in_body (declarations: DSAStatement list) (dsaBody: DSAStatement list) =
    match dsaBody with
    | DSAVar(v, e) :: rest -> DSAVar(v, e) :: insert_missing_vars_declarations_in_body declarations rest
    | statement :: rest -> declarations @ statement :: rest
    | _ -> []

// given the id of the var, return it without the counter
let extract_var_name(id: string) =
    let lastIndex = id.LastIndexOf("_")
    id.[..(lastIndex - 1)]

// given the ident of the var, returns its type
let rec get_var_type (dsaBody: DSAStatement list, id: ident) : ty option =
    match dsaBody with
    | DSAVar((i, t), _) :: _ when (extract_var_name i) = (extract_var_name id) -> Some t
    | DSAChoice(c1, c2) :: r ->
        let t = get_var_type (c1, id)
        match t with
        | Some _ -> t
        | None -> get_var_type (c2, id)
    | _ :: xs -> get_var_type (xs, id)
    | _ -> None


// finds vars in the body without declaration and declares them at the top of the body.
// e.g., if we have x2 = 1, then DSAVar (("x2", Int), None); will be added
let add_missing_var_declarations (dsaBody: DSAStatement list, finalVarsMap: Map<string, int>) : list<DSAStatement> =
    let declaredVars = extract_var_declarations_from_dsa_body dsaBody
    let presentVars = List.distinct (extract_var_ids_from_dsa_body dsaBody)

    let missingVars =
        List.filter (fun v -> not (List.contains v declaredVars)) presentVars // missing var declarations

    let newVarStatements =
        missingVars
        |> List.collect (fun id ->
            let count =
                match finalVarsMap |> Map.tryFind id with
                | Some(value) -> value
                | None -> 0

            let t = match get_var_type(dsaBody, id) with
                | Some x -> x
                | None -> raise(InnerError("var declaration not found"))
                
            
            [ for _ in 0..count -> DSAVar(($"{id}", t), None) ])

    insert_missing_vars_declarations_in_body newVarStatements dsaBody


// returns a DSA body with all the var declarations moved at the top (prenex normal form)
let var_declarations_on_top_body (dsaBody: DSAStatement list) : DSAStatement list =
    // returns the header of the body with all the declarations in the body, and the body without the var declarations
    let rec move_on_top_var_declarations
        (
            varDecl: DSAStatement list,
            restBody: DSAStatement list
        ) : DSAStatement list * DSAStatement list =
        match restBody with
        | [] -> varDecl, []
        | DSAVar((i, typ), Some(e)) :: r ->
            move_on_top_var_declarations (varDecl @ [ DSAVar((i, typ), None) ], (DSAAssignment(i, e)) :: r)
        | DSAVar(i, e) :: r -> move_on_top_var_declarations (varDecl @ [ DSAVar(i, e) ], r)
        | DSAChoice(c1, c2) :: r ->
            let (varDecl1, restBody1) = move_on_top_var_declarations (varDecl, c1)
            let (varDecl2, restBody2) = move_on_top_var_declarations (varDecl1, c2)
            let (v, b) = move_on_top_var_declarations (varDecl2, r) in
            (v, DSAChoice(restBody1, restBody2) :: b)

        | s :: r -> let (v, b) = move_on_top_var_declarations (varDecl, r) in (v, s :: b)

    let header, body = move_on_top_var_declarations ([], dsaBody)
    (List.distinct (header)) @ body


// translates a IVL1 method into a DSA one
let IVL1_method_to_DSA
    ({ V1name = n
       V1body = b
       is_abstract = abstract_flag })
    =
    let rec translate_statement statements varsMapAcc =
        match statements with
        | [] -> [], varsMapAcc
        | stmt :: rest ->
            let dsaStmt, updatedVarsMap = IVL1_stmt_to_DSA(stmt, varsMapAcc)
            let restStmts, finalVarsMap = translate_statement rest updatedVarsMap
            (dsaStmt @ restStmts), finalVarsMap

    let varsMap: Map<string, int> = Map.empty
    let dsaBody, finalVarsMap = translate_statement b varsMap


    let dsaBodyDeclarations = add_missing_var_declarations (dsaBody, finalVarsMap)

    let dsaBodyComplete = dsaBodyDeclarations |> var_declarations_on_top_body

    { DSAname = n
      DSAbody = dsaBodyComplete
      is_abstract = abstract_flag },
    finalVarsMap

// translates a IVL1 document into a DSA one
let IVL1_to_DSA (doc: v1_document) =

    let v1doc_item_to_IVL0 (di: v1_document_item) : DSA_document_item =
        match di with
        | V1Method(m) -> let m', _ = IVL1_method_to_DSA m in DSAMethod(m')

        | _ -> raise (InnerError("functions yet to be implemented")) in

    List.map v1doc_item_to_IVL0 doc




// ------------------ DSA -> IVL0 ------------------

// translates a DSA statement into a IVL0 one
let rec DSA_stmt_to_IVL0 (cmd: DSAStatement, varsMap: Map<string, int>) : v0Statement =
    match cmd with
    | DSAVar(id, e) -> (V0Var(id, e))

    | DSAAssert(i, e) -> V0Assert(i, e)
    | DSAAssume e -> V0Assume e
    | DSAAssignment(id, e) -> V0Assume(Binary(Eq, Ref(id), e, dummy_info))
    | DSAChoice(c1, c2) ->
        let c1 = List.map (fun stmt -> DSA_stmt_to_IVL0(stmt, varsMap)) c1
        let c2 = List.map (fun stmt -> DSA_stmt_to_IVL0(stmt, varsMap)) c2
        V0Choice(c1, c2)

let rec add_assumes (b: v0Body) =
    match b with
    | [] -> []
    | V0Assert(i, e) :: t -> V0Assert(i, e) :: V0Assume(e) :: (add_assumes t)
    | V0Choice(c1, c2) :: t -> V0Choice(add_assumes c1, add_assumes c2) :: add_assumes t
    | h :: t -> h :: add_assumes t

// translates a DSA method into a IVL0 one
let DSA_method_to_IVL0
    ({ DSAname = n
       DSAbody = b
       is_abstract = abstract_flag })
    =
    let varsMap: Map<string, int> = Map.empty
    let b' = b |> List.map (fun stmt -> DSA_stmt_to_IVL0(stmt, varsMap)) |> add_assumes in

    { V0name = n
      V0body = b'
      is_abstract = abstract_flag }

// translates a DSA document into a IVL0 one
let DSA_to_IVL0 (doc: DSA_document) =

    let DSAdoc_item_to_IVL0 (di: DSA_document_item) : v0_document_item =
        match di with
        | DSAMethod(m) -> let m' = DSA_method_to_IVL0 m in V0Method(m')
        | _ -> raise (InnerError("functions yet to be implemented")) in

    List.map DSAdoc_item_to_IVL0 doc
