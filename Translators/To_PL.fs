module To_PL

open AST
open Microsoft.FSharp.Core
open PLAST
open V1AST
open V0AST
open System
open ErrorInfo

exception InnerErorr of string


// ------------------ IVL0 -> PL ------------------

// This function computes the set efficent weakest precondition of a body in IVL0
let rec sewp_of_body (cl, s: Set<plExpr>) =
    match cl with
    | [] -> s
    | h :: t ->
        (match h with
         | V0Assert(i, e) -> Set.union (sewp_of_body (t, s)) (Set.singleton (i, e))
         | V0Assume e -> Set.map (fun (i, e') -> (i, Binary(Implies, e, e', dummy_info))) (sewp_of_body (t, s))

         | V0Choice(c1, c2) ->
             Set.union (sewp_of_body (c1, sewp_of_body (t, s))) (sewp_of_body (c2, sewp_of_body (t, s)))

         | _ -> sewp_of_body (t, s))


// THis fuction returns a map that associates to each identifier(of a variable) its type, given a IVL0 document
let rec build_var_type_map (doc: v0_document) : Map<ident, ty> =

    let rec build_map_from_body (b: v0Body) : Map<ident, ty> =
        match b with
        | [] -> Map.empty
        | (V0Var((x, typ), _)) :: t -> (build_map_from_body t).Add(x, typ)
        | _ :: t -> (build_map_from_body t) in

    let rec build_map_from_docitem (d: v0_document_item) : Map<ident, ty> =
        match d with
        | V0Method { V0name = _; V0body = b } -> build_map_from_body b
        | _ -> raise (InnerErorr("Functions not implemented yet")) in

    let join (m1: Map<'a, 'b>) (m2: Map<'a, 'b>) = Map.foldBack Map.add m2 m1 in

    match doc with
    | [] -> Map.empty
    | h :: t ->
        let m' = build_map_from_docitem h in
        let m'' = build_var_type_map t in

        join m' m''





// translates a IVL0 document into a PL one
let IVL0_to_PL (doc: v0_document) =


    let v0doc_item_to_PL(di : v0_document_item) : plExpr list = 
        match di with   
        | V0Method(m) when not m.is_abstract-> 
            let m' = sewp_of_body(m.V0body, Set.empty) in Set.toList m'

        | V0Method(m) when m.is_abstract -> []

        | _ -> raise (InnerErorr("functions yet to be implemented"))
    in

    List.concat(List.map v0doc_item_to_PL doc)