module Checkers

open AST
open V1AST
open V0AST
open PLAST
open Prettyprint
open ErrorInfo
open To_IVL0
open To_IVL1
open To_PL
open To_Z3
open Microsoft.Z3
open System

(*----------------------Function to handle z3 types----------------------*)
let downcast_to_bool (e: Expr) : BoolExpr = e :?> BoolExpr

let rec downcast_list_to_bool (el: (info * Expr) list) : (info * BoolExpr) list =

    match el with
    | [] -> []
    | (i, e) :: t -> (i, downcast_to_bool (e)) :: (downcast_list_to_bool t)


// This function returns true if the formula is unsatisfiable (i.e. if the original formula is valid), false otherwise
let is_formula_valid (f: BoolExpr, s: Solver) : bool =
    match s.Check f with
    | Status.SATISFIABLE -> false

    | Status.UNSATISFIABLE -> true

    | _ -> false

// This function takes as input a microviper document and returns a rasult of type check_result, which is either True or False  with error infos
let check_validity (doc: document) : check_result =
    let v0_doc = doc |> micro_to_IVL1 |> IVL1_to_DSA |> DSA_to_IVL0

    let varmap = build_var_type_map v0_doc
    let ctx = new Context()
    let solver = ctx.MkSolver()

    let z3_formulas =
        v0_doc
        |> IVL0_to_PL
        |> (fun d -> To_Z3(d, ctx, varmap))
        |> downcast_list_to_bool


    // if the negated formula is SAT, it means that the original formula is not valid
    let neg_formulas = List.map (fun (i, e) -> (i, ctx.MkNot(e))) z3_formulas in

    let neg_formuals_res =
        List.map (fun (i, elem) -> i, is_formula_valid (elem, solver)) neg_formulas

    let unverified_list =
        neg_formuals_res
        |> List.filter (fun (i, b) -> not b)
        |> Set.ofList
        |> Set.toList //eliminate duplicate formulas

    match unverified_list with
    | [] -> True
    //Console.WriteLine("The program verifies!!!!")

    | _ -> False(List.map (fun (i: info, b: bool) -> i) unverified_list)
    //Console.WriteLine("The program does not verify :(((")

let test () =
    let correct_programs =
        [ "examples/Core1/00-test.vpr"
          "examples/Core1/01-triple.vpr"
          "examples/Core1/02-triple.vpr"
          "examples/Extension1/03-triple.vpr"
          "examples/Core1/05-max.vpr"
          "examples/Core1/06-triple.vpr"
          "examples/Extension1/07-triple.vpr"
          "examples/01-using-viper/08-isqrt.vpr"
          "examples/Extension1/09-maxsum.vpr"
          "examples/Extension1/10-unsound.vpr"

          "examples/Core1/00-abs.vpr"
          "examples/Extension1/02-triples.vpr"
          "examples/Core1/03-quintuple.vpr"
          "examples/Core1/04-forward.vpr"
          "examples/Core1/05-backward.vpr"
          "examples/Core1/06-var.vpr"
          "examples/Extension1/07-choice.vpr"
          "examples/Core1/08-mistake.vpr"

          "examples/Core3/annotsum.vpr"
          "examples/Core3/expr.vpr"
          "examples/Core1/getting_started_example.vpr"
          "examples/Core3/simplewhile.vpr"
          "examples/Core3/sum.vpr"

          "examples/Extension4/dec_above.vpr"
          "examples/Extension4/dec_diff.vpr"
          "examples/Extension5/fac.vpr"
          "examples/Extension5/if_decreases.vpr"
          "examples/Extension4/inc_below.vpr"
          "examples/Extension4/inc_different.vpr"
          "examples/Extension6/reassign_and_decrease.vpr"
          "examples/Extension4/while_dec.vpr"
          "examples/Extension4/while_if_while.vpr"

          "examples/Extension3/long_ewp.vpr"
          "examples/Extension3/longer_ewp.vpr"
          "examples/Extension3/nested_if.vpr"
          "examples/Extension3/nested_while.vpr"
          "examples/Extension3/weird_if.vpr"

          "examples/Extension6/if_reassignment.vpr"
          "examples/Extension6/multiple_params.vpr"
          "examples/Extension6/multiple_reassignment.vpr"
          "examples/Extension6/plus_one.vpr"
          "examples/Extension6/wrong_ensures.vpr" ]

    let build_error_info (m: string option) (l: int) (e: verification_error option) : info =
        { method_name = m
          no_line = l
          error_type = e }

    let unverified_programs =
        [ ("examples/Extension1/04-triple.vpr",
           [ build_error_info (Some "triple") 2 (Some(PostconditionError(Some "r == 3 * x"))) ])

          ("examples/Extension5/multi_decreases.vpr",
           [ build_error_info (Some "multidec") 4 (Some(MethodVariantGTZeroError(Some "n + m"))) ])
          ("examples/Extension6/nonterminating.vpr",
           [ build_error_info (Some "nonterminating") 11 (Some(MethodVariantDecreasingError(None))) ])

          ("examples/Extension4/assert_false_after_while.vpr",
           [ build_error_info (Some "sum") 15 (Some(AssertionError(Some "false"))) ])
          ("examples/Core1/assert_false.vpr",
           [ build_error_info (Some "triple") 5 (Some(AssertionError(Some "false"))) ])
          ("examples/Core1/assume_false_if.vpr",
           [ build_error_info (Some "triple") 14 (Some(AssertionError(Some "false"))) ])
          ("examples/Core1/div_by_zero_implies.vpr", 
          [ build_error_info (Some "division") 6 (Some(DivByZeroError(Some "n"))) ])
          ("examples/Core1/division_by_zero.vpr",
           [ build_error_info (Some "division") 3 (Some(PostconditionError(Some "res > 0")))
             build_error_info (Some "division") 5 (Some(DivByZeroError(Some "n"))) ])
          ("examples/Core3/invariant_err_before_loop.vpr",
           [ build_error_info (Some "sum") 10 (Some(InvariantEntryError(Some "res > 0"))) ])
          ("examples/Core3/invariant_err_inside_loop.vpr",
           [ build_error_info (Some "sum") 10 (Some(InvariantHoldingError(Some "res == 0"))) ])
          ("examples/Core3/invariant_err_plus_one.vpr",
           [ build_error_info (Some "foo") 3 (Some(PostconditionError(Some "y < 10"))) ])
          ("examples/Core3/not_enough_invariants.vpr",
           [ build_error_info (Some "sum") 3 (Some(PostconditionError(Some "res == (n * (n + 1)) / 2"))) ])
          ("examples/Core1/two_wrong_postconds.vpr",
           [ build_error_info (Some "foo") 3 (Some(PostconditionError(Some "y < 10")))
             build_error_info (Some "foo") 4 (Some(PostconditionError(Some "y > 10"))) ])
          ("examples/Extension4/wrong_while_dec.vpr",
           [ build_error_info (Some "main") 10 (Some(WhileVariantError(Some "m + 1"))) ])
          ("examples/Core1/wrong_postcond.vpr",
           [ build_error_info (Some "foo") 5 (Some(PostconditionError(Some "y <= 0"))) ])
          ("examples/Extension6/scope_reassignment.vpr",
           [ build_error_info (Some "scope") 2 (Some(PostconditionError(Some "n == 2"))) ]) ]

    for p in correct_programs do
        Console.WriteLine("-------Checking: {0}-------", p)
        let res = check_validity (Syntax.parse_file p) in

        match res with
        | True -> Console.WriteLine("Passed") // Console.WriteLine("Passed {0} test", p)
        | False(err_list) -> Console.WriteLine(String.concat "\n" (List.map (string_of_info) err_list))

    Console.WriteLine("-------Checking unverified programs-------")

    for p in unverified_programs do
        Console.WriteLine("-------Checking: {0}-------", fst p)
        let res = check_validity (Syntax.parse_file (fst p)) in

        match res with
        | True -> Console.WriteLine("UNSOUND: {0} should not verify", fst p)
        | False(err_list) ->
            if err_list = snd p then
                Console.WriteLine("Passed")
            else
                Console.WriteLine("FAILED: {0} should have different errors", fst p)
                Console.WriteLine("Expected: {0}", String.concat "\n" (List.map (string_of_info) (snd p)))
                Console.WriteLine("Actual: {0}", String.concat "\n" (List.map (string_of_info) err_list))
