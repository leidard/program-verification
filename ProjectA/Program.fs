open System
open Microsoft.Z3
open To_IVL1
open Prettyprint
open To_IVL0
open To_Z3
open To_PL
open AST
open Checkers

let unwrap =
    function
    | Ok r -> r
    | Error e -> raise e

//To test the verifier with tests specified in Checker.fs run the program with the argument "test"
// To test the verifies with a specific file run the program with the path to the file as an argument
[<EntryPoint>]
let main (args) =
    for f in args do

        if f = "test" then
             test ()
        else
            Console.WriteLine("Parsing: {0}", f)
            Console.WriteLine("-----MICROVIPER----\n{0}", string_of_document (Syntax.parse_file f))
            let res = micro_to_IVL1 (Syntax.parse_file f) in
            Console.WriteLine("-----IVL1----\n{0}", string_of_IVL1_document res)
            let dsa_res = IVL1_to_DSA res in
            Console.WriteLine("----------DSA---------\n{0}", string_of_dsa_document dsa_res)
            let v0_res = DSA_to_IVL0 dsa_res in
            Console.WriteLine("----------IVL0---------\n{0}", string_of_v0_document v0_res)
            let pl_res = IVL0_to_PL v0_res in

            Console.WriteLine(
                "----------PL---------\n{0}",
                String.concat "\n" (List.map string_of_plExpr (IVL0_to_PL v0_res))
            )

            Console.WriteLine("----------Checking----------")
            let check_res = check_validity (Syntax.parse_file f)
            print_check_result (check_res)
        

    0
