module PLAST

open AST
open ErrorInfo

// a plExpr carries an expression to check later using Z3 and info to report in case of an error
type plExpr = info * expr 

type plSet = plExpr list

// result used to report if the program is valid or not (with error infos)
type check_result = 
    | True 
    | False of info list