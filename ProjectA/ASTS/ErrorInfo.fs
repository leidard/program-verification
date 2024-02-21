module ErrorInfo

// Every type of error we could have to report
type verification_error = 
    | AssertionError of string option
    | PreconditionError of string option
    | PostconditionError of string option
    | InvariantEntryError of string option
    | InvariantHoldingError of string option
    | MethodPreconditionError of string option
    | MethodPostconditionError of string option
    | WhileVariantError of string option
    | MethodVariantDecreasingError of string option
    | MethodVariantGTZeroError of string option
    | DivByZeroError of string option

// info needed to report in case of an error
type info = {
    method_name : string option;
    no_line : int;
    error_type : verification_error option
}

let dummy_info = { method_name = None; no_line = -1; error_type = None }