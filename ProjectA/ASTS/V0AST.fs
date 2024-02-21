module V0AST

open AST
open ErrorInfo

//expressions, operators and other types are the same defined in the AST file

// DSA
type DSAStatement =
    | DSAVar of var * expr option //option because there could be an initialization or not
    | DSAAssert of info * expr
    | DSAAssume of expr
    | DSAAssignment of ident * expr // to remove ? fare un tipo intermedio?
    | DSAChoice of DSAStatement list * DSAStatement list
// Maybe Seq, for now we will try to implement it as lists
and DSABody = DSAStatement list

type DSAmethod = { DSAname: ident; DSAbody: DSABody ; is_abstract: bool}

type DSA_document_item = DSAMethod of DSAmethod // functions not implemented

type DSA_document = DSA_document_item list




// IVLO
type v0Statement =
    | V0Var of var * expr option //option because there could be an initialization or not
    | V0Assert of info * expr
    | V0Assume of expr
    | V0Choice of v0Statement list * v0Statement list
and v0Body = v0Statement list

type v0method = { V0name: ident; V0body: v0Body; is_abstract: bool}

type v0_document_item = V0Method of v0method // functions not implemented

type v0_document = v0_document_item list
