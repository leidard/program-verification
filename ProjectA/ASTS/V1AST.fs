module V1AST

open AST
open ErrorInfo

//expressions and other types are the same defined in the AST file

type v1Statement = 
    | V1Var of var * expr option //option because there could be an initialization or not
    | V1Assert of info * expr 
    | V1Assume of expr
    | V1Assignment of ident * expr
    | V1Choice of v1Statement list * v1Statement list
    | V1Havoc of var list
and v1Body = v1Statement list

type v1method = {
    V1name: ident 
    V1body: v1Body
    is_abstract: bool
}

type v1_document_item = V1Method of v1method // functions not implemented

type v1_document = v1_document_item list


