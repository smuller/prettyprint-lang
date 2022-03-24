type const = Num of int
           | String of string
           | Bool of bool
           | Unit
           | Nil

type 'a typ = TInt
            | TString
            | TBool
            | TUnit
            | TList of 'a
            | TArrow of 'a * 'a
            | TProd of 'a * 'a

type base_type = base_type typ
                    
type paren = Atom | Nonatom
type nl = Top | Bottom | Internal | Not | Both
type info = { left  : int;
              width : int;
              nl    : nl }
type pedantic_type = info * (pedantic_type typ)
                   
type infixop = Plus | Minus | Times | Div
               | Lt | Le | Gt | Ge | Eq | Ne
               | And | Or
               | Concat
           
type 'a value = VConst of const
           | VPair of 'a value * 'a value
           | VCons of 'a value * 'a value
           | VFun of string * 'a expr
           | VNamedFun of string * string * 'a expr (* fun f x -> e *)
           | VAnnot of 'a value * base_type

and 'a expr_desc =
  | EVar of string
  | EConst of const
  | EFun of string * 'a expr
  | EInfixop of infixop * 'a expr * 'a expr
  | EIf of 'a expr * 'a expr * 'a expr (* if e1 then e2 else e3 *)
  | ELet of string * base_type option * 'a expr * 'a expr (* let x (: t) = e1 in e2 *)
  (* let (rec?) f (x (:t1)) (:t2) = e1 in e2 *)
  | ELetFun of bool * string * string * base_type option * base_type option * 'a expr * 'a expr
  | ELetPair of string * string * 'a expr * 'a expr (* let (x, y) = e1 in e2 *)
  | EApp of 'a expr * 'a expr
  (* match e1 with | [] -> e2 | h::t -> e3 *)
  | EMatchList of 'a expr * 'a expr * string * string * 'a expr
  | EPair of 'a expr * 'a expr
  | ECons of 'a expr * 'a expr
  | EAnnot of 'a expr * base_type
  | EParen of 'a expr
  | ELinebreakAfter of 'a expr
  | ELinebreakBefore of 'a expr
  | ESpaceAfter of 'a expr
  | ESpaceBefore of 'a expr

and 'a expr =
  { desc  : 'a expr_desc;
    annot : 'a }

let desc e = e.desc
let ann e = e.annot

let mk a e = {desc = e; annot = a}
              
            (*
type decl =
  | DVal of string * typ option * expr (* let x (: t) = e *)

  | DFun of bool * string * string * typ option * typ option * expr 

type prog = decl list * expr
             *)
