open Types
open Context

let rec string_of_typ t =
  match t with
  | TInt -> "int"
  | TString -> "string"
  | TBool -> "bool"
  | TUnit -> "unit"
  | TList t -> (string_of_typ t) ^ " list"
  | TArrow (t1, t2) -> (string_of_typ t1) ^ " -> " ^ (string_of_typ t2)
  | TVar s -> s
   
(* Substitute t' for typevar x in t *)
let rec substitute (t: typ) (x: string) (t': typ) =
  match t with
  | TInt -> TInt
  | TString -> TString
  | TBool -> TBool
  | TUnit -> TUnit
  | TList t0 -> TList (substitute t0 x t')
  | TArrow (t1, t2) -> TArrow (substitute t1 x t', substitute t2 x t')
  | TVar x' ->
     if x = x' then t'
     else t

type substitution = (string * typ) list

let substitute_all (s: substitution) (t: typ) =
  List.fold_right (fun (x, t') t -> substitute t x t') s t

let sub_ctx (s: substitution) (c: ctx) : ctx =
  VMap.map (substitute_all s) c

exception UnificationFailure of string
  
let rec mgu (t1: typ) (t2: typ) =
  let rec contains_var t x =
    match t with
    | TVar x' -> x = x'
    | TList t -> contains_var t x
    | TArrow (t1, t2) -> contains_var t1 x || contains_var t2 x
    | _ -> false
  in
  match (t1, t2) with
  | (TInt, TInt) -> []
  | (TString, TString) -> []
  | (TBool, TBool) -> []
  | (TUnit, TUnit) -> []
  | (TList t1, TList t2) -> mgu t1 t2
  | (TArrow (t1a, t1b), TArrow (t2a, t2b)) ->
     (mgu t1a t2a) @ (mgu t1b t2b)
  | (TVar s, _) ->
     if contains_var t2 s then
       raise (UnificationFailure
                (Printf.sprintf "cannot unify %s and %s; %s is contained in %s"
                   (string_of_typ t1)
                   (string_of_typ t2)
                   (string_of_typ t1)
                   (string_of_typ t2)))
     else
       [(s, t2)]
  | (_, TVar t) ->
     if contains_var t1 t then
       raise (UnificationFailure
                (Printf.sprintf "cannot unify %s and %s; %s is contained in %s"
                   (string_of_typ t1)
                   (string_of_typ t2)
                   (string_of_typ t2)
                   (string_of_typ t1)))
     else
       [(t, t1)]
  | _ -> raise (UnificationFailure
                  (Printf.sprintf "cannot unify %s and %s"
                     (string_of_typ t1)
                     (string_of_typ t2)))

let ctr = ref 0
let new_tvar () =
  let v = "'?" ^ (string_of_int !ctr) in
  let _ = ctr := (!ctr) + 1 in
  v
