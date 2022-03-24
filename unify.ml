open Types


type 'a orevar = A of 'a | Evar of int
let evar_ctr = ref (-1)
let new_evar () =
  (evar_ctr := (!evar_ctr) + 1;
   ref (Evar (!evar_ctr)))

type uinfo = { left  : int orevar ref;
               width : int orevar ref;
               nl    : nl orevar ref}
type utype = (uinfo * (utype typ) orevar ref)

let new_uinfo nl = { left = new_evar () ;
                     width = new_evar ();
                     nl = new_evar () }

let new_type () = (new_uinfo (), new_evar ())

exception UnificationFailure

(* sum of l <= sum of r if all nl <> Not *)
type constr =
  (int orevar ref list) * (int orevar ref list) * (nl orevar ref  list)

(* if (v_i = n_i) for all i, then v = n *)
type nlconst = (nl orevar * nl) list * (nl orevar * nl)

let leftconsts : constr list ref = ref []
let widthconsts : constr list ref = ref []
let nlconsts : nlconst list ref = ref []

let nl_const c : nlconsts := c::(!nlconsts)

let occurs_info i e =
  (!(i.left)) = Evar e || !(i.width) = Evar e || !(i.nl) = Evar e

let rec occurs (i, t) e =
  match !t with
  | Evar n -> n = e
  | A (TList t) -> occurs t e
  | A (TArrow (t1, t2)) -> occurs t1 e || occurs t2 e
  | A (TProd (t1, t2)) -> occurs t1 e || occurs t2 e
  | A TInt | A TString | A TBool | A TUnit -> false

let left_constraint (left_types : utype list)
      (left_const : int)
      (right_types : utype list)
      (right_const : int)
      (nl : utype list)
  =
  let lvars = List.map (fun (i, _) -> i.left) left_types in
  let lvars = if left_const = 0 then lvars
              else (ref (A left_const))::lvars
  in
  let rvars = List.map (fun (i, _) -> i.left) right_types in
  let rvars = if right_const = 0 then rvars
              else (ref (A right_const))::rvars
  in
  leftconsts := (lvars, rvars, List.map (fun (i, _) -> i.nl) nl)::(!leftconsts)

let left_constraint_eq (left_types : utype list)
      (left_const : int)
      (right_types : utype list)
      (right_const : int)
      (nl : utype list)
  =
  left_constraint left_types left_const right_types right_const nl;
  left_constraint right_types right_const left_types left_const nl
  
let width_constraint (left_types : utype list)
      (left_const : int)
      (right_types : utype list)
      (right_const : int)
      (nl : utype list)
  =
  let lvars = List.map (fun (i, _) -> i.width) left_types in
  let lvars = if left_const = 0 then lvars
              else (ref (A left_const))::lvars
  in
  let rvars = List.map (fun (i, _) -> i.width) right_types in
  let rvars = if right_const = 0 then rvars
              else (ref (A right_const))::rvars
  in
  widthconsts := (lvars, rvars, List.map (fun (i, _) -> i.nl) nl)::(!widthconsts)

let mix_width (left_lefts : utype list)
      (left_widths : utype list)
      (left_const : int)
      (right_type : utype)
  =
  let lvars1 = List.map (fun (i, _) -> i.left) left_lefts in
  let lvars2 = List.map (fun (i, _) -> i.width) left_widths in
  let lvars = if left_const = 0 then lvars1 @ lvars2
              else (ref (A left_const))::(lvars1 @ lvars2)
  in
  widthconsts := (lvars, [(fst right_type).width], [])::(!widthconsts)
  
let nl (i, _) = i.nl
  
let rec unify_nl (i1, _) (i2, _) =
  match (!(i1.nl), !(i2.nl)) with
  | (Evar _, _) -> (i1.nl) := !(i2.nl)
  | (_, Evar _) -> i2.nl := !(i1.nl)
  | (A Not, A Both) -> ()
  | _ -> if !(i1.nl) <> !(i2.nl) then raise UnificationFailure
                 
let rec unify ((_, t1) as it1) ((_, t2) as it2) =
  match (!t1, !t2) with
  | (Evar n1, Evar n2) when n1 = n2 -> ()
  | (Evar n, _) ->
     if occurs it2 n then raise (UnificationFailure)
     else t1 := !t2
  | (_, Evar n) ->
     if occurs it1 n then raise (UnificationFailure)
     else t2 := !t1
  | (A (TList t1), A (TList t2)) -> full_unify t1 t2
  | (A (TArrow (t1a, t1b)), A (TArrow (t2a, t2b))) ->
     (full_unify t1a t2a;
      full_unify t1b t2b)
  | (A (TProd (t1a, t1b)), A (TProd (t2a, t2b))) ->
     (full_unify t1a t2a;
      full_unify t1b t2b)
  | (A TInt, A TInt)
    | (A TString, A TString)
    | (A TBool, A TBool)
    | (A TUnit, A TUnit) -> ()
  | _ -> raise (UnificationFailure
                  (*(Printf.sprintf "Shape mismatch: can't unify %s and %s"
                     (string_of_ttyp t1)
                     (string_of_ttyp t2))*))
and full_unify t1 t2 =
  left_constraint [t2] 0 [t1] 0 [];
  width_constraint [t1] 0 [t2] 0 [];
  unify_nl t1 t2;
  unify t1 t2

let unify_skip (t1: utype) (t2: utype typ) =
  unify t1 (new_uinfo (), t2) 

let rec unify_head (_, t1) (t: base_type) =
  match (!t1, t) with
  | (Evar n, _) ->
     t1 := A t
  | (A TInt, TInt)
    | (A TString, TString)
    | (A TBool, TBool)
    | (A TUnit, TUnit) -> ()
  | _ -> raise UnificationFailure
