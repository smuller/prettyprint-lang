open Types
open Z3
module A = Arithmetic

type uvar = Expr.expr

let ctx = mk_context []

let nl_sort = Sort.mk_uninterpreted_s ctx "nl"
let top = Expr.mk_const_s ctx "top" nl_sort
let bottom = Expr.mk_const_s ctx "bottom" nl_sort
let internal = Expr.mk_const_s ctx "internal" nl_sort
let no_nl = Expr.mk_const_s ctx "not" nl_sort
let both = Expr.mk_const_s ctx "both" nl_sort
let nl_le = FuncDecl.mk_func_decl_s ctx "lt" [nl_sort; nl_sort]
              (Boolean.mk_sort ctx)

let exp_of_nl =
  function Top -> top | Bottom -> bottom | Internal -> internal | Not -> no_nl
           | Both -> both
         
let solver =
  Solver.mk_simple_solver ctx

exception UnificationFailure

let print_consts () =
  List.iter (fun e -> Printf.printf "%s\n" (Expr.to_string e))
    (Solver.get_assertions solver)
        
let solve_consts () =
  let _ = Printf.printf "solving %d constraints\n"
            (Solver.get_num_assertions solver)
  in
  let _ = print_consts ()
  in
  match Solver.check solver (Solver.get_assertions solver) with
  | SATISFIABLE -> ()
  | UNSATISFIABLE | UNKNOWN -> raise UnificationFailure


        
let _ =
  Boolean.(
    let x = Quantifier.mk_bound ctx 0 (nl_sort) in
    let y = Quantifier.mk_bound ctx 1 (nl_sort) in
    Solver.add solver
      [Quantifier.expr_of_quantifier
         (Quantifier.mk_forall
            ctx
            [nl_sort]
            [Symbol.mk_string ctx "x"]
            (mk_or ctx
               [ mk_eq ctx x top;
                 mk_eq ctx x bottom;
                 mk_eq ctx x internal;
                 mk_eq ctx x no_nl;
                 mk_eq ctx x both ]
            )
            None
            []
            []
            None
            None
         ) (*;
       Quantifier.expr_of_quantifier
         (Quantifier.mk_forall
            ctx
            [nl_sort; nl_sort]
            [Symbol.mk_string ctx "x"; Symbol.mk_string ctx "y"]
            (mk_iff ctx (mk_eq ctx (Expr.mk_app ctx nl_le [x; y]) (mk_true ctx))
               (mk_or ctx [mk_eq ctx x y;
                           mk_and ctx [mk_eq ctx x no_nl;
                                       mk_eq ctx y internal]]))
            None
            []
            []
            None
            None
         ) *)
  ])

let all_pairs f l =
  let rec ap2 l1 l2 =
    (match l2 with
     | [] -> ()
     | x::l2 ->
        List.iter (f x) l1;
        List.iter (f x) l2;
        ap2 (x::l1) l2)
  in
  ap2 [] l

let _ =
  all_pairs (fun x y ->
      Solver.add solver
        [Boolean.mk_not ctx (Expr.mk_app ctx nl_le [x; y])])
    [top; bottom; internal; no_nl; both]

let evar_ctr = ref (-1)
let new_nlvar () =
  let _ = evar_ctr := (!evar_ctr) + 1 in
  Expr.mk_const_s ctx (string_of_int (!evar_ctr)) nl_sort
let new_intvar () =
  let _ = evar_ctr := (!evar_ctr) + 1 in
  A.Integer.mk_const_s ctx (string_of_int (!evar_ctr))
let mk_int n =
  A.Integer.mk_numeral_i ctx n

(* let _ = Solver.add solver [A.mk_le ctx (A.mk_add ctx [mk_int 5]) (mk_int 0)] *)
  
let _ = solve_consts ()

type 'a orevar = A of 'a | Evar of int

let new_evar () =
  (evar_ctr := (!evar_ctr) + 1;
   ref (Evar (!evar_ctr)))

type uinfo = { left  : uvar;
               width : uvar;
               nl    : uvar }
type utype = (uinfo * (utype typ) orevar ref)

let string_of_int_var model v =
  match Z3.Model.eval model v false with
  | Some n -> Z3.Expr.to_string n
  | None -> "ERROR"

let string_of_nl_var model v =
  (match Z3.Model.eval model v false with
   | Some e -> Z3.Expr.to_string e
   | None -> "ERROR")
  
let string_of_info model i =
  Printf.sprintf "(%s, %s, %s)"
    (string_of_int_var model i.left)
    (string_of_int_var model i.width)
    (string_of_nl_var model i.nl)

let rec string_of_utype model (i, t) =
  Printf.sprintf "(%s %s)"
    (string_of_info model i)
    (match !t with
     | A t ->
        (match t with
         | TInt _ -> "int"
         | TString _ -> "string"
         | TBool _ -> "bool"
         | TUnit _ -> "unit"
         | TList (t) -> (string_of_utype model t) ^ " list"
         | TArrow (t1, t2) -> Printf.sprintf "%s -> %s"
                                (string_of_utype model t1)
                                (string_of_utype model t2)
         | TProd (t1, t2) -> Printf.sprintf "%s * %s"
                               (string_of_utype model t1)
                               (string_of_utype model t2)
        )
     | Evar _ -> "")

let new_uinfo () =
  let i = { left = new_intvar () ;
            width = new_intvar ();
            nl = new_nlvar () }
  in
  Solver.add solver [A.mk_ge ctx i.left (mk_int 0);
                     A.mk_ge ctx i.width (mk_int 0)];
  i

let new_type () = (new_uinfo (), new_evar ())

(* sum of l <= sum of r if all nl <> Not *)
type constr =
  (int orevar ref list) * (int orevar ref list) * (nl orevar ref  list)

(* if (v_i = n_i) for all i, then v = n *)
type nlconst = (nl orevar * nl) list * (nl orevar * nl)

let leftconsts : constr list ref = ref []
let widthconsts : constr list ref = ref []
let nlconsts : nlconst list ref = ref []

let nl_const l ((i, _), nl) =
  Solver.add solver
    [Boolean.mk_or ctx
       ((Expr.mk_app ctx nl_le [i.nl; exp_of_nl nl])::
          List.map
            (fun ((i, _), nl) ->
              Boolean.mk_not ctx (Expr.mk_app ctx nl_le [i.nl; exp_of_nl nl]))
            l)
    ]

               (*
let occurs_info i e =
  (!(i.left)) = Evar e || !(i.width) = Evar e || !(i.nl) = Evar e
                *)
               
let rec occurs (i, t) e =
  match !t with
  | Evar n -> n = e
  | A (TList t) -> occurs t e
  | A (TArrow (t1, t2)) -> occurs t1 e || occurs t2 e
  | A (TProd (t1, t2)) -> occurs t1 e || occurs t2 e
  | A TInt | A TString | A TBool | A TUnit -> false

let add_const c =
  Solver.add solver [c]
                                            
let build_left_constraint (left_types : utype list)
      (left_const : int)
      (right_types : utype list)
      (right_const : int)
      (nl : utype list)
  =
  let lvars = List.map (fun (i, _) -> i.left) left_types in
  let lvars = (* if left_const = 0 then lvars
              else *) (mk_int left_const)::lvars
  in
  let rvars = List.map (fun (i, _) -> i.left) right_types in
  let rvars = (*if right_const = 0 then rvars
              else *) (mk_int right_const)::rvars
  in
  Boolean.mk_or ctx
       ((A.mk_le ctx
           (A.mk_add ctx lvars)
           (A.mk_add ctx rvars))::
          (List.map
             (fun (i, _) ->
               Boolean.mk_not ctx (Boolean.mk_eq ctx i.nl no_nl))
             nl))


let left_constraint (left_types : utype list)
      (left_const : int)
      (right_types : utype list)
      (right_const : int)
      (nl : utype list)
  =
  add_const (build_left_constraint left_types left_const right_types
               right_const nl)
  
let left_constraint_eq (left_types : utype list)
      (left_const : int)
      (right_types : utype list)
      (right_const : int)
      (nl : utype list)
  =
  left_constraint left_types left_const right_types right_const nl;
  left_constraint right_types right_const left_types left_const nl

let build_left_constraint_eq (left_types : utype list)
      (left_const : int)
      (right_types : utype list)
      (right_const : int)
      (nl : utype list)
  =
  Boolean.mk_and ctx
    [build_left_constraint left_types left_const right_types right_const nl;
     build_left_constraint right_types right_const left_types left_const nl]
  
let build_width_constraint (left_types : utype list)
      (left_const : int)
      (right_types : utype list)
      (right_const : int)
      (nl : utype list)
  =
  let lvars = List.map (fun (i, _) -> i.width) left_types in
  let lvars = if left_const = 0 then lvars
              else (mk_int left_const)::lvars
  in
  let rvars = List.map (fun (i, _) -> i.width) right_types in
  let rvars = if right_const = 0 then rvars
              else (mk_int right_const)::rvars
  in
  Boolean.mk_or ctx
       ((A.mk_le ctx
           (A.mk_add ctx lvars)
           (A.mk_add ctx rvars))::
          (List.map
             (fun (i, _) ->
               Boolean.mk_not ctx (Boolean.mk_eq ctx i.nl no_nl))
             nl))

let width_constraint (left_types : utype list)
      (left_const : int)
      (right_types : utype list)
      (right_const : int)
      (nl : utype list)
  =
  add_const (build_width_constraint left_types left_const right_types
               right_const nl)
  
let build_mix_width (left_lefts : utype list)
      (left_widths : utype list)
      (left_const : int)
      (right_type : utype)
  =
  let lvars1 = List.map (fun (i, _) -> i.left) left_lefts in
  let lvars2 = List.map (fun (i, _) -> i.width) left_widths in
  let lvars = if left_const = 0 then lvars1 @ lvars2
              else (mk_int left_const)::(lvars1 @ lvars2)
  in
  A.mk_le ctx
       (A.mk_add ctx lvars)
       (fst right_type).width

let mix_width (left_lefts : utype list)
      (left_widths : utype list)
      (left_const : int)
      (right_type : utype)
  =
  add_const (build_mix_width left_lefts left_widths left_const right_type)

let nl_dep_consts vs pats =
  Printf.printf "dep_consts\n";
  add_const
    (Boolean.mk_or ctx
       (List.map
          (fun (nls, consts) ->
            Boolean.mk_and ctx
              ((List.map2 (fun (i, _) nl ->
                    Expr.mk_app ctx nl_le [i.nl; exp_of_nl nl])
                  vs nls)
               @ consts))
          pats))
  
  
let nl (i, _) = i.nl
  
let rec unify_nl (i1, _) (i2, _) =
  Solver.add solver
    [Expr.mk_app ctx nl_le [i1.nl; i2.nl];
     Expr.mk_app ctx nl_le [i2.nl; i1.nl]]
(*
    match (!(i1.nl), !(i2.nl)) with
  | (Evar _, _) -> (i1.nl) := !(i2.nl)
  | (_, Evar _) -> i2.nl := !(i1.nl)
  | (A Not, A Both) -> ()
  | _ -> if !(i1.nl) <> !(i2.nl) then raise UnificationFailure
 *)               
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
  unify t1 (new_uinfo (), ref (A t2))

let rec unify_head (_, t1) (t: base_type) =
  match (!t1, t) with
  | (Evar n, TInt) -> t1 := A TInt
  | (Evar n, TString) -> t1 := A TString
  | (Evar n, TBool) -> t1 := A TBool
  | (Evar n, TUnit) -> t1 := A TUnit
  | (A TInt, TInt)
    | (A TString, TString)
    | (A TBool, TBool)
    | (A TUnit, TUnit) -> ()
  | _ -> raise UnificationFailure
