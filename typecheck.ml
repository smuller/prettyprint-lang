open Types
open Unifyz3
open Context

   (*
let type_of_const (c: const) : tvar =
  match c with
       | Num _ -> TTInt
       | String _ -> TTString
       | Bool _ -> TTBool
       | Unit -> TTUnit
       | Nil -> TTList (new_type ()))

    *)
   (*
let type_of_op (o: infixop) : base_type * base_type * base_type =
  match o with
  | Plus | Minus | Times | Div -> (TInt (), TInt (), TInt ())
  | Lt | Le | Gt | Ge | Eq | Ne -> (TInt (), TInt (), TBool ())
  | And | Or -> (TBool (), TBool (), TBool ())
  | Concat -> (TString (), TString (), TString ())
    *)
exception TypeError of string

let deferred_consts : (unit -> unit) list ref = ref []
let defer c = deferred_consts := c::(!deferred_consts)

let rec typecheck_exp (c: ctx) (e: unit expr) : utype expr =
  match desc e with
  | EConst (Num n) ->
     let t = new_type () in
     let _ = unify_head t TInt in
     let _ = width_constraint [] (String.length (string_of_int n)) [t] 0 [] in
     let _ = nl_const [] (t, Not) in
     mk t (EConst (Num n))
  | EConst (String s) ->
     let t = new_type () in
     let _ = unify_head t TString in
     let _ = width_constraint [] (String.length s) [t] 0 [] in
     let _ = nl_const [] (t, Not) in
     mk t (EConst (String s))
  | EVar x ->
     (match ctx_find c x with
      | None -> raise (TypeError (Printf.sprintf "unbound identifier %s"
                                    x))
      | Some t ->
         let t' = new_type () in
         let _ = full_unify t t' in
         let _ = left_constraint [] 0 [t'] 0 [] in
         let _ = left_constraint [t'] 0 [] 0 [] in
         let _ = width_constraint [] (String.length x) [t'] 0 [] in
         mk t' (EVar x)
     )
  | EInfixop (o, e1, e2) ->
     raise (TypeError "unsupported") (*
     let (t1, t2, t3) = type_of_op o in
     let t1' = typecheck_exp c e1 in
     let t2' = typecheck_exp c e2 in
     let _ = unify t1' (varify t1) in
     let _ = unify t2' (varify t2) in
     varify t3 *)
  | EIf (e1, e2, e3) ->
     let e1' = typecheck_exp c e1 in
     let t1 = ann e1' in
     let _ = unify_head t1 TBool in
     let e2' = typecheck_exp c e2 in
     let e3' = typecheck_exp c e3 in
     let (t2, t3) = (ann e2', ann e3') in
     let t' = new_type () in
     (* Base types must be equal *)
     let _ = unify t2 t' in
     let _ = unify t3 t' in
     let _ = nl_const [(t1, Not); (t2, Not); (t3, Not)] (t', Not) in
     let _ = nl_const [(t1, Not); (t2, Both); (t3, Top)] (t', Internal) in
     let _ = nl_const [(t1, Both); (t2, Both); (t3, Internal)] (t', Internal) in
           
     let _ =
       nl_dep_consts [t1; t2; t3]
         [
           ([Not; Not; Not],
            [build_left_constraint [] 1 [t1] 0 [];
             build_left_constraint [] 1 [t2] 0 [];
             build_left_constraint [] 1 [t3] 0 [];
             build_mix_width [t1; t2; t3] [t1; t2; t3] 12 t']);
           ([Not; Both; Top],
            [build_left_constraint [] 1 [t1] 0 [];
             build_left_constraint [] 1 [t2] 0 [];
             build_left_constraint [] 1 [t3] 0 [];
             build_left_constraint_eq [t2] 0 [t3] 0 [];
             build_mix_width [t1] [t1] 2 t';
             build_mix_width [t2] [t2] 0 t';
             build_mix_width [t3] [t3] 0 t']);
           ([Both; Both; Internal],
            [build_left_constraint [] 1 [t1] 0 [];
             build_left_constraint [] 1 [t2] 0 [];
             build_left_constraint [] 1 [t3] 0 [];
             build_left_constraint_eq [t2] 0 [t3] 0 [];
             build_mix_width [] [] 4 t';
             build_mix_width [t2] [t2] 0 t';
             build_mix_width [t3] [t3] 0 t'])
         ]
     (*
     let _ = defer
         (fun () ->
           match (nl t1, nl t2, nl t3) with
             (* All on one line *)
           | (Not, Not, Not) ->
              left_constraint [] 1 [t1] 0;
              left_constraint [] 1 [t2] 0;
              left_constraint [] 1 [t3] 0;
              mix_width [t1; t2; t3] [t1; t2; t3] 12 t';
           | (Not, Both, Top) ->
              left_constraint [] 1 [t1] 0;
              left_constraint [] 1 [t2] 0;
              left_constraint [] 1 [t3] 0;
              left_constraint_eq [t2] 0 [t3] 0;
              mix_width [t1] [t1] 2 t';
              mix_width [t2] [t2] 0 t';
              mix_width [t3] [t3] 0 t';
           | (Both, Both, Internal) ->
              left_constraint [] 1 [t1] 0;
              left_constraint [] 1 [t2] 0;
              left_constraint [] 1 [t3] 0;
              left_constraint_eq [t2] 0 [t3] 0;
              mix_width [] [] 4 t';
              mix_width [t2] [t2] 0 t';
              mix_width [t3] [t3] 0 t';
           | _ -> raise (TypeError "Incompatible newlines")
         ) *)
     in
     mk t' (EIf (e1', e2', e3'))
  | ELet (x, t, e1, e2) ->
     let e1' = typecheck_exp c e1 in
     let t1 = ann e1' in
     let _ = (match t with
                None -> ()
              | Some t' -> unify_head t1 t')
     in
     let c' = ctx_add c x t1 in
     let e2' = typecheck_exp c' e2 in
     let t2 = ann e2' in
     let t' = new_type () in
     let _ = unify t2 t' in
     let _ = nl_const [(t1, Not); (t2, Not)] (t', Not) in
     let _ = nl_const [(t1, Not); (t2, Top)] (t', Internal) in
     let _ = nl_const [(t1, Both); (t2, Top)] (t', Internal) in

(*
     let _ =
       defer
         (fun () ->
           match (nl t1, nl t2) with
             (* All on one line *)
           | (Not, Not) ->
              left_constraint [] 1 [t2] 0;
              mix_width [t1; t2] [t1; t2] (9 + (String.length x)) t';
           | (Not, Both) ->
              left_constraint [] 1 [t2] 0;
              mix_width [t1] [t1] (9 + (String.length x)) t';
              mix_width [t2] [t2] 0 t';
           | (Both, Both) ->
              left_constraint [] 1 [t1] 0;
              left_constraint [] 1 [t2] 0;
              left_constraint_eq [t1] 0 [t2] 0;
              mix_width [] [] (6 + (String.length x)) t';
              mix_width [t1] [t1] 0 t';
              mix_width [t2] [t2] 0 t';
           | _ -> raise (TypeError "Incompatible newlines")
         )
     in
 *)
     let _ =
       nl_dep_consts [t1; t2]
         [([Not; Not],
           [build_left_constraint [] 1 [t2] 0 [];
            build_mix_width [t1; t2] [t1; t2] (9 + (String.length x)) t']);
          ([Not; Top],
           [build_left_constraint [] 1 [t2] 0 [];
            build_mix_width [t1] [t1] (9 + (String.length x)) t';
            build_mix_width [t2] [t2] 0 t']);
          ([Both; Top],
           [build_left_constraint [] 1 [t1] 0 [];
            build_left_constraint [] 1 [t2] 0 [];
            build_left_constraint_eq [t1] 0 [t2] 0 [];
            build_mix_width [] [] (6 + (String.length x)) t';
            build_mix_width [t1] [t1] 0 t';
            build_mix_width [t2] [t2] 0 t'])
         ]
     in
     mk t' (ELet (x, t, e1', e2'))
  | ELetFun (is_rec, f, x, t1o, t2o, e1, e2) ->
     let tx = new_type () in
     let _ =
       (match t1o with
        | Some t1' -> unify_head tx t1'
        | None -> ())
     in
     let tr = new_type () in
     let _ =
       (match t2o with
        | Some t2' -> unify_head tr t2'
        | None -> ())
     in
     let c' = ctx_add c x tx in
     let tf = new_type () in
     let _ = unify_skip tf (TArrow (tx, tr)) in
     let c' = if is_rec then ctx_add c' f tf else c' in
     let e1' = typecheck_exp c' e1 in
     let te = ann e1' in
     let _ = full_unify tr te in
     let c'' = ctx_add c f tf in
     let e2' = typecheck_exp c'' e2 in
     let t2 = ann e2' in
     let t' = new_type () in
     let _ = nl_const [(te, Not)] (tf, Not) in
     let _ = nl_const [(te, Top)] (tf, Internal) in
     let _ = nl_const [(te, Not); (t2, Not)] (t', Not) in
     let _ = nl_const [(te, Not); (t2, Both)] (t', Internal) in
     let _ = nl_const [(te, Both); (t2, Both)] (t', Internal) in
     let baselen = 4 + (if is_rec then 4 else 0)
                   + (String.length f) + 1 + (String.length x) + 2
     in
(*
     let _ =
       defer
         (fun () ->
           match (nl te, nl t2) with
             (* All on one line *)
           | (Not, Not) ->
              left_constraint [] 1 [t2] 0;
              mix_width [t1; t2] [t1; t2] (baselen + 3) t';
           | (Not, Both) ->
              left_constraint [] 1 [t2] 0;
              mix_width [t1] [t1] (baselen + 3) t';
              mix_width [t2] [t2] 0 t';
           | (Both, Both) ->
              left_constraint [] 1 [t1] 0;
              left_constraint [] 1 [t2] 0;
              left_constraint_eq [t1] 0 [t2] 0;
              mix_width [] [] baselen t';
              mix_width [t1] [t1] 0 t';
              mix_width [t2] [t2] 0 t';
           | _ -> raise (TypeError "Incompatible newlines")
         )
     in
 *)
     let _ =
       nl_dep_consts [te; tr]
           [([Not; Not],
             [build_left_constraint [] 1 [tr] 0 [];
              build_mix_width [tx; tr] [tx; tr] (baselen + 3) t']);
           ([Not; Both],
            [build_left_constraint [] 1 [tr] 0 [];
             build_mix_width [tx] [tx] (baselen + 3) t';
             build_mix_width [tr] [tr] 0 t']);
           ([Both; Both],
            [build_left_constraint [] 1 [tx] 0 [];
             build_left_constraint [] 1 [tr] 0 [];
             build_left_constraint_eq [tx] 0 [tr] 0 [];
             build_mix_width [] [] baselen t';
             build_mix_width [tx] [tx] 0 t';
             build_mix_width [tr] [tr] 0 t'])
           ]
     in
     mk t' (ELetFun (is_rec, f, x, t1o, t2o, e1', e2'))
  | ELetPair (x, y, e1, e2) ->
     let tx = new_type () in
     let ty = new_type () in
     let e1' = typecheck_exp c e1 in
     let t1 = ann e1' in
     let _ = unify_skip t1 (TProd (tx, ty))
     in
     let c' = ctx_add c x tx in
     let c' = ctx_add c' y ty in
     let e2' = typecheck_exp c' e2 in
     let t2 = ann e2' in
     let t' = new_type () in
     let _ = unify t2 t' in
     let _ = nl_const [(t1, Not); (t2, Not)] (t', Not) in
     let _ = nl_const [(t1, Not); (t2, Both)] (t', Internal) in
     let _ = nl_const [(t1, Both); (t2, Both)] (t', Internal) in
     let baselen = 5 + (String.length x) + 2 + (String.length y) + 3 in
     
(*
     let _ =
       defer
         (fun () ->
           match (nl t1, nl t2) with
             (* All on one line *)
           | (Not, Not) ->
              left_constraint [] 1 [t2] 0;
              mix_width [t1; t2] [t1; t2] (baselen + 3) t';
           | (Not, Both) ->
              left_constraint [] 1 [t2] 0;
              mix_width [t1] [t1] (baselen + 3) t';
              mix_width [t2] [t2] 0 t';
           | (Both, Both) ->
              left_constraint [] 1 [t1] 0;
              left_constraint [] 1 [t2] 0;
              left_constraint_eq [t1] 0 [t2] 0;
              mix_width [] [] baselen t';
              mix_width [t1] [t1] 0 t';
              mix_width [t2] [t2] 0 t';
           | _ -> raise (TypeError "Incompatible newlines")
         )
     in
 *)
     let _ =
       nl_dep_consts [t1; t2]
         [
         (* All on one line *)
           ([Not; Not],
            [build_left_constraint [] 1 [t2] 0 [];
             build_mix_width [t1; t2] [t1; t2] (baselen + 3) t']);
           ([Not; Both],
            [build_left_constraint [] 1 [t2] 0 [];
             build_mix_width [t1] [t1] (baselen + 3) t';
             build_mix_width [t2] [t2] 0 t']);
           ([Both; Both],
            [build_left_constraint [] 1 [t1] 0 [];
             build_left_constraint [] 1 [t2] 0 [];
             build_left_constraint_eq [t1] 0 [t2] 0 [];
             build_mix_width [] [] baselen t';
             build_mix_width [t1] [t1] 0 t';
             build_mix_width [t2] [t2] 0 t'])]
     in
     mk t2 (ELetPair (x, y, e1', e2'))
  | EApp (e1, e2) ->
     let e1' = typecheck_exp c e1 in
     let e2' = typecheck_exp c e2 in
     let (t1, t2) = (ann e1', ann e2') in
     let tr = new_type () in
     let _ = unify_skip t1 (TArrow (t2, tr)) in
     let t' = new_type () in
     let _ = unify tr t' in
     let _ = unify_nl tr t' in
(*
     let _ =
       defer
         (fun () ->
           match (nl t1, nl t2) with
           (* fun arg *)
           | (Not, Not) ->
              left_constraint [t1] 0 [t'] 0;
              mix_width [t2] [t1; t2] 1 [t']
                        (* fun
                            arg *)
           | (Bot, Internal)
             | (Internal, Top) ->
              left_constraint [t1] 1 [t2] 0;
              left_constraint [t1] 0 [t'] 0;
              width_constraint [t1] 0; [t'] 0;
         )
     in
 *)
     let _ =
       nl_dep_consts [t1; t2]
         [(* fun arg *)
           ([Not; Not],
            [build_left_constraint [t1] 0 [t'] 0 [];
             build_mix_width [t2] [t1; t2] 1 t']);
                        (* fun
                            arg *)
           ([Bottom; Internal],
            [build_left_constraint [t1] 1 [t2] 0 [];
             build_left_constraint [t1] 0 [t'] 0 [];
             build_width_constraint [t1] 0 [t'] 0 []]);
           ([Internal; Top],
            [build_left_constraint [t1] 1 [t2] 0 [];
             build_left_constraint [t1] 0 [t'] 0 [];
             build_width_constraint [t1] 0 [t'] 0 []])]
     in
     mk t' (EApp (e1', e2'))

  | EMatchList (e1, e2, h, t, e3) -> raise (TypeError "unsupported")
                                   (*
     let t1 = typecheck_exp c e1 in
     let ta = new_type () in
     let _ = unify t1 (ref (TTList ta)) in
     let t2 = typecheck_exp c e2 in
     let c' = ctx_add (ctx_add c h (SMono ta)) t (SMono t1) in
     let t3 = typecheck_exp c' e3 in
     let _ = unify t2 t3 in
     t3 *)
  | EPair (e1, e2) ->
     let e1' = typecheck_exp c e1 in
     let e2' = typecheck_exp c e2 in
     let (t1, t2) = (ann e1', ann e2') in
     let t' = new_type () in
     let _ = unify_skip t' (TProd (t1, t2)) in
     let _ = nl_const [(t1, Not); (t2, Not)] (t', Not) in
     let _ = nl_const [(t1, Internal); (t2, Top)] (t', Internal) in
(*
     let _ = defer
               (fun () ->
                 match (nl t1, nl t2) with
                 | (Not, Not) ->
                    mix_width [t1; t2] [t1; t2] 3 t'
                 | (Internal, Top) ->
                    left_constraint [t1] 1 [t2] 0;
                    mix_width [t2] [t2] 0 t')
     in
 *)
     let _ = nl_dep_consts [t1; t2]
               [([Not; Not],
                 [build_mix_width [t1; t2] [t1; t2] 3 t']);
                ([Internal; Top],
                 [build_left_constraint [t1] 1 [t2] 0 [];
                  build_mix_width [t2] [t2] 0 t'])
               ]
     in
     mk t' (EPair (e1', e2'))
  | ECons (e1, e2) -> raise (TypeError "unsupported")
                    (*
     let t1 = typecheck_exp c e1 in
     let t2 = typecheck_exp c e2 in
     let tl = ref (TTList t1) in
     let _ = unify t2 tl in
     t2
                     *)
  | EAnnot (e, t) -> raise (TypeError "unsupported")
                   (*
     let t' = typecheck_exp c e in
     let _ = unify (varify t) t' in
     t'*)
  | EParen e ->
     let e' = typecheck_exp c e in
     let t = ann e' in
     let t' = new_type () in
     let _ = unify t t' in
     let _ = nl_const [(t, Not)] (t', Not) in
     let _ = nl_const [(t, Top)] (t', Internal) in
     let _ = nl_const [(t, Bottom)] (t', Internal) in
     let _ = nl_const [(t, Internal)] (t', Internal) in
     let _ = nl_const [(t, Both)] (t', Internal) in
(*
     let _ = defer
               (fun () ->
                 match nl t with
                 | Not -> width_constraint t 2 t' 0;
                 | Both -> width_constraint t 0 t' 0
                 | _ -> width_constraint t 1 t' 0)
     in
 *)
     let _ = nl_dep_consts [t]
               [([Not], [build_width_constraint [t] 2 [t'] 0 []]);
                ([Both], [build_width_constraint [t] 0 [t'] 0 []]);
                ([Top], [build_width_constraint [t] 1 [t'] 0 []]);
                ([Bottom], [build_width_constraint [t] 1 [t'] 0 []]);
                ([Internal], [build_width_constraint [t] 1 [t'] 0 []])]
                
     in
     mk t' (EParen e')
  | ELinebreakAfter e ->
     let e' = typecheck_exp c e in
     let t = ann e' in
     let t' = new_type () in
     let _ = unify t t' in
     let _ = nl_const [(t, Not)] (t', Bottom) in
     let _ = nl_const [(t, Top)] (t', Both) in
     let _ = nl_const [(t, Bottom)] (t', Bottom) in
     let _ = nl_const [(t, Internal)] (t', Bottom) in
     let _ = nl_const [(t, Both)] (t', Both) in
     let _ = width_constraint [t] 0 [t'] 0 [] in
     let _ = left_constraint [t] 0 [t'] 0 [] in
     let _ = left_constraint [t'] 0 [t] 0 [] in
     mk t' (ELinebreakAfter e')
  | ELinebreakBefore e ->
     let e' = typecheck_exp c e in
     let t = ann e' in
     let t' = new_type () in
     let _ = unify t t' in
     let _ = nl_const [(t, Not)] (t', Top) in
     let _ = nl_const [(t, Top)] (t', Top) in
     let _ = nl_const [(t, Bottom)] (t', Both) in
     let _ = nl_const [(t, Internal)] (t', Top) in
     let _ = nl_const [(t, Both)] (t', Both) in
     let _ = width_constraint [t] 0 [t'] 0 [] in
     let _ = left_constraint [t] 0 [t'] 0 [] in
     let _ = left_constraint [t'] 0 [t] 0 [] in
     mk t' (ELinebreakBefore e')
     
  | ESpaceAfter e ->
     let e' = typecheck_exp c e in
     let t = ann e' in
     let t' = new_type () in
     let _ = unify t t' in
     let _ = unify_nl t t' in
     let _ = width_constraint [t] 1 [t'] 0 [] in
     mk t' (ESpaceAfter e')
  | ESpaceBefore e ->
     let e' = typecheck_exp c e in
     let t = ann e' in
     let t' = new_type () in
     let _ = unify t t' in
     let _ = unify_nl t t' in
     let _ = left_constraint [t] 1 [t'] 0 [] in
     let _ = width_constraint [t] 1 [t'] 0 [] in
     mk t' (ESpaceBefore e')


  (*
let rec typecheck_value (c: ctx) (v: value) : typ * substitution =
  match v with
  | VConst c -> (type_of_const c, [])
  | Var x ->
     (match ctx_find c x with
      | None -> raise (TypeError (Printf.sprintf "unbound identifier %s"
                                    x))
      | Some t -> t)
  | VPair (v1, v2) ->
     let (t1, s1) = typecheck_value c v1 in
     let (t2, s2) = typecheck_value (sub_ctx s1 c) v2 in
     (TProd (t1, t2), s2 @ s1)
  | VCons (v1, v2) ->
     let (t1, s1) = typecheck_value c v1 in
     let (t2, s2) = typecheck_value (sub_ctx s1 c) v2 in
     let s3 = mgu (
 *)

     (*
let rec subtype t1 t2 =
  let pedantic_subtype (l1, w1, d1, p1) (l2, w2, d2, p2) =
    l1 >= l2
    && w1 <= w2
    && (d1 = d2 || (d1 = Not && d2 = Matched))
    && (match (p1, p2) with
        | (Atom, _) -> true
        | (Nonatom, Nonatom) -> true
        | (Nonatom, Atom) -> false)
  in
  match (t1, t2) with
  | (TInt i1, TInt i2)
    | (TString i1, TString i2)
    | (TBool i1, TBool i2)
    | (TUnit i1, TUnit i2) -> pedantic_subtype i1 i2
  | (TList (i1, t1), TList (i2, t2)) ->
     subtype t1 t2 && pedantic_subtype i1 i2
  | (TArrow (i1, t1a, t1r), TArrow (i2, t2a, t2r)) ->
     subtype t2a t1a && subtype t1r t2r && pedantic_subtype i1 i2
  | (TProd (i1, t1l, t1r), TArrow (i2, t2l, t2r)) ->
     subtype t1l t2l && subtype t1r t2r && pedantic_subtype i1 i2
  | _ -> false

let def = (0, 0, Horizontal, Atom)

exception Unsupported

let get_info (t: pedantic_type) =
  match t with
  | TInt i | TString i | TBool i | TUnit i | TList (i, _)
    | TArrow (i, _, _) | TProd (i, _, _) -> i
  | TVar _ -> raise Unsupported

let left t = let (l, _, _, _) = get_info t in l
let width t = let (_, w, _, _) = get_info t in w
let nl t = let (_, _, nl, _) = get_info t in nl
let paren t = let (_, _, _, p) = get_info t in p

let make_pedantic (t: 'a typ) i : pedantic_type =
  match t with
  | TInt _ -> TInt i
  | TString _ -> TString i
  | TBool _ -> TBool i
  | TUnit _ -> TUnit i
  | _ -> raise Unsupported

let rec same_base (a: 'a typ) (b: 'b typ) : bool =
  match (a, b) with
  | (TInt _, TInt _)
    | (TString _, TString _)
    | (TBool _, TBool _)
    | (TUnit _, TUnit _) -> true
  | (TList (_, a), TList (_, b)) -> same_base a b
  | (TArrow (_, a1, a2), TArrow (_, b1, b2)) ->
     same_base a1 b1 && same_base a2 b2
  | (TProd (_, a1, a2), TProd (_, b1, b2)) ->
     same_base a1 b1 && same_base a2 b2
  | (TVar a, TVar b) -> a = b
  | _ -> false

let error e t_expected t_actual =
  raise (TypeError
           (Printf.sprintf "Type Error: Expression\n%s\nhas type\n%s\nbut an expression was expected of type\n%s\n"
              (Print.string_of_expr e)
              (Print.string_of_type t_actual)
              (Print.string_of_type t_expected)))

let error_unmatched e t =
  let t_expected =
    make_pedantic t (left t, width t, Matched, paren t)
  in
  error e t_expected t

let is_matched t =
  match nl t with
  | Not | Matched -> true
  | _ -> false

let check_matched e t =
  if is_matched t then ()
  else error_unmatched e t
       
let op_width =
  function Plus | Minus | Times | Div | Lt | Gt | Eq | Concat -> 1
           | Le | Ge | Ne | And | Or -> 2
(*
let join_nl n1 n2 =
  match (n1, n2) with
  | (Top, Bottom) | (Matched, Matched) -> Matched
  | (Not, Not) -> Not
  | (Not, Matched) -> Bottom
  | (Matched, Not) -> Top
  | (Top, _) -> Top
  | (_, Bottom) -> Bottom
  | _ -> Internal
let rec syn_expr (c: ctx) (e: expr) : pedantic_type =
  match e with
  | EVar x ->
     (match ctx_find c x with
      | Some t -> t
      | None -> raise (TypeError ("unbound variable " ^ x)))
  | EConst (Num _) -> TInt def
  | EConst (String _) -> TString def
  | EConst (Bool _) -> TBool def
  | EConst Unit -> TUnit def
  | EInfixop (o, e1, e2) ->
     let (t1, t2, t3) = type_of_op o in
     let t1' = syn_expr c e1 in
     let t2' = syn_expr c e2 in
     if same_base t1 t1' then
       if same_base t2 t2' then
         make_pedantic t3
           (left t1',
            width t1' + width t2' + op_width o,
            join_nl (nl t1') (nl t2'),
            Nonatom)
       else error e2 t2 t2'
     else error e1 t1 t2'
  | EIf (e1, e2, e3) ->
     let t1 = syn_expr c e1 in
     let t2 = syn_expr c e2 in
     let t3 = syn_expr c e3 in
     let _ = check_matched e1 t1 in
     let _ = check_matched e2 t2 in
     let _ = check_matched e3 t3 in
     if same_base t1 (TBool ()) then
       if same_base t2 t3 then
         make_pedantic t2
           (0,
            max (width t2) (max (width t3) 4),
            join_nl (nl t2, nl t3),
            Nonatom)
       else error e3 t2 t3
     else raise (TypeError "if expected bool")
  | ELet (x, t, e1, e2) ->
         

       
let rec typecheck_value (c: ctx) (v: value) : tvar =
  match v with
  | VConst c -> type_of_const c
  | VPair (v1, v2) ->
     let t1 = typecheck_value c v1 in
     let t2 = typecheck_value c v2 in
     ref (TTProd (t1, t2))
  | VCons (v1, v2) ->
     let t1 = typecheck_value c v1 in
     let t2 = typecheck_value c v2 in
     let tl = ref (TTList t1) in
     let _ = unify t2 tl in
     t2
  | VFun (x, e) ->
     let xt = new_type () in
     let c' = ctx_add c x (SMono xt) in
     let t' = typecheck_exp c' e in
     ref (TTArrow (xt, t'))
  | VNamedFun (f, x, e) -> failwith "named lambdas shouldn't appear in source"
  | VAnnot (v, t) ->
     let t' = typecheck_value c v in
     let _ = unify (varify t) t' in
     t'

and typecheck_exp (c: ctx) (e: expr) : tvar =
  match e with
  | EValue v -> typecheck_value c v
  | EVar x ->
     (match ctx_find c x with
      | None -> raise (TypeError (Printf.sprintf "unbound identifier %s"
                                    x))
      | Some t -> inst t)
  | EInfixop (o, e1, e2) ->
     let (t1, t2, t3) = type_of_op o in
     let t1' = typecheck_exp c e1 in
     let t2' = typecheck_exp c e2 in
     let _ = unify t1' (varify t1) in
     let _ = unify t2' (varify t2) in
     varify t3
  | EIf (e1, e2, e3) ->
     let t1 = typecheck_exp c e1 in
     let _ = unify t1 (ref TTBool) in
     let t2 = typecheck_exp c e2 in
     let t3 = typecheck_exp c e3 in
     let _ = unify t2 t3 in
     t2
  | ELet (x, t, e1, e2) ->
     let t1 = typecheck_exp c e1 in
     let _ = (match t with
                None -> ()
              | Some t' -> unify t1 (varify t'))
     in
     let c' = ctx_add c x (gen t1) in
     let t2 = typecheck_exp c' e2 in
     t2
  | ELetFun (is_rec, f, x, t1, t2, e1, e2) ->
     let tx = new_type () in
     let _ =
       (match t1 with
        | Some t1' -> unify tx (varify t1')
        | None -> ())
     in
     let tr = new_type () in
     let _ =
       (match t2 with
        | Some t2' -> unify tr (varify t2')
        | None -> ())
     in
     let c' = ctx_add c x (SMono tx) in
     let tf = ref (TTArrow (tx, tr)) in
     let c' = if is_rec then ctx_add c' f (SMono tf) else c' in
     let te = typecheck_exp c' e1 in
     let _ = unify tr te in
     let c'' = ctx_add c f (SMono tf) in
     typecheck_exp c'' e2
  | ELetPair (x, y, e1, e2) ->
     let t1 = typecheck_exp c e1 in
     let tx = new_type () in
     let ty = new_type () in
     let _ = unify t1 (ref (TTProd (tx, ty))) in
     let c' = ctx_add (ctx_add c x (SMono tx)) y (SMono ty) in
     let t2 = typecheck_exp c' e2 in
     t2
  | EApp (e1, e2) ->
     let t1 = typecheck_exp c e1 in
     let t2 = typecheck_exp c e2 in
     let tr = new_type () in
     let _ = unify t1 (ref (TTArrow (t2, tr))) in
     tr
  | EMatchList (e1, e2, h, t, e3) ->
     let t1 = typecheck_exp c e1 in
     let ta = new_type () in
     let _ = unify t1 (ref (TTList ta)) in
     let t2 = typecheck_exp c e2 in
     let c' = ctx_add (ctx_add c h (SMono ta)) t (SMono t1) in
     let t3 = typecheck_exp c' e3 in
     let _ = unify t2 t3 in
     t3
  | EPair (e1, e2) ->
     let t1 = typecheck_exp c e1 in
     let t2 = typecheck_exp c e2 in
     ref (TTProd (t1, t2))
  | ECons (e1, e2) ->
     let t1 = typecheck_exp c e1 in
     let t2 = typecheck_exp c e2 in
     let tl = ref (TTList t1) in
     let _ = unify t2 tl in
     t2
  | EAnnot (e, t) ->
     let t' = typecheck_exp c e in
     let _ = unify (varify t) t' in
     t'
;;
       (*
let typecheck_decl (c: ctx) (d: decl) : tvar =
  match d with
  | DVal (_, topt, e) ->
     let t = typecheck_exp c e in
     let t' =
       (match topt with
        | Some t' ->
           let t' = varify t' in
           unify t t';
           t'
        | None -> t)
     in
     t'
  | DFun (is_rec, f, x, t1, t2, e) ->
     let tx = new_type () in
     let _ =
       (match t1 with
        | Some t1' -> unify tx (varify t1')
        | None -> ())
     in
     let tr = new_type () in
     let _ =
       (match t2 with
        | Some t2' -> unify tr (varify t2')
        | None -> ())
     in
     let c' = ctx_add c x (SMono tx) in
     let tf = ref (TTArrow (tx, tr)) in
     let c' = if is_rec then ctx_add c' f (SMono tf) else c' in
     let te = typecheck_exp c' e in
     let _ = unify tr te in
     tf

let var_of_decl d =
  match d with
  | DVal (x, _, _) -> x
  | DFun (_, f, _, _, _, _) -> f
     
let typecheck_prog ((ds, e) : prog) : tvar =
  let rec typecheck_decls (c: ctx) (ds: decl list) =
    match ds with
    | [] -> c
    | d::ds ->
       let td = typecheck_decl c d in
       let gtd = gen td in
       let tdm = inst gtd in
       let x = var_of_decl d in
       let _ = Printf.printf "%s: %s\n"
                 x
                 (string_of_ttyp tdm)
       in
       let c' = ctx_add c x gtd in
       typecheck_decls c' ds
  in
  let c = typecheck_decls empty_ctx ds in
  typecheck_exp c e
  *)
  *)
  *)

let print_model m = Printf.printf "%s\n" (Z3.Model.to_string m)

let print_with_model (e: utype expr) =
  let f : string -> utype -> string =
    match Z3.Solver.get_model solver with
    | Some m ->
       (fun e a -> Printf.sprintf "(%s : %s)" e (string_of_utype m a))
    | None -> (fun e a -> e)
  in
  Printf.printf "%s\n" (Print.string_of_expr f e)

                  
let typecheck_exp_full e =
  let e' = typecheck_exp empty_ctx e in
  let t = ann e' in
  let () = left_constraint_eq [] 0 [t] 0 [] in
  let () = width_constraint [t] 0 [] 80 [] in
  let _ = solve_consts () in
  let _ = match Z3.Solver.get_model solver with
    | Some model ->
       print_model model;
       Printf.printf "width: %s\n"
         (match Z3.Model.eval model ((fst t).width) false with
          | Some n -> Z3.Expr.to_string n
          | None -> "ERROR")
    | None -> ()
  in
  let _ = print_with_model e' in
  t


