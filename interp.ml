open Types

exception TypeError of string
exception UnboundVariable of string


let rec sub_expr (e: expr) (x: string) (v: expr) =
  match e with
  | EVar x' -> if x = x' then v else e
  | EConst _ -> e
  | EInfixop (o, e1, e2) -> EInfixop (o, sub_expr e1 x v, sub_expr e2 x v)
  | EFun (x', e') -> if x = x' then e else EFun (x', sub_expr e' x v)
  | EIf (e1, e2, e3) ->
     EIf (sub_expr e1 x v, sub_expr e2 x v, sub_expr e3 x v)
  | ELet (x', t, e1, e2) ->
     ELet (x', t, sub_expr e1 x v,
           if x <> x' then sub_expr e2 x v else e2)
  | ELetFun (is_rec, f, x', t1, t2, e1, e2) ->
     ELetFun (is_rec, f, x', t1, t2,
              (if x <> x' && (x <> f || not is_rec) then sub_expr e1 x v
               else e1),
              (if x <> f then sub_expr e2 x v else e2))
  | ELetPair (x', y, e1, e2) ->
     ELetPair (x', y, sub_expr e1 x v,
               if x <> x' && x <> y then sub_expr e2 x v else e2)
  | EApp (e1, e2) -> EApp (sub_expr e1 x v, sub_expr e2 x v)
  | EMatchList (e1, e2, h, t, e3) ->
     EMatchList (sub_expr e1 x v, sub_expr e2 x v, h, t,
                 if x <> h && x <> t then sub_expr e3 x v else e3)
  | EPair (e1, e2) -> EPair (sub_expr e1 x v, sub_expr e2 x v)
  | ECons (e1, e2) -> ECons (sub_expr e1 x v, sub_expr e2 x v)
  | EAnnot (e, t) -> EAnnot (sub_expr e x v, t)
  | EParen e -> EParen (sub_expr e x v)
  | ELinebreakAfter e -> ELinebreakAfter (sub_expr e x v)
  | ELinebreakBefore e -> ELinebreakBefore (sub_expr e x v)
  | ESpaceAfter e -> ESpaceAfter (sub_expr e x v)
  | ESpaceBefore e -> ESpaceBefore (sub_expr e x v)

let eval_op (o: infixop) (v1: value) (v2: value) : value =
  VConst (
  match (o, v1, v2) with
  | (Plus, VConst (Num n1), VConst (Num n2)) -> Num (n1 + n2)
  | (Minus, VConst (Num n1), VConst (Num n2)) -> Num (n1 - n2)
  | (Times, VConst (Num n1), VConst (Num n2)) -> Num (n1 * n2)
  | (Div, VConst (Num n1), VConst (Num n2)) -> Num (n1 / n2)
  | (Lt, VConst (Num n1), VConst (Num n2)) -> Bool (n1 < n2)
  | (Le, VConst (Num n1), VConst (Num n2)) -> Bool (n1 <= n2)
  | (Gt, VConst (Num n1), VConst (Num n2)) -> Bool (n1 > n2)
  | (Ge, VConst (Num n1), VConst (Num n2)) -> Bool (n1 >= n2)
  | (Eq, VConst (Num n1), VConst (Num n2)) -> Bool (n1 = n2)
  | (Ne, VConst (Num n1), VConst (Num n2)) -> Bool (n1 <> n2)
  | (And, VConst (Bool b1), VConst (Bool b2)) -> Bool (b1 && b2)
  | (Or, VConst (Bool b1), VConst (Bool b2)) -> Bool (b1 || b2)
  | (Concat, VConst (String s1), VConst (String s2)) -> String (s1 ^ s2)
  | _ -> raise (TypeError "op"))



let rec unannot_expr (e: expr) =
  match e with
  | EVar _ -> e
  | EValue v -> EValue (unannot_value v)
  | EInfixop (o, e1, e2) -> EInfixop (o, unannot_expr e1, unannot_expr e2)
  | EIf (e1, e2, e3) -> EIf (unannot_expr e1, unannot_expr e2, unannot_expr e3)
  | ELet (x, _, e1, e2) ->
     ELet (x, None, unannot_expr e1, unannot_expr e2)
  | ELetFun (is_rec, f, x, _, _, e1, e2) ->
     ELetFun (is_rec, f, x, None, None, unannot_expr e1, unannot_expr e2)
  | ELetPair (x, y, e1, e2) ->
     ELetPair (x, y, unannot_expr e1, unannot_expr e2)
  | EApp (e1, e2) -> EApp (unannot_expr e1, unannot_expr e2)
  | EMatchList (e1, e2, h, t, e3) ->
     EMatchList (unannot_expr e1, unannot_expr e2, h, t, unannot_expr e3)
  | EPair (e1, e2) -> EPair (unannot_expr e1, unannot_expr e2)
  | ECons (e1, e2) -> ECons (unannot_expr e1, unannot_expr e2)
  | EAnnot (e, _) -> unannot_expr e
and unannot_value (v: value) =
  match v with
  | VConst _ -> v
  | VPair (v1, v2) -> VPair (unannot_value v1, unannot_value v2)
  | VCons (v1, v2) -> VCons (unannot_value v1, unannot_value v2)
  | VFun (x, e) -> VFun (x, unannot_expr e)
  | VNamedFun (f, x, e) -> VNamedFun (f, x, unannot_expr e)
  | VAnnot (v, _) -> unannot_value v
                   
let rec eval_expr (e: expr) : value =
  match e with
  | EVar x -> raise (UnboundVariable x)
  | EValue v -> v
  | EInfixop (o, e1, e2) ->
     let v1 = eval_expr e1 in
     let v2 = eval_expr e2 in
     (*let _ = Print.print_value v1 in
     let _ = Print.print_value v2 in *)
     eval_op o v1 v2
  | EIf (e1, e2, e3) ->
     let b = eval_expr e1 in
     (match b with
      | VConst (Bool true) -> eval_expr e2
      | VConst (Bool false) -> eval_expr e3
      | _ -> raise (TypeError "expected bool")
     )
  | ELet (x, t, e1, e2) ->
     let v = eval_expr e1 in
     eval_expr (sub_expr e2 x v)
  | ELetFun (is_rec, f, x, _, _, e1, e2) ->
     let e2' = sub_expr e2 f
                (if is_rec then VNamedFun (f, x, e1) else VFun (x, e1))
     in
     eval_expr e2'
  | ELetPair (x, y, e1, e2) ->
     (match eval_expr e1 with
      | VPair (v1, v2) ->
         eval_expr (sub_expr (sub_expr e2 x v1) y v2)
      | _ -> raise (TypeError "expected pair"))
  | EApp (e1, e2) ->
     let v2 = eval_expr e2 in
     (match eval_expr e1 with
      | VFun (x, e) -> eval_expr (sub_expr e x v2)
      | VNamedFun (f, x, e) ->
         eval_expr (sub_expr (sub_expr e x v2) f (VNamedFun (f, x, e)))
      | _ -> raise (TypeError "expected function"))
  | EMatchList (e1, e2, h, t, e3) ->
     (match eval_expr e1 with
      | VConst Nil -> eval_expr e2
      | VCons (v1, v2) ->
         eval_expr (sub_expr (sub_expr e3 h v1) t v2)
      | _ -> raise (TypeError "expected list"))
  | EPair (e1, e2) ->
     VPair (eval_expr e1, eval_expr e2)
  | ECons (e1, e2) ->
     VCons (eval_expr e1, eval_expr e2)
  | EAnnot (e, t) ->
     VAnnot (eval_expr e, t)
                
