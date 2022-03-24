open Types

let const_to_string c =
  match c with
  | Num n -> string_of_int n
  | String s -> s
  | Bool true -> "true"
  | Bool false -> "false"
  | Unit -> "()"
  | Nil -> "[]"

let string_of_op =
  function Plus -> "+"
         | Minus -> "-"
         | Times -> "*"
         | Div -> "/"
         | Lt -> "<"
         | Le -> "<="
         | Gt -> ">"
         | Ge -> ">="
         | Eq -> "="
         | Ne -> "<>"
         | And -> "&&"
         | Or -> "||"
         | Concat -> "^"
         
let rec pprint_value f v =
  match v with
  | VConst c -> Format.fprintf f "%s" (const_to_string c)
  | VPair (v1, v2) -> Format.fprintf f "@[(@[%a@], @[%a@])@]"
                        pprint_value v1
                        pprint_value v2
  | VCons (v1, v2) -> Format.fprintf f "@[(@[%a@])::(@[%a@])@]"
                        pprint_value v1
                        pprint_value v2
  | VFun _
    | VNamedFun _ -> Format.fprintf f "<fun>"
  | VAnnot (v, _) -> pprint_value f v

let print_value v =
  (pprint_value Format.std_formatter v;
   Format.pp_print_newline Format.std_formatter ())

let rec string_of_type t =
  match t with
  | TInt _ -> "int"
  | TString _ -> "string"
  | TBool _ -> "bool"
  | TUnit _ -> "unit"
  | TList (t) -> (string_of_type t) ^ " list"
  | TArrow (t1, t2) -> Printf.sprintf "%s -> %s"
                         (string_of_type t1)
                         (string_of_type t2)
  | TProd (t1, t2) -> Printf.sprintf "%s * %s"
                        (string_of_type t1)
                        (string_of_type t2)
(*  | TVar v -> v *)

  
let rec string_of_expr_desc f e =
  let string_of_expr = string_of_expr f in
  match e with
  | EVar x -> x
  | EConst c -> const_to_string c
  | EFun (x, e) -> Printf.sprintf "fun %s ->%s"
                     x
                     (string_of_expr e)
  | EInfixop (o, e1, e2) -> Printf.sprintf "%s%s%s"
                              (string_of_expr e1)
                              (string_of_op o)
                              (string_of_expr e2)
  | EIf (e1, e2, e3) -> Printf.sprintf "if%sthen%selse%s"
                          (string_of_expr e1)
                          (string_of_expr e2)
                          (string_of_expr e3)
  | ELet (x, Some t, e1, e2) -> Printf.sprintf "let (%s:%s) =%sin%s"
                                  x
                                  (string_of_type t)
                                  (string_of_expr e1)
                                  (string_of_expr e2)
  | ELet (x, None, e1, e2) -> Printf.sprintf "let %s =%sin%s"
                                  x
                                  (string_of_expr e1)
                                  (string_of_expr e2)
  | ELetFun (is_rec, f, x, t1, t2, e1, e2) ->
      Printf.sprintf "let %s%s %s%s =%sin%s"
        (if is_rec then "rec " else "")
        f
        (match t1 with
         | None -> x
         | Some t -> Printf.sprintf "(%s : %s)"
                       x
                       (string_of_type t))
        (match t2 with
         | None -> ""
         | Some t -> " : " ^ (string_of_type t))
        (string_of_expr e1)
        (string_of_expr e2)
  | ELetPair (x, y, e1, e2) ->
     Printf.sprintf "let (%s, %s) =%sin%s"
       x
       y
       (string_of_expr e1)
       (string_of_expr e2)
  | EPair (e1, e2) ->
     Printf.sprintf "%s, %s"
       (string_of_expr e1)
       (string_of_expr e2)
  | EApp (e1, e2) -> Printf.sprintf "%s %s"
                       (string_of_expr e1)
                       (string_of_expr e2)
  | EParen e -> Printf.sprintf "(%s)" (string_of_expr e)
  | ELinebreakAfter e -> Printf.sprintf "%s\n" (string_of_expr e)
  | ELinebreakBefore e -> Printf.sprintf "\n%s" (string_of_expr e)
  | ESpaceAfter e -> Printf.sprintf "%s " (string_of_expr e)
  | ESpaceBefore e -> Printf.sprintf " %s" (string_of_expr e)
                           
and string_of_expr f e =
  f (string_of_expr_desc f (desc e)) (ann e)
