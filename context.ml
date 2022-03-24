open Types
open Unifyz3

module S =
  struct
    type t = string
    let compare = String.compare
  end

module VMap = Map.Make(S)

type ctx = utype VMap.t

let empty_ctx = VMap.empty

let ctx_add (c: ctx) (x: string) ((i, t): utype) =
  VMap.add x ({i with left = mk_int 0}, t) c
let ctx_find (c: ctx) (x: string) = VMap.find_opt x c
