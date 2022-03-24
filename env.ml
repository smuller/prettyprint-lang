open Types

module S =
  struct
    type t = string
    let compare = String.compare
  end

module VMap = Map.Make(S)

type env = value VMap.t

let empty_ctx = VMap.empty

let env_add (e: env) (x: string) (v: value) = VMap.add x v e
let env_find (e: env) (x: string) = VMap.find_opt x e
