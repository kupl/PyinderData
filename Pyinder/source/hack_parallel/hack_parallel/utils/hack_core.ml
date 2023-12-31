(*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)

module List = struct
  include Hack_core_list

  let rec fold_left_env env l ~init ~f = match l with
    | [] -> env, init
    | x :: xs ->
        let env, init = f env init x in
        fold_left_env env xs ~init ~f

  let rec map_env env xs ~f = match xs with
    | [] -> env, []
    | x :: xs ->
        let env, x = f env x in
        let env, xs = map_env env xs ~f in
        env, x :: xs

  let rev_map_env env xs ~f =
    let f2 env init x =
      let env, x = f env x in
      env, x :: init
    in
    fold_left_env env xs ~init:[] ~f:f2

  let rec map2_env env l1 l2 ~f = match l1, l2 with
    | [], [] -> env, []
    | [], _ | _, [] -> raise @@ Invalid_argument "map2_env"
    | x1 :: rl1, x2 :: rl2 ->
        let env, x = f env x1 x2 in
        let env, rl = map2_env env rl1 rl2 ~f in
        env, x :: rl

  let for_all2 = List.for_all2
end
