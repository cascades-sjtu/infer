(*
 * Copyright (c) Facebook, Inc. and its affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)

open! IStd
module F = Format

type t = int

let leq ~lhs:_ ~rhs:_ = assert false

let join _a _b = assert false

let widen ~prev:_ ~next:_ ~num_iters:_ = assert false

let pp fmt astate = F.fprintf fmt "%d" astate

let acquire_resource astate = astate + 1

let release_resource astate = astate - 1

let has_leak astate = astate > 0

let initial = 0

type summary = t
