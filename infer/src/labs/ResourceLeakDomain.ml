(*
 * Copyright (c) Facebook, Inc. and its affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)

open! IStd
module F = Format

module FiniteBounds = struct
  type t = int

  let leq ~lhs ~rhs = lhs <= rhs

  let join a b = max a b

  let widen ~prev ~next ~num_iters:_ = join prev next

  let pp fmt astate = F.fprintf fmt "%d" astate
end

module BoundsWithTop = struct
  open AbstractDomain.Types
  include AbstractDomain.TopLifted (FiniteBounds)

  let widening_threshold = 5

  let widen ~prev ~next ~num_iters =
    match (prev, next) with
    | Top, _ | _, Top ->
        Top
    | NonTop prev, NonTop next when num_iters < widening_threshold ->
        NonTop (FiniteBounds.widen ~prev ~next ~num_iters)
    | NonTop _, NonTop _ ->
        Top
end

module ReturnResource = AbstractDomain.BooleanOr
include AbstractDomain.Pair (BoundsWithTop) (ReturnResource)
open AbstractDomain.Types

let acquire_resource = function
  | (Top, _) as astate ->
      astate
  | NonTop astate, returns_resource ->
      (NonTop (astate + 1), returns_resource)


let release_resource = function
  | (Top, _) as astate ->
      astate
  | NonTop astate, returns_resource ->
      (NonTop (astate - 1), returns_resource)


let has_leak = function
  | Top, _ ->
      false
  | NonTop astate, _ when astate > 0 ->
      true
  | NonTop _, _ ->
      false


let apply_summary ~summary:(summary_count, summary_returns_resource)
    (current_count, current_returns_resource) =
  let new_count =
    match current_count with
    | Top ->
        Top
    | NonTop current_count ->
        let return_count = if summary_returns_resource then 1 else 0 in
        let summary_count = match summary_count with Top -> 0 | NonTop count -> count in
        NonTop (current_count + summary_count + return_count)
  in
  (new_count, current_returns_resource)


let record_return_resource (count, _) = (count, true)

let initial = (NonTop 0, false)

type summary = t
