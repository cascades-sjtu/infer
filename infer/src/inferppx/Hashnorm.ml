(*
 * Copyright (c) Facebook, Inc. and its affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)
open! IStd
open Ppxlib

let normalize_from_typename = function "t" -> "normalize" | s -> "normalize_" ^ s

let normalize_of_longident ?(suffix = "") lid =
  match lid with
  | Lident "string" ->
      (* [HashNormalizer.StringNormalizer.normalize] *)
      Ldot (Ldot (Lident "HashNormalizer", "StringNormalizer"), "normalize" ^ suffix)
  | Lident typename ->
      (* [t]/[x] is not enclosed in a module *)
      Lident (normalize_from_typename typename ^ suffix)
  | Ldot (l, typename) ->
      (* [M.t]/[M.x] *)
      Ldot (Ldot (l, "Normalizer"), normalize_from_typename typename ^ suffix)
  | _ ->
      Format.eprintf "Could not parse ident: %a@\n" Common.pp_longident lid ;
      assert false


(* ident `A.B.C.normalize`/`A.B.C.normalize_opt` from the type `A.B.C.t`/`A.B.C.t option` *)
let normalize_of_core_type ~loc ct =
  match ct.ptyp_desc with
  | Ptyp_constr (l, []) ->
      (* monomorphic type *)
      normalize_of_longident l.txt |> Loc.make ~loc
  | Ptyp_constr ({txt= Lident "option"}, [{ptyp_desc= Ptyp_constr (l, [])}]) ->
      (* option type *)
      normalize_of_longident ~suffix:"_opt" l.txt |> Loc.make ~loc
  | Ptyp_constr _
  | Ptyp_any
  | Ptyp_var _
  | Ptyp_arrow _
  | Ptyp_tuple _
  | Ptyp_object _
  | Ptyp_class _
  | Ptyp_alias _
  | Ptyp_variant _
  | Ptyp_poly _
  | Ptyp_package _
  | Ptyp_extension _ ->
      assert false


(* [let name = body] where [name] = normalization function from type name *)
let make_normalize_function ~loc typ_name body =
  let func_name = normalize_from_typename typ_name.txt in
  Common.make_function ~loc func_name body


(* [let var' = (normalize_of_core_type typ) var in acc] *)
let let_varprime_equal_f_var_expr ~loc acc var typ =
  let lhs_pat = Ast_helper.Pat.var ~loc (Loc.make ~loc (var ^ "'")) in
  let var_expr = Common.make_ident_exp ~loc var in
  let f = normalize_of_core_type ~loc typ |> Ast_helper.Exp.ident ~loc in
  [%expr
    let [%p lhs_pat] = [%e f] [%e var_expr] in
    [%e acc]]


(* [phys_equal var var'] *)
let var_phys_equal_varprime ~loc var =
  let var_expr = Common.make_ident_exp ~loc var in
  let varprime_expr = Common.make_ident_exp ~loc (var ^ "'") in
  [%expr phys_equal [%e var_expr] [%e varprime_expr]]


(* [if (phys_equal a a' && phys_equal b b' && ...) then t else else_exp] *)
let if_phys_equal_then_t ~loc ~else_exp vars =
  let guard = List.map vars ~f:(var_phys_equal_varprime ~loc) |> Common.conjunction ~loc in
  [%expr if [%e guard] then t else [%e else_exp]]


(* [M.normalize (t : core_type)] *)
let create_normalize_initializer ~loc t_expr core_type =
  let func_lid = normalize_of_core_type ~loc core_type in
  let func_name = Ast_helper.Exp.ident ~loc func_lid in
  [%expr [%e func_name] [%e t_expr]]


(* [Field.normalize t.field] *)
let create_normalize_field_initializer ~loc (ld : label_declaration) =
  let field_lid = Common.make_longident ~loc ld.pld_name.txt in
  let lhs_access = Common.access ~loc "t" field_lid in
  create_normalize_initializer ~loc lhs_access ld.pld_type


let should_normalize_type core_type =
  match core_type.ptyp_desc with
  | Ptyp_constr ({txt= Lident ("option" | "string")}, _) ->
      true
  | Ptyp_constr ({txt= Ldot (_, "t")}, _) ->
      true
  | _ ->
      false


let normalize_tuple_impl ~loc ptype_name core_types =
  let rhs_expr =
    if List.for_all core_types ~f:(Fn.non should_normalize_type) then (* just return [t] *)
      [%expr t]
    else
      let vars = List.mapi core_types ~f:(fun i _ -> Printf.sprintf "x%d" i) in
      let vars_pattern =
        List.map vars ~f:(fun var -> Loc.make ~loc var |> Ast_helper.Pat.var ~loc)
        |> Ast_helper.Pat.tuple ~loc
      in
      let return_tuple =
        (* [(x0, x1', x2, ...)] where a variable is primed if it's normalizable *)
        List.map2_exn vars core_types ~f:(fun var typ ->
            (if should_normalize_type typ then var ^ "'" else var) |> Common.make_ident_exp ~loc )
        |> Ast_helper.Exp.tuple ~loc
      in
      let normalizable_vars, normalizable_typs =
        List.zip_exn vars core_types
        |> List.filter ~f:(fun (_var, typ) -> should_normalize_type typ)
        |> List.unzip
      in
      let physeq_guarded = if_phys_equal_then_t ~loc normalizable_vars ~else_exp:return_tuple in
      let rhs =
        List.fold2_exn normalizable_vars normalizable_typs ~init:physeq_guarded
          ~f:(let_varprime_equal_f_var_expr ~loc)
      in
      [%expr
        let [%p vars_pattern] = t in
        [%e rhs]]
  in
  make_normalize_function ~loc ptype_name [%expr fun t -> [%e rhs_expr]]


let normalize_record_impl ~loc ptype_name (lds : label_declaration list) =
  let lds = List.filter lds ~f:(fun ld -> should_normalize_type ld.pld_type) in
  let record_exp = Common.create_record ~loc ~with_value:[%expr t] lds in
  let guarded = Common.if_phys_equal_then_var ~loc "t" lds record_exp in
  let final_expr =
    List.fold lds ~init:guarded
      ~f:(Common.let_field_equal_rhs_expr ~loc create_normalize_field_initializer)
  in
  let body = [%expr fun t -> [%e final_expr]] in
  make_normalize_function ~loc ptype_name body


let normalize_passthrough_impl ~loc ptype_name manifest_type =
  let normalize_name = normalize_from_typename ptype_name.txt in
  Common.generate_passthrough_function ~loc normalize_of_core_type normalize_name manifest_type


let normalize_type_declaration ~loc (td : type_declaration) =
  match td with
  | {ptype_kind= Ptype_record fields; ptype_name} ->
      [normalize_record_impl ~loc ptype_name fields]
  | {ptype_kind= Ptype_abstract; ptype_manifest= Some {ptyp_desc= Ptyp_tuple core_types}; ptype_name}
    ->
      [normalize_tuple_impl ~loc ptype_name core_types]
  | { ptype_kind= Ptype_abstract
    ; ptype_manifest= Some ({ptyp_desc= Ptyp_constr _} as manifest_type)
    ; ptype_name } ->
      (* passthrough case like `let nonrec t = t` *)
      [normalize_passthrough_impl ~loc ptype_name manifest_type]
  | {ptype_loc; _} ->
      let ext = Location.error_extensionf ~loc:ptype_loc "Cannot derive functions for this type" in
      [Ast_builder.Default.pstr_extension ~loc ext []]


let generate_impl ~ctxt (_rec_flag, type_declarations) =
  let loc = Expansion_context.Deriver.derived_item_loc ctxt in
  List.map type_declarations ~f:(normalize_type_declaration ~loc) |> List.concat


let _ =
  let str_type_decl = Deriving.Generator.V2.make_noarg generate_impl in
  Deriving.add "normalize" ~str_type_decl