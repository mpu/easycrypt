(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcUtils
open EcSymbols
open EcPath
open EcDecl
open EcModules

(* -------------------------------------------------------------------- *)
module Sp = EcPath.Sp

(* -------------------------------------------------------------------- *)
type theory = theory_item list

and theory_item =
  | Th_type      of (symbol * tydecl)
  | Th_operator  of (symbol * operator)
  | Th_axiom     of (symbol * axiom)
  | Th_schema    of (symbol * ax_schema)
  | Th_modtype   of (symbol * module_sig)
  | Th_module    of module_expr
  | Th_theory    of (symbol * (theory * thmode))
  | Th_export    of EcPath.path
  | Th_instance  of (ty_params * EcTypes.ty) * tcinstance
  | Th_typeclass of (symbol * typeclass)
  | Th_baserw    of symbol
  | Th_addrw     of EcPath.path * EcPath.path list
  | Th_reduction of (EcPath.path * rule_option * rule option) list
  | Th_auto      of (bool * int * symbol option * path list)

and tcinstance = [ `Ring of ring | `Field of field | `General of path ]
and thmode     = [ `Abstract | `Concrete ]

and rule_pattern =
  | Rule of top_rule_pattern * rule_pattern list
  | Cost of EcMemory.memenv * rule_pattern * rule_pattern (* memenv, pre, expr *)
  | Int  of EcBigInt.zint
  | Var  of EcIdent.t

and top_rule_pattern =
  [`Op of (EcPath.path * EcTypes.ty list) | `Tuple]

and rule = {
  rl_tyd   : EcDecl.ty_params;
  rl_vars  : (EcIdent.t * EcTypes.ty) list;
  rl_evars : (EcIdent.t * EcTypes.ty) list;
  rl_pvars : EcIdent.t list;
  rl_cond  : EcCoreFol.form list;
  rl_ptn   : rule_pattern;
  rl_tg    : EcCoreFol.form;
  rl_prio  : int;
}

and rule_option = {
  ur_delta  : bool;
  ur_eqtrue : bool;
  ur_mode   : [`Ax | `Sc];
}

(* -------------------------------------------------------------------- *)
type ctheory = {
  cth_desc   : ctheory_desc;
  cth_struct : ctheory_struct;
}

and ctheory_desc =
  | CTh_struct of ctheory_struct
  | CTh_clone  of ctheory_clone

and ctheory_struct = ctheory_item list

and ctheory_item =
  | CTh_type      of (symbol * tydecl)
  | CTh_operator  of (symbol * operator)
  | CTh_axiom     of (symbol * axiom)
  | CTh_schema    of (symbol * ax_schema)
  | CTh_modtype   of (symbol * module_sig)
  | CTh_module    of module_expr
  | CTh_theory    of (symbol * (ctheory * thmode))
  | CTh_export    of EcPath.path
  | CTh_instance  of (ty_params * EcTypes.ty) * tcinstance
  | CTh_typeclass of (symbol * typeclass)
  | CTh_baserw    of symbol
  | CTh_addrw     of EcPath.path * EcPath.path list
  | CTh_reduction of (EcPath.path * rule_option * rule option) list
  | CTh_auto      of (bool * int * symbol option * path list)

and ctheory_clone = {
  cthc_base : EcPath.path;
  cthc_ext  : (EcIdent.t * ctheory_override) list;
}

and ctheory_override =
| CTHO_Type   of EcTypes.ty

(* -------------------------------------------------------------------- *)
let module_comps_of_module_sig_comps
    (comps : module_sig_body)
    (restr : mod_restr) : module_comps
  =
  let onitem = function
    | Tys_function funsig ->
      let param = Msym.find funsig.fs_name restr.mr_params in
        MI_Function {
          f_name = funsig.fs_name;
          f_sig  = funsig;
          f_def  = FBabs (param, (restr.mr_cost, funsig.fs_name));
        }
  in
    List.map onitem comps

(* -------------------------------------------------------------------- *)
let module_expr_of_module_sig
    (name : EcIdent.t)
    (mp : module_type)
    (tymod : module_sig) : module_expr
  =
  (* Abstract modules must be fully applied. *)
  assert (List.length mp.mt_params = List.length mp.mt_args);

  let tycomps = module_comps_of_module_sig_comps tymod.mis_body mp.mt_restr in
    { me_name     = EcIdent.name name;
      me_body     = ME_Decl mp;
      me_comps    = tycomps;
      me_sig_body = tymod.mis_body;
      me_params   = tymod.mis_params ; }
