(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2021 - Inria
 * Copyright (c) - 2012--2021 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcUtils
open EcParsetree
open EcTypes
open EcModules
open EcFol
open EcEnv
open EcPV
open EcCHoare

open EcCoreGoal
open EcLowGoal
open EcLowPhlGoal

module PT  = EcProofTerm
module TTC = EcProofTyping

(* -------------------------------------------------------------------- *)
let wp_asgn_call env m lv res post =
  match lv with
  | None -> post
  | Some lv ->
      let lets = lv_subst m lv res in
      mk_let_of_lv_substs env ([lets], post)

let subst_args_call env m e s =
  PVM.add env pv_arg m (form_of_expr m e) s

(* -------------------------------------------------------------------- *)
let wp2_call
  env fpre fpost (lpl,fl,argsl) modil (lpr,fr,argsr) modir ml mr post hyps
=
  let fsigl = (Fun.by_xpath fl env).f_sig in
  let fsigr = (Fun.by_xpath fr env).f_sig in
  (* The wp *)
  let pvresl = pv_res and pvresr = pv_res in
  let vresl = LDecl.fresh_id hyps "result_L" in
  let vresr = LDecl.fresh_id hyps "result_R" in
  let fresl = f_local vresl fsigl.fs_ret in
  let fresr = f_local vresr fsigr.fs_ret in
  let post = wp_asgn_call env ml lpl fresl post in
  let post = wp_asgn_call env mr lpr fresr post in
  let s    = PVM.empty in
  let s    = PVM.add env pvresr mr fresr s in
  let s    = PVM.add env pvresl ml fresl s in
  let fpost = PVM.subst env s fpost in
  let post = generalize_mod env mr modir (f_imp_simpl fpost post) in
  let post = generalize_mod env ml modil post in
  let post =
    f_forall_simpl
      [(vresl, GTty fsigl.fs_ret);
       (vresr, GTty fsigr.fs_ret)]
      post in
  let spre = subst_args_call env ml (e_tuple argsl) PVM.empty in
  let spre = subst_args_call env mr (e_tuple argsr) spre in
  f_anda_simpl (PVM.subst env spre fpre) post

(* -------------------------------------------------------------------- *)
let t_hoare_call fpre fpost tc =
  let env = FApi.tc1_env tc in
  let hs = tc1_as_hoareS tc in
  let (lp,f,args),s = tc1_last_call tc hs.hs_s in
  let m = EcMemory.memory hs.hs_m in
  let fsig = (Fun.by_xpath f env).f_sig in
  (* The function satisfies the specification *)
  let f_concl = f_hoareF fpre f fpost in
  (* The wp *)
  let pvres = pv_res in
  let vres = EcIdent.create "result" in
  let fres = f_local vres fsig.fs_ret in
  let post = wp_asgn_call env m lp fres hs.hs_po in
  let fpost = PVM.subst1 env pvres m fres fpost in
  let modi = f_write env f in
  let post = generalize_mod env m modi (f_imp_simpl fpost post) in
  let post = f_forall_simpl [(vres, GTty fsig.fs_ret)] post in
  let spre = subst_args_call env m (e_tuple args) PVM.empty in
  let post = f_anda_simpl (PVM.subst env spre fpre) post in
  let concl = f_hoareS_r { hs with hs_s = s; hs_po=post} in

  FApi.xmutate1 tc `HlCall [f_concl; concl]

(* -------------------------------------------------------------------- *)
let t_choare_call fpre fpost fcost tc =
  let env = FApi.tc1_env tc in
  let chs = tc1_as_choareS tc in
  let (lp,f,args),s = tc1_last_call tc chs.chs_s in
  let m = EcMemory.memory chs.chs_m in
  let fsig = (Fun.by_xpath f env).f_sig in
  (* The function satisfies the specification *)
  let f_concl = f_cHoareF fpre f fpost fcost in
  (* The wp *)
  let pvres = pv_res in
  let vres = EcIdent.create "result" in
  let fres = f_local vres fsig.fs_ret in
  let post = wp_asgn_call env m lp fres chs.chs_po in
  let fpost = PVM.subst1 env pvres m fres fpost in
  let modi = f_write env f in
  let post = generalize_mod env m modi (f_imp_simpl fpost post) in
  let post = f_forall_simpl [(vres, GTty fsig.fs_ret)] post in
  let spre = subst_args_call env m (e_tuple args) PVM.empty in
  let post = f_anda_simpl (PVM.subst env spre fpre) post in

  (* The cost of the remaining code must be bounded by the cost of the
     conclusion [chs.chs_co], minus the cost of the call [fcost], and minus
     the cost of the arguments' evaluation.
     Remark: the cost of the evaluation of the return is accounted for in
     [fcost]. *)
  let args_cost : form =
    List.fold_left (fun cost e ->
      f_xadd cost (EcCHoare.cost_of_expr_any chs.chs_m e)
    ) f_x0 args
  in
  let { cond = cond1; res = cost } = cost_sub ~c:chs.chs_co ~sub:fcost in
  let { cond = cond2; res = cost } = EcCHoare.cost_sub_self ~c:cost ~sub:args_cost in
  let concl = f_cHoareS_r { chs with chs_s = s;
                                     chs_po = post;
                                     chs_co = cost } in

  FApi.xmutate1 tc `HlCall [f_concl; cond1; cond2; concl]

(* -------------------------------------------------------------------- *)
let bdhoare_call_spec pf fpre fpost f cmp bd opt_bd =
  let msg =
    "optional bound parameter not allowed for upper-bounded judgements" in

  match cmp, opt_bd with
  | FHle, Some _  -> tc_error pf "%s" msg
  | FHle, None    -> f_bdHoareF fpre f fpost FHle bd
  | FHeq, Some bd -> f_bdHoareF fpre f fpost FHeq bd
  | FHeq, None    -> f_bdHoareF fpre f fpost FHeq bd
  | FHge, Some bd -> f_bdHoareF fpre f fpost FHge bd
  | FHge, None    -> f_bdHoareF fpre f fpost FHge bd

(* -------------------------------------------------------------------- *)
let t_bdhoare_call fpre fpost opt_bd tc =
  let env = FApi.tc1_env tc in
  let bhs = tc1_as_bdhoareS tc in
  let (lp,f,args),s = tc1_last_call tc bhs.bhs_s in
  let m = EcMemory.memory bhs.bhs_m in
  let fsig = (Fun.by_xpath f env).f_sig in
  let f_concl =
    bdhoare_call_spec !!tc fpre fpost f bhs.bhs_cmp bhs.bhs_bd opt_bd in

  (* The wp *)
  let pvres = pv_res in
  let vres = EcIdent.create "result" in
  let fres = f_local vres fsig.fs_ret in
  let post = wp_asgn_call env m lp fres bhs.bhs_po in
  let fpost = PVM.subst1 env pvres m fres fpost in
  let modi = f_write env f in
  let post =
    match bhs.bhs_cmp with
    | FHle -> f_imp_simpl   post fpost
    | FHge -> f_imp_simpl  fpost  post

    | FHeq when f_equal bhs.bhs_bd f_r0 ->
        f_imp_simpl post fpost

    | FHeq when f_equal bhs.bhs_bd f_r1 ->
        f_imp_simpl  fpost post

    | FHeq -> f_iff_simpl fpost  post in

  let post = generalize_mod env m modi post in
  let post = f_forall_simpl [(vres, GTty fsig.fs_ret)] post in
  let spre = subst_args_call env m (e_tuple args) PVM.empty in
  let post = f_anda_simpl (PVM.subst env spre fpre) post in

  (* most of the above code is duplicated from t_hoare_call *)
  let concl = match bhs.bhs_cmp, opt_bd with
    | FHle, None ->
        f_hoareS bhs.bhs_m bhs.bhs_pr s post
    | FHeq, Some bd ->
        f_bdHoareS_r { bhs with
          bhs_s = s; bhs_po = post; bhs_bd = f_real_div bhs.bhs_bd bd; }
    | FHeq, None ->
        f_bdHoareS_r { bhs with
          bhs_s = s; bhs_po = post; bhs_bd = f_r1; }
    | FHge, Some bd ->
        f_bdHoareS_r { bhs with
          bhs_s = s; bhs_po = post; bhs_bd = f_real_div bhs.bhs_bd bd; }
    | FHge, None ->
        f_bdHoareS_r { bhs with
          bhs_s = s; bhs_po = post; bhs_cmp = FHeq; bhs_bd = f_r1; }
    | _, _ -> assert false
  in

  FApi.xmutate1 tc `HlCall [f_concl; concl]

(* -------------------------------------------------------------------- *)
let t_equiv_call fpre fpost tc =
  let env, hyps, _ = FApi.tc1_eflat tc in
  let es = tc1_as_equivS tc in
  let (lpl,fl,argsl),sl = tc1_last_call tc es.es_sl in
  let (lpr,fr,argsr),sr = tc1_last_call tc es.es_sr in
  let ml = EcMemory.memory es.es_ml in
  let mr = EcMemory.memory es.es_mr in
  (* The functions satisfy their specification *)
  let f_concl = f_equivF fpre fl fr fpost in
  let modil = f_write env fl in
  let modir = f_write env fr in
  (* The wp *)
  let post =
    wp2_call env fpre fpost
      (lpl,fl,argsl) modil (lpr,fr,argsr) modir
      ml mr es.es_po hyps
  in
  let concl =
    f_equivS_r { es with es_sl = sl; es_sr = sr; es_po = post; } in

  FApi.xmutate1 tc `HlCall [f_concl; concl]

(* -------------------------------------------------------------------- *)
let t_equiv_call1 side fpre fpost tc =
  let env = FApi.tc1_env tc in
  let equiv = tc1_as_equivS tc in

  let (me, stmt) =
    match side with
    | `Left  -> (EcMemory.memory equiv.es_ml, equiv.es_sl)
    | `Right -> (EcMemory.memory equiv.es_mr, equiv.es_sr)
  in

  let (lp, f, args), fstmt = tc1_last_call tc stmt in
  let fsig = (Fun.by_xpath f env).f_sig in

  (* The function satisfies its specification *)
  let fconcl = f_bdHoareF fpre f fpost FHeq f_r1 in

  (* WP *)
  let pvres  = pv_res in
  let vres   = LDecl.fresh_id (FApi.tc1_hyps tc) "result" in
  let fres   = f_local vres fsig.fs_ret in
  let post   = wp_asgn_call env me lp fres equiv.es_po in
  let subst  = PVM.add env pvres me fres PVM.empty in
  let msubst = Fsubst.f_bind_mem Fsubst.f_subst_id EcFol.mhr me in
  let fpost  = PVM.subst env subst (Fsubst.f_subst msubst fpost) in
  let modi   = f_write env f in
  let post   = f_imp_simpl fpost post in
  let post   = generalize_mod env me modi post in
  let post   = f_forall_simpl [(vres, GTty fsig.fs_ret)] post in
  let spre   = PVM.empty in
  let spre   = subst_args_call env me (e_tuple args) spre in
  let post   =
    f_anda_simpl (PVM.subst env spre (Fsubst.f_subst msubst fpre)) post in
  let concl  =
    match side with
    | `Left  -> { equiv with es_sl = fstmt; es_po = post; }
    | `Right -> { equiv with es_sr = fstmt; es_po = post; } in
  let concl  = f_equivS_r concl in

  FApi.xmutate1 tc `HlCall [fconcl; concl]

(* -------------------------------------------------------------------- *)
let call_error env tc f1 f2 =
  tc_error_lazy !!tc (fun fmt ->
      let ppe = EcPrinting.PPEnv.ofenv env in
      Format.fprintf fmt
        "call cannot be used with a lemma referring to `%a': \
         the last statement is a call to `%a'"
        (EcPrinting.pp_funname ppe) f1
        (EcPrinting.pp_funname ppe) f2)

let t_call side ax tc =
  let env   = FApi.tc1_env  tc in
  let concl = FApi.tc1_goal tc in

  match ax.f_node, concl.f_node with
  | FhoareF hf, FhoareS hs ->
      let (_, f, _), _ = tc1_last_call tc hs.hs_s in
      if not (EcEnv.NormMp.x_equal env hf.hf_f f) then
        call_error env tc hf.hf_f f;
      t_hoare_call hf.hf_pr hf.hf_po tc

  | FcHoareF chf, FcHoareS chs ->
      let (_, f, _), _ = tc1_last_call tc chs.chs_s in
      if not (EcEnv.NormMp.x_equal env chf.chf_f f) then
        call_error env tc chf.chf_f f;
      t_choare_call chf.chf_pr chf.chf_po chf.chf_co tc

  | FbdHoareF hf, FbdHoareS hs ->
      let (_, f, _), _ = tc1_last_call tc hs.bhs_s in
      if not (EcEnv.NormMp.x_equal env hf.bhf_f f) then
        call_error env tc hf.bhf_f f;
      t_bdhoare_call hf.bhf_pr hf.bhf_po None tc

  | FequivF ef, FequivS es ->
      let (_, fl, _), _ = tc1_last_call tc es.es_sl in
      let (_, fr, _), _ = tc1_last_call tc es.es_sr in
      if not (EcEnv.NormMp.x_equal env ef.ef_fl fl) ||
         not (EcEnv.NormMp.x_equal env ef.ef_fr fr) then
        tc_error_lazy !!tc (fun fmt ->
          let ppe = EcPrinting.PPEnv.ofenv env in
            Format.fprintf fmt
              "call cannot be used with a lemma referring to `%a/%a': \
               the last statement is a call to `%a/%a'"
              (EcPrinting.pp_funname ppe) ef.ef_fl
              (EcPrinting.pp_funname ppe) ef.ef_fr
              (EcPrinting.pp_funname ppe) fl
              (EcPrinting.pp_funname ppe) fr);
      t_equiv_call ef.ef_pr ef.ef_po tc

  | FbdHoareF hf, FequivS _ ->
      let side =
        match side with
        | None -> tc_error !!tc "call: a side {1|2} should be provided"
        | Some side -> side
      in
        t_equiv_call1 side hf.bhf_pr hf.bhf_po tc

  | _, _ -> tc_error !!tc "call: invalid goal shape"

(* -------------------------------------------------------------------- *)
let mk_inv_spec (_pf : proofenv) env inv fl fr =
  match NormMp.is_abstract_fun fl env with
  | true ->
    let { top = topl; fsig = sigl; oi_param = oil; },
        { top = topr; fsig = sigr } =
      EcLowPhlGoal.abstract_info2 env fl fr
    in
    let eqglob = f_eqglob topl mleft topr mright in
    let lpre = if is_in oil then [eqglob;inv] else [inv] in
    let eq_params =
      f_eqparams
        sigl.fs_arg sigl.fs_anames mleft
        sigr.fs_arg sigr.fs_anames mright in
    let eq_res = f_eqres sigl.fs_ret mleft sigr.fs_ret mright in
    let pre    = f_ands (eq_params::lpre) in
    let post   = f_ands [eq_res; eqglob; inv] in
      f_equivF pre fl fr post

  | false ->
      let defl = EcEnv.Fun.by_xpath fl env in
      let defr = EcEnv.Fun.by_xpath fr env in
      let sigl, sigr = defl.f_sig, defr.f_sig in
      let testty =
           EcReduction.EqTest.for_type env sigl.fs_arg sigr.fs_arg
        && EcReduction.EqTest.for_type env sigl.fs_ret sigr.fs_ret
      in

      if not testty then raise EqObsInError;
      let eq_params =
        f_eqparams
          sigl.fs_arg sigl.fs_anames mleft
          sigr.fs_arg sigr.fs_anames mright in
      let eq_res = f_eqres sigl.fs_ret mleft sigr.fs_ret mright in
      let pre = f_and eq_params inv in
      let post = f_and eq_res inv in
        f_equivF pre fl fr post

let process_call side info tc =
  let process_spec tc side cost =
    let (hyps, concl) = FApi.tc1_flat tc in
      match concl.f_node, side, cost with
      | FhoareS hs, None, None ->
          let (_,f,_) = fst (tc1_last_call tc hs.hs_s) in
          let penv, qenv = LDecl.hoareF f hyps in
          (penv, qenv, fun pre post -> f_hoareF pre f post)

      | FcHoareS chs, None, Some cost ->
          let (_,f,_),_ = tc1_last_call tc chs.chs_s in
          let penv, qenv = LDecl.hoareF f hyps in

          let cost  = TTC.tc1_process_form tc tcost cost in

          (penv, qenv, fun pre post -> f_cHoareF pre f post cost)

      | FbdHoareS bhs, None, None ->
          let (_,f,_) = fst (tc1_last_call tc bhs.bhs_s) in
          let penv, qenv = LDecl.hoareF f hyps in
          (penv, qenv, fun pre post ->
            bdhoare_call_spec !!tc pre post f bhs.bhs_cmp bhs.bhs_bd None)

      | FbdHoareS _, Some _, _
      | FhoareS  _, Some _, _
      | FcHoareS  _, Some _, _ ->
          tc_error !!tc "side can only be given for prhl judgements"

      | FbdHoareS _, _, Some _
      | FhoareS  _, _, Some _
      | FequivS   _, _, Some _->
          tc_error !!tc "cost can only be given for choare judgements"

      | FcHoareS _, None, None ->
            tc_error !!tc "a cost must be given for choare judgements"

      | FequivS es, None, None ->
          let (_,fl,_) = fst (tc1_last_call tc es.es_sl) in
          let (_,fr,_) = fst (tc1_last_call tc es.es_sr) in
          let penv, qenv = LDecl.equivF fl fr hyps in
          (penv, qenv, fun pre post -> f_equivF pre fl fr post)

      | FequivS es, Some side, None ->
          let fstmt = sideif side es.es_sl es.es_sr in
          let (_,f,_) = fst (tc1_last_call tc fstmt) in
          let penv, qenv = LDecl.hoareF f hyps in
          (penv, qenv, fun pre post -> f_bdHoareF pre f post FHeq f_r1)

      | _ -> tc_error !!tc "the conclusion is not a hoare or an equiv" in

  let process_inv tc side :
    LDecl.hyps * (EcFol.form -> EcPhlFun.inv_inf option -> EcFol.form)
    =
    if not (is_none side) then
      tc_error !!tc "cannot specify side for call with invariants";

    let check_none inv_info =
      if not (is_none inv_info) then
        tc_error !!tc "can supply additional information for call with an \
                       invariant only if the conclusion is a choare" in

    let hyps, concl = FApi.tc1_flat tc in
    match concl.f_node with
    | FhoareS hs ->
        let (_,f,_) = fst (tc1_last_call tc hs.hs_s) in
        let penv = LDecl.inv_memenv1 hyps in
        (penv, fun inv inv_info ->
            check_none inv_info;
            f_hoareF inv f inv)

    | FcHoareS chs ->
      let (_,f,_) = fst (tc1_last_call tc chs.chs_s) in
      let penv = LDecl.inv_memenv1 hyps in
      (penv, fun inv inv_info ->
          let inv_info = odfl (EcPhlFun.CostAbs []) inv_info in
          match inv_info with
          | EcPhlFun.Std c ->
            let env = FApi.tc1_env tc in
            if NormMp.is_abstract_fun f env then
              tc_error !!tc "the procedure %a is abstract: costs information \
                             must be supplied for its oracles (and optionally, \
                             variants)."
                (EcPrinting.pp_funname (EcPrinting.PPEnv.ofenv env)) f;

            f_cHoareF inv f inv c

          | EcPhlFun.CostAbs inv_inf ->
            let env = FApi.tc1_env tc in
            if not @@ NormMp.is_abstract_fun f env then
              tc_error !!tc "the procedure %a is not abstract: only a cost must \
                             be supplied."
                (EcPrinting.pp_funname (EcPrinting.PPEnv.ofenv env)) f;

            (* TODO A: why are we throwing away the sub-goals ?*)
            let pre, post, cost, _ =
              EcPhlFun.FunAbsLow.choareF_abs_spec !!tc env f inv inv_inf in
            f_cHoareF pre f post cost)

    | FbdHoareS bhs ->
      let (_,f,_) = fst (tc1_last_call tc bhs.bhs_s) in
      let penv = LDecl.inv_memenv1 hyps in
      (penv, fun inv inv_info ->
          check_none inv_info;
         bdhoare_call_spec !!tc inv inv f bhs.bhs_cmp bhs.bhs_bd None)

    | FequivS es ->
      let (_,fl,_) = fst (tc1_last_call tc es.es_sl) in
      let (_,fr,_) = fst (tc1_last_call tc es.es_sr) in
      let penv = LDecl.inv_memenv hyps in
      let env  = LDecl.toenv hyps in
      (penv, fun inv inv_info ->
          check_none inv_info;
          mk_inv_spec !!tc env inv fl fr)

    | _ -> tc_error !!tc "the conclusion is not a hoare or an equiv" in

  let process_upto tc side info =
    if not (is_none side) then
      tc_error !!tc "cannot specify side for call with invariants";
    let env, _, concl = FApi.tc1_eflat tc in
      match concl.f_node with
      | FequivS es ->
        let (_,fl,_) = fst (tc1_last_call tc es.es_sl) in
        let (_,fr,_) = fst (tc1_last_call tc es.es_sr) in
        let bad,invP,invQ = EcPhlFun.process_fun_upto_info info tc in
        let { top = topl; fsig = sigl; oi_param = oil; },
            { top = topr; fsig = sigr } =
          EcLowPhlGoal.abstract_info2 env fl fr
        in
        let bad2 = Fsubst.f_subst_mem mhr mright bad in
        let eqglob = f_eqglob topl mleft topr mright in
        let lpre = if is_in oil then [eqglob;invP] else [invP] in
        let eq_params =
          f_eqparams
            sigl.fs_arg sigl.fs_anames mleft
            sigr.fs_arg sigr.fs_anames mright in
        let eq_res = f_eqres sigl.fs_ret mleft sigr.fs_ret mright in
        let pre    = f_if_simpl bad2 invQ (f_ands (eq_params::lpre)) in
        let post   = f_if_simpl bad2 invQ (f_ands [eq_res;eqglob;invP]) in
        (bad,invP,invQ, f_equivF pre fl fr post)

    | _ -> tc_error !!tc "the conclusion is not an equiv" in

  let subtactic = ref t_id in

  let process_inv_inf tc hyps inv inv_inf : form * EcPhlFun.inv_inf option =
    match inv_inf with
    | None ->
      let inv = TTC.pf_process_form !!tc hyps tbool inv in
      inv, None

    | Some (P_Std c) ->
      let inv = TTC.pf_process_form !!tc hyps tbool inv in
      inv, Some (Std (TTC.pf_process_form !!tc hyps tcost c))

    | Some (P_CostAbs aii) ->
      let inv, abs_inv_inf =
        EcPhlFun.process_inv_pabs_inv_finfo tc inv aii in
      inv, Some (CostAbs abs_inv_inf)
  in

  let process_cut tc info =
    match info with
    | CI_spec (pre, post, ocost) ->
      let penv,qenv,fmake = process_spec tc side ocost in
      let pre  = TTC.pf_process_form !!tc penv tbool pre  in
      let post = TTC.pf_process_form !!tc qenv tbool post in
      fmake pre post

    | CI_inv (inv, inv_inf) ->
      let env, fmake = process_inv tc side in
      let inv, inv_inf = process_inv_inf tc env inv inv_inf in
      subtactic := (fun tc ->
        FApi.t_firsts t_trivial 2 (EcPhlFun.t_fun inv inv_inf tc));
      fmake inv inv_inf

    | CI_upto info ->
      let bad, p, q, form = process_upto tc side info in
      let t_tr = FApi.t_or (t_assumption `Conv) t_trivial in
      subtactic := (fun tc ->
        FApi.t_firsts t_tr 3 (EcPhlFun.t_equivF_abs_upto bad p q tc));
      form
  in

  let pt = PT.tc1_process_full_pterm_cut ~prcut:(process_cut tc) tc info
  in

  let pt =
    let rec doit pt =
      match TTC.destruct_product ~reduce:true (FApi.tc1_hyps tc) pt.PT.ptev_ax with
      | None   -> pt
      | Some _ -> doit (EcProofTerm.apply_pterm_to_hole pt)
    in doit pt in

  let pt, ax =
    if not (PT.can_concretize pt.PT.ptev_env) then
      tc_error !!tc "cannot infer all placeholders";
    PT.concretize pt in

  let ts =
    match (FApi.tc1_goal tc).f_node with
    | FcHoareS _ ->
      [ (fun x -> t_trivial x); t_trivial; t_id]
    | _ -> [t_id]
  in

  FApi.t_seqsub
    (t_call side ax)
    ( FApi.t_seqs
        [EcLowGoal.Apply.t_apply_bwd_hi ~dpe:true pt;
         !subtactic; t_trivial] :: ts)
    tc
