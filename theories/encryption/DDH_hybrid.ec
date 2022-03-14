(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2021 - Inria
 * Copyright (c) - 2012--2021 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

require import Real Int IntDiv.

(** The group **)
require (*--*) Group.

clone export Group.CyclicGroup.

(* The group has order p *)
axiom prime_order: prime order.

clone import PowZMod
proof
  prime_order by rewrite prime_order.
export ZModE ZModE.DZmodP.

require (*--*) Hybrid.

op n : { int | 0 < n } as n_pos.
clone import Hybrid as H with
  type input <- unit,
  type output <- group * group * group,
  type inleaks <- unit,
  type outleaks <- unit,
  type outputA <- bool,
  op q <- n 
  proof* by smt(n_pos).

module DDHl = {
  proc orcl () : group * group * group = {
    var x, y: exp;
    x <$ dunifin;
    y <$ dunifin;
    return (g^x, g^y, g^(x * y));
  }
}.

module DDHr = {
  proc orcl () : group * group * group = {
    var x, y, z: exp;
    x <$ dunifin;
    y <$ dunifin;
    z <$ dunifin;
    return (g^x, g^y, g^z);
  }
}.

module DDHb : H.Orclb = {
  proc leaks () : unit = { }
  proc orclL = DDHl.orcl
  proc orclR = DDHr.orcl
}.

lemma islossless_leaks : islossless DDHb.leaks.
proof. by proc; auto. qed.

lemma islossless_orcl1 : islossless DDHb.orclL.
proof. by proc; auto; rewrite dunifin_ll. qed.

lemma islossless_orcl2 : islossless DDHb.orclR.
proof. by proc; auto; rewrite dunifin_ll. qed.

section.

declare module A <: H.AdvOrclb {Count, HybOrcl, DDHb}.

declare axiom losslessA : forall (Ob0 <: Orclb{A}) (LR <: Orcl{A}),
  islossless LR.orcl =>
  islossless Ob0.leaks =>
  islossless Ob0.orclL =>
  islossless Ob0.orclR => islossless A(Ob0, LR).main.

lemma Hybrid:
  forall &m,
    Pr[Ln(DDHb, HybGame(A)).main() @ &m : (res /\ HybOrcl.l <= n) /\ Count.c <= 1 ] -
    Pr[Rn(DDHb, HybGame(A)).main() @ &m : (res /\ HybOrcl.l <= n) /\ Count.c <= 1 ] =
    1%r / n%r *
     (Pr[Ln(DDHb, A).main() @ &m : (res /\ Count.c <= n) ] -
      Pr[Rn(DDHb, A).main() @ &m : (res /\ Count.c <= n) ]).
proof.
move=> &m.
apply (H.Hybrid_div DDHb A _ _ _ _ &m (fun _ _ _ (r:bool)=> r)).
+ exact: islossless_leaks.
+ exact: islossless_orcl1.
+ exact: islossless_orcl2.
+ exact: losslessA.
exact/StdOrder.IntOrder.gtr_eqF/n_pos.
qed.

end section.
