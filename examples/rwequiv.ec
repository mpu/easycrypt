require import AllCore Distr.

type t, u.

module BiSample = {
  proc sample(dt : t distr, du : u distr) = {
    var t, u;

    t <$ dt;
    u <$ du;
    return (t, u);
  }
}.

module Prod = {
  proc sample(dt : t distr, du : u distr) = {
    var tu;

    tu <$ dt `*` du;
    return tu;
  }
}.

equiv eq: BiSample.sample ~ Prod.sample: ={arg} ==> ={res}.
proof. admitted.

equiv eq': BiSample.sample ~ Prod.sample: ={arg} ==> ={res}.
proof.
proc.
transitivity {1} { (t,u) <@ BiSample.sample(dt,du); }
  (={dt,du} ==> ={t,u})
  (={dt,du} ==> (t,u){1} = tu{2});
  [ 4:transitivity {1} { (t,u) <@ Prod.sample(dt,du); }
        (={dt,du} ==> ={t,u})
        (={dt,du} ==> (t,u){1} = tu{2})];
  [   3:by inline *; auto
  | 2,5:done
  |   6:by call eq ].
+ smt().
+ smt().
by inline *; auto=> /#.
qed.

pred P. pred Q.
axiom PQ: P => Q.

require Distr.
equiv eq2: BiSample.sample ~ Prod.sample: arg{2} = arg{1} /\ P ==> res{2} = res{1} /\ Q.
proof.
proc.
rewrite equiv [{1} 1 eq (dt, du) (t,u) (dt, du) tu]=> //.
+ move=> &1 &2 H; exists dt{1} du{1}; split.
  + congr; try reflexivity.
  exact: H.
+ move=> &1 &2 H; exists dt{1} du{1}; split.
  + reflexivity.
  exact: H.
by inline *; auto=> /> &1 /PQ /#.
qed.

equiv eq3: Prod.sample ~ BiSample.sample: arg{2} = arg{1} /\ P ==> res{2} = res{1} /\ Q.
proof.
proc.
rewrite equiv [{2} 1 eq (dt, du) (t,u) (dt, du) tu]=> //.
+ move=> &1 &2 H; exists dt{1} du{1}; split.
  + congr; try reflexivity.
  exact: H.
+ move=> &1 &2 H; exists dt{1} du{1}; split.
  + reflexivity.
  exact: H.
by inline *; auto=> /> &1 /PQ /#.
qed.
