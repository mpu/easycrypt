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
  [ 4:transitivity {2} { tu <@ Prod.sample(dt,du); }
        (={dt,du} ==> (t,u){1} = tu{2})
        (={dt,du} ==> ={tu})];
  [ 3,7:by inline *; auto
  | 2,5:done
  |   6:call eq; skip=> /> ].
+ smt().
+ smt().
by move=> [].
qed.

pred P. pred Q.
axiom PQ: P => Q.

require Distr.
equiv eq2: BiSample.sample ~ Prod.sample: arg{2} = arg{1} /\ P ==> res{2} = res{1} /\ Q.
proof.
proc.
rewrite equiv [{1} 1 eq (dt, du) (t,u) (dt, du) tu]=> //.
+ move=> &1 &2 /> P; exists dt{1} du{1}.
  reflexivity.
+ move=> &1 &2 /> P; exists dt{1} du{1}.
  reflexivity.
by auto=> /> /PQ -> [].
qed.

equiv eq3: Prod.sample ~ BiSample.sample: arg{2} = arg{1} /\ P ==> res{2} = res{1} /\ Q.
proof.
proc.
rewrite equiv [{2} 1 eq (dt, du) (t,u) (dt, du) tu]=> //.
+ move=> &1 &2 /> P; exists dt{2} du{2}.
  reflexivity.
+ move=> &1 &2 /> P; exists dt{2} du{2}.
  reflexivity.
by auto=> /> /PQ -> [].
qed.
