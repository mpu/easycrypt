(* -------------------------------------------------------------------- *)
require import Int.
require AlgTactic.

(* -------------------------------------------------------------------- *)
instance ring with int
  op rzero = Int.zero
  op rone  = Int.one
  op add   = Int.( + )
  op opp   = Int.([-])
  op mul   = Int.( * )
  op expr  = Int.Power.( ^ )
  op sub   = Int.(-)

  proof oner_neq0 by smt
  proof addr0     by smt
  proof addrA     by smt
  proof addrC     by smt
  proof addrN     by smt
  proof mulr1     by smt
  proof mulrA     by smt
  proof mulrC     by smt
  proof mulrDl    by smt
  proof expr0     by smt
  proof exprS     by smt
  proof subrE     by smt.

(* -------------------------------------------------------------------- *)
lemma b25  (a b : int):
  (a + b) ^ 25 = ((((((((((((((((((((((((b + 25 * a) * b + 300 * a ^ 2) * b + 2300 * a ^ 3) *
                     b + 12650 * a ^ 4) *
                    b + 53130 * a ^ 5) *
                   b + 177100 * a ^ 6) *
                  b + 480700 * a ^ 7) *
                 b + 1081575 * a ^ 8) *
                b + 2042975 * a ^ 9) *
               b + 3268760 * a ^ 10) *
              b + 4457400 * a ^ 11) *
             b + 5200300 * a ^ 12) *
            b + 5200300 * a ^ 13) *
           b + 4457400 * a ^ 14) *
          b + 3268760 * a ^ 15) *
         b + 2042975 * a ^ 16) *
        b + 1081575 * a ^ 17) *
       b + 480700 * a ^ 18) *
      b + 177100 * a ^ 19) *
     b + 53130 * a ^ 20) *
    b + 12650 * a ^ 21) *
   b + 2300 * a ^ 22) *
  b + 300 * a ^ 23) *
 b + 25 * a ^ 24) *
b + (a ^ 25).
proof. by ring. qed.

lemma binom (x y : int): (x+y)^2 = x^2 + 2 * x * y + y^2.
proof. by ring. qed.

(* -------------------------------------------------------------------- *)
require Prime_field.

const k : int.

axiom ge0_k : 0 <= k.

clone import Prime_field as Zq with op q = k.

type zq = Zq.gf_q.

op (^^) : zq -> int -> zq.

axiom qf_expr0 : forall (x : zq), x^^0 = gf_q1.
axiom qf_exprS : forall (x : zq) i, 0 <= i => x^^(i+1) = x * x^^i.
axiom qf_exprN : forall (x : zq) i, 0 <= i => x^^(-i) = inv (x^^i).

op ofint : int -> zq.

axiom qf_ofint0 : ofint 0 = Zq.gf_q0.
axiom qf_ofint1 : ofint 1 = Zq.gf_q1.
axiom qf_ofintS : forall i, 0 <= i => ofint (i+1) = ofint i + gf_q1.
axiom qf_ofintN : forall (i : int), ofint (-i) = -(ofint i).

instance field with zq
  op rzero = Zq.gf_q0
  op rone  = Zq.gf_q1
  op add   = Zq.( + )
  op opp   = Zq.([-])
  op mul   = Zq.( * )
  op expr  = (^^)
  op sub   = Zq.( - )
  op ofint = ofint
  op inv   = Zq.inv
  op div   = Zq.(/)

  proof oner_neq0 by smt
  proof addr0     by smt
  proof addrA     by smt
  proof addrC     by smt
  proof addrN     by smt
  proof mulr1     by smt
  proof mulrA     by smt
  proof mulrC     by smt
  proof mulrDl    by smt
  proof mulrV     by smt
  proof expr0     by smt
  proof exprS     by smt
  proof exprN     by smt
  proof subrE     by smt
  proof divrE     by smt
  proof ofint0    by smt
  proof ofint1    by smt
  proof ofintS    by smt
  proof ofintN    by smt.

lemma rbinom (x y : zq): (x - y)^^2 = x^^2 - (ofint 2) * x * y + y^^2.
proof. by field. qed.

lemma test (x : zq): x <> gf_q0 => inv x = inv x.
proof. by intros=> h; field. qed.


(* FIXME: to be sync'ed with new ring/field tactics
lemma b24 : forall (a b c: zq) ,
    a = b =>
    c = (ofint 2) * a =>  
    c ^^ 2 = Zq.( * )( b ^^ 2) (ofint 4).
proof.
intros a b c T U.
by field T U.
qed.

lemma bij1_fst:
forall (a b c d : zq),
    a - (b * c) <> gf_q0 =>
  forall (r s : zq),
    (( a * (c * s + r)) +
       c * d - 
       c * (a * s + b * r + d)) /
          (a - b * c) = r.
proof.
intros a b c d H r s.
(*by field.*)
admit.
qed.


lemma bij1_snd:
forall (a b c d : zq), a - b * c <> Zq.gf_q0 =>
  forall (r s : zq),
      ((a * s + b * r + d - d) -
        (b * (c * s + r))) /
 (a - b * c) = s.
proof.
intros a b c d H r s.
(*by field.*)
admit.
qed.

lemma bij1:
forall (a b c d : zq), a - b * c <> Zq.gf_q0 =>
  forall (r s : zq),
    let (u,v) = (a * s + b * r + d, c * s + r) in 
    ((a * v + c * d - (c * u)) / (a - b * c),(u - d - b * v) / (a - b * c)) = (r,s).
proof.
intros a b c d H r s.
split.
(*by field.*)
admit.
(*by field.*)
admit.
qed.

lemma bij2_fst:
forall (a b c d : zq), a - b * c <> Zq.gf_q0 =>
  forall (u  v : zq),
  ((a * (u - d - b * v)) / (a - b * c)) + ( b * ((a * v + c * d - c * u) / (a - b * c))+ d) = u.
proof.
intros a b c d H u v.
(*by field.*)
admit.
qed.

lemma bij2_snd:
forall (a b c d : zq), a - b * c <> Zq.gf_q0 =>
  forall (u  v : zq),
   ((c * ((u - d) - (b * v))) / (a - (b * c))) + ((a * v + c * d - c * u) / (a - (b * c))) = v.
proof.
intros a b c d H u v.
(* by field. *)
admit.
qed.

lemma bij2:
forall (a b c d : zq), a - b * c <> Zq.gf_q0 =>
  forall (u  v : zq),
   let (r,s) = ((a * v + c * d - c * u) / (a - b * c),( u - d - b * v) / (a - b * c)) in 
   (a * s + b * r + d,c * s + r) = (u,v).
proof.
intros a b c d H u v.
split.
(*by field.*)
admit.
(*by field.*)
admit.
qed.