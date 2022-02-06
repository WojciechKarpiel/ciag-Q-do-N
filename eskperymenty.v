From mathcomp Require Import all_ssreflect.
From mathcomp Require Import algebra.rat.
From mathcomp Require Import ssrint seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*****************************

Próby stworzenia biekcji (N*N) <-> N

*****************************)



Notation "√ n" := (Nat.sqrt n) (at level 51).


(*
0: 0,0
1: 0,1
2: 1,0
3: 1,1
4: 0,2
5: 1,2
6: 2,0
7: 2,1
8: 2,2
9: 0,3

*)
Definition zgn (kw : nat) : (nat * nat) :=
  let n := √kw in
  let r := kw - n^2 in
  if r < n then (r,n) else (n,r-n).

Eval compute in (map (fun x => (x, zgn x)) (iota 0 20)).

Definition odgn (k : nat * nat) : nat :=
  let (a, b) := k in
  if a < b then b^2 + a else a^2+a +b.


Eval compute in (map (fun x => (odgn (zgn x)) == x) (iota 0 70)).


Lemma roznica_miedzy_kwadratami n : n.+1^2 = n^2 + 2*n +1.
Proof.
  rewrite -addn1 sqrnD -![n^2 + _ + _]addnA [1 ^2 + 2*_]addnC -[1^2]/1 muln1 //.
Qed.


Lemma roznica_miedzy_kwadratami' n : n.+1^2 = (n^2 + 2*n).+1.
Proof.
  rewrite -[in RHS]addn1.  apply: roznica_miedzy_kwadratami.
Qed.

Lemma xqnat n m : (n*m)%coq_nat = n*m.
Proof.
  done.
Qed.
Print xqnat.

Lemma sqrt_specif (n: nat): (((√ n) ^ 2) <= n) && (n < ((√ n).+1)^2).
Proof.
  move : (PeanoNat.Nat.sqrt_specif n) .
  rewrite !xqnat => [[h1 h2]].
  move : h1 h2 => /leP h1 /ltP h2.
  by apply /andP; split.
Qed.
Print sqrt_specif.
Eval compute in (map (fun n => (√ n) ^ 2 + (n - ((√ n) ^ 2)) == n) (iota 0 40)).

Lemma coo a b : a <= b -> a + (b - a) == b.
Proof.

  move=>H.
  apply /eqP .
  apply: subnKC.
  assumption.
Qed.

Lemma xd n : (√ n) ^ 2 + (n - ((√ n) ^ 2)) == n.
Proof.
  apply /eqP.
  apply: subnKC.
  by move: (sqrt_specif n) => /andP; case.
Qed.  

Lemma reszta_ogr n : (n - ((√ n) ^ 2)) <= n.*2.
Proof.
  elim: n => // n H.

  case: (PeanoNat.Nat.sqrt_succ_or n) => ->.
  rewrite roznica_miedzy_kwadratami'.
  rewrite subSS.

  (*
subnDA: forall m n p : nat, n - (m + p) = n - m - p
subnDr: forall p m n : nat, m + p - (n + p) = m - n
subnDl: forall p m n : nat, p + m - (p + n) = m - n
   *)

  apply: (@leq_trans (n - (√ n) ^ 2)).

  apply: leq_sub2l.

  apply: leq_addr.
  apply: (@leq_trans n.*2).
  apply: H.
  rewrite doubleS.
  rewrite -addn1 -addn1 -addnA.
  apply: leq_addr.

  apply: (@leq_trans n.+1).
  apply: leq_subr.
  
   rewrite -addnn -addn1.
   apply: leq_addr.
Qed.

   Lemma zo1 n : odgn (zgn n) == n.
  rewrite /zgn /odgn . 
  case: ifP; [by move => ->; rewrite xd|rewrite ltnNge; move => /negbFE H].
  case: ifP.
  move: (reszta_ogr n) => Q J.
  (*
    H : nq <= r
    J : 2*nq < r (H potrzebne żeby to wywnioskować)
    Q: r <= 2*n

    2*nq < r <= 2*n
*)
  
