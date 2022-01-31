From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From mathcomp Require Import algebra.rat.


(* każdy skończony ciąg liczb wymiernych da się zakodować liczbą naturalną *)
Definition hipoteza :=
  exists f : nat -> seq rat, forall qs : seq rat, exists n, f n = qs.


(* Najpierw potrzeba funkcji parującej.
   Ta jest prosta, ale nie jest bijekcją.
   Za Stefan G. Simpson - "Subsystems of Second Order Arithmetic" (II.2)
*)
Definition zgniec (para: nat*nat) : nat := let (i, j) := para in ((i+j)^2)+i.
Check Nat.sqrt.
Definition odgniec (k: nat): (nat*nat) :=
  let m := Nat.sqrt k in
  let i := k - (m^2) in
  (i,m-i).


(* Jeśli będę chciał potem poszpanować, to zmienię powyższą funkcję parującą na bijekcję *)
(* 
0 1 3 6 A F
2 4 7 B 10
5 8 C 11
9 D 12
E

m-ty wiersz n-ta kolmna
 *)
Definition zgniec' (para: nat*nat) : nat :=
  let (m, n) := para in (((m+n)*(m+n+1)) %/ 2)+m.

Definition odgniec' (n : nat) : nat * nat :=
  let fix f (a nr_przek na_przek : nat) : nat * nat :=
    match a with
    | O => (nr_przek, na_przek)
    | n.+1 => if nr_przek == na_przek then f n nr_przek.+1 0 else f n nr_przek na_przek.+1
    end
  in let (nr_przek, na_przek) := f n 0 0
     in (na_przek, nr_przek - na_przek).
(* No ale podmiankę zachowam se na koniec *)


Lemma sqrp1 n : n.+1^2 = n^2 + 2*n +1.
Proof.
  rewrite -addn1 sqrnD -![n^2 + _ + _]addnA [1 ^2 + 2*_]addnC -[1^2]/1 muln1 //.
Qed.


(* 
PeanoNat.Nat.sqrt_unique:
  forall a b : nat,
  ((b * b)%coq_nat <= a)%coq_nat /\ (a < (b.+1 * b.+1)%coq_nat)%coq_nat -> PeanoNat.Nat.sqrt a = b
*)
Lemma sqrt_ij i j : Nat.sqrt ((i + j) ^ 2 + i) = (i+j).
Proof.
  apply: PeanoNat.Nat.sqrt_unique.
  rewrite -[(_ * _)%coq_nat]/((i+j) * (i+j)) -[(_ * _)%coq_nat]/((i+j).+1 * (i+j).+1) !mulnn.
  split.
  apply /leP.
  apply: leq_addr.
  apply /ltP.
  rewrite sqrp1.
  rewrite -(@addnA ((i+j)^2) (2*(i+j)) 1) ltn_add2l.
  rewrite mul2n -addnn. rewrite -[i in X in X < _]addn0.
  Check (((i + j) + (i + j)) + 1).
  Check (addnA 1 2 3).
  rewrite -[_ + _ + 1 ]addnA -[i+  j + _ ]addnA  ltn_add2l.
  rewrite addnA addn1.
  apply: ltn0Sn.
Qed.

Lemma aplusbminusa a b : a + b -a = b.
Proof.
  rewrite -[a in X in _+_-X=_]addn0 subnDl subn0 //.
Qed.

Lemma zgniec_odgniec k : odgniec (zgniec k) = k.
Proof.
  case: k => i j.
  rewrite /zgniec /odgniec !sqrt_ij pair_equal_spec !aplusbminusa //.
Qed.

