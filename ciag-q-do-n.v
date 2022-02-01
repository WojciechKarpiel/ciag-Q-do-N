From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From mathcomp Require Import algebra.rat.
From mathcomp Require Import ssrint.


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

Definition intdnat(z : int) : nat :=
  match z with
  | ssrint.Posz n => zgniec (n, 0)
  | ssrint.Negz n => zgniec (n, 1)          
  end.

Definition natdint(n : nat) :=
  let (a,b) := odgniec n in
  if b == 0 then Posz a else Negz a.

Lemma intdookola z : natdint (intdnat z) =z.
Proof.
  case : z => n ;  rewrite /natdint /intdnat  zgniec_odgniec //.
Qed.

Definition ratdnat (r : rat) : nat :=
  let (a,b) := rat.valq r in  zgniec(intdnat(a), intdnat(b)).


Definition natdrat (n : nat): rat .
  pose (ab := odgniec n).
  pose (a := natdint ab.1).
  pose (b := natdint ab.2).
  Locate "_ < _".
  Open Scope order_scope.
  pose (b'  :=  (if (Posz 0) < b then b else (Posz 1 : int))).
  pose (a' := if (coprime `|a| `|b' |) then a else (Posz 1 : int)). 
  refine (@Rat (a', b') _ ).
  apply /andP; constructor.
  rewrite -[(a',b').2]/b' /b'.
  by case: (ifP).
  Close Scope order_scope.
  rewrite -[(_,_).1]/a' -[(_,_).2]/b'.
  rewrite  /a'. case: ifP => //= _.
  apply: coprime1n.
Defined.

Lemma ratdookolaq r : natdrat (ratdnat r) == r.
Proof.
  case : r => [[a b]] H.
  rewrite -[_ == _]/(valq _ == valq _).
  rewrite -[valq (Rat H)]/(a,b).
  (* pozbyć się d, bo z nim to lipa *)
  rewrite /ratdnat .
  rewrite -[valq (Rat H)]/(a,b).

  
 (* clear d. (* będę tego potrzebował potem, ale dobrze, że nie ma tego na teraz *) *)

  rewrite /natdrat.
  

  apply /eqP.
  rewrite [(a,b) in RHS]surjective_pairing. 
  rewrite  pair_equal_spec.
  rewrite !zgniec_odgniec !intdookola.
  split.
  case: ifP => // X.
  exfalso.
  move : H => /andP [x d].
  rewrite x in X.
  simpl in d.
  Search _ (_ = false) _.
  rewrite X in d .
  move : d => //.

    move : H => /andP [x d].
    by     rewrite x.
Qed.


Lemma ratdookola r : natdrat (ratdnat r) = r.
Proof.
  apply /eqP.
  apply: ratdookolaq.
Qed.
