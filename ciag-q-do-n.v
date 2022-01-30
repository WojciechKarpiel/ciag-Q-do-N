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



Lemma zgniec_odgniec k : odgniec (zgniec k) = k.
Proof.
  case: k => i j.
  rewrite /zgniec /odgniec.
  rewrite pair_equal_spec; split.


