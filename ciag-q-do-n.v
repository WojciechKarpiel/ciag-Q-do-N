From mathcomp Require Import all_ssreflect.
From mathcomp Require Import algebra.rat.
From mathcomp Require Import ssrint seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

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


Lemma roznica_miedzy_kwadratami n : n.+1^2 = n^2 + 2*n +1.
Proof.
  rewrite -addn1 sqrnD -![n^2 + _ + _]addnA [1 ^2 + 2*_]addnC -[1^2]/1 muln1 //.
Qed.

(* Lemat pomocniczy do zgniec_odgniec;
 w pewnym sensie, to słabsza wersja różnicy między kwadratami *)
Lemma sqrt_ij i j : Nat.sqrt ((i + j) ^ 2 + i) = (i+j).
Proof.
  apply: PeanoNat.Nat.sqrt_unique.
  rewrite -[(_ * _)%coq_nat]/((i+j) * (i+j)) -[(_ * _)%coq_nat]/((i+j).+1 * (i+j).+1) !mulnn.
  split; [by apply /leP; apply: leq_addr| apply /ltP].
  rewrite roznica_miedzy_kwadratami  -(@addnA ((i+j)^2) (2*(i+j)) 1) ltn_add2l.
  rewrite mul2n -addnn -[i in X in X < _]addn0 -[_ + _ + 1 ]addnA -[i+  j + _ ]addnA.
  rewrite ltn_add2l addnA addn1.
  apply: ltn0Sn.
Qed.

Lemma a_plus_b_minus_a a b : a + b - a = b.
Proof.
  by rewrite -[a in X in _+_-X=_]addn0 subnDl subn0.
Qed.

(* Podstawowy lemat mówiący, że 2 liczby naturalne można zakodować za pomocą jednej
   cała reszta dowodu bazuje na zgniataniu i odgniataniu par liczb naturalnych *)
Lemma zgniec_odgniec k : odgniec (zgniec k) = k.
Proof.
  case: k => i j.
  by rewrite /zgniec /odgniec !sqrt_ij pair_equal_spec !a_plus_b_minus_a.
Qed.

(* Liczby całkowite można zakodować parą liczb natualnych
 możliwych kodowań jest dużo, to tutaj nie jest eleganckie,
 ale łatwo się dowodzi jego odwracalność*)
Definition int_do_nat(z : int) : nat :=
  match z with
  | ssrint.Posz n => zgniec (n, 0)
  | ssrint.Negz n => zgniec (n, 1)          
  end.

Definition nat_do_int(n : nat) :=
  let (a, b) := odgniec n in
  if b == 0 then Posz a else Negz a.

Lemma zgniec_odgniec_int z : nat_do_int (int_do_nat z) = z.
Proof.
  by case : z => n; rewrite /nat_do_int /int_do_nat  zgniec_odgniec.
Qed.

(* Liczby wymierne można zakodować parą liczb całkowitych *)
Definition rat_do_nat (r : rat) : nat :=
  let (a, b) := rat.valq r in zgniec(int_do_nat a, int_do_nat b).


(* udziwnienia przy definicji a' i b' mają na celu
   ułatwienie spełnienia wymagań konstruktora Rat *)
Definition nat_do_rat (n : nat): rat .
  pose (ab := odgniec n).
  pose (a := nat_do_int ab.1).
  pose (b := nat_do_int ab.2).
  Open Scope order_scope.
  pose (b' := (if (Posz 0) < b then b else (Posz 1))).
  Close Scope order_scope.
  pose (a' := if (coprime `|a| `|b'|) then a else (Posz 1)). 
  refine (@Rat (a', b') _ ).
  apply /andP; split;
    [by rewrite /b'; case: ifP | rewrite  /a'; case: ifP => //= _; apply: coprime1n].
Defined.

Lemma zgniec_odgniec_rat r : nat_do_rat (rat_do_nat r) = r.
Proof.
  apply /eqP; case : r => [[a b]] H.
  rewrite -[_ == _]/(valq _ == valq _) -[valq (Rat H)]/(a,b) /rat_do_nat -[valq (Rat H)]/(a,b).
  (* H nie znajduje się teraz w celu, będzie potrzebne dopiero na końcu  *)
  rewrite /nat_do_rat; apply /eqP.
  rewrite [(a,b) in RHS]surjective_pairing pair_equal_spec !zgniec_odgniec !zgniec_odgniec_int.
  move: H => /andP [zero_ltn_b wzgl_pierwsze]. (* teraz H jest potrzebne *)
  split; [by case: ifP => //; rewrite zero_ltn_b wzgl_pierwsze | by rewrite zero_ltn_b].
Qed.

(* Kodowanie ciągu liczb wymiernych o długości n:
 (n, (a1, a2, a3, a4, ..., a_n, 0),
 gdzie a_n to zakodowany n-ty wyrac ciągu.
 Liczba na końcu to wartownik, mogło by go nie być, ale tak było mi łatwiej *)
Definition seq_do_nat (sq : seq rat) : nat :=
  zgniec ((length sq), foldr (fun r z => zgniec ((rat_do_nat r), z)) 0 sq).

(* Funkcja pomocnicza do odkodowywania.
   Jeśli ciąg jest zakodowany jako (n, (a1, a2, a3,....)),
   to pierwszy argument funkcji to n, a drugi to (a1, a2 ...) *)
Fixpoint odgniec_seq' dlugosc wartosci :=
  match dlugosc with
  | 0 => [::]
  | n.+1 => let (a_i, reszta) := odgniec wartosci in (nat_do_rat a_i) :: (odgniec_seq' n reszta)
  end.

Definition nat_do_seq (n : nat): seq rat :=
  let (dlugosc, wartosci) := odgniec n in odgniec_seq' dlugosc wartosci.

(* pomocnicze lematy do wykonywania pojedyńczego kroku obliczeń *)
Lemma fold1krok {A B : Type} (f : A -> B -> B) z q qs : foldr f z (q::qs) = f q (foldr f z qs).
Proof. done. Qed.

Lemma fold0 {A B : Type} (f : A -> B -> B) z: foldr  f z  [::] = z.
Proof. done. Qed.

Lemma odgniec1krok dlugosc wartosci :
  odgniec_seq' dlugosc.+1 wartosci =
    let (a_i, reszta) := odgniec wartosci in (nat_do_rat a_i) :: (odgniec_seq' dlugosc reszta).
Proof. done. Qed.

(* Dodatkowo, przy poprawnym rozkodowywaniu wartosci=0, ale to nie istotne *)
Lemma odgniec0 wartosci : odgniec_seq' 0 wartosci = [::].
Proof. done. Qed.


Lemma seq_do_nat1krok q sq :
  seq_do_nat (q :: sq) =
    zgniec (length (q ::sq), zgniec (rat_do_nat q, foldr (fun r z => zgniec ((rat_do_nat r), z)) 0 sq)).
Proof. done. Qed.

(* Koniec nudnych lematów, teraz zasadnicze mięsko *)
Lemma nat_do_seq_glowa q qs :
  nat_do_seq (seq_do_nat (q :: qs)) = q :: (nat_do_seq (seq_do_nat qs)).
Proof.
  rewrite seq_do_nat1krok {1}/nat_do_seq zgniec_odgniec.
  rewrite odgniec1krok. (* czemu "length" się otwiera? nie powinno *)
  rewrite zgniec_odgniec zgniec_odgniec_rat.
  apply (f_equal (fun qs => q :: qs)).
  by rewrite /seq_do_nat /nat_do_seq zgniec_odgniec.
Qed.

Lemma zgniec_odgniec_seq qs : nat_do_seq (seq_do_nat qs) = qs.
Proof.
  elim : qs => // q qs H.
  rewrite -[in RHS]H.
  apply: nat_do_seq_glowa.
Qed.

Lemma twierdzenie: hipoteza.
Proof.
  exists nat_do_seq => qs.
  exists (seq_do_nat qs).
  apply: zgniec_odgniec_seq.
Qed.

(* Teraz udowodnić, że istnieje bijekcja N <-> [Q],
   taką bijekcją jest zgniec' i odgniec' *)
