From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From mathcomp Require Import algebra.rat.
From mathcomp Require Import ssrint seq.


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

Search "fold".
Definition seqdonat (sq : seq rat) : nat :=
 zgniec ((length sq),  foldr (fun  r z => zgniec ( (ratdnat r),z)) 0 sq).


  (*foldl (fun z r => zgniec (z, (ratdnat r))) (length sq) sq.*)
  (*foldr (fun  r z => zgniec (z, (ratdnat r))) (length sq) sq.*)

Fixpoint  odgn ln wrt :=
    match ln with
    | O => [::]
    | S n => let (x, r) := odgniec wrt in (natdrat x) :: (odgn  n r)
    end.

  
  Definition natdoseq (n : nat): seq rat :=
  let (len, wartosci) := odgniec n in
  odgn len wartosci.



Open Scope rat_scope.
Definition t1 : rat := 1. (*[rat (2: int) // (3 : int)].*)
Definition t2 : rat := ratz (2:int). (*[rat (3: int) // (2 : int)].*)
Definition t3 : rat := [rat (9: int) // (4 : int)].
Eval compute in (ratdnat t1).
(* Eval compute in (seqdonat [:: t1]). *)
Close Scope rat_scope.


Lemma foldl1step {A B : Type} (f : A ->B -> A) z q qs : foldl f z (q::qs) = foldl f (f z q) qs.
Proof. done. Qed.

Lemma fold1step {A B : Type} (f : B -> A-> A) (z:A) (q:B) qs : foldr f z  (q::qs) = f q (foldr  f  z qs) .
Proof. done. Qed.

Lemma foldl0 {A B : Type} (f : A ->B -> A) z  : foldl f z [::] = z.
Proof. done. Qed.

Lemma fold0 {A B : Type} (f : A ->B -> B) z  : foldr  f z  [::] = z.
Proof. done. Qed.


Lemma odgn1 ln wrt : odgn ln.+1 wrt = let (x, r) := odgniec wrt in (natdrat x) :: (odgn  ln r).
Proof. done. Qed.

Lemma odgn0 wrt : odgn 0 wrt = [::].
Proof. done. Qed.

Lemma seqdookola0  : natdoseq (seqdonat [:: ]) = [:: ]. Proof. done. Qed.

Lemma seqdookola1 a : natdoseq (seqdonat [:: a]) = [:: a].
Proof.
  rewrite /seqdonat.
  rewrite fold1step fold0. 
  rewrite /natdoseq.
  rewrite zgniec_odgniec.
  rewrite -[length [:: a]]/1.
  rewrite odgn1 . rewrite zgniec_odgniec // .

  rewrite ratdookola //.
Qed.


Lemma seqdookola2  (a  b: rat):  natdoseq (seqdonat [:: a; b]) = [:: a ;b].
Proof.
  rewrite /seqdonat.
  rewrite fold1step fold1step fold0.
  rewrite /natdoseq.
  rewrite zgniec_odgniec.
  rewrite -[length _]/(0.+1.+1).
  rewrite odgn1 zgniec_odgniec.
  rewrite odgn1 zgniec_odgniec odgn0 !ratdookola.
  done.
Qed.

(* chyba działa, ale jeszcze się muszę upewnić *) 
Lemma seqdookola3  (a  b c: rat):  natdoseq (seqdonat [:: a; b;c]) = [:: a ;b;c].
Proof.
  rewrite /seqdonat.
  rewrite !fold1step fold0.
  rewrite /natdoseq.
  rewrite zgniec_odgniec.
  rewrite -[length _]/(3).
  rewrite odgn1 zgniec_odgniec.
  rewrite odgn1 zgniec_odgniec.
  rewrite odgn1 zgniec_odgniec.
  rewrite odgn0 !ratdookola.
  done.
Qed.

Lemma sqdnatdef sq : seqdonat sq =
                       zgniec ((length sq),  foldr (fun  r z => zgniec ( (ratdnat r),z)) 0 sq).
Proof. done. Qed.

Lemma sqdnatdef1 a  sq : seqdonat (a ::sq) =
                       zgniec ((length (a ::sq)), zgniec ( ratdnat a,   foldr (fun  r z => zgniec ( (ratdnat r),z)) 0 (sq))).
Proof. done. Qed.


Lemma eloo a l :natdoseq (seqdonat (a :: l)) = a :: (natdoseq (seqdonat l)).
Proof.
  rewrite sqdnatdef1.
  rewrite {1}/natdoseq zgniec_odgniec.
  rewrite odgn1. (* czemu to mi się "length" otwiera, to przeszkadza *)
  rewrite zgniec_odgniec ratdookola.
  apply (f_equal (fun x => a :: x)).
  by rewrite /seqdonat /natdoseq zgniec_odgniec.
Qed.

Lemma seqdookola sq : natdoseq (seqdonat sq) = sq.
Proof.
  elim : sq => //q qs H.
  rewrite -[in RHS]H.
  apply: eloo.
Qed.



Lemma twierdzenie: hipoteza.
Proof.
  exists natdoseq => qs.
  exists (seqdonat qs).
  apply: seqdookola.
Qed.
