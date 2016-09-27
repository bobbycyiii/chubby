Require Export Coq.omega.Omega.
Require Export Coq.Arith.Lt.
Require Export Coq.Arith.PeanoNat.
Require Export Coq.Sorting.Permutation.
Require Export Coq.Sorting.Sorted.
Require Export Coq.Lists.List.
Require Export Coq.Bool.Bool.
Require Export Coq.Program.Basics.
Require Import Coq.Logic.FunctionalExtensionality.
Require aux0.
Require aux1.
Require aux2.
Require aux3.
Require aux4.
Require aux5.
Require aux6.
Require aux7.

Lemma beq_reflect : forall x y, reflect (x = y) (x =? y).
Proof.
  intros x y.
  apply iff_reflect. symmetry.  apply beq_nat_true_iff.
Qed.

Lemma blt_reflect : forall x y, reflect (x < y) (x <? y).
Proof.
  intros x y.
  apply iff_reflect. symmetry. apply Nat.ltb_lt.
Qed.

Lemma ble_reflect : forall x y, reflect (x <= y) (x <=? y).
Proof.
  intros x y.
  apply iff_reflect. symmetry. apply Nat.leb_le.
Qed.

(* from Andrew Appel's online notes "Verified Functional Algorithms."
     We note that Ltac definitions may be treated as black boxes;
     it is presumed impossible to prove falsity by introducing
     Ltac definitions and using them. *)

Hint Resolve blt_reflect ble_reflect beq_reflect : bdestruct.
Ltac bdestruct X :=
  let H := fresh in let e := fresh "e" in
                    evar (e: Prop);
                      assert (H: reflect e X); subst e;
                      [eauto with bdestruct
                      | destruct H as [H|H];
                        [ | try first [apply not_lt in H | apply not_le in H]]].

  Definition rt (n t m : nat) :=
    match (m <? n) with
      | true =>
        match (m + t <? n) with
          | true => m + t
          | false => m + t - n
        end
      | false =>
        match (m + t <? 2*n) with
          | true => m + t
          |false => m + t - n
        end
    end.
  
Lemma rt_inv : forall (n t m : nat),
                  t < n -> m < 2 * n -> rt n t (rt n (n - t) m) = m.
Proof.
  intros n t m ltn fm. unfold rt.
  bdestruct (m <? n); bdestruct (m + (n - t) <? n);
  bdestruct (m + (n - t) <? n); bdestruct (m + (n - t) + t <? n);
  try omega.
  bdestruct (m + (n - t) - n <? n).
  bdestruct (m + (n - t) - n + t <? n).
  bdestruct (t =? 0).
  assert (qt0: t = 0).
  {assumption. }
  rewrite qt0 in *.
  rewrite Nat.sub_0_r in *.
  rewrite plus_0_r in *.
  replace (m + n - n) with (m) in *.
  reflexivity. omega.
  apply (aux0.aux0 n t m ltn H H0 H3 H4 H5).
  bdestruct (t =? 0).
  assert (qt0: t = 0).
  {assumption. }
  rewrite qt0 in *.
  rewrite Nat.sub_0_r in *.
  rewrite plus_0_r in *.
  replace (m + n - n) with (m) in *.
  omega. omega.
  apply (aux1.aux1 n t m ltn H H0 H3 H4 H5).
  bdestruct (m + (n - t) - n + t <? 2 * n).
  bdestruct (t =? 0).
  assert (qt0: t = 0).
  {assumption. }
  rewrite qt0 in *.
  rewrite Nat.sub_0_r in *.
  rewrite plus_0_r in *.
  replace (m + n - n) with (m) in *.
  reflexivity.  omega.
  apply (aux2.aux2 n t m ltn H H0 H3 H4 H5).
  bdestruct (t =? 0).
  assert (qt0: t = 0).
  {assumption. }
  rewrite qt0 in *.
  rewrite Nat.sub_0_r in *.
  rewrite plus_0_r in *.
  replace (m + n - n) with (m) in *.
  omega. omega.
  apply (aux3.aux3 n t m ltn H H0 H3 H4 H5).
  bdestruct (m + (n - t) <? 2 * n).
  bdestruct (m + (n - t) <? n).
  bdestruct (m + (n - t) + t <? n).
  bdestruct (t =? 0).
  assert (qt0: t = 0).
  {assumption. }
  rewrite qt0 in *.
  rewrite Nat.sub_0_r in *.
  rewrite plus_0_r in *.
  replace (m + n - n) with (m) in *.
  omega. omega. omega.
  bdestruct (t =? 0).
  assert (qt0: t = 0).
  {assumption. }
  rewrite qt0 in *.
  rewrite Nat.sub_0_r in *.
  rewrite plus_0_r in *.
  replace (m + n - n) with (m) in *.
  reflexivity. omega. omega.
  bdestruct (m + (n - t) + t <? 2 * n).
  bdestruct (t =? 0).
  assert (qt0: t = 0).
  {assumption. }
  rewrite qt0 in *.
  rewrite Nat.sub_0_r in *.
  rewrite plus_0_r in *.
  replace (m + n - n) with (m) in *.
  omega. omega. omega.
  bdestruct (t =? 0).
  assert (qt0: t = 0).
  {assumption. }
  rewrite qt0 in *.
  rewrite Nat.sub_0_r in *.
  rewrite plus_0_r in *.
  replace (m + n - n) with (m) in *.
  reflexivity. omega. omega.
  bdestruct (m + (n - t) - n <? n).
  bdestruct (m + (n - t) - n + t <? n).
  bdestruct (t =? 0).
  assert (qt0: t = 0).
  {assumption. }
  rewrite qt0 in *.
  rewrite Nat.sub_0_r in *.
  rewrite plus_0_r in *.
  replace (m + n - n) with (m) in *.
  reflexivity. omega.
  apply (aux4.aux4 n t m ltn fm H H3 H5 H6).
  bdestruct (t =? 0).
  assert (qt0: t = 0).
  {assumption. }
  rewrite qt0 in *.
  rewrite Nat.sub_0_r in *.
  rewrite plus_0_r in *.
  replace (m + n - n) with (m) in *.
  omega. omega.
  apply (aux5.aux5 n t m ltn fm H H3 H4 H5 H6).
  bdestruct (m + (n - t) - n + t <? 2 * n).
  bdestruct (t =? 0).
  assert (qt0: t = 0).
  {assumption. }
  rewrite qt0 in *.
  rewrite Nat.sub_0_r in *.
  rewrite plus_0_r in *.
  replace (m + n - n) with (m) in *.
  reflexivity. omega.
  apply (aux6.aux6 n t m ltn fm H H3 H5 H6).
  bdestruct (t =? 0).
  assert (qt0: t = 0).
  {assumption. }
  rewrite qt0 in *.
  rewrite Nat.sub_0_r in *.
  rewrite plus_0_r in *.
  replace (m + n - n) with (m) in *.
  omega. omega.
  apply (aux7.aux7 n t m ltn fm H H3 H5 H6).
Qed.

  
  
  
  
  
  
  
        