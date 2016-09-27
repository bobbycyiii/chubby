Require Export Coq.omega.Omega.
Require Export Coq.Arith.Lt.
Require Export Coq.Arith.PeanoNat.
Require Export Coq.Sorting.Permutation.
Require Export Coq.Sorting.Sorted.
Require Export Coq.Lists.List.
Require Export Coq.Bool.Bool.
Require Export Coq.Program.Basics.
Require Import Coq.Logic.FunctionalExtensionality.

Lemma aux5: forall (n t m: nat),
              t < n -> m < 2 * n -> m >= n ->
              m + (n - t) >= 2 * n ->
              m + (n - t) - n < n ->
              m + (n - t) - n + t >= n ->
              t <> 0 ->
              m + (n - t) - n + t - n = m.
Proof.
  intros. assert (contr: m + (n - t) < 2 * n).
  { omega. } unfold ge in *.
  apply le_not_lt in H2. contradiction.  
Qed.
