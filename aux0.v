Require Export Coq.omega.Omega.
Require Export Coq.Arith.Lt.
Require Export Coq.Arith.PeanoNat.
Require Export Coq.Sorting.Permutation.
Require Export Coq.Sorting.Sorted.
Require Export Coq.Lists.List.
Require Export Coq.Bool.Bool.
Require Export Coq.Program.Basics.
Require Import Coq.Logic.FunctionalExtensionality.

Lemma aux0: forall (n t m: nat),
              t < n -> m < n -> m + (n - t) >= n ->
              m + (n - t) - n < n ->
              m + (n - t) - n + t < n ->
              t <> 0 -> m + (n - t) - n + t = m.
Proof.
  intros. omega.
Qed.
