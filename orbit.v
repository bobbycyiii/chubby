Require Export Coq.omega.Omega.
Require Export Coq.Arith.Lt.
Require Export Coq.Arith.PeanoNat.
Require Export Coq.Sorting.Permutation.
Require Export Coq.Sorting.Sorted.
Require Export Coq.Lists.List.
Require Export Coq.Bool.Bool.
Require Export Coq.Program.Basics.
Require Import Coq.Logic.FunctionalExtensionality.
Require rt_inv.

(* from Andrew Appel's online notes "Verified Functional Algorithms."
     We note that Ltac definitions may be treated as black boxes;
     it is presumed impossible to prove falsity by introducing
     Ltac definitions and using them. *)


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

Hint Resolve blt_reflect ble_reflect beq_reflect : bdestruct.
Ltac bdestruct X :=
  let H := fresh in let e := fresh "e" in
                    evar (e: Prop);
                      assert (H: reflect e X); subst e;
                      [eauto with bdestruct
                      | destruct H as [H|H];
                        [ | try first [apply not_lt in H | apply not_le in H]]].

Ltac inv H := inversion H; clear H; subst.

Module Necklace.
  Parameter n : nat.
  
  (*We label the faces of the n-dipyramid as follows.
    Inscribe the dipyramid in the unit sphere and
    apply stereographic projection. The result looks like

                        |
                        |
                        |
            2           |           1
                        |
                       /|\
                      / | \
                     /  |  \
                    /   |   \
                   /    |    \
                  /     |     \
                 /  5   |   4  \
                /     /   \     \
               /    /       \    \
              /   /           \   \
             /  /       3       \  \
            / /                   \ \
           //_______________________\\
          /                           \
        /                               \
      /                 0                 \
    /                                       \
  
   Thus we model faces of the n-dipyramid by
   natural numbers less than 2*n. *)

  Definition face (m : nat) : Prop := m < 2 * n.


  (*
   The following operations are supposed to
   correspond to generators of the
   the dipyramidal symmetry group (preserving
   polarity if n = 4). The reader should verify
   that these do correspond to the action of
   these on the labels.
   *)

  (* This corresponds to a rotation by 2*pi*t/n 
     about a line through the two suspension poles. *)

  Definition rot (t m : nat) := rt_inv.rt n t m.
  
  Lemma rot_face : forall (t m : nat),
                    t < n -> face m -> face (rot t m).
  Proof.
    unfold face.
    intros t m ltn lm2n.
    unfold rot. unfold rt_inv.rt.
    bdestruct (m <? n); bdestruct (m + t <? n);
    bdestruct (m+t <? 2 * n); omega.
  Qed.

  Definition on_top (m : nat) : Prop := m < n.
  
  Lemma rot_top : forall (t m : nat),
                     t < n -> face m -> (on_top m <-> on_top (rot t m)).
  Proof.
    unfold on_top. unfold face.
    intros t m ltn lm2n.
    split; intro H;
    unfold rot in *; unfold rt_inv.rt in *;
    bdestruct (m <? n); bdestruct (m + t <? n);
    bdestruct (m+t <? 2 * n); omega.
  Qed.
  
  Lemma rot_inj : forall (t m0 m1 : nat),
                         t < n -> face m0 -> face m1 ->
                         (rot t m0) = (rot t m1) ->
                         m0 = m1.
  Proof.
    unfold face in *.
    intros t m0 m1 ltn lt0 lt1 rq.
    unfold rot in rq; unfold rt_inv.rt in rq.
    bdestruct (m0 <? n);
      bdestruct (m0 + t <? n);
      bdestruct (m0 + t <? 2 * n);
      bdestruct (m1 <? n);
      bdestruct (m1 + t <? n);
      bdestruct (m1 + t <? 2 * n);
      omega.
  Qed.

  Lemma rot_0_id : forall (m : nat), face m -> rot 0 m = m.
  Proof.
    intro m. unfold face. intro fm.
    unfold rot. unfold rt_inv.rt. rewrite plus_0_r.
    bdestruct (m <? n); bdestruct (m <? 2*n); omega.
  Qed.
                                      
  (* rot is bijective on faces because it's an injection
     from a finite set to itself; also, it's invertible. *)

  Lemma rot_inv : forall (t m : nat),
                    t < n -> face m -> rot t (rot (n - t) m) = m.
  Proof.
    unfold face. unfold rot. apply rt_inv.rt_inv.
  Qed.
  
  
  (* The p-flip is the reflection through
     the plane in which the polygon lies of
     which the dipyramid is a suspension. *)

  Definition p_flip (m : nat) : nat :=
    match (m <? n) with
      | true => m + n
      | false => m - n
    end.
  
  Lemma p_flip_face : forall (m : nat), face m -> face (p_flip m).
  Proof.
    unfold face.
    intros m H.
    unfold p_flip.
    bdestruct (m <? n); omega.
  Qed.
  
  Definition p_flip_inj :
    forall (m0 m1 : nat), face m0 -> face m1 ->
                          p_flip m0 = p_flip m1 -> m0 = m1.
  Proof.
    unfold face.
    intros m0 m1 lt0 lt1 pq.
    unfold p_flip in pq.
    bdestruct (m0 <? n); bdestruct (m1 <? n); omega.
  Qed.

  Definition p_flip_inv :
    forall (m : nat), face m -> p_flip (p_flip m) = m.
  Proof.
    unfold face.
    intros m fm. unfold p_flip.
    bdestruct (m <? n).
    - bdestruct (m + n <? n); omega.
    - bdestruct (m - n <? n); omega.
  Qed.
  
  (* The v-flip is the reflection through
     the plane through the poles and the
     vertex common to the faces 0, n-1, n, 2*n - 1. *)

  (* We note for the benefit of the reader that
     this flip's action on the top faces is readily
     guessed: it should look something like m => n - m.
     That doesn't quite work; in fact, it acts as
     m => n - (m + 1). Its action on the bottom
     is gotten by conjugating the action on the
     top by a p-flip. So it's 
     m => n + (n - ((m - n) + 1)), which is
     m => 3 * n - (m + 1). *)
  
  Definition v_flip (m : nat) : nat :=
    match m <? n with
      | true => n - (S m)
      | false => 3 * n - (S m)
    end.  

  Lemma v_flip_face : forall (m : nat), face m -> face (v_flip m).
  Proof.
    unfold face.
    intros m H.
    unfold v_flip.
    bdestruct (m <? n); omega.
  Qed.

  Lemma v_flip_inj : forall (m0 m1 : nat),
                           face m0 -> face m1 ->
                           v_flip m0 = v_flip m1 ->
                           m0 = m1.
  Proof.
    unfold face.
    intros m0 m1 pf0 pf1 vq.
    unfold v_flip in vq.
    bdestruct (m0 <? n);
      bdestruct (m1 <? n);
      omega.
  Qed.

  Lemma v_flip_inv : forall (m : nat),
                       face m -> v_flip (v_flip m) = m.
  Proof.
    unfold face.
    intros m fm. unfold v_flip.
    bdestruct (m <? n).
    - bdestruct (n - S m <? n); omega.
    - bdestruct (3 * n - S m <? n); omega.
  Qed.
  
  (* The dipyramidal symmetry group is generated by
     these operations. (We note that a dipyramidal
     symmetry must, by definition, preserve the
     suspension structure---it must take suspension
     points to suspension points. This is only 
     important when it is a 4-dipyramid.) 

     In fact, every pole-preserving symmetry is
     either a rotation or a rotation followed by
     the v-flip; and every symmetry is either a pole-
     preserving symmetry or a pole-preserving symmetry
     followed by the p-flip. We take this as our
     definition of the dipyramidal symmetry group.

     The least tenable claim made in the above
     paragraph is the one about pole-preserving
     symmetries. This claim reduces to a similar
     claim about the generation of the usual dihedral
     group, which the reader will enjoy verifying.

     The action of the subgroup PR generated by rot
     and p_flip is strongly transitive on the faces,
     so the faces are a PR torsor, if you like.
     I don't (yet). *)
                      
  (* Having introduced the symmetry group, we now
     introduce the other objects of interest on which
     it acts---clash-free face-pairings. This action
     arises from an action on face-pairs, which in
     turn arises from the action on faces. In prepar-
     ation for this introduction we introduce some
     auxiliary functions on pairs and pair-lists,
     and prove their specifications. *)
  
  Fixpoint faces (l : list (nat*nat)) : list nat :=
    match l with
      | nil => nil
      | p :: ps =>
        match p with
          | (m0, m1) =>
            m0 :: (m1 :: (faces ps))
        end
    end.

  (* If l is a list of pairs of numbers, then
     (faces l) should be a list L of numbers such
     that a number x is in L if and only if x
     is an entry of some pair in L, i.e. if there
     exists a pair y in L such that x is an entry of y. *)

  Lemma faces_spec : forall (l : list (nat*nat)) (x : nat),
                       In x (faces l) <-> exists (y: nat*nat),
                                            (In y l /\ (x = fst y \/ x = snd y)).
  Proof.
    intro l. induction l; intro x; split; intro H.
    - inv H.
    - destruct H as [y H].
      destruct H as [contr _].
      inv contr.
    - destruct a. simpl in H.
      destruct H as [n0x | H].
      + rewrite <- n0x in *.
        exists (n0,n1). split.
        * unfold In. left. reflexivity.
        * left. reflexivity.
      + destruct H as [n1x | inxfl].
        * rewrite <- n1x in *.
          exists (n0,n1). split.
          unfold In. left. reflexivity.
          right. reflexivity.
        * apply IHl in inxfl.
          destruct inxfl as [y H].
          exists y. split.
          change (In y ((n0,n1) :: l)) with ((n0,n1) = y \/ In y l).
          right. destruct H. assumption.
          destruct H. assumption.
    - destruct a. simpl. destruct H as [y H].
      destruct H as [inynl xy].
      destruct inynl.
      + rewrite <- H in *.
        destruct xy as [xn | xn]; simpl in xn; symmetry in xn.
        * left. assumption.
        * right. left. assumption.
      + right. right. apply IHl. exists y.
        split; assumption.
  Qed.
  
                           
  Fixpoint nums (b : nat) : list nat :=
    match b with
      | 0 => nil
      | S b' => b' :: nums b'
    end.

  (* nums b should be all the numbers less than b. *)
  Lemma nums_spec : forall (n' x : nat), x < n' <-> In x (nums n').
  Proof.
    intro n'. induction n'; intro x; split; intro H.
    - omega.
    - inv H.
    - simpl. bdestruct (n' =? x).
      + left. assumption.
      + right. assert (x < n').
        { omega. }
        apply IHn'. assumption.
    - inv H. omega. apply IHn' in H0. omega.
  Qed.
    
  Definition range (l : nat) (r : nat) : list nat :=
    map (fun x => x + l) (nums (r - l)).

  Theorem map_compose : forall (A : Type) (l : list A) (B C : Type) (g : B -> C) (f : A -> B),
                          map g (map f l) = map (compose g f) l.
  Proof.
    intros A l. induction l; intros.
    - reflexivity.
    - simpl. unfold compose at 1.
      apply f_equal. apply IHl.
  Qed.

  (* range l r should be all the numbers x between l and r in the
     computer science (and what ought to be the mathematical) standard
     sense, viz. l <= x < r. See EWD 831. *)
  
  Lemma range_spec : forall (l r x : nat), (l <= x /\ x < r) <-> (In x (range l r)).
  Proof.
    intros l r x. split; intro H.
    - assert (inq0: x - l < r - l).
      { omega. }
      apply nums_spec in inq0.
      apply in_map with (f:= (fun y => y + l)) in inq0.
      replace (x - l + l) with (x) in inq0. 2: omega.
      unfold range. assumption.
    - split; generalize dependent H; generalize dependent x;
      generalize dependent r; generalize dependent l.
      + intro l; induction l.
        * intros. omega.
        * intros r x H. unfold range in H.
          induction (r - S l).
          inv H.
          inversion H. omega. apply IHn0. assumption.
      + intros l r x inx. unfold range in inx.
        apply in_map with (f:= (fun z => z - l)) in inx.
        rewrite map_compose in inx.
        replace (compose (fun z : nat => z - l) (fun x : nat => x + l))
        with (fun z : nat => z) in inx.
        replace (map (fun z : nat => z) (nums (r - l))) with (nums (r - l)) in inx.
        apply nums_spec in inx. omega.
        symmetry. apply map_id.
        extensionality zz. unfold compose. omega.
  Qed.          

  Fixpoint adiff (s m : list nat) : list nat :=
    match m with
      | nil => s
      | h :: t => remove Nat.eq_dec h (adiff s t)
    end.

  Definition asymmetric_difference := adiff.

  (* The following is not in the standard library where
     I could find it. Perhaps I should get better
     at looking for things. At any rate, this is a
     theorem we use in the proof of the specification
     of adiff. *)
  
  Theorem in_remove_in : forall (A : Type) (eq_dec : forall x y : A, {x = y} + {x <> y})
                                (l : list A) (x y : A),
                           In x (remove eq_dec y l) <-> (x <> y /\ In x l).
  Proof.
    intros A eq_dec l. induction l; intros x y; split; intro H.
    - inv H.
    - destruct H as [_ contr]. inv contr.
    - assert (xny: x <> y).
      { intro contr. rewrite contr in H.
        apply remove_In in H. assumption. }
      split. assumption.
      change (In x (a :: l)) with (a = x \/ In x l).
      destruct (eq_dec a x).
      left. assumption.
      right. assert (inx: In x (remove eq_dec y l)).
      { change (remove eq_dec y (a :: l))
        with (if eq_dec y a then remove eq_dec y l else a :: remove eq_dec y l) in H.
        destruct (eq_dec y a). assumption.
        change (In x (a :: remove eq_dec y l))
        with (a = x \/ In x (remove eq_dec y l)) in H.
        destruct H. contradiction. assumption. }
      apply IHl in inx. destruct inx. assumption.
    - change (remove eq_dec y (a :: l))
      with (if eq_dec y a then remove eq_dec y l else a :: remove eq_dec y l).
      destruct (eq_dec y a) as [yqa | yna].
      apply IHl. rewrite yqa in *.
      destruct H as [xna inxal].
      destruct inxal. symmetry in H. contradiction.
      split; assumption.
      change (In x (a :: remove eq_dec y l))
      with (a = x \/ In x (remove eq_dec y l)).
      destruct (eq_dec a x) as [aqx | anx].
      left. assumption.
      right. apply IHl. destruct H as [xny inxal]. split. assumption.
      destruct inxal as [xqa | inxl].
      contradiction. assumption.
  Qed.

  (* For all lists of naturals s and m (subtrahend and minuend), 
     for every natural number x, x should be in (adiff s m) if and only if 
     both x is in s and x is not in m. *)
  
  Theorem adiff_spec : forall (s m : list nat) (x : nat),
                         In x (adiff s m) <-> (In x s /\ not (In x m)).
  Proof.
    intros s m. generalize dependent s. induction m; intros s x; split; intro H.
    - simpl in H. split. assumption. intro contr. inv contr.
    - simpl. destruct H. assumption.
    - simpl in H. rewrite in_remove_in in H.
      destruct H as [xna inxad].
      apply IHm in inxad. destruct inxad as [inxs ninxm].
      split. assumption. intro contr. inv contr.
      pose(uhoh:= eq_refl x). apply xna in uhoh.
      assumption. contradiction.
    - destruct H as [inx ninxam].
      simpl. rewrite in_remove_in. split.
      + intro contr. rewrite contr in *.
        simpl in ninxam. tauto.
      + apply IHm. split.
        * assumption.
        * intro contr. simpl in ninxam. tauto.
  Qed.
      
  Definition missing_below (m : nat) (l : list nat) :=
    adiff (nums m) l.

  (* A number x should be missing in l below m
     if and only if both x is less than m and 
     x is not in l. *)
  
  Lemma mb_spec: forall (n': nat),
                 forall (l : list nat),
                 forall (x : nat),
                   ((In x (missing_below n' l))
                    <->
                    (x < n' /\ not (In x l))).
  Proof.
    intros. split; intro H.
    - unfold missing_below in H.
      apply adiff_spec in H.
      destruct H as [inxn ninxl].
      apply nums_spec in inxn. split; assumption.
    - destruct H.
      unfold missing_below.
      apply adiff_spec.
      rewrite <- nums_spec. split; assumption.
  Qed.

  (* Having finished the auxiliary functions, we move on
     to the objects acted upon by our group. *)

  (* A face pair is a pair of disjoint faces
     of the n-dipyramid. Since they are disjoint,
     we can represent the unordered pair uniquely
     by a---literally---ordered pair, i. e. not just
     a pair in any particular order, but in fact 
     in the order agreeing with <. *)
  
  Definition face_pair (m0 m1 : nat) : Prop := face m0 /\ face m1 /\ m0 < m1.

  (* Two pairs will be said to *clash* when
     they have an entry in common. Clashing is not
     an equivalence relation, nor is its negation. *)
  
  Definition clash (p0 p1 : nat * nat) : Prop := 
    fst p0 = fst p1 \/ fst p0 = snd p1 \/ snd p0 = fst p1 \/ snd p0 = snd p1.

    
  Notation "p0 ## p1" := (clash p0 p1) (at level 40).
  
  Definition clashb (p0 p1 : nat * nat) : bool :=
    orb (fst p0 =? fst p1)
        (orb (fst p0 =? snd p1)
             (orb (snd p0 =? fst p1)
                  (snd p0 =? snd p1))).
  Notation "p0 #? p1" := (clashb p0 p1) (at level 40).

  Lemma clash_reflect: forall (p0 p1 : nat*nat), reflect (clash p0 p1) (clashb p0 p1).
  Proof.
    intros. apply iff_reflect.
    unfold clash. unfold clashb.
    destruct p0. destruct p1.
    simpl. split; intro H.
    - rewrite orb_true_iff.
      rewrite orb_true_iff. rewrite orb_true_iff.
      rewrite Nat.eqb_eq. rewrite Nat.eqb_eq.
      rewrite Nat.eqb_eq. rewrite Nat.eqb_eq.
      assumption.
    - rewrite <- Nat.eqb_eq. rewrite <- Nat.eqb_eq.
      rewrite <- Nat.eqb_eq. rewrite <- Nat.eqb_eq.
      rewrite <- orb_true_iff. rewrite <- orb_true_iff.
      rewrite <- orb_true_iff. assumption.
  Qed.
    
  Hint Resolve clash_reflect : bdestruct.

  (* A list of face pairs will be said to be *clash-free*
     when no two of its elements clash. One could formulate
     this by defining the cartesian square of a list and then
     the cartesian square minus the diagonal, but that's more
     complicated than the following inductive definition. *)
  
  Inductive clash_free : list (nat * nat) -> Prop :=
  | cf_nil : clash_free nil
  | cf_cons : forall (p : nat * nat) (ls : list (nat * nat)),
                clash_free ls ->
                Forall (fun p' => not (clash p p')) ls ->
                clash_free (p :: ls).

  
    
End Necklace.