Require Export Coq.omega.Omega.
Require Export Coq.Arith.Lt.
Require Export Coq.Arith.PeanoNat.
Require Export Coq.Sorting.Sorting.
Require Export Coq.Lists.List.
Require Export Coq.Bool.Bool.
Require Export Coq.Program.Basics.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Recdef.
Require rt_inv.


Require Import Orders.

(* from Andrew Appel's online notes "Verified Functional Algorithms."
     We note that Ltac definitions may be treated as black boxes;
     it is presumed impossible to prove falsity by introducing
     Ltac definitions and using them. *)
Notation "x >? y" := (y <? x).
Notation "x >=? y" := (y <=? x).

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

Lemma bgt_reflect : forall x y, reflect (x > y) (x >? y).
Proof.
  intros x y.
  apply iff_reflect. symmetry. apply Nat.ltb_lt.
Qed.

  
Lemma bge_reflect : forall x y, reflect (x >= y) (x >=? y).
Proof.
  intros x y.
  apply iff_reflect. symmetry. apply Nat.leb_le.
Qed.

Hint Resolve blt_reflect ble_reflect beq_reflect bge_reflect bgt_reflect: bdestruct.
Ltac bdestruct X :=
  let H := fresh in let e := fresh "e" in
                    evar (e: Prop);
                      assert (H: reflect e X); subst e;
                      [eauto with bdestruct
                      | destruct H as [H|H];
                        [ | try first [apply not_lt in H | apply not_le in H]]].

Ltac inv H := inversion H; clear H; subst.

Definition pair_ge (p0 p1 : nat * nat) : Prop :=
  match p0 with
    | (m00, m01) =>
      match p1 with
        | (m10, m11) =>
          m00 > m10 \/ (m00 = m10 /\ m01 >= m11)
      end
  end.


Definition pair_geb (p0 p1 : nat * nat) : bool :=
  match p0 with
    | (m00, m01) =>
      match p1 with
        | (m10, m11) =>
          orb (m00 >? m10)
              (andb (m00 =? m10)
                    (m01 >=? m11))
      end
  end.

Lemma reflect_pair_ge_geb : forall (p0 p1 : nat * nat),
                              reflect (pair_ge p0 p1) (pair_geb p0 p1).
Proof.
  intros p0 p1. destruct p0 as [m00 m01].
  destruct p1 as [m10 m11]. apply iff_reflect.
  unfold pair_ge. unfold pair_geb.
  split; intro H; bdestruct (m00 >? m10);
  bdestruct (m00 =? m10); bdestruct (m01 >=? m11);
  try omega; try reflexivity; try inv H.
Qed.

Hint Resolve reflect_pair_ge_geb : bdestruct.

Module FPOrder <: TotalLeBool.
  Definition t := prod nat nat.
  Definition leb := pair_geb.
  Theorem leb_total : forall a1 a2,
                        leb a1 a2 = true \/ leb a2 a1 = true.
  Proof.
    intros. unfold leb. destruct a1 as [a11 a12].
    destruct a2 as [a21 a22]. simpl.
    bdestruct (a11 >? a21); bdestruct (a11 =? a21);
    bdestruct (a12 >=? a22); bdestruct (a21 >? a11);
    bdestruct (a21 =? a11); bdestruct (a22 >=? a12);
    try omega; simpl; try (left; reflexivity);
    try (right; reflexivity).
  Qed.
End FPOrder.

Module Import FPSort := Sort FPOrder.

Section Necklace.

  Variable n : nat.
  
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
  Definition faceb (m : nat) : bool := m <? 2 * n.
  Lemma reflect_face : forall (m : nat), reflect (face m) (faceb m).
  Proof.
    intro. apply iff_reflect.
    unfold face. unfold faceb.
    rewrite Nat.ltb_lt. tauto.
  Qed.

  Hint Resolve reflect_face : bdestruct.
  
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
                       In x (faces l) <->
                       exists (y: nat*nat),
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
     in the order agreeing with >. We use > instead
     of < so that missing_below, nums, range and
     other functions are more convenient to code.
     Using < would probably involve futzing around
     with reverse, constantly subtracting n or 2 *n,
     or even having to use a coinductive definition
     of nums. So we use >. *)
  
  Definition face_pair (p : nat*nat) : Prop := face (fst p) /\ face (snd p) /\ fst p > snd p.

  Definition face_pairb (p : nat*nat) : bool :=
    andb (faceb (fst p))
         (andb (faceb (snd p))
               ((fst p) >? (snd p))).

  Lemma reflect_face_pair : forall (p : nat*nat),
                              reflect (face_pair p) (face_pairb p).
  Proof.
    intro p. apply iff_reflect.
    unfold face_pair. unfold face_pairb.
    do 2 rewrite andb_true_iff.
    destruct p as [p0 p1]. simpl.
    bdestruct (faceb p0); bdestruct (faceb p1);
    bdestruct (p0 >? p1); unfold face in *;
    split; intro SH; destruct SH as [SH0 SH];
    destruct SH as [SH1 SH2]; try split; try split;
    try reflexivity; try assumption; try omega;
    try inv SH0; try inv SH1; try inv SH2.
  Qed.

  Hint Resolve reflect_face_pair : bdestruct.
  
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

  Lemma reflect_clash: forall (p0 p1 : nat*nat), reflect (clash p0 p1) (clashb p0 p1).
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
    
  Hint Resolve reflect_clash : bdestruct.

  (* We will represent face-pairings by lists of face-pairs.
     Just as we represent face-pairs by properly ordered
     pairs, we represent face-pairings by properly ordered,
     i.e. sorted, lists of face-pairs. To sort, we have to
     introduce an order on face-pairs. *)

  (* The above is the lexicographic
     ordering, which is what we're familiar with.
     However, a test for this relation will lie deep within
     loops. It behooves us to make it as fast as
     possible. In fact, since we'll only be using
     non-clashing pairs, we can omit the right disjunct. *)
     
  Definition pair_ge' (p0 p1 : nat * nat) : Prop := fst p0 > fst p1.
  Definition pair_geb' (p0 p1 : nat * nat) : bool := fst p0 >? fst p1.

  Lemma reflect_pair_ge'_geb' : forall (p0 p1 : nat * nat),
                                  reflect (pair_ge' p0 p1) (pair_geb' p0 p1).
  Proof.
    intros p0 p1. destruct p0 as [m00 m01].
    destruct p1 as [m10 m11]. apply iff_reflect.
    unfold pair_ge'. unfold pair_geb'.
    split; intro H; simpl in *; bdestruct (m00 >? m10);
    try omega; try reflexivity; try inv H.
  Qed.

  Hint Resolve reflect_pair_ge'_geb' : bdestruct.

  Lemma pair_ge'_no_clash : forall (p0 p1 : nat * nat),
                              face_pair p0 -> face_pair p1 ->
                              not (clash p0 p1) ->
                              (pair_ge p0 p1 <-> pair_ge' p0 p1).
  Proof.
    intros p0 p1 fp0 fp1 nc.
    destruct p0 as [m00 m01].
    destruct p1 as [m10 m11].
    unfold face_pair in *.
    apply Decidable.not_or in nc.
    destruct nc as [nqff nc].
    apply Decidable.not_or in nc.
    destruct nc as [nqfs nc].
    apply Decidable.not_or in nc.
    destruct nc as [nqsf nqss].
    simpl in *. unfold face in *.
    destruct fp0 as [lt00 [lt01 lt0001]].
    destruct fp1 as [lt10 [lt11 lt1011]].
    split; intro H.
    - unfold pair_ge'. simpl.
      destruct H as [ | H].
      + assumption.
      + destruct H as [q0010 lt0111]. omega.
    - unfold pair_ge' in H. simpl in H.
      left. assumption.
  Qed.

  (* Having introduced an ordering on face-pairs, we can
     almost say what is a partial face-pairing. The remaining
     concept we need is clash-freedom. *)
  
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

  Fixpoint clash_freeb (l : list (nat * nat)) : bool :=
    match l with
      | nil => true
      | p :: ps => andb (forallb (fun p' => negb (clashb p p')) ps)
                        (clash_freeb ps)
    end.
  
  Lemma reflect_clash_free : forall (l: list (nat*nat)),
                               reflect (clash_free l) (clash_freeb l).
  Proof.
    intro l. induction l; apply iff_reflect; split; intro H.
    - reflexivity.
    - apply cf_nil.
    - simpl. apply andb_true_iff.
      split; inversion H; rewrite Forall_forall in H3.
      + apply forallb_forall.
        intro x. intro inxl.
        apply negb_true_iff.
        apply H3 in inxl. bdestruct (a #? x).
        contradiction. reflexivity.
      + inversion IHl. reflexivity. contradiction.
    - simpl in H. apply andb_true_iff in H.
      destruct H as [fbt clbt].
      rewrite forallb_forall in fbt.
      apply cf_cons.
      + inversion IHl. assumption.
        rewrite <- H in clbt. inv clbt.
      + rewrite Forall_forall. intro x.
        intro inxl. apply fbt in inxl.
        bdestruct (a #? x). inv inxl. assumption.
  Qed.

  Hint Resolve reflect_clash_free : bdestruct.      

  Lemma clash_free_ge_ge' :
    forall (l: list (nat * nat)),
      clash_free l ->
      Forall face_pair l ->
      (LocallySorted pair_ge l <-> LocallySorted pair_ge' l).
  Proof.
    intro l. induction l; intro csl; intro ffpl; split; intro H;
             try apply LSorted_nil; destruct l;
             try apply LSorted_cons1; try apply LSorted_consn;
             inv H; inv csl; inv ffpl.
    - apply IHl; assumption.
    - inv H6. inv H3.
      apply pair_ge'_no_clash; assumption.
    - apply IHl; assumption.
    - inv H6. inv H3.
      apply pair_ge'_no_clash; assumption.
  Qed.
       
  (* Thus we say a *(partial) face-pairing* is a sorted,
     clash-free list of face-pairs. *)

  Definition face_pairing (l: list (nat * nat)) : Prop :=
    Forall face_pair l /\ (Sorted pair_ge l) /\ clash_free l.

  (* We should reflect this. To do so, we need a
     reflection of sortedness. *)

  Fixpoint locally_sortedb (l : list (nat*nat)) : bool :=
    match l with
      | nil => true
      | p0 :: ps =>
        match ps with
          | nil => true
          | p1 :: ps' =>
            andb (pair_geb' p0 p1) (locally_sortedb ps)
        end
    end.
  

  (* Note that we recur on ps, *not* on ps'. *)

  Lemma reflect_locally_sorted_b :
    forall (l: list (nat*nat)),
      reflect (LocallySorted pair_ge' l) (locally_sortedb l).
  Proof.
    intro l. apply iff_reflect. induction l; split; intro H.
    - reflexivity.
    - apply LSorted_nil.
    - destruct l as [ | a' l].
      + reflexivity.
      + change (locally_sortedb (a :: a' :: l))
        with (pair_geb' a a' && locally_sortedb (a' :: l)).
        apply andb_true_iff. inv H. split.
        * bdestruct (pair_geb' a a'). reflexivity.
          unfold pair_ge' in H4. omega.
        * apply IHl. assumption.
    - destruct l as [ | a' l].
      + apply LSorted_cons1.
      + change (locally_sortedb (a :: a' :: l))
        with (pair_geb' a a' && locally_sortedb (a'::l)) in H.
        apply andb_true_iff in H. 
        destruct H as [pgaa lst].
        apply LSorted_consn.
        apply IHl in lst. assumption.
        bdestruct (pair_geb' a a').
        assumption. inv pgaa.
  Qed.

  Hint Resolve reflect_locally_sorted_b : bdestruct.

  Definition face_pairingb (l: list (nat * nat)) : bool :=
    andb (forallb face_pairb l)
         (andb (locally_sortedb l)
               (clash_freeb l)).
  
  Lemma reflect_face_pairing :
    forall (l: list (nat * nat)),
      reflect (face_pairing l) (face_pairingb l).
  Proof.
    intro l. apply iff_reflect.
    unfold face_pairing. unfold face_pairingb.
    rewrite andb_true_iff. rewrite andb_true_iff.
    split; intro H; destruct H as [frl H]; destruct H as [srtl cl];
    split; try split.
    - apply forallb_forall. rewrite Forall_forall in frl.
      intro x. intro inxl. apply frl in inxl.
      bdestruct (face_pairb x). reflexivity. contradiction.
    - apply Sorted_LocallySorted_iff in srtl.
      apply clash_free_ge_ge' in srtl.
      2: assumption. 2: assumption.
      bdestruct (locally_sortedb l). reflexivity. contradiction.
    - bdestruct (clash_freeb l). reflexivity. contradiction.
    - apply Forall_forall. rewrite forallb_forall in frl.
      intros x inxl. apply frl in inxl. bdestruct (face_pairb x).
      assumption. inv inxl.
    - apply Sorted_LocallySorted_iff.
      bdestruct (locally_sortedb l).
      apply clash_free_ge_ge'. bdestruct (clash_freeb l).
      assumption. inv cl. apply Forall_forall.
      intros x inxl. rewrite forallb_forall in frl.
      apply frl in inxl. bdestruct (face_pairb x).
      assumption. inv inxl. assumption. inv srtl.
    - bdestruct (clash_freeb l). assumption. inv cl.
  Qed.
  
  Hint Resolve reflect_face_pairing : bdestruct.                             
    
  Definition complete_face_pairing (l: list (nat * nat)) : Prop :=
    face_pairing l /\ length l = n.

  (* Now we are in a position to describe our master plan.
     We might like, if feasible, to enumerate all clash-free
     complete (i.e. length n) lists of face-pairs, then have
     Regina construct their associated manifolds and determine
     their JSJ structure. However, the dipyramidal group acts
     on these gluings; most gluings will be asymmetrical, and
     hence there will be several face-pairings associated to
     a given homeomorphism class. We cannot eliminate altogether
     the occurrence of "repeat" homeomorphism classes; a
     given necklace manifold can admit inequivalent instantiations
     as a dipyramidal gluing. But it would be remiss not to
     take advantage of the symmetry group.

     To take account of the symmetry group, we will only give
     Regina *maximal* face-pairings, where "l is maximal" will
     mean "l is lexicographically >-maximal in its dipyr-group orbit", and
     ">" will be the lexicographic ordering on permutations
     in cycle notation, not Cayley notation. 

     One might think that the use of cycle notation 
     would make it possible to do a sensible
     one-step-at-a-time generation of the required face-pairings, 
     where at each step one has a list of "partial" face-pairings
     (i.e. lists of face-pairs with length less than n), and
     one adds faces to these in all but only the *sensible* ways,
     where to be sensible an addition must not only maintain
     clash-freedom, but also it must maintain <-minimality. 

     Unfortunately, this doesn't work.

     Following Milley, we could just enumerate length-2*n face-pairings,
     put them in a list L, make a new list R, then for each element p of L, remove
     p's orbit from L, and put p in R. At the conclusion of this algorithm,
     R will contain exactly one representative from each dipyr-group orbit
     of face-pairings.

     However, we think that requires a large amount of time and space compared with
     the following more complicated scheme, which we sketch briefly in this comment.

     First of all, we have a proper-prefix relation on partial face-pairings.
     This induces a tree structure T on partial face-pairings---not, in general, a binary
     tree structure---so that we may regard a partial face-pairing as a
     path with no backtracks in T beginning at the root, and a
     complete face-pairing as a maximum-length such path. We should be able to
     implement maximum-path removal algorithms on T more efficient than
     element removal algorithms on lists. We could thus rewrite the approach
     above as "Put all length-2*n face-pairings as leaves in T, make a new
     list R, then for each leaf p of T, remove p's orbit from T, and put p in R."
     At the conclusion of this algorithm, R will contain one rep from each orbit.
     But T will require much less storage space than L, and removal from T
     will be much quicker. Or so we hope. *)

  (* Now we should determine the action on lists of face-pairs.
     We should first, then, determine the action on face-pairs.
     This isn't completely straightforward because our definition
     of face-pair involves the order condition. *)

  (* It's also even less straightforward because this group
     is acting on several things at once. So we condescend now
     to an abstraction which is, we hope, not too pompous. *)

  Inductive DPGp : Type :=
  | Rot : forall t : nat, DPGp
  | VRot : forall t : nat, DPGp
  | PRot : forall t : nat, DPGp
  | VPRot : forall t : nat, DPGp.

  Definition act_natural (s : DPGp) (m : nat) :=
    match s with
      | Rot t => rot t m
      | VRot t => v_flip (rot t m)
      | PRot t => p_flip (rot t m)
      | VPRot t => v_flip (p_flip (rot t m))
    end.

  Definition a_n := act_natural.

  Definition act_face_pair (s : DPGp) (p : nat * nat) :=
    match p with
      | (m0, m1) =>
        (let (x,y) := (a_n s m0, a_n s m1) in 
        match x >? y with
          | true => (x, y)
          | false => (y, x)
        end)
    end.

  Definition act_face_pairing (s : DPGp) (l : list (nat * nat)) : list (nat * nat) :=
    sort (map (act_face_pair s) l).

  Definition afp := act_face_pairing.

  (* If this is too slow, we could improve on this by
     using bucket sort instead. *)
  
  (* Another option would be to just use map here.
     However, this would mean representing face-pairings
     by possibly non-sorted lists. This would require
     a different ordering proposition than the one
     we defined above; we would have to find and compare
     maximal elements. It seems like in either case we
     would need to do sorting or heap-building of some kind
     repeatedly. Possibly this group is nice enough that
     one can say something useful about its action on
     already sorted lists of already sorted pairs. We hope
     such considerations will turn out to be unnecessary. *)

  Definition app'' (l0 l1 : list (list (nat * nat))) := app l0 l1.
  Definition orbit_with_repeats (l : list (nat * nat)) : list (list (nat * nat)) :=
    fold_right app'' nil
               (map (fun nm =>
                       map (fun dpgp => afp dpgp l)
                           (map (fun dpg => dpg nm)
                                (Rot :: VRot :: PRot :: VPRot :: nil)))
                    (nums n)).
  
  (* If we have already a partial face-pairing l,
     then the *next* face-pairs are the face-pairs
     of the form (M,m), where M is the first (>-maximal)
     element of missing_below 2*n (faces l), and m is
     some other element thereof. We might could make
     this faster by redesigning missing_below somehow
     and maintaining some state about the faces used
     "so far" or something like that. We hopefully
     press onward with what we have, though. *)
 
  Definition next_face_pairs (l : list (nat * nat)) : list (nat * nat) :=
    let mb := (missing_below (2*n) (faces l)) in
    match mb with
      | nil => nil
      | M :: ms => map (fun m => (M,m)) ms
    end.

  (* Here we use an aspect missing_below not provided in its spec!
     So we should prove it. *)

  Lemma adiff_nil : forall (l : list nat), adiff nil l = nil.
  Proof.
    intro l. induction l.
    - reflexivity.
    - simpl. rewrite IHl. reflexivity.
  Qed.

  Lemma sorted_nums : forall (m : nat), Sorted ge (nums m).
  Proof.
    intro m. induction m.
    - apply Sorted_nil.
    - change (nums (S m)) with (m :: nums m).
      apply Sorted_cons. assumption.
      destruct m. apply HdRel_nil.
      change (nums (S m)) with (m :: nums m).
      apply HdRel_cons. omega.
  Qed.

  Lemma pair_ge_trans: Relations_1.Transitive pair_ge.
  Proof.
    unfold Relations_1.Transitive.
    intros x y z.
    destruct x as [x0 x1].
    destruct y as [y0 y1].
    destruct z as [z0 z1].
    unfold pair_ge.
    intros pgxy pgyz.
    omega.
  Qed.

  Lemma ge_trans: Relations_1.Transitive ge.
  Proof.
    unfold Relations_1.Transitive.
    unfold ge. intros. eapply le_trans.
    apply H0. apply H.
  Qed.

  Lemma Forall_remove : forall (l : list nat) (m : nat) (P : nat -> Prop),
                          Forall P l -> Forall P (remove Nat.eq_dec m l).
  Proof.
    intro l. induction l.
    - intros. apply Forall_nil.
    - intros m P fpal.
      change (remove Nat.eq_dec m (a :: l))
      with (if Nat.eq_dec m a then remove Nat.eq_dec m l else a :: remove Nat.eq_dec m l).
      inv fpal. destruct (Nat.eq_dec m a).
      apply IHl. assumption. apply Forall_cons.
      assumption. apply IHl. assumption.
  Qed.
  
  Lemma sorted_remove : forall (l : list nat) (m : nat),
                          Sorted ge l -> Sorted ge (remove Nat.eq_dec m l).
  Proof.
    intro l. induction l.
    - intros. apply Sorted_nil.
    - intros m srtal.
      Print remove.
      change (remove Nat.eq_dec m (a :: l))
      with (if Nat.eq_dec m a then remove Nat.eq_dec m l else a :: remove Nat.eq_dec m l).
      destruct (Nat.eq_dec m a).
      apply IHl. inv srtal. assumption.
      apply StronglySorted_Sorted.
      apply SSorted_cons. apply Sorted_StronglySorted.
      apply ge_trans. apply IHl. inv srtal. assumption.
      apply Sorted_StronglySorted in srtal.
      2: apply ge_trans. inv srtal.
      apply Forall_remove. assumption.
  Qed.
                                          
  Lemma sorted_missing_below : forall (m : nat) (l : list nat),
                                 Sorted ge (missing_below m l).
  Proof.
    intro m. induction m; intro l; induction l.
    - compute. apply Sorted_nil.
    - unfold missing_below.
      simpl. rewrite adiff_nil. simpl. apply Sorted_nil.
    - unfold missing_below.
      simpl. change (m :: nums m) with (nums (S m)).
      apply sorted_nums.
    - unfold missing_below. Print adiff.
      change (adiff (nums (S m)) (a :: l))
      with (remove Nat.eq_dec a (adiff (nums (S m)) l)).
      change (adiff (nums (S m)) l)
      with (missing_below (S m) l).
      apply sorted_remove. assumption.
  Qed.
  
  (* The following seems obvious but is surprisingly difficult to nail down. *)

  Lemma next_no_clash :
    forall (l : list (nat*nat)) (s: nat * nat),
      clash_free l -> In s (next_face_pairs l) -> clash_free (s :: l).
  Proof.
    intro l. induction l.
    - intros. apply cf_cons. apply cf_nil.
      apply Forall_nil.
    - intros s cfal insnal.
      apply cf_cons. assumption.
      apply Forall_forall. intros x inxal.
      unfold next_face_pairs in insnal.
      remember (missing_below (2 * n) (faces (a :: l))) as mbl.
      destruct mbl as [ | m ms]. inv insnal.
      destruct a as [a0 a1]. destruct s as [s0 s1]. destruct x as [x0 x1].
      change (faces ((a0, a1) :: l)) with (a0 :: (a1 :: (faces l))) in Heqmbl.
      assert (mmb: In m (missing_below (2 * n) (a0 :: a1 :: faces l))).
      { rewrite <- Heqmbl. unfold In. left. reflexivity. }
      apply mb_spec in mmb.
      assert (famsmb: forall m', In m' ms -> (m' < 2 * n /\ not (In m' (a0 :: a1 :: faces l)))).
      { intro m'. rewrite <- mb_spec. intro Inmms.
        rewrite <- Heqmbl. apply in_cons. assumption. }
      assert (aux0: forall (ls: list nat) (s s' m':nat),
                      In (s,s') (map (fun m0 : nat => (m',m0)) ls) ->
                      (s = m' /\ In s' ls)).
      { intro ls. induction ls; intros s s' m' inh; try contradiction.
        change (map (fun m0 : nat => (m', m0)) (a :: ls))
        with ((m', a) :: (map (fun m0 : nat => (m', m0)) ls)) in inh.
        change (In (s, s') ((m', a) :: (map (fun m0 : nat => (m', m0)) ls)))
        with ((m',a) = (s,s') \/ In (s,s') (map (fun m0 : nat => (m', m0)) ls)) in inh.
        destruct inh; split.
        - inv H. reflexivity.
        - inv H. unfold In. left. reflexivity.
        - apply IHls in H. destruct H. assumption.
        - apply IHls in H. destruct H.
          change (In s' (a :: ls)) with (a = s' \/ In s' ls).
          right. assumption. }
      apply aux0 in insnal. inv insnal. inv mmb. inv inxal.
      + inv H2.
        assert (nmx0: x0 <> m).
        { change (In m (x0 :: x1 :: faces l))
          with (x0 = m \/ In m (x1 :: faces l)) in H1.
          intro contr. assert (x0 = m \/ In m (x1 :: faces l)).
          { left. assumption. } contradiction. }
        assert (nmx1: x1 <> m).
        { change (In m (x0 :: x1 :: faces l))
          with (x0 = m \/ In m (x1 :: faces l)) in H1.
          change (In m (x1 :: faces l))
          with (x1 = m \/ In m (faces l)) in H1.
          intro contr. assert (x0 = m \/ x1 = m \/ In m (faces l)).
          { right. left. assumption. } contradiction. }
        assert (ns1x0: x0 <> s1).
        { apply famsmb in H0. destruct H0.
          intro contr. assert (In s1 (x0 :: x1 :: faces l)).
          { unfold In. left. assumption. } contradiction. }
        assert (ns1x1: x1 <> s1).
        { apply famsmb in H0. destruct H0.
          intro contr. assert (In s1 (x0 :: x1 :: faces l)).
          { unfold In. right. left. assumption. } contradiction. }
        intro contr. unfold clash in contr.
        simpl in contr. omega.
      + assert (aux1: forall (ls: list (nat*nat)) (x x' : nat),
                        In (x,x') ls -> (In x (faces ls) /\ In x' (faces ls))).
        { intro ls. induction ls; intros x x' inxl.
          - inv inxl.
          - destruct a as [a a'].
            simpl. change (In (x,x') ((a,a') :: ls))
            with ((a,a') = (x,x') \/ In (x,x') ls) in inxl.
            destruct inxl.
            + inv H3. simpl. split.
              left. reflexivity. right.
              left. reflexivity.
            + apply IHls in H3. destruct H3.
              split; right; right; assumption. }
        apply aux1 in H2. destruct H2.
        assert (nmfl: not (In m (faces l))).
        { intro contr. assert (In m (a0 :: a1 :: faces l)).
          { simpl. right. right. assumption. } contradiction. }
        assert (ns1fl: not (In s1 (faces l))).
        { apply famsmb in H0. destruct H0.
          intro contr. assert (In s1 (a0 :: a1 :: faces l)).
          { simpl. right. right. assumption. } contradiction. }
        intro contr. unfold clash in contr.
        simpl in contr. destruct contr as [bad | contr].
        rewrite bad in *. contradiction.
        destruct contr as [bad | contr].
        rewrite bad in *. contradiction.
        destruct contr as [contr | contr];
          rewrite contr in *; contradiction.
  Qed.

  (* Now we can define our tree with confidence. 
     We actually end up modelling it as a binary
     tree, with a right-most path starting from
     the root representing a list of face-pairs all
     beginning with the same face. *)

  Inductive PairTree : Type :=
  | PTLeaf : PairTree
  | PTBranch : (nat*nat) -> PairTree -> PairTree -> PairTree.

  Fixpoint properb (pt : PairTree) : bool :=
    match pt with
      | PTLeaf => true
      | PTBranch _ l r =>
        match l with
          | PTBranch _ _ _ =>
            andb (properb l) (properb r)
          | PTLeaf =>
            match r with
              | PTBranch _ _ _ => false
              | PTLeaf => true
            end
        end
    end.

  Inductive proper : PairTree -> Prop :=
  | proper_leaf : proper PTLeaf
  | proper_branch_1 : forall (p : nat*nat) (l: PairTree),
                      proper l -> proper (PTBranch p l PTLeaf)
  | proper_branch_2 : forall (p pl pr: nat*nat) (ll lr rl rr : PairTree),
                        proper (PTBranch pl ll lr) ->
                        proper (PTBranch pr rl rr) ->
                        proper (PTBranch p (PTBranch pl ll lr) (PTBranch pr rl rr)).
  
  Lemma reflect_proper_pairtree :
    forall (pt : PairTree), reflect (proper pt) (properb pt).
  Proof.
    intro pt. apply iff_reflect. induction pt; split; intro H.
    - reflexivity.
    - apply proper_leaf.
    - inv H.
      + simpl. apply IHpt1 in H1. rewrite H1.
        destruct pt1; reflexivity.
      + rewrite IHpt1 in H2. rewrite IHpt2 in H4.
        change (properb (PTBranch p (PTBranch pl ll lr) (PTBranch pr rl rr)))
        with (andb (properb (PTBranch pl ll lr)) (properb (PTBranch pr rl rr))).
        apply andb_true_iff. split; assumption.
    - simpl in H. destruct pt1; destruct pt2.
      + apply proper_branch_1. apply proper_leaf.
      + inv H.
      + apply andb_true_iff in H. destruct H.
        apply IHpt1 in H.
        apply proper_branch_1. assumption.
      + apply andb_true_iff in H. destruct H.
        apply IHpt1 in H. apply IHpt2 in H0.
        apply proper_branch_2; assumption.
  Qed.
  
  Hint Resolve reflect_proper_pairtree : bdestruct.
  Fixpoint shloop (remains memory : list nat) :=
    match memory with
      | nil => remains
      | h :: t => shloop (h :: remains) t
    end.
  
  Fixpoint fueled_prefix_part' (gas:nat) (remaining remembering: list nat) : PairTree :=
    match gas with
      | 0 => PTLeaf
      | S gas' =>
        match remaining with
          | nil => PTLeaf
          | f :: fs =>
            match fs with
              | nil => PTLeaf
              | f' :: fs' =>
                PTBranch (f,f')
                         (fueled_prefix_part' gas' (shloop fs' remembering) nil)
                         (fueled_prefix_part' gas' (f :: fs') (f' :: remembering))
            end
        end
    end.

  (* What is going wrong here?

  Function fueled_prefix_part (gas : nat) (remaining remembering: list nat) {measure (fun x => x) gas} : PairTree :=
    match gas >? 0 with
      | false => PTLeaf
      | true =>
        match remaining with
          | nil => PTLeaf
          | f :: fs =>
            match fs with
              | nil => PTLeaf
              | f' :: fs' =>
                let gas' := gas - 1 in
                PTBranch (f,f')
                         (fueled_prefix_part gas' (shloop fs' remembering) nil)
                         (fueled_prefix_part gas' (f :: fs') (f' :: remembering))
            end
        end
    end.
  Proof.
    intro gas. induction gas; intros _ _ teq _ _ _ _ _ _.
    inv teq.
    omega.
    intro gas. induction gas; intros _ _ teq _ _ _ _ _ _.
    inv teq.
    omega.
  Defined.

  *)
  
  Definition prefix_tree : PairTree := fueled_prefix_part (n * n) (nums (2 * n)) nil.

  Inductive is_top_path : PairTree -> list (nat*nat) -> Prop :=
  | top_path_nil : forall (pt : PairTree), is_top_path pt nil
  | top_path_cons_left : forall (ptl ptr : PairTree) (p : nat*nat) (l: list (nat*nat)),
                          is_top_path ptl l -> is_top_path (PTBranch p ptl ptr) (p :: l)
  | top_path_cons_right : forall (ptl ptr : PairTree) (p : nat*nat) (l: list (nat*nat)),
                            is_top_path ptr l -> is_top_path (PTBranch p ptl ptr) l.

  Fixpoint left_top (pt : PairTree) : list (nat*nat) :=
    match pt with
      | PTLeaf => nil
      | PTBranch p lt rt => p :: (left_top lt)
    end.

  Definition pair_eqb (p0 p1 : nat*nat) :=
    match p0 with
      | (p00, p01) =>
        match p1 with
            (p10, p11) =>
            andb (p00 =? p10) (p01 =? p11)
        end
    end.
  
  Fixpoint remove_top_path (l : list (nat*nat)) (pt : PairTree) : PairTree :=
    match l with
      | nil => pt
      | p :: ps =>
        match pt with
          | PTLeaf => PTLeaf
          | PTBranch p' lt rt =>
            match pair_eqb p p' with
              | false => PTBranch p' lt (remove_top_path l rt)
              | true =>
                let lt' := remove_top_path ps lt in
                match lt' with
                  | PTLeaf => rt
                  | PTBranch _ _ _ => PTBranch p' lt' rt
                end
            end
        end
    end.

  Fixpoint num_leaves (pt : PairTree) : nat :=
    match pt with
      | PTLeaf => 1
      | PTBranch _ lt rt => (num_leaves lt) + (num_leaves rt)
    end.

  
  Definition pop_top (pp: prod (list (list (nat*nat))) PairTree) :
    prod (list (list (nat*nat))) PairTree :=
    match pp with
      | (reps, pt) =>
        match pt with
          | PTLeaf => (reps, pt)
          | _ =>
            let lp := left_top pt in
            (lp :: reps, fold_right remove_top_path pt (orbit_with_repeats lp))
        end
    end.
  
  Fixpoint fueled_reps (gas : nat) (pp: prod (list (list (nat*nat))) PairTree) :=
    match gas with
      | 0 => pp
      | S gas' => pop_top (fueled_reps gas' pp)
    end.
    
  Definition orbit_reps : list (list (nat * nat)) :=
    fst (fueled_reps (num_leaves prefix_tree) (nil, prefix_tree)).  
  
End Necklace.
