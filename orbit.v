Require Export Coq.omega.Omega.
Require Export Coq.Arith.Lt.
Require Export Coq.Arith.PeanoNat.
Require Export Coq.Sorting.Permutation.
Require Export Coq.Sorting.Sorted.
Require Export Coq.Lists.List.
Require Export Coq.Bool.Bool.
Require Export Coq.Program.Basics.
Require Import Coq.Logic.FunctionalExtensionality.


Fixpoint labels (m : nat) :=
  match m with
    | 0 => nil
    | S n' => n' :: (labels n')
  end.

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

  Definition face := {f : nat | f < 2 * n}.

  (* For "convenience" we establish some trivial
     but important operations on faces, corresponding
     to operations on natural numbers. *)
  Definition fpf (f0 : face) : nat := proj1_sig f0.
  (* fp for "forget proof face", viz. the proof that
     whatever is less than 2 * n. *)
  Definition eq_face (f0 f1 : face) : Prop := fpf f0 = fpf f1.
  Notation "f0 f= f1" := (eq_face f0 f1) (at level 70).
  Definition eqb_face (f0 f1 : face) : bool := fpf f0 =? fpf f1.
  Notation "f0 f=? f1" := (eqb_face f0 f1) (at level 70).
  Definition lt_face (f0 f1 : face) : Prop := fpf f0 < fpf f1.
  Notation "f0 f< f1" := (lt_face f0 f1) (at level 70).
  Definition ltb_face (f0 f1 : face) : bool := fpf f0 <? fpf f1.
  Notation "f0 f<? f1" := (ltb_face f0 f1) (at level 70).
  Definition le_face (f0 f1 : face) : Prop := fpf f0 <= fpf f1.
  Notation "f0 f<= f1" := (le_face f0 f1) (at level 70).
  Definition leb_face (f0 f1 : face) : bool := fpf f0 <=? fpf f1.
  Notation "f0 f<=? f1" := (leb_face f0 f1) (at level 70).

  Lemma eqf_reflect: forall (f0 f1:face), reflect (f0 f= f1) (f0 f=? f1).
  Proof.
    intros. apply iff_reflect.
    unfold eq_face. unfold eqb_face.
    destruct f0. destruct f1. simpl.
    symmetry. apply Nat.eqb_eq.
  Qed.

  Lemma eq_face_refl : forall (f: face), f f= f.
  Proof.
    intro. destruct f. unfold eq_face. reflexivity.
  Qed.
  
    
  
  Lemma ltf_reflect: forall (f0 f1:face), reflect (f0 f< f1) (f0 f<? f1).
  Proof.
    intros. apply iff_reflect.
    unfold lt_face. unfold ltb_face.
    destruct f0. destruct f1. simpl.
    symmetry. apply Nat.ltb_lt.
  Qed.

  Lemma lef_reflect: forall (f0 f1:face), reflect (f0 f<= f1) (f0 f<=? f1).
  Proof.
    intros. apply iff_reflect.
    unfold le_face. unfold leb_face.
    destruct f0. destruct f1. simpl.
    symmetry. apply Nat.leb_le.
  Qed.
  
  Lemma not_lt_face: forall (f0 f1:face), not ( f0 f< f1 ) -> f1 f<= f0.
  Proof.
    intros. unfold le_face. unfold lt_face in H.
    destruct f0. destruct f1. simpl in *. omega.
  Qed.

  Lemma not_le_face: forall (f0 f1:face), not ( f0 f<= f1 ) -> f1 f< f0.
  Proof.
    intros. unfold lt_face. unfold le_face in H.
    destruct f0. destruct f1. simpl in *. omega.
  Qed.
      
  Hint Resolve eqf_reflect ltf_reflect lef_reflect : bdestruct.
  (* Basically just A. Appel's bdestruct and inv tactics from Perm.v, 
     from his online notes *Verified functional algorithms.* *)
  Ltac bdestruct_f X :=
    let H := fresh in let e := fresh "e" in
                      evar (e: Prop);
                        assert (H: reflect e X); subst e;
                        [eauto with bdestruct
                        | destruct H as [H|H];
                          [ | try first [apply not_lt_face in H | apply not_le_face in H]]].

  Ltac inv H := inversion H; clear H; subst.

  (* A face pair is a pair of disjoint faces
     of the n-dipyramid. Since they are disjoint,
     we can represent the unordered pair uniquely
     by the literally ordered pair, i. e. not just
     a pair in any order, but in order agreeing with f<. *)
  Definition face_pair := { p : face * face | fst p f< snd p }.
  Definition fpff (p : face * face) : nat * nat := (proj1_sig (fst p), proj1_sig (snd p)).
  (* "Forget proof face*face". *)
  Definition fpfp (p : face_pair) : nat * nat := fpff (proj1_sig p).

  (* Two face-pairs will be said to *clash* when
     they have a face in common. Clashing is not
     an equivalence relation, nor is its negation. *)
  Definition clash_nat (p0 p1 : nat * nat) : Prop :=
    fst p0 = fst p1 \/ fst p0 = snd p1 \/ snd p0 = fst p1 \/ snd p0 = snd p1.
  Definition clash (fp0 fp1 : face_pair) : Prop :=
    clash_nat (fpfp fp0) (fpfp fp1).    
    
  Notation "p0 ## p1" := (clash p0 p1) (at level 40).
  Definition clashb_nat (p0 p1 : nat * nat) : bool :=
    orb (fst p0 =? fst p1)
        (orb (fst p0 =? snd p1)
             (orb (snd p0 =? fst p1)
                  (snd p0 =? snd p1))).
  Definition clashb (fp0 fp1 : face_pair) : bool :=
    clashb_nat (fpfp fp0) (fpfp fp1).
         
  Notation "p0 #? p1" := (clashb p0 p1) (at level 40).

  Lemma clash_reflect: forall (fp0 fp1 : face_pair), reflect (clash fp0 fp1) (clashb fp0 fp1).
  Proof.
    intros. apply iff_reflect.
    unfold clash. unfold clashb.
    destruct fp0. destruct fp1.
    unfold clash_nat. unfold clashb_nat.
    simpl. destruct x. destruct x0.
    simpl. destruct f. destruct f0.
    destruct f1. destruct f2. simpl.
    split; intro H.
    - destruct H. rewrite H.
      replace (x1 =? x1) with true. reflexivity.
      symmetry. apply Nat.eqb_refl.
      destruct H. rewrite H. rewrite Bool.orb_comm.
      replace (x2 =? x2) with true. reflexivity.
      symmetry. apply Nat.eqb_refl.
      destruct H. rewrite H.
      SearchAbout orb. rewrite orb_true_iff.
      right. rewrite orb_true_iff. right.
      rewrite orb_true_iff. left. replace (x1 =? x1) with true.
      reflexivity. symmetry. apply Nat.eqb_refl.
      rewrite H. rewrite orb_true_iff. right.
      rewrite orb_true_iff. right. rewrite orb_true_iff. right.
      apply Nat.eqb_refl.
    - rewrite orb_true_iff in H.
      destruct H. left. apply Nat.eqb_eq. assumption.
      rewrite orb_true_iff in H.
      destruct H. right. left. apply Nat.eqb_eq. assumption.
      rewrite orb_true_iff in H.
      destruct H. right. right. left. apply Nat.eqb_eq. assumption.
      right. right. right. apply Nat.eqb_eq. assumption.
  Qed.
  
  Hint Resolve clash_reflect : bdestruct.

  Check Forall.
  
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
  Ltac bdestruct_nat X :=
    let H := fresh in let e := fresh "e" in
                      evar (e: Prop);
                        assert (H: reflect e X); subst e;
                        [eauto with bdestruct
                        | destruct H as [H|H];
                          [ | try first [apply not_lt in H | apply not_le in H]]].

  (* A list of face pairs will be said to be *clash-free*
     when no two of its elements clash. One could formulate
     this by defining the cartesian square of a list and then
     the cartesian square minus the diagonal, but that's more
     complicated than the following inductive definition. *)
  
  Inductive clash_free : list face_pair -> Prop :=
  | cf_nil : clash_free nil
  | cf_cons : forall (fp : face_pair) (ls : list face_pair),
                clash_free ls ->
                Forall (fun fp' => not (clash fp fp')) ls ->
                clash_free (fp :: ls).

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

  Definition znz := { y : nat | y < n }.  
  Definition rot_part (t m : nat) :=
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
  
  Lemma rot_aux : forall (t m : nat),
                    t < n -> m < 2 * n -> rot_part t m < 2 * n.
  Proof.
    intros t m ltn lm2n.
    unfold rot_part.
    bdestruct_nat (m <? n); bdestruct_nat (m + t <? n);
    bdestruct_nat (m+t <? 2 * n); omega.
  Qed.

  Definition rot (tn : znz) (f : face) : face :=
    match tn with
      | exist _ t pft =>
        match f with
          | exist _ m pfm =>
            exist (fun y => y < 2 * n) (rot_part t m) (rot_aux t m pft pfm)
        end
    end.  

  Lemma rot_aux_pole : forall (t m : nat),
                     t < n -> m < 2 * n -> (m < n) <-> ((rot_part t m) < n).
  Proof.
    intros t m ltn lm2n.
    split; intro H;
    unfold rot_part in *;
    bdestruct_nat (m <? n); bdestruct_nat (m + t <? n);
    bdestruct_nat (m+t <? 2 * n); omega.
  Qed.

  Definition on_top (f:face) : Prop :=
    match f with
      | exist _ m pfm => m < n
    end.
        
  Lemma rot_pole: forall (tn : znz) (f: face), on_top f <-> on_top (rot tn f).                        
  Proof.
    intros tn f. destruct tn as [t pft].
    destruct f as [m pfm].
    simpl. apply rot_aux_pole. assumption. assumption.
  Qed.    
  
  Lemma rot_part_inj : forall (t m0 m1 : nat),
                         t < n -> m0 < 2 * n -> m1 < 2 * n ->
                         (rot_part t m0) = (rot_part t m1) ->
                         m0 = m1.
  Proof.
    intros t m0 m1 ltn lt0 lt1 rq.
    unfold rot_part in rq.
    bdestruct_nat (m0 <? n);
      bdestruct_nat (m0 + t <? n);
      bdestruct_nat (m0 + t <? 2 * n);
      bdestruct_nat (m1 <? n);
      bdestruct_nat (m1 + t <? n);
      bdestruct_nat (m1 + t <? 2 * n);
      omega.
  Qed.

  Lemma rot_inj : forall (tn : znz) (f0 f1 : face),
                    rot tn f0 f= rot tn f1 -> f0 f= f1.
  Proof.
    intros tn f0 f1 rq.
    destruct tn as [t pft].
    destruct f0 as [m0 pf0].
    destruct f1 as [m1 pf1].
    unfold rot in rq.
    unfold eq_face in *.
    unfold fpf in *.
    unfold proj1_sig in *.
    apply (rot_part_inj t m0 m1 pft pf0 pf1 rq).
  Qed.
      
  (* The p-flip is the reflection through
     the plane in which the polygon lies of
     which the dipyramid is a suspension. *)

  Definition p_flip_nat (m : nat) : nat :=
    match (m <? n) with
      | true => m + n
      | false => m - n
    end.
  
  Lemma p_flip_nat_2n : forall (m : nat), m < 2 * n -> p_flip_nat m < 2 * n.
  Proof.
    intros m H.
    unfold p_flip_nat.
    bdestruct_nat (m <? n); omega.
  Qed.
  
  Definition p_flip (f : face) : face :=
    match f with
      | exist _ m pf => exist _ (p_flip_nat m) (p_flip_nat_2n m pf)
    end.

  Definition p_flip_nat_inj :
    forall (m0 m1 : nat), m0 < 2 * n -> m1 < 2 * n ->
                          p_flip_nat m0 = p_flip_nat m1 -> m0 = m1.
  Proof.
    intros m0 m1 lt0 lt1 pq.
    unfold p_flip_nat in pq.
    bdestruct_nat (m0 <? n); bdestruct_nat (m1 <? n); omega.
  Qed.

  Lemma p_flip_inj : forall (f0 f1 : face),
                            p_flip f0 f= p_flip f1 -> f0 f= f1.
  Proof.
    intros f0 f1 H.
    destruct f0 as [m0 pf0]. destruct f1 as [m1 pf1].
    unfold p_flip in H. unfold eq_face in *.
    unfold fpf in *. unfold proj1_sig in *.
    apply (p_flip_nat_inj m0 m1 pf0 pf1 H).
  Qed.

  Lemma aux_p_flip : forall (f0 f1 : face),
                       f0 f< f1 -> not (p_flip f0 f= p_flip f1).
  Proof.
    intros f0 f1 H.
    unfold not. intro. apply p_flip_inj in H0.
    destruct f0 as [m0]. destruct f1 as [m1].
    unfold eq_face in *. unfold lt_face in *.
    unfold fpf in *. unfold proj1_sig in *. omega.
  Qed.
  
  Lemma lt_face_dich : forall (f0 f1 : face),
                         not (f0 f= f1) -> ((f0 f< f1) \/ (f1 f< f0)).
  Proof.
    intros f0 f1 nq01.
    destruct f0 as [m0 pf0]. destruct f1 as [m1 pf1].
    unfold eq_face in nq01. unfold lt_face.
    unfold fpf in *. unfold proj1_sig in *.
    omega.
  Qed.

  Lemma lt_face_neq : forall (f0 f1 : face),
                        f0 f< f1 -> not (f0 f= f1).
  Proof.
    intros f0 f1 lt01.
    destruct f0 as [m0 pf0]. destruct f1 as [m1 pf1].
    unfold lt_face in lt01. unfold eq_face.
    unfold fpf in *. unfold proj1_sig in *.
    omega.
  Qed.

  Lemma aux_flip_fp : forall (f0 f1 : face),
                        f0 f< f1 -> ((p_flip f0 f< p_flip f1) \/
                                     (p_flip f1 f< p_flip f0)).
  Proof.
    intros f0 f1 H.
    apply lt_face_dich.
    apply aux_p_flip. assumption.
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
  
  Definition v_flip_nat (m : nat) : nat :=
    match m <? n with
      | true => n - (S m)
      | false => 3 * n - (S m)
    end.  

  Lemma v_flip_nat_2n : forall (m : nat), m < 2 * n -> v_flip_nat m < 2 * n.
  Proof.
    intros m H.
    unfold v_flip_nat.
    bdestruct_nat (m <? n); omega.
  Qed.

  Definition v_flip (f : face) : face :=
    match f with
      | exist _ m pfm =>
        exist (fun y => y < 2 * n) (v_flip_nat m)
              (v_flip_nat_2n m pfm)
    end.
  
  Lemma v_flip_nat_inj : forall (m0 m1 : nat),
                           m0 < 2 * n -> m1 < 2 * n ->
                           v_flip_nat m0 = v_flip_nat m1 ->
                           m0 = m1.
  Proof.
    intros m0 m1 pf0 pf1 vq.
    unfold v_flip_nat in vq.
    bdestruct_nat (m0 <? n);
      bdestruct_nat (m1 <? n);
      omega.
  Qed.
    
  Lemma v_flip_inj : forall (f0 f1 : face),
                       v_flip f0 f= v_flip f1 -> f0 f= f1.
  Proof.
    intros f0 f1.
    destruct f0 as [m0 pf0].
    destruct f1 as [m1 pf1].
    unfold v_flip. unfold eq_face.
    unfold fpf. unfold proj1_sig.
    apply (v_flip_nat_inj m0 m1 pf0 pf1).
  Qed.

  Definition label (f : face) : nat :=
    match f with
      | exist _ m pfm => m
    end.

  Fixpoint faces (l : list face_pair) : list face :=
    match l with
      | nil => nil
      | fp :: fps =>
        match fp with
          | exist _ p pfp =>
            match p with
              | (f0, f1) =>
                f0 :: (f1 :: (faces fps))
            end
        end
    end.

  Check map.
  Check In.
  SearchAbout In.

  Fixpoint inbf (f : face) (l : list face) : bool :=
    match l with
      | nil => false
      | f' :: fs => if f f=? f' then true else (inbf f fs)
    end.

  Fixpoint In_face (f : face) (l : list face) : Prop :=
    match l with
      | nil => False
      | f' :: fs => f f= f' \/ (In_face f fs)
    end.

  Lemma reflect_in_face : forall (f : face) (l : list face),
                            reflect (In_face f l) (inbf f l).
  Proof.
    intros. apply iff_reflect.
    induction l; split; intro; inversion H;
    unfold inbf; bdestruct_f (f f=? a).
    - reflexivity.
    - contradiction.
    - reflexivity.
    - fold inbf. apply IHl. assumption.
    - unfold In_face. left. assumption.
    - unfold In_face. right. fold In_face.
      apply IHl. assumption.
  Qed.

  Fixpoint nums (b : nat) : list nat :=
    match b with
      | 0 => nil
      | S b' => b' :: nums b'
    end.

  Lemma nums_spec : forall (n' x : nat), x < n' <-> In x (nums n').
  Proof.
    intro n'. induction n'; intro x; split; intro H.
    - omega.
    - inv H.
    - simpl. bdestruct_nat (n' =? x).
      + left. assumption.
      + right. assert (x < n').
        { omega. }
        apply IHn'. assumption.
    - inv H. omega. apply IHn' in H0. omega.
  Qed.
  
  Check map.
  
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
        
  Lemma in_adiff_in : forall (m s : list nat) (x : nat),
                       In x (adiff s m) -> In x s.
  Proof.
    intro m; induction m; intros s x; intro H.
    - simpl in H. assumption.
    - simpl in H. 
    
  Lemma adiff_nil : forall (l : list nat), adiff nil l = nil.
  Proof.
    intro l; induction l.
    - reflexivity.
    - simpl. assumption.
  Qed.
    
  Definition missing_below (m : nat) (l : list nat) :=
    asymmetric_difference (nums m) l.
      

  Lemma mb_0 : forall (l: list nat), missing_below 0 l = nil.
  Proof.
    intro l; induction l.
    - reflexivity.
    - unfold missing_below. fold missing_below. assumption.
  Qed.
      

                          
    

  Lemma mb_spec: forall (n': nat),
                 forall (l : list nat),
                   LocallySorted gt l ->
                   forall (x : nat),
                     ((In x (missing_below n' l))
                      <->
                      (x < n' /\ not (In x l))).
  Proof.
    destruct n'.
    
        
      
    
      
      
      
      
        
      
              
                      
                      
                      
          
      
      
                      
    
  
  
    
    
  
End Necklace.