(** * A Formalization that (compositional) Z property implies confluence in a nominal framework *)

Require Export Arith Lia.
Require Export Metalib.Metatheory.
Require Export Metalib.LibDefaultSimp.

Inductive n_sexp : Set :=
 | n_var (x:atom)
 | n_abs (x:atom) (t:n_sexp)
 | n_app (t1:n_sexp) (t2:n_sexp)
 | n_sub (t1:n_sexp) (x:atom) (t2:n_sexp).

Lemma aux_not_equal : forall (x:atom) (y:atom),
    x <> y -> y <> x.
Proof.
  intros. unfold not. intros. unfold not in H.
  assert (x = y). {
    rewrite H0. reflexivity.
  }
  contradiction.
Qed.

Lemma Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof.
  intros n m H. inversion H.
  - apply le_n.
  - apply (le_trans n (S n) m).
    -- apply le_S. reflexivity.
    -- assumption.
Qed.

Fixpoint size (t : n_sexp) : nat :=
  match t with
  | n_var x => 1
  | n_abs x t => 1 + size t
  | n_app t1 t2 => 1 + size t1 + size t2
  | n_sub t1 x t2 => 1 + size t1 + size t2
  end.

Lemma strong_induction :
 forall (P:nat->Prop),
   (forall n, (forall m, m < n -> P m) -> P n) ->
   (forall n, P n).
Proof.
  intros Q IH n.
  assert (H := nat_ind (fun n => (forall m : nat, m < n -> Q m))).
  apply IH. apply H.
  - intros m Hlt; inversion Hlt.
  - intros n' H' m Hlt. apply IH.
    intros m0 Hlt'. apply H'.
    apply lt_n_Sm_le in Hlt.
    apply lt_le_trans with m; assumption.
Qed.

Fixpoint fv_nom (n : n_sexp) : atoms :=
  match n with
  | n_var x => {{x}}
  | n_abs x n => remove x (fv_nom n)
  | n_app t1 t2 => fv_nom t1 `union` fv_nom t2
  | n_sub t1 x t2 => (remove x (fv_nom t1)) `union` fv_nom t2
  end.

Lemma fv_nom_dec: forall t x, x `in` fv_nom t \/ x `notin` fv_nom t.
Proof.
  induction t.
  - intros x'. pose proof eq_dec. specialize (H x x'). destruct H.
    + subst. left. simpl. auto.
    + right. simpl. auto.
  - intro x'. simpl. pose proof eq_dec. specialize (H x x'). destruct H.
    + subst. specialize (IHt x'). destruct IHt; default_simp.
    + specialize (IHt x'). destruct IHt.
      * left. default_simp.
      * right. default_simp.
  - intro x. simpl. specialize (IHt1 x). destruct IHt1.
    + left. default_simp.
    + specialize (IHt2 x). destruct IHt2.
      * left. default_simp.
      * right. default_simp.
  - intro x'. simpl. pose proof eq_dec. specialize (H x x'). destruct H.
    + subst. specialize (IHt1 x'). destruct IHt1.
      * specialize (IHt2 x'). destruct IHt2.
        ** left. default_simp.
        ** right. default_simp.
      * specialize (IHt2 x'). destruct IHt2.
        ** left. default_simp.
        ** right. default_simp.
    + specialize (IHt1 x'). destruct IHt1.
      * specialize (IHt2 x'). destruct IHt2.
        ** left. default_simp.
        ** left. default_simp.
      * specialize (IHt2 x'). destruct IHt2.
        ** left. default_simp.
        ** right. default_simp.
Qed.
      
Lemma fv_nom_app: forall t1 t2 x, x `notin` fv_nom (n_app t1 t2) -> x `notin` fv_nom t1  /\ x `notin` fv_nom t2.
Proof.
  intros t1 t2 x H. simpl in H. split.
  - apply notin_union_1 in H. assumption.
  - apply notin_union_2 in H. assumption.
Qed.  
  
Definition swap_var (x:atom) (y:atom) (z:atom) :=
  if (z == x) then y else if (z == y) then x else z.

Lemma swap_var_id: forall x y, (swap_var x x y = y).
Proof.
  intros. unfold swap_var. case (y == x); intros; subst; reflexivity.
Qed.

Fixpoint swap (x:atom) (y:atom) (t:n_sexp) : n_sexp :=
  match t with
  | n_var z     => n_var (swap_var x y z)
  | n_abs z t1  => n_abs (swap_var x y z) (swap x y t1)
  | n_app t1 t2 => n_app (swap x y t1) (swap x y t2)
  | n_sub t1 z t2 => n_sub (swap x y t1) (swap_var x y z) (swap x y t2)
  end.

Lemma swap_id : forall t x,
    swap x x t = t.
Proof.
  induction t; simpl; unfold swap_var; default_simp.
Qed.

Lemma swap_size_eq : forall x y t,
    size (swap x y t) = size t.
Proof.
  induction t; simpl; auto.
Qed.

Hint Rewrite swap_size_eq.

Lemma swap_symmetric : forall t x y,
    swap x y t = swap y x t.
Proof.
  induction t.
  - intros x' y. simpl. unfold swap_var. default_simp.
  - intros x' y; simpl. unfold swap_var. default_simp.
  - intros x y; simpl. rewrite IHt1. rewrite IHt2; reflexivity.
  - intros. simpl. unfold swap_var. default_simp.
Qed.

Lemma swap_symmetric_2: forall x y x' y' t,
    x <> x' -> y <> y' -> x <> y'-> y <> x' -> swap x y (swap x' y' t) = swap x' y' (swap x y t). 
Proof.
  intros. induction t; simpl in *; unfold swap_var in *; default_simp.
Qed.

Lemma swap_involutive : forall t x y,
    swap x y (swap x y t) = t.
Proof.
 induction t; intros; simpl; unfold swap_var; default_simp.
Qed.

(** Equivariance is the property that all functions and 
    relations are preserved under swapping. *)

Lemma swap_var_equivariance : forall v x y z w,
    swap_var x y (swap_var z w v) =
    swap_var (swap_var x y z) (swap_var x y w) (swap_var x y v).
Proof.
  intros; unfold swap_var; case(v == z); case (w == x); default_simp.
Qed.

Lemma swap_equivariance : forall t x y z w,
    swap x y (swap z w t) = swap (swap_var x y z) (swap_var x y w) (swap x y t).
Proof.
  induction t.
  - intros. unfold swap_var. case (z == x0).
    -- case (w == x0).
       --- intros. rewrite swap_id. rewrite e; rewrite e0.
           rewrite swap_id. reflexivity.
       --- intros. case (w == y).
           + intros. rewrite swap_symmetric. rewrite e; rewrite e0.
             reflexivity.
           + intros. unfold swap. unfold swap_var. default_simp.
    -- unfold swap. unfold swap_var. intros. default_simp.
  - intros. simpl. rewrite IHt. unfold swap_var.
    case (x == z).
    -- case (w == x0); default_simp.
    -- case (w == x0).
       --- default_simp.
       --- intros. case (x == w); intros; case (z == x0); default_simp.
  - intros. simpl. rewrite IHt1. rewrite IHt2. reflexivity.
  - intros. simpl. rewrite IHt1. rewrite IHt2. unfold swap_var.
    default_simp.    
Qed.

Lemma fv_nom_swap : forall z y t,
  z `notin` fv_nom t ->
  y `notin` fv_nom (swap y z t).
Proof.
  induction t; intros; simpl; unfold swap_var; default_simp.
Qed.

Lemma n_sexp_induction :
 forall P : n_sexp -> Prop,
 (forall x, P (n_var x)) ->
 (forall t1 z,
    (forall t2 x y, size t2 = size t1 ->
    P (swap x y t2)) -> P (n_abs z t1)) ->
 (forall t1 t2, P t1 -> P t2 -> P (n_app t1 t2)) ->
 (forall t1 t3 z, P t3 -> 
    (forall t2 x y, size t2 = size t1 ->
    P (swap x y t2)) -> P (n_sub t1 z t3)) -> 
 (forall t, P t).
Proof.
  intros P Hvar Habs Happ Hsub t.
  remember (size t) as n.
  generalize dependent t.
  induction n using strong_induction.
  intro t; case t.
  - intros x Hsize.
    apply Hvar.
  - intros x t' Hsize.
    apply Habs.
    intros t'' x1 x2 Hsize'.
    apply H with (size t'').
    + rewrite Hsize'.
      rewrite Hsize.
      simpl.
      apply Nat.lt_succ_diag_r.
    + symmetry.
      apply swap_size_eq.
  - intros. apply Happ.
    + apply H with ((size t1)).
      ++ simpl in Heqn. rewrite Heqn.
         apply le_lt_n_Sm.
         apply le_plus_l.
      ++ reflexivity.
    + apply H with ((size t2)).
      ++ simpl in Heqn. rewrite Heqn.
          apply le_lt_n_Sm.
         apply le_plus_r.
      ++ reflexivity.
  - intros. apply Hsub.
    + apply H with ((size t2)).
      ++ simpl in Heqn. rewrite Heqn.
          apply le_lt_n_Sm.
         apply le_plus_r.
      ++ reflexivity.
    + intros. apply H with ((size (swap x0 y t0))).
      ++ rewrite swap_size_eq. rewrite H0.
         simpl in Heqn. rewrite Heqn.
         apply le_lt_n_Sm.
         apply le_plus_l.
      ++ reflexivity.
Qed. 

(** printing < %\ensuremath{<}% *)
Lemma n_sexp_size_induction: forall P: n_sexp -> Prop,
    (forall x, (forall y, size y < size x -> P y) -> P x) -> forall z, P z.
Proof.
  intros. remember (size z) as n. generalize dependent z. induction n using strong_induction;intros.
  case z eqn:H';intros.
  - apply H. intros. destruct y;default_simp.
  - apply H. intros. apply (H0 (size y)).
    -- rewrite Heqn. assumption.
    -- reflexivity.
  - apply H. intros. apply (H0 (size y)).
    -- rewrite Heqn. assumption.
    -- reflexivity.
  - apply H. intros. apply (H0 (size y)).
    -- rewrite Heqn. assumption.
    -- reflexivity.
Qed. 

(** We define the "alpha-equivalence" relation that declares when two nominal terms are equivalent (up to renaming of bound variables). Note the two different rules for [n_abs] and [n_sub]: either the binders are the same and we can directly compare the bodies, or the binders differ, but we can swap one side to make it look like the other.  *)

Inductive aeq : n_sexp -> n_sexp -> Prop :=
 | aeq_var : forall x,
     aeq (n_var x) (n_var x)
 | aeq_abs_same : forall x t1 t2,
     aeq t1 t2 -> aeq (n_abs x t1) (n_abs x t2)
 | aeq_abs_diff : forall x y t1 t2,
     x <> y -> x `notin` fv_nom t2 ->
     aeq t1 (swap y x t2) ->
     aeq (n_abs x t1) (n_abs y t2)
 | aeq_app : forall t1 t2 t1' t2',
     aeq t1 t1' -> aeq t2 t2' ->
     aeq (n_app t1 t2) (n_app t1' t2')
 | aeq_sub_same : forall t1 t2 t1' t2' x,
     aeq t1 t1' -> aeq t2 t2' ->
     aeq (n_sub t1 x t2) (n_sub t1' x t2')
 | aeq_sub_diff : forall t1 t2 t1' t2' x y,
     aeq t2 t2' -> x <> y -> x `notin` fv_nom t1' ->
     aeq t1 (swap y x t1') ->
     aeq (n_sub t1 x t2) (n_sub t1' y t2').

Hint Constructors aeq.
Notation "t =a u" := (aeq t u) (at level 60).

Example aeq1 : forall x y, x <> y -> aeq (n_abs x (n_var x)) (n_abs y (n_var y)).
Proof.
  intros.
  eapply aeq_abs_diff; auto.
  simpl; unfold swap_var; default_simp.
Qed.

Lemma aeq_var_2 : forall x y, aeq (n_var x) (n_var y) -> x = y.
Proof.
  intros. inversion H; subst. reflexivity.
Qed.

Lemma remove_singleton_empty: forall x,
    remove x (singleton x) [=] empty.
Proof.
  intros. rewrite AtomSetProperties.singleton_equal_add.
  rewrite AtomSetProperties.remove_add.
  - reflexivity.
  - apply notin_empty_1.
Qed.

Lemma remove_singleton: forall t1 t2,
    remove t1 (singleton t1) [=] remove t2 (singleton t2).
Proof.
  intros. repeat rewrite remove_singleton_empty. reflexivity.
Qed.

Lemma notin_singleton_is_false: forall x,
    x `notin` (singleton x) -> False.
Proof.
  intros. intros. apply notin_singleton_1 in H. contradiction.
Qed.

Lemma double_remove: forall x s,
           remove x (remove x s) [=] remove x s.
Proof.
  intros. pose proof AtomSetProperties.remove_equal.
  assert (x `notin` remove x s). {
    apply AtomSetImpl.remove_1. reflexivity.
  }
  specialize (H (remove x s) x). apply H in H0. assumption.
Qed.

Lemma remove_symmetric: forall x y s,
           remove x (remove y s) [=] remove y (remove x s).
Proof.
  intros. split.
  - intros. case (a == x); intros; case (a == y); intros; subst.
    apply AtomSetImpl.remove_3 in H.
    -- rewrite double_remove. assumption.
    -- apply remove_iff in H. inversion H. contradiction.
    -- apply remove_iff in H. inversion H.
       apply remove_iff in H0. inversion H0.
       contradiction.
    -- pose proof H. apply AtomSetImpl.remove_3 in H.
       apply AtomSetImpl.remove_2.
       --- apply aux_not_equal; assumption.
       --- apply AtomSetImpl.remove_2.
           + apply aux_not_equal; assumption.
           + apply AtomSetImpl.remove_3 in H. assumption.
  - intros. case (a == x); intros; case (a == y); intros; subst.
    apply AtomSetImpl.remove_3 in H.
    -- rewrite double_remove. assumption.
    -- apply remove_iff in H. inversion H.
       apply remove_iff in H0. inversion H0.
       contradiction.
    -- apply remove_iff in H. inversion H. contradiction.
    -- pose proof H. apply AtomSetImpl.remove_3 in H.
       apply AtomSetImpl.remove_2.
       --- apply aux_not_equal; assumption.
       --- apply AtomSetImpl.remove_2.
           + apply aux_not_equal; assumption.
           + apply AtomSetImpl.remove_3 in H. assumption.
Qed.

Lemma remove_empty: forall x,
    remove x empty [=] empty.
Proof.
  intros. pose proof notin_empty. specialize (H x).
  apply AtomSetProperties.remove_equal in H.
  assumption.
Qed.

Require Export Metalib.LibLNgen.

Lemma swap_remove_reduction: forall x y t,
    remove x (remove y (fv_nom (swap y x t))) [=] remove x (remove y (fv_nom t)).
Proof.
  induction t.
  - rewrite remove_symmetric. simpl. unfold swap_var. default_simp.
    -- repeat rewrite remove_singleton_empty.
       repeat rewrite remove_empty. reflexivity.
    -- rewrite remove_symmetric. rewrite remove_singleton_empty.
       rewrite remove_symmetric. rewrite remove_singleton_empty.
       repeat rewrite remove_empty. reflexivity.
    -- rewrite remove_symmetric. reflexivity.
  - simpl. unfold swap_var. default_simp.
    -- rewrite double_remove. rewrite remove_symmetric.
       rewrite double_remove. rewrite remove_symmetric.
       assumption.
    -- rewrite double_remove. symmetry.
       rewrite remove_symmetric. rewrite double_remove.
       rewrite remove_symmetric. symmetry.
       assumption.
    -- assert (remove y (remove x0 (fv_nom (swap y x t))) [=] remove x0 (remove y (fv_nom (swap y x t)))). {
         rewrite remove_symmetric. reflexivity.
       }
       assert (remove y (remove x0 (fv_nom  t)) [=] remove x0 (remove y (fv_nom t))). {
         rewrite remove_symmetric. reflexivity.
       }
       rewrite H; rewrite H0. rewrite remove_symmetric.
       symmetry. rewrite remove_symmetric. rewrite IHt.
       reflexivity.       
  - simpl. repeat rewrite remove_union_distrib.
    apply Equal_union_compat.
    -- assumption.
    -- assumption.
  - simpl. unfold swap_var. default_simp.
    -- repeat rewrite remove_union_distrib.
       apply Equal_union_compat.
       --- rewrite remove_symmetric. rewrite double_remove.
           rewrite double_remove. rewrite remove_symmetric.
           assumption.
       --- assumption.
    -- repeat rewrite remove_union_distrib.
       apply Equal_union_compat.
       --- rewrite double_remove. symmetry.
           rewrite remove_symmetric.
           rewrite double_remove. rewrite remove_symmetric.
           symmetry. assumption.
       --- assumption.
    -- repeat rewrite remove_union_distrib.
       apply Equal_union_compat.
       --- assert (remove y (remove x0 (fv_nom (swap y x t1))) [=] remove x0 (remove y (fv_nom (swap y x t1)))). {
         rewrite remove_symmetric. reflexivity.
           }
           assert (remove y (remove x0 (fv_nom  t1)) [=] remove x0 (remove y (fv_nom t1))). {
         rewrite remove_symmetric. reflexivity.
           }
           rewrite H; rewrite H0.
           rewrite remove_symmetric. symmetry.
           rewrite remove_symmetric. symmetry.
           rewrite IHt1. reflexivity.
       --- assumption.
Qed.

Lemma diff_remove: forall x y s,
    x <> y -> x `notin` s -> x `notin` remove y s.
Proof.
  intros. apply notin_remove_2. assumption.
Qed.

Lemma remove_fv_swap: forall x y t, x `notin` fv_nom t -> remove x (fv_nom (swap y x t)) [=] remove y (fv_nom t).
Proof.
  intros x y t. induction t.
  - intro. simpl. unfold swap_var. case (x0 == y); intros; subst.
    -- simpl. pose proof remove_singleton.
       specialize (H0 x y); assumption.
    -- case (x0 == x); intros; subst.
       --- simpl in H. apply notin_singleton_is_false in H.
           inversion H.
       --- apply aux_not_equal in n; apply aux_not_equal in n.
           apply notin_singleton_2 in n;
           apply notin_singleton_2 in n0;
           apply AtomSetProperties.remove_equal in n;
           apply AtomSetProperties.remove_equal in n0.
           rewrite n; rewrite n0; reflexivity.
  - intros; simpl. unfold swap_var. case (x0 == y); intros; subst.
    -- case (x == y); intros; subst.
       --- rewrite swap_id. reflexivity.
       --- rewrite double_remove. symmetry; rewrite double_remove.
           symmetry; apply IHt. simpl in H.
           apply notin_remove_1 in H. inversion H.
           + symmetry in H0; contradiction.
           + assumption.
    -- case (x0 == x); intros; subst.
       --- rewrite swap_remove_reduction. rewrite remove_symmetric.
           reflexivity.
       --- rewrite remove_symmetric. symmetry.
           rewrite remove_symmetric. symmetry.
           apply AtomSetProperties.Equal_remove.
           apply IHt. simpl in H. apply notin_remove_1 in H.
           inversion H.
           + contradiction.
           + assumption.           
  - intros. simpl. simpl in H. pose proof H.

    apply notin_union_1 in H; apply notin_union_2 in H0.
    apply IHt1 in H; apply IHt2 in H0.
    pose proof remove_union_distrib. pose proof H1.
    specialize (H1 (fv_nom (swap y x t1)) (fv_nom (swap y x t2)) x).
    specialize (H2 (fv_nom t1) (fv_nom t2) y).
    rewrite H in H1; rewrite H0 in H1.
    rewrite H1; rewrite H2; reflexivity.
  - intros. simpl. pose proof remove_union_distrib. pose proof H0.
    specialize (H0 (remove (swap_var y x x0) (fv_nom (swap y x t1))) (fv_nom (swap y x t2)) x).
    specialize (H1 (remove x0 (fv_nom t1)) (fv_nom t2) y).
    unfold swap_var. case (x0 == y); intros; subst.
    -- unfold swap_var in H0. case (y == y) in H0.
       --- simpl in H. rewrite double_remove in H0.
           rewrite double_remove in H1. pose proof H.
           apply notin_union_1 in H; apply notin_union_2 in H2.
           apply IHt2 in H2. case (x == y); intros; subst.
           + rewrite swap_id; rewrite swap_id. reflexivity.
           + apply notin_remove_1 in H. inversion H; subst.
             ++ contradiction.
             ++ pose proof H3 as Hnotin. apply IHt1 in H3.
                rewrite H3. pose proof remove_union_distrib.
                pose proof H4.
                specialize (H4 (remove y (fv_nom t1)) (fv_nom (swap y x t2)) x).
                specialize (H5 (remove y (fv_nom t1)) (fv_nom t2) y).
                apply diff_remove with x y (fv_nom t1) in n.
                +++ rewrite double_remove in H5. Search "remove".
                    apply AtomSetProperties.remove_equal in n.
                    rewrite H2 in H4.
                    rewrite n in H4; rewrite H4; rewrite H5.
                      reflexivity.
                +++ assumption.
       --- contradiction.
  -- case (x0 == x); intros; subst.
     --- unfold swap_var in H0. case (x == y) in H0; intros.
         + contradiction.
         + case (x == x) in H0; intros.
           ++ simpl in H. pose proof H. apply notin_union_1 in H.
              apply notin_union_2 in H2. apply IHt2 in H2.
              rewrite H2 in H0. symmetry. Search "remove_union".
              rewrite remove_union_distrib. symmetry.
              rewrite remove_symmetric.
              rewrite swap_remove_reduction in H0. assumption.
           ++ contradiction.
     --- simpl in H. pose proof H. apply notin_union_1 in H.
         apply notin_remove_1 in H. inversion H; subst.
         + contradiction.
         + apply notin_union_2 in H2.
           apply IHt1 in H3; apply IHt2 in H2.
           unfold swap_var in H0. default_simp.
           rewrite H0. rewrite remove_symmetric.
           rewrite H1; rewrite H2; rewrite H3.
           rewrite remove_symmetric. reflexivity.        
Qed.

Lemma aeq_fv_nom:forall t1 t2, aeq t1 t2 -> fv_nom t1 [=] fv_nom t2.
Proof.
  intros. induction H.
  - reflexivity.
  - simpl. rewrite IHaeq. reflexivity.
  - simpl. inversion H1; subst; rewrite IHaeq; apply remove_fv_swap; assumption.
  - simpl. rewrite IHaeq1; rewrite IHaeq2. reflexivity.
  - simpl. rewrite IHaeq1; rewrite IHaeq2. reflexivity.
  - simpl. pose proof remove_fv_swap.
    specialize (H3 x y t1'). apply H3 in H1.
    inversion H2; subst; rewrite IHaeq1; rewrite IHaeq2; rewrite H1; reflexivity.
Qed.  

Lemma fv_nom_swap_2 : forall z y t,
  z `notin` fv_nom (swap y z t) -> y `notin` fv_nom t.
Proof.
  intros. induction t; simpl in *; unfold swap_var in H; default_simp.
Qed.

Lemma fv_nom_swap_remove: forall t x y y0, x <> y ->  x <> y0 -> x `notin` fv_nom (swap y0 y t) -> x `notin` fv_nom t.
Proof.
  intros. induction t; simpl in *; unfold swap_var in *; default_simp.
Qed.

Lemma shuffle_swap : forall w y n z,
    w <> z -> y <> z ->
    (swap w y (swap y z n)) = (swap w z (swap w y n)).
Proof.
  induction n; intros; simpl; unfold swap_var; default_simp.
Qed.

Lemma aeq_swap2: forall t1 t2 x y, aeq (swap x y t1) (swap x y t2) -> aeq t1 t2.
Proof.
  induction t1.
  - intros. induction t2.
    -- simpl in H. unfold swap_var in H. default_simp.
    -- simpl in H. inversion H.
    -- simpl in H. inversion H.
    -- simpl in H. inversion H.
  - intros. induction t2.
    -- simpl in H. inversion H.
    -- simpl in H. inversion H.
       --- unfold swap_var in *. default_simp.
           + specialize (IHt1 t2 x0 y). apply aeq_abs_same.
             apply IHt1. assumption.
           + specialize (IHt1 t2 x0 y). apply aeq_abs_same.
             apply IHt1. assumption.
           + specialize (IHt1 t2 x0 y). apply aeq_abs_same.
             apply IHt1. assumption.
       --- unfold swap_var in *. default_simp.
           + apply aeq_abs_diff.
             ++ assumption.
             ++ apply fv_nom_swap_2 with x0.
                rewrite swap_symmetric; assumption.
             ++ specialize (IHt1 (swap x0 y t2) x0 y).
                apply IHt1.
                assert (swap x0 y (swap x0 y t2) = swap y x0 (swap x0 y t2)).
                rewrite swap_symmetric; reflexivity.
                rewrite H0. assumption.
           + apply aeq_abs_diff.
             ++ assumption.
             ++ apply fv_nom_swap_remove with x0 y.
                +++ assumption.
                +++ assumption.
                +++ rewrite swap_symmetric; assumption.
             ++ specialize (IHt1 (swap x0 x t2) x0 y).
                apply IHt1.
                assert (swap x0 y (swap x0 x t2) = swap y x0 (swap x0 x t2)).
                rewrite swap_symmetric; reflexivity.
                rewrite H0. rewrite shuffle_swap.
                +++ assert (swap x0 y t2 = swap y x0 t2).
                    rewrite swap_symmetric; reflexivity.
                    rewrite <- H1. assumption.
                +++ apply aux_not_equal; assumption.
                +++ apply aux_not_equal; assumption.
           + apply aeq_abs_diff.
             ++ apply aux_not_equal; assumption.
             ++ apply fv_nom_swap_2 with y. assumption.
             ++ specialize (IHt1 (swap y x0 t2) x0 y).
                apply IHt1.
                assert (swap y x0 t2 = swap x0 y t2).
                rewrite swap_symmetric; reflexivity.
                rewrite H0. assumption.
           + apply aeq_abs_diff.
             ++ assumption.
             ++ apply fv_nom_swap_remove with x0 y.
                +++ assumption.
                +++ assumption.
                +++ rewrite swap_symmetric; assumption.
             ++ specialize (IHt1 (swap y x t2) x0 y).
                apply IHt1. rewrite shuffle_swap.
                +++ assumption.
                +++ apply aux_not_equal; assumption.
                +++ apply aux_not_equal; assumption.
           + apply aeq_abs_diff.
             ++ apply aux_not_equal. assumption.
             ++ apply fv_nom_swap_2 with y. assumption.
             ++ specialize (IHt1 (swap x1 x0 t2) x0 y).
                apply IHt1.
                assert (swap x0 y (swap x1 x0 t2) = swap y x0 (swap x1 x0 t2)).
                rewrite swap_symmetric; reflexivity.
                rewrite H0.
                assert (swap x1 x0 t2 = swap x0 x1 t2).
                rewrite swap_symmetric; reflexivity.
                rewrite H1. rewrite shuffle_swap.
                +++ assert (swap x1 y (swap y x0 t2) = swap y x1 (swap y x0 t2)).
                    rewrite swap_symmetric; reflexivity.
                    rewrite <- H2.
                    assert (swap y x0 t2 = swap x0 y t2).
                    rewrite swap_symmetric; reflexivity.
                    rewrite H3. assumption.
                +++ apply aux_not_equal; assumption.
                +++ apply aux_not_equal; assumption.
           + apply aeq_abs_diff.
             ++ apply aux_not_equal. assumption.
             ++ apply fv_nom_swap_2 with x0.
                rewrite swap_symmetric; assumption.
             ++ specialize (IHt1 (swap x1 y t2) x0 y).
                apply IHt1.
                assert (swap x1 y t2 = swap y x1 t2).
                rewrite swap_symmetric; reflexivity.
                rewrite H0. rewrite shuffle_swap.
                +++ assert (swap x0 x1 (swap x0 y t2) = swap x1 x0 (swap x0 y t2)).
                    rewrite swap_symmetric; reflexivity.
                    rewrite H1. assumption.
                +++ apply aux_not_equal; assumption.
                +++ apply aux_not_equal; assumption.
           + apply aeq_abs_diff.
             ++ assumption.
             ++ apply fv_nom_swap_remove with x0 y.
                +++ assumption.
                +++ assumption.
                +++ rewrite swap_symmetric; assumption.
             ++ specialize (IHt1 (swap x1 x t2) x0 y).
                apply IHt1. rewrite swap_symmetric_2.
                +++ assumption.
                +++ apply aux_not_equal; assumption.
                +++ apply aux_not_equal; assumption.
                +++ apply aux_not_equal; assumption.
                +++ apply aux_not_equal; assumption.
    -- simpl in H. inversion H.
    -- simpl in H. inversion H.
  - intros. induction t2.
    -- simpl in H. inversion H.
    -- simpl in H. inversion H.
    -- simpl in H. inversion H.
       apply aeq_app.
       --- apply IHt1_1 with x y. assumption.
       --- apply IHt1_2 with x y. assumption.
    -- simpl in H. inversion H.
  - intros. induction t2.
    -- simpl in H. inversion H.
    -- simpl in H. inversion H.
    -- simpl in H. inversion H.
    -- simpl in H. inversion H.
       --- simpl in *; unfold swap_var in *. default_simp.
           + apply aeq_sub_same.
             ++ apply IHt1_1 with x0 y. assumption.
             ++ apply IHt1_2 with x0 y. assumption.
           + apply aeq_sub_same.
             ++ apply IHt1_1 with x0 y. assumption.
             ++ apply IHt1_2 with x0 y. assumption.
           + apply aeq_sub_same.
             ++ apply IHt1_1 with x0 y. assumption.
             ++ apply IHt1_2 with x0 y. assumption.
       --- simpl in *; unfold swap_var in *. default_simp.
           + apply aeq_sub_diff.
             ++ apply IHt1_2 with x0 y. assumption.
             ++ assumption.
             ++ apply fv_nom_swap_2 with x0.
                rewrite swap_symmetric; assumption.
             ++ apply IHt1_1 with x0 y.
                assert (swap y x0 (swap x0 y t2_1) = swap x0 y (swap x0 y t2_1)).
                rewrite swap_symmetric; reflexivity.
                rewrite <- H0. assumption.
           + apply aeq_sub_diff.
             ++ apply IHt1_2 with x0 y. assumption.
             ++ assumption.
             ++ apply fv_nom_swap_remove with x0 y.
                +++ assumption.
                +++ assumption.
                +++ rewrite swap_symmetric; assumption.
             ++ apply IHt1_1 with x0 y.
                assert (swap x0 y (swap x0 x t2_1) = swap y x0 (swap x0 x t2_1)).
                rewrite swap_symmetric; reflexivity.
                rewrite H0. rewrite shuffle_swap.
                +++ assert (swap y x0 t2_1 = swap x0 y t2_1).
                    rewrite swap_symmetric; reflexivity.
                    rewrite H1. assumption.
                +++ apply aux_not_equal; assumption.
                +++ apply aux_not_equal; assumption.
           + apply aeq_sub_diff.
             ++ apply IHt1_2 with x0 y. assumption.
             ++ apply aux_not_equal; assumption.
             ++ apply fv_nom_swap_2 with y. assumption.
             ++ apply IHt1_1 with x0 y.
                assert (swap y x0 t2_1 = swap x0 y t2_1).
                rewrite swap_symmetric; reflexivity.
                rewrite H0. assumption.
           + apply aeq_sub_diff.
             ++ apply IHt1_2 with x0 y. assumption.
             ++ assumption.
             ++ apply fv_nom_swap_remove with x0 y.
                +++ assumption.
                +++ assumption.
                +++ rewrite swap_symmetric; assumption.
             ++ specialize (IHt1_1 (swap y x t2_1) x0 y).
                apply IHt1_1. rewrite shuffle_swap.
                +++ assumption.
                +++ apply aux_not_equal; assumption.
                +++ apply aux_not_equal; assumption.
           + apply aeq_sub_diff.
             ++ apply IHt1_2 with x0 y. assumption.
             ++ apply aux_not_equal. assumption.
             ++ apply fv_nom_swap_2 with y. assumption.
             ++ specialize (IHt1_1 (swap x1 x0 t2_1) x0 y).
                apply IHt1_1.
                assert (swap x0 y (swap x1 x0 t2_1) = swap y x0 (swap x1 x0 t2_1)).
                rewrite swap_symmetric; reflexivity.
                rewrite H0.
                assert (swap x1 x0 t2_1 = swap x0 x1 t2_1).
                rewrite swap_symmetric; reflexivity.
                rewrite H1. rewrite shuffle_swap.
                +++ assert (swap x1 y (swap y x0 t2_1) = swap y x1 (swap y x0 t2_1)).
                    rewrite swap_symmetric; reflexivity.
                    rewrite <- H2.
                    assert (swap y x0 t2_1 = swap x0 y t2_1).
                    rewrite swap_symmetric; reflexivity.
                    rewrite H3. assumption.
                +++ apply aux_not_equal; assumption.
                +++ apply aux_not_equal; assumption.
           + apply aeq_sub_diff.
             ++ apply IHt1_2 with x0 y. assumption.
             ++ apply aux_not_equal. assumption.
             ++ apply fv_nom_swap_2 with x0.
                rewrite swap_symmetric; assumption.
             ++ specialize (IHt1_1 (swap x1 y t2_1) x0 y).
                apply IHt1_1.
                assert (swap x1 y t2_1 = swap y x1 t2_1).
                rewrite swap_symmetric; reflexivity.
                rewrite H0. rewrite shuffle_swap.
                +++ assert (swap x0 x1 (swap x0 y t2_1) = swap x1 x0 (swap x0 y t2_1)).
                    rewrite swap_symmetric; reflexivity.
                    rewrite H1. assumption.
                +++ apply aux_not_equal; assumption.
                +++ apply aux_not_equal; assumption.
           + apply aeq_sub_diff.
             ++ apply IHt1_2 with x0 y. assumption.
             ++ assumption.
             ++ apply fv_nom_swap_remove with x0 y.
                +++ assumption.
                +++ assumption.
                +++ rewrite swap_symmetric; assumption.
             ++ specialize (IHt1_1 (swap x1 x t2_1) x0 y).
                apply IHt1_1. rewrite swap_symmetric_2.
                +++ assumption.
                +++ apply aux_not_equal; assumption.
                +++ apply aux_not_equal; assumption.
                +++ apply aux_not_equal; assumption.
                +++ apply aux_not_equal; assumption.
Qed.

Lemma fv_nom_remove_swap: forall t x y y0, x <> y ->  x <> y0 -> x `notin` fv_nom t -> x `notin` fv_nom (swap y0 y t).
  Proof.
    induction t; simpl in *; unfold swap_var; default_simp.
Qed.

Lemma aeq_size: forall t1 t2, aeq t1 t2 -> size t1 = size t2.
Proof.
  induction 1.
  - reflexivity.
  - simpl. rewrite IHaeq; reflexivity.
  - simpl. rewrite IHaeq. rewrite swap_size_eq. reflexivity.
  - simpl. rewrite IHaeq1. rewrite IHaeq2. reflexivity.
  - simpl. rewrite IHaeq1. rewrite IHaeq2. reflexivity.
  - simpl. rewrite IHaeq1. rewrite IHaeq2. rewrite swap_size_eq. reflexivity.
Qed.

Lemma aeq_refl : forall n, aeq n n.
Proof.
  induction n; auto.
Qed.

Lemma aeq_swap1: forall t1 t2 x y, aeq t1 t2 -> aeq (swap x y t1) (swap x y t2).
Proof.
  intros. induction H.
  - apply aeq_refl.
  - simpl. unfold swap_var. case (x0 == x); intros; subst.
    -- apply aeq_abs_same. assumption.
    -- case (x0 == y); intros; subst.
       --- apply aeq_abs_same. assumption.
       --- apply aeq_abs_same. assumption.
  - simpl. unfold  swap_var. default_simp.
    -- apply aeq_abs_diff.
       + assumption.
       + apply fv_nom_swap with x y t2 in H0.
         rewrite swap_symmetric. assumption.
       + assert (swap x y t2 = swap y x t2).
         rewrite swap_symmetric; reflexivity.
         rewrite H2. assumption.
    -- apply aeq_abs_diff.
       + apply aux_not_equal. assumption.
       + apply fv_nom_swap with x y t2 in H0.
         rewrite swap_symmetric. assumption.
       + case (x == y); intros; subst.
         ++ repeat rewrite swap_id. repeat rewrite swap_id in IHaeq.
            assumption.
         ++ assert (swap x y t2 = swap y x t2).
            rewrite swap_symmetric; reflexivity.
            rewrite H2. pose proof shuffle_swap.
            pose proof H3.
            specialize (H3 y0 y t2 x).
            rewrite H3.
            +++ specialize (H4 x y0 t2 y).
                assert (swap y0 x (swap y0 y t2) = swap x y0 (swap y0 y t2)). rewrite swap_symmetric; reflexivity.
                rewrite H5.
                rewrite H4.
                * assert (swap y0 x t2 = swap x y0 t2).
                  apply swap_symmetric; reflexivity.
                  rewrite <- H6. assumption.
                * assumption.
                * assumption.
            +++ assumption.       
            +++ apply aux_not_equal. assumption.
    -- apply aeq_abs_diff.
       + apply aux_not_equal; assumption.
       + apply fv_nom_swap with y x t2 in H0. assumption.
       + assert (swap y x (swap x y t2) = swap x y (swap x y t2)).
         rewrite swap_symmetric; reflexivity.
         rewrite H2. assumption. 
    -- apply aeq_abs_diff.
       + apply aux_not_equal; assumption.
       + apply fv_nom_swap. assumption.
       + rewrite shuffle_swap.
         ++ assert (swap y0 y (swap y0 x t2) = swap y y0 (swap y0 x t2)). rewrite swap_symmetric; reflexivity.
            rewrite H2.
            rewrite shuffle_swap.
            +++ assert (swap y x (swap y y0 t2) = swap x y (swap y y0 t2)). rewrite swap_symmetric; reflexivity.
                assert ((swap y y0 t2) = (swap y0 y t2)). rewrite swap_symmetric; reflexivity.
                rewrite H3; rewrite H4.
                assumption.
            +++ assumption.
            +++ assumption.
         ++ assumption.
         ++ apply aux_not_equal; assumption.
    -- apply aeq_abs_diff.
       + assumption.
       + apply fv_nom_remove_swap; assumption.
       + case (x == y); intros; subst.
         ++ repeat rewrite swap_id; repeat rewrite swap_id in IHaeq.
            assumption.
         ++ assert (swap y x0 (swap x y t2) = swap x0 y (swap x y t2)).
            rewrite swap_symmetric; reflexivity.
            rewrite H2.
            assert (swap x y t2 = swap y x t2).
            rewrite swap_symmetric; reflexivity.
            rewrite H3. rewrite shuffle_swap.
            +++ assert (swap x0 x (swap x0 y t2) = swap x x0 (swap x0 y t2)). rewrite swap_symmetric; reflexivity.
            rewrite H4. rewrite shuffle_swap.
                * assumption.
                * assumption.
                * assumption.
            +++ assumption.
            +++ apply aux_not_equal; assumption.        
    -- apply aeq_abs_diff.
       + assumption.
       + apply fv_nom_remove_swap; assumption.
       + assert (swap x x0 (swap x y t2) = swap x0 x (swap x y t2)).
         rewrite swap_symmetric; reflexivity.
         rewrite H2. rewrite shuffle_swap.
         ++ assert (swap x0 y (swap x0 x t2) = swap y x0 (swap x0 x t2)).
            rewrite swap_symmetric; reflexivity.
            rewrite H3; rewrite shuffle_swap.
            +++ assert (swap y x (swap y x0 t2) = swap x y (swap y x0 t2)).
                rewrite swap_symmetric; reflexivity.
                rewrite H4.
                assumption.
            +++ assumption.
            +++ assumption.
         ++ assumption.
         ++ apply aux_not_equal; assumption.     
    -- apply aeq_abs_diff.
       + assumption.
       + apply fv_nom_remove_swap.
         ++ assumption.
         ++ assumption.
         ++ assumption.
       + assert (swap x0 y0 (swap x y t2) = swap x y (swap x0 y0 t2)). {
           rewrite swap_equivariance. unfold swap_var. default_simp.
         }
         assert (swap y0 x0 t2 = swap x0 y0 t2).
         rewrite swap_symmetric; reflexivity.
         assert ((swap y0 x0 (swap x y t2)) = swap x0 y0 (swap x y t2)).
         rewrite swap_symmetric; reflexivity.
         rewrite H3 in IHaeq. rewrite H4.
         rewrite H2. assumption.
  - simpl. apply aeq_app.
    -- assumption.
    -- assumption.
  - simpl. apply aeq_sub_same.
    -- assumption.
    -- assumption.
  - simpl. unfold swap_var. default_simp.
    -- apply aeq_sub_diff.
       --- assumption.
       --- assumption.
       --- apply fv_nom_swap with x y t1' in H1.
           rewrite swap_symmetric. assumption.
       --- assert (swap y x t1' = swap x y t1').
           rewrite swap_symmetric; reflexivity.
           rewrite <- H3. assumption.
    -- apply aeq_sub_diff.
       --- assumption.
       --- apply aux_not_equal; assumption.
       --- rewrite swap_symmetric. apply fv_nom_swap. assumption.
       --- case (x == y); intros; subst.
           + repeat rewrite swap_id.
             repeat rewrite swap_id in IHaeq2. assumption.
           + assert (swap y x t1' = swap x y t1').
             rewrite swap_symmetric; reflexivity.
             rewrite <- H3. rewrite shuffle_swap.
             ++ assert (swap y0 x (swap y0 y t1') = swap x y0 (swap y0 y t1')). rewrite swap_symmetric; reflexivity.
                rewrite H4. rewrite shuffle_swap.
                +++ assert (swap x y0 t1' = swap y0 x t1').
                    rewrite swap_symmetric; reflexivity.
                    rewrite H5. assumption.
                +++ assumption.
                +++ assumption.
             ++ assumption.
             ++ apply aux_not_equal; assumption.
    -- apply aeq_sub_diff.
       --- assumption.
       --- apply aux_not_equal; assumption.
       --- apply fv_nom_swap. assumption.
       --- assert (swap y x (swap x y t1') = swap x y (swap x y t1')).
           rewrite swap_symmetric; reflexivity.
           rewrite H3. rewrite swap_involutive.
           rewrite swap_involutive in IHaeq2. assumption.
    -- apply aeq_sub_diff.
       --- assumption.
       --- apply aux_not_equal; assumption.
       --- apply fv_nom_swap. assumption.
       --- rewrite shuffle_swap.
           + assert (swap y0 y (swap y0 x t1') = swap y y0 (swap y0 x t1')). rewrite swap_symmetric; reflexivity.
             rewrite H3. rewrite shuffle_swap.
             ++ assert (swap y x (swap y y0 t1') = swap x y(swap y y0 t1')).
                rewrite swap_symmetric; reflexivity.
                rewrite H4.
                assert (swap y0 y t1' = swap y y0 t1').
                rewrite swap_symmetric; reflexivity.
                rewrite <- H5. assumption.
             ++ assumption.
             ++ assumption.
           + assumption.
           + apply aux_not_equal; assumption.
    -- apply aeq_sub_diff.
       --- assumption.
       --- assumption.
       --- apply fv_nom_remove_swap.
           + assumption.
           + assumption.
           + assumption.
       --- case (x == y); intros; subst.
           + repeat rewrite swap_id.
             repeat rewrite swap_id in IHaeq2.
             assumption.
           + assert (swap y x0 (swap x y t1') = swap x0 y (swap x y t1')).
             rewrite swap_symmetric; reflexivity.
             rewrite H3.
             assert (swap x y t1' = swap y x t1').
             rewrite swap_symmetric; reflexivity.
             rewrite H4. rewrite shuffle_swap.
             ++ assert (swap x0 x (swap x0 y t1') = swap x x0 (swap x0 y t1')). rewrite swap_symmetric; reflexivity.
                rewrite H5. rewrite shuffle_swap.
                * assumption.
                * assumption.
                * assumption.
             ++ assumption.
             ++ apply aux_not_equal; assumption.
    -- apply aeq_sub_diff.
       --- assumption.
       --- assumption.
       --- apply fv_nom_remove_swap.
           + assumption.
           + assumption.
           + assumption.
       --- assert (swap x x0 (swap x y t1') = swap x0 x (swap x y t1')).
           rewrite swap_symmetric; reflexivity.
           rewrite H3. rewrite shuffle_swap.
           + assert (swap x0 y (swap x0 x t1') = swap y x0 (swap x0 x t1')).
             rewrite swap_symmetric; reflexivity.
             rewrite H4; rewrite shuffle_swap.
             ++ assert (swap y x (swap y x0 t1') = swap x y (swap y x0 t1')).
                rewrite swap_symmetric; reflexivity.
                rewrite H5. assumption.
             ++ assumption.
             ++ assumption.
           + assumption.
           + apply aux_not_equal; assumption.
    -- apply aeq_sub_diff.
       --- assumption.
       --- assumption.
       --- apply fv_nom_remove_swap.
           + assumption.
           + assumption.
           + assumption.
       --- case (x == y); intros; subst.
           + repeat rewrite swap_id.
             repeat rewrite swap_id in IHaeq2.
             assumption.
           + assert (swap x0 y0 (swap x y t1') = swap x y (swap x0 y0 t1')). {
           rewrite swap_equivariance. unfold swap_var. default_simp.
         }
         assert (swap y0 x0 t1' = swap x0 y0 t1').
         rewrite swap_symmetric; reflexivity.
         assert ((swap y0 x0 (swap x y t1')) = swap x0 y0 (swap x y t1')).
         rewrite swap_symmetric; reflexivity.
         rewrite H4 in IHaeq2. rewrite H5.
         rewrite H3. assumption.
Qed.

Corollary aeq_swap: forall t1 t2 x y, aeq t1 t2 <-> aeq (swap x y t1) (swap x y t2).
Proof.
  intros. split.
  - apply aeq_swap1.
  - apply aeq_swap2.
Qed.

Lemma aeq_abs: forall t x y, y `notin` fv_nom t -> aeq (n_abs y (swap x y t)) (n_abs x t).
Proof.
  intros. case (x == y); intros; subst.
  - rewrite swap_id. apply aeq_refl.
  - apply aeq_abs_diff.
    -- apply aux_not_equal. assumption.
    -- assumption.
    -- apply aeq_refl.
Qed.

Lemma swap_reduction: forall t x y,
    x `notin` fv_nom t -> y `notin` fv_nom t -> aeq (swap x y t)  t.
Proof.
  induction t.
  - intros x' y H1 H2.
    simpl.
    unfold swap_var.
    destruct (x == x'); subst.
    + apply notin_singleton_is_false in H1.
      contradiction.
    + destruct (x == y); subst.
      * apply notin_singleton_is_false in H2.
        contradiction. 
      * apply aeq_refl.
  - intros x' y H1 H2.
    simpl in *.
    unfold swap_var.
    apply notin_remove_1 in H1.
    apply notin_remove_1 in H2.
    destruct H1.
    + destruct (x == x').
      * subst.
        destruct H2.
        ** subst.
           rewrite swap_id.
           apply aeq_refl.
        ** apply aeq_abs; assumption.
      * contradiction.
    + destruct (x == x').
      * subst.
        destruct H2.
        ** subst.
           rewrite swap_id.
           apply aeq_refl.
        ** apply aeq_abs; assumption.
      * destruct H2.
        ** subst.
           destruct (y == y).
           *** rewrite swap_symmetric.
               apply aeq_abs; assumption.
           *** contradiction.
        ** destruct (x == y).
           *** subst.
               rewrite swap_symmetric.
               apply aeq_abs; assumption.
           *** apply aeq_abs_same.
               apply IHt; assumption.
  - intros x y H1 H2.
    simpl in *.
    assert (H1' := H1).
    apply notin_union_1 in H1.
    apply notin_union_2 in H1'.
    assert (H2' := H2).
    apply notin_union_1 in H2.
    apply notin_union_2 in H2'.
    apply aeq_app.
    + apply IHt1; assumption.
    + apply IHt2; assumption.
  - intros x' y H1 H2.
    simpl in *.
    assert (H1' := H1).
    apply notin_union_1 in H1.
    apply notin_union_2 in H1'.
    assert (H2' := H2).
    apply notin_union_1 in H2.
    apply notin_union_2 in H2'.
    apply notin_remove_1 in H1.
    apply notin_remove_1 in H2.
    unfold swap_var.
    destruct H1.
    + subst.
      destruct (x' == x').
      * destruct H2.
        ** subst.
           repeat rewrite swap_id.
           apply aeq_refl.
        ** case (x' == y); intros; subst.
           *** repeat rewrite swap_id. apply aeq_refl.
           *** apply aeq_sub_diff.
           **** apply IHt2; assumption.
           **** apply aux_not_equal; assumption.
           **** assumption.
           **** apply aeq_refl.
      * contradiction.
    + destruct (x == x').
      * subst.
        destruct H2.
        ** subst.
           repeat rewrite swap_id.
           apply aeq_refl.
        ** case (x' == y); intros; subst.
           *** repeat rewrite swap_id. apply aeq_refl.
           *** apply aeq_sub_diff.
           **** apply IHt2; assumption.
           **** apply aux_not_equal; assumption.
           **** assumption.
           **** apply aeq_refl.
      * destruct H2.
        ** subst.
           destruct (y == y).
           *** rewrite swap_symmetric.
               replace (swap x' y t2) with (swap y x' t2).
               **** apply aeq_sub_diff.
               ***** apply IHt2; assumption.
               ***** apply aux_not_equal; assumption.
               ***** assumption.
               ***** apply aeq_refl.
               **** apply swap_symmetric.             
           *** contradiction.
        ** destruct (x == y).
           *** subst.
               rewrite swap_symmetric.
               replace (swap x' y t2) with (swap y x' t2).
               **** apply aeq_sub_diff.
               ***** apply IHt2; assumption.
               ***** apply aux_not_equal; assumption.
               ***** assumption.
               ***** apply aeq_refl.
               **** apply swap_symmetric.
           *** rewrite swap_symmetric.
               replace (swap x' y t2) with (swap y x' t2).
               **** apply aeq_sub_same.
                    ***** apply IHt1; assumption.
                    ***** apply IHt2; assumption.
               **** apply swap_symmetric.
Qed.

Lemma aeq_swap_swap: forall t x y z, z `notin` fv_nom t -> x `notin` fv_nom t -> aeq (swap z x (swap x y t)) (swap z y t).
Proof.
  intros. case (x == z); intros; subst.
  - rewrite swap_id; apply aeq_refl.
  - case (y == z); intros; subst.
    -- replace (swap x z t) with (swap z x t).
       --- rewrite swap_involutive; rewrite swap_id. apply aeq_refl.
       --- rewrite swap_symmetric; reflexivity.
    -- case (x == y); intros; subst.
       --- rewrite swap_id; apply aeq_refl.
       --- rewrite shuffle_swap.
           + apply aeq_swap. apply swap_reduction; assumption.
           + apply aux_not_equal; assumption.
           + assumption.
Qed.

Lemma aeq_sym: forall t1 t2, aeq t1 t2 -> aeq t2 t1.
Proof.
  induction 1.
  - apply aeq_refl.
  - apply aeq_abs_same; assumption.
  - apply aeq_abs_diff.
    -- apply aux_not_equal; assumption.
    -- apply fv_nom_swap with x y t2 in H0.
       apply aeq_fv_nom in H1.
       rewrite H1; assumption.
    -- apply aeq_swap2 with x y.
       rewrite swap_involutive.
       rewrite swap_symmetric.
       assumption.
  - apply aeq_app; assumption.
  - apply aeq_sub_same; assumption.
  - apply aeq_sub_diff.
    -- assumption.
    -- apply aux_not_equal. assumption.
    -- apply aeq_fv_nom in H2. rewrite H2.
       apply fv_nom_swap. assumption.
    -- rewrite swap_symmetric. apply aeq_swap2 with y x.
       rewrite swap_involutive. assumption.
Qed.

Lemma aeq_trans: forall t1 t2 t3, aeq t1 t2 -> aeq t2 t3 -> aeq t1 t3.
Proof.
  induction t1 using n_sexp_induction.
  - intros t2 t3 H1 H2. inversion H1; subst. assumption.
  - intros t2 t3 H1 H2. inversion H1; subst.
    + inversion H2; subst.
      * apply aeq_abs_same. replace t1 with (swap z z t1).
        ** apply H with t4.
           *** reflexivity.
           *** rewrite swap_id; assumption.
           *** assumption.
        ** apply swap_id.
      * apply aeq_abs_diff.
        ** assumption.
        ** assumption.
        ** apply aeq_sym.
           apply H with t4.
           *** apply eq_trans with (size t4).
               **** apply aeq_size in H8.
                    rewrite swap_size_eq in H8.
                    symmetry; assumption.
               **** apply aeq_size in H5.
                    symmetry; assumption.
           *** apply aeq_sym; assumption.
           *** apply aeq_sym; assumption.
    + inversion H2; subst.
      * apply aeq_abs_diff.
        ** assumption.
        ** apply aeq_fv_nom in H8.
           rewrite <- H8; assumption.
        ** apply aeq_sym.
           apply H with (swap y z t4).
           *** apply eq_trans with (size t4).
               **** apply aeq_size in H8.
                    symmetry; assumption.
               **** apply aeq_size in H7.
                    rewrite H7.
                    rewrite swap_size_eq.
                    reflexivity.
           *** apply aeq_sym.
               apply aeq_swap1; assumption.
           *** apply aeq_sym; assumption.
      * case (z == y0).
        ** intro Heq; subst.
           apply aeq_abs_same.
           apply aeq_swap1 with t4 (swap y0 y t2) y0 y in H10.
           rewrite swap_involutive in H10.
           apply aeq_sym.
           replace t2 with (swap y y t2).
           *** apply H with (swap y0 y t4).
               **** apply aeq_size in H7.
                    rewrite  H7.
                    apply aeq_size in H10.
                    rewrite <- H10.
                    rewrite swap_symmetric.
                    reflexivity.
               **** apply aeq_sym.
                    rewrite swap_id; assumption.
               **** apply aeq_sym.
                    rewrite swap_symmetric; assumption.
           *** apply swap_id.             
        ** intro Hneq.
           apply aeq_fv_nom in H10.
           assert (H5' := H5).
           rewrite H10 in H5'.
           apply fv_nom_swap_remove in H5'.           
           *** apply aeq_abs_diff.
               **** assumption.
               **** assumption.
               **** apply aeq_sym.
                    apply H with (swap z y t4).
                    ***** inversion H2; inversion H1; subst.
                    ****** apply aeq_size in H3.
                           apply aeq_size in H14.
                           rewrite <- H3; rewrite H14.
                           reflexivity.
                    ****** apply aeq_size in H3.
                           apply aeq_size in H19.
                           rewrite swap_size_eq in H19.
                           rewrite <- H3; rewrite H19.
                           reflexivity.
                    ****** apply aeq_size in H14.
                           apply aeq_size in H16.
                           rewrite swap_size_eq in H14.
                           rewrite <- H14; rewrite H16.
                           reflexivity.
                    ****** apply aeq_size in H14.
                           apply aeq_size in H21.
                           rewrite swap_size_eq in H14.
                           rewrite swap_size_eq in H21.
                           rewrite <- H14; rewrite H21.
                           reflexivity. 
                    ***** replace (swap z y t4) with (swap y z t4).
                          ****** inversion H2; subst.
                                 ******* apply aeq_sym.
                                         apply aeq_swap1; assumption.
                                 ******* apply aeq_sym.
                                         apply aeq_swap2 with y z.
                                         rewrite swap_involutive.
                                         apply aeq_sym.
                                         apply H with (swap y0 y t2).
                                         ******** rewrite swap_size_eq.
                                         apply aeq_size in H7.
                                         rewrite swap_size_eq in H7.
                                         inversion H2; subst.
                                         ********* apply aeq_size in H3.
                                                   rewrite H7; rewrite <- H3.
                                                   reflexivity.
                                         ********* apply aeq_size in H17. rewrite swap_size_eq in H17.
                                                   rewrite H7; rewrite <- H17. reflexivity.
                                         ******** replace (swap y0 z t2) with (swap z y0 t2).
                                                  ********* replace (swap y0 y t2) with (swap y y0 t2). 
                                                            ********** apply aeq_swap_swap; assumption.
                                                            ********** apply swap_symmetric.
                                                  ********* apply swap_symmetric.

                                         ******** apply aeq_sym; assumption.
                        ****** apply swap_symmetric.
                  ***** rewrite swap_symmetric.
                        apply aeq_sym; assumption.
           *** assumption.
           *** assumption.
  - intros. inversion H; subst. inversion H0; subst.
    apply aeq_app.
    -- specialize (IHt1_1 t1' t1'0). apply IHt1_1 in H3.
       --- assumption.
       --- assumption.
    -- specialize (IHt1_2 t2' t2'0). apply IHt1_2 in H5.
       --- assumption.
       --- assumption.
  - intros. inversion H0; subst.
    -- inversion H1; subst.
       --- apply aeq_sub_same.
           + specialize (H t1_1 z z).
             assert (size t1_1 = size t1_1). reflexivity.
             apply H with t1' t1'0 in H2; clear H.
             ++ rewrite swap_id in H2. assumption.
             ++ rewrite swap_id. assumption.
             ++ assumption.
           + specialize (IHt1_1 t2' t2'0). apply IHt1_1.
             ++ assumption.
             ++ assumption.
       --- apply aeq_sub_diff.
           + specialize (H t1'0 y z).
             assert (size t1_1 = size t1'0). {
               apply aeq_size in H6; apply aeq_size in H11.
               rewrite swap_size_eq in H11. rewrite <- H11.
               assumption.
             }
             symmetry in H2.
             apply H with t1' (swap y z t1'0) in H2.
             ++ specialize (IHt1_1 t2' t2'0). apply IHt1_1.
                +++ assumption.
                +++ assumption.
             ++ apply H with (swap y z t1'0) t1' in H2.
                +++ assumption.
                +++ apply aeq_refl.
                +++ apply aeq_sym. assumption.
             ++ assumption.
           + assumption.
           + assumption.
           + specialize (H (swap y z t1_1) y z).
             rewrite swap_size_eq in H.
             assert (size t1_1 = size t1_1). reflexivity.
             apply H with t1' (swap y z t1'0) in H2; clear H.
             ++ rewrite swap_involutive in H2. assumption.
             ++ rewrite swap_involutive. assumption.
             ++ assumption.
    -- inversion H1; subst.            
       --- apply aeq_sub_diff.
           + specialize (IHt1_1 t2' t2'0). apply IHt1_1.
             ++ assumption.
             ++ assumption.
           + assumption.
           + apply aeq_fv_nom in H10. rewrite H10 in H8.
             assumption.
           + specialize (H (swap y z t1_1) y z).
             assert (size (swap y z t1_1) = size t1_1).
             rewrite swap_size_eq; reflexivity.
             apply H with (swap y z t1') (swap y z t1'0) in H2.
             ++ rewrite swap_involutive in H2. assumption.
             ++ rewrite swap_involutive. assumption.
             ++ apply aeq_swap. assumption.     
       --- case (z == y0); intros; subst.
           + apply aeq_sub_same.
             specialize (H t1_1 y0 y).
             assert (size t1_1 = size t1_1). reflexivity.
             apply aeq_swap2 with y0 y.
             apply H with (swap y y0 (swap y y0 t1')) (swap y y0 t1'0) in H2.
             ++ apply aeq_sym; rewrite swap_symmetric; apply aeq_sym.
                assumption.
             ++ rewrite swap_involutive. apply aeq_swap2 with y y0.
                rewrite swap_symmetric. rewrite swap_involutive.
                assumption.
             ++ rewrite swap_involutive. rewrite swap_symmetric.
                assumption.
             ++ specialize (IHt1_1 t2' t2'0). apply IHt1_1.
                +++ assumption.
                +++ assumption.
           + apply aeq_sub_diff.
             ++ specialize (IHt1_1 t2' t2'0). apply IHt1_1.
                +++ assumption.
                +++ assumption.
             ++ assumption.
             ++ apply aeq_fv_nom in H13.
                rewrite H13 in H8.
                apply fv_nom_swap_remove in H8.
                +++ assumption.
                +++ assumption.
                +++ assumption.
             ++ pose proof H as H'. specialize (H t1_1 y0 z).
                assert (size t1_1 = size t1_1). reflexivity.
                apply H with (swap y0 z (swap y z t1')) t1'0 in H2.
                +++ apply aeq_swap2 with y0 z.
                    rewrite swap_involutive. assumption.
                +++ apply aeq_swap1. assumption.
                +++ pose proof H13.
                    apply aeq_swap1 with t1' (swap y0 y t1'0) y0 y in H3.
                    rewrite swap_involutive in H3.
                    apply aeq_fv_nom in H3.
                    rewrite <- H3 in H12.
                    apply fv_nom_swap_2 in H12.
                    pose proof swap_reduction.
                    specialize (H4 t1' y0 z).
                    apply aeq_sym in H4.
                    * specialize (H' (swap y z t1') y0 z).
                      assert (size (swap y z t1') = size t1_1).
                      apply aeq_size in H9; rewrite H9; reflexivity.
                      apply H' with (swap y y0 t1') t1'0 in H11.
                      ** assumption.
                      ** assert (swap y z t1' = swap z y t1').
                         rewrite swap_symmetric; reflexivity.
                         rewrite H14.
                         rewrite shuffle_swap.
                         *** rewrite swap_symmetric.
                             apply aeq_swap.
                             apply aeq_sym.
                             assumption.
                         *** apply aux_not_equal; assumption.
                         *** assumption.
                      ** apply aeq_swap2 with y y0.
                         rewrite swap_involutive.
                         rewrite swap_symmetric.
                         assumption.
                    * assumption.
                    * assumption.
Qed.                 

Require Import Setoid Morphisms.

Instance Equivalence_aeq: Equivalence aeq.
Proof.
  split.
  - unfold Reflexive. apply aeq_refl.
  - unfold Symmetric. apply aeq_sym.
  - unfold Transitive. apply aeq_trans.
Qed.

(**
 The original rules are implemented as the following recursive function:
 *)

Fixpoint f_pix (t: n_sexp): n_sexp :=
  match t with
  | (n_sub (n_var x) y e) => if x == y then e else (n_var x)
  | (n_sub (n_abs x e1) y e2) =>
      let (z,_) :=
        atom_fresh (fv_nom (n_abs x e1) `union` fv_nom e2 `union` {{y}}) in
      (n_abs z (n_sub (swap x z e1) y e2))
  | (n_sub (n_app e1 e2) y e3) => (n_app (n_sub e1 y e3) (n_sub e2 y e3))
  | _ => t
  end.


(* In this inductive definition, I didn't find a way to generate a fresh atom for the step_abs rule. For this kind of definition, we need to split the abs rule into three other rules: *)

Inductive pix : n_sexp -> n_sexp -> Prop :=
| step_var : forall (e: n_sexp) (y: atom),
    pix (n_sub (n_var y) y e) e
| step_gc : forall (e: n_sexp) (x y: atom),
    x <> y -> pix (n_sub (n_var x) y e) (n_var x)
| step_abs1 : forall (e1 e2: n_sexp) (y : atom),
    pix (n_sub (n_abs y e1) y e2)  (n_abs y e1)
| step_abs2 : forall (e1 e2: n_sexp) (x y: atom),
    x <> y -> x `notin` fv_nom e2 ->
    pix (n_sub (n_abs x e1) y e2)  (n_abs x (n_sub e1 y e2))
| step_abs3 : forall (e1 e2: n_sexp) (x y: atom),
    x <> y -> x `in` fv_nom e2 -> forall z, z <> x -> z <> y -> z `notin` fv_nom e1 -> z `notin` fv_nom e2 ->
    pix (n_sub (n_abs x e1) y e2)  (n_abs z (n_sub (swap x z e1) y e2))
| step_app : forall (e1 e2 e3: n_sexp) (y: atom),
    pix (n_sub (n_app e1 e2) y e3) (n_app (n_sub e1 y e3) (n_sub e2 y e3)).

(**
   The transitive closure of a binary relation over [n_sexp] is defined as follows:
 *)

Inductive trans (R: n_sexp -> n_sexp -> Prop): n_sexp -> n_sexp -> Prop :=
| singl: forall a b,  R a b -> trans R a b
| transit: forall b a c,  R a b -> trans R b c -> trans R a c.

(**
   The rule  [step_gc] can be generalized as follows:     
 *)

Lemma step_gc_gen: forall t u x, x `notin` fv_nom t -> trans pix (n_sub t x u) t.
Proof.
  induction t.
  - intros u x' H. simpl in H. apply notin_singleton_1 in H. apply singl. apply step_gc. assumption.
  - intros u x' H. simpl in H. apply notin_remove_1 in H. destruct H.
    + subst. apply singl. apply step_abs1.
    + case (x == x').
      * intro Heq. subst. apply singl. apply step_abs1.
      * intro Hneq. pose proof fv_nom_dec as Hfv. specialize (Hfv u x). destruct Hfv.
        ** pick_fresh z. apply transit with (n_abs x (n_sub t x' u)).
           *** apply step_abs3. assumption.
           *** 
        ** 
  -
  -
  
  
(**
   The [f_pix] function and the inductive definition have the same semantics in the following sense:
 *)

Lemma pix_to_f_pix: forall t u, pix t u -> f_pix t =a u.
Proof.
  induction 1.
  - simpl. rewrite eq_dec_refl. apply aeq_refl.
  - simpl. destruct (x == y).
    + contradiction.
    + apply aeq_refl.
  - simpl. destruct (atom_fresh (union (remove y (fv_nom e1)) (union (fv_nom e2) (singleton y)))).
    Admitted.

Lemma f_pix_to_pix: forall t u, f_pix t = u -> exists u', u =a u' /\ pix t u'.
Proof.    
  Admitted.
  
Instance aeq_R: forall (a: n_sexp), Proper (aeq ==> flip impl) (pix a).
Proof.
  repeat intro. induction H0.
  - Admitted.

(** We define the reflexive transitive closure of a reduction relation on [n_sexp] based on this notion of alpha-equivalence.
 *)
  
Inductive refltrans_aeq (R: n_sexp -> n_sexp -> Prop) : n_sexp -> n_sexp -> Prop :=
| refl_aeq: forall a b, aeq a b -> (refltrans_aeq R) a b
| rtrans_aeq: forall a b c, R a b -> refltrans_aeq R b c -> refltrans_aeq R a c.

Lemma aeq_one_r: forall a b c (R: n_sexp -> n_sexp -> Prop), R a b -> b =a c -> R a c.
Proof.
  intros a b c R H Haeq. generalize dependent c. generalize dependent a. induction b.
  - intros a H1 c H2. rewrite <- H2. assumption.
Admitted.

Lemma aeq_one_l: forall a b c (R: n_sexp -> n_sexp -> Prop), a =a b -> R b c -> R a c.
Admitted.

Lemma aeq_refltrans_aeq: forall a b R, aeq a b -> refltrans_aeq R a b.
Proof.
  intros a b R Haeq. apply refl_aeq. assumption.
Qed.

Lemma aeq_refltrans_refltrans_aeq: forall a b c R, aeq a b -> refltrans_aeq R b c -> refltrans_aeq R a c.
Proof.
  intros a b c R Haeq H. generalize dependent a. induction H.
  - intros a' Haeq. apply refl_aeq. apply aeq_trans with a; assumption.
  - intros a' Haeq. apply rtrans_aeq with b. ?? apply IHrefltrans_aeq. assumption.
Qed.

Lemma refltrans_aeq_composition (R: Rel n_sexp): forall t u v, refltrans_aeq R t u -> refltrans_aeq R u v -> refltrans_aeq R t v.
Proof.  
  intros t u v H1 H2. induction H1.
  - apply rtrans with b.
    + assumption.
    + apply IHrefltrans; assumption.  
Qed. 

Inductive refltrans {A:Type} (R: Rel A) : A -> A -> Prop :=
| refl: forall a, refltrans R a a
| rtrans: forall a b c, R a b -> refltrans R b c -> refltrans R a c.
(* begin hide *)
Lemma refltrans_composition {A} (R: Rel A): forall t u v, refltrans R t u -> refltrans R u v -> refltrans R t v.
Proof.
  intros t u v.
  intros H1 H2.
  induction H1.
  - assumption.
  - apply rtrans with b.
    + assumption.
    + apply IHrefltrans; assumption.
Qed.

Lemma refltrans_composition2 {A} (R: Rel A): forall t u v, refltrans R t u -> R u v -> refltrans R t v.
Proof.
  intros t u v H1 H2. induction H1.
  - apply rtrans with v.
    + assumption.
    + apply refl.
  - apply IHrefltrans in H2.
    apply rtrans with b; assumption.
Qed.

Lemma trans_to_refltrans {A:Type} (R: Rel A): forall a b, trans R a b -> refltrans R a b.
Proof.
  intros a b Htrans.
  induction Htrans.
  - apply rtrans with b.
    + assumption.
    + apply refl.
  - apply rtrans with b; assumption.
Qed.
(* end hide *)
(** The reflexive transitive closure of a relation is used to define
    the notion of confluence: no matter how the reduction is done, the
    result will always be the same. In other words, every divergence
    is joinable as stated by the following diagram:

    $\centerline{\xymatrix{ & a \ar@{->>}[dl] \ar@{->>}[dr] & \\ b
    \ar@{.>>}[dr] & & c \ar@{.>>}[dl] \\ & d & }}$

Formally, this means that if an expression $a$ can be reduced in two
different ways to $b$ and $c$, then there exists an expression $d$
such that both $b$ and $c$ reduce to $d$. The existential
quantification is expressed by the dotted lines in the diagram. This
notion is defined in the Coq system as follows: *)

Definition Confl {A:Type} (R: Rel A) := forall a b c, (refltrans R) a b -> (refltrans R) a c -> (exists d, (refltrans R) b d /\ (refltrans R) c d).

(** In %\cite{dehornoy2008z}%, V. van Oostrom gives a sufficient condition
for an ARS to be confluent. This condition is based on the $\textit{Z
  Property}$ that is defined as follows:

%\begin{definition} Let $(A,\to_R)$ be an ARS. A mapping $f:A \to A$ satisfies the Z property for $\to_R$, if $a \to_R b$ implies
$b \tto_R f a  \tto_R f b$, for any $a, b \in A$. 
\end{definition}%

The name of the property comes from the following diagrammatic
representation of this definition:
    
$\xymatrix{ a \ar[r]_R & b \ar@{.>>}[dl]^R\\ f a \ar@{.>>}[r]_R & f
    b \\ }$

If a function [f] satisfies the Z property for $\to_R$ then
we say that [f] is Z for $\to_R$, and the corresponding Coq
definition is given by the following predicate: *)

Definition f_is_Z {A:Type} (R: Rel A) (f: A -> A) := forall a b, R a b -> ((refltrans R)  b (f a) /\ (refltrans R) (f a) (f b)).

(** Alternatively, an ARS $(A,\to_R)$ satisfies the Z property if there
exists a mapping $f:A \to A$ such that $f$ is Z for $\to_R$: *)

Definition Z_prop {A:Type} (R: Rel A) := exists f:A -> A, forall a b, R a b -> ((refltrans R) b (f a) /\ (refltrans R) (f a) (f b)).

(** The first contribution of this work is a constructive proof of the fact that the Z property implies confluence. Our proof uses nested induction, and hence it differs from the one in %\cite{kesnerTheoryExplicitSubstitutions2009}% (that follows %\cite{dehornoy2008z}%) and the one in %\cite{felgenhauerProperty2016}% in the sense that it does not rely on the analyses of whether a term is in normal form or not, avoiding the necessity of the law of the excluded middle. As a result, we have an elegant inductive proof of the fact that if an ARS satisfies the Z property then it is confluent. *)

Theorem Z_prop_implies_Confl {A:Type}: forall R: Rel A, Z_prop R -> Confl R.
Proof.
  intros R HZ_prop. (** %\comm{Let $R$ be a relation over $A$ that satisfies
    the Z property, which will be denoted by $HZ\_prop$ for future
    reference.}% *)

  unfold Z_prop, Confl in *. (** %\comm{Unfolding both definitions of
  $Z\_prop$ and $Confl$, we get the following proof context:

     \includegraphics[scale=0.5]{figs/fig3.png} }% *)

  intros a b c Hrefl1 Hrefl2. (** %\comm{Let $a, b$ and $c$ be elements of
     the set $A$, $Hrefl1$ the hypothesis that $a \tto_R b$, and
     $Hrefl2$ the hypothesis that $a\tto_R c$. We need to prove that
     there exists $d$ such that $b\tto_R d$ and $c\tto_R d$.}% *)
  
  destruct HZ_prop as [g HZ_prop]. (** %\comm{We know from the hypothesis
     $HZ\_prop$ that there exists a mapping $f$ that is Z. Let's call
     $g$ this mapping, and we get following proof context:

      %\includegraphics[scale=0.6]{figs/fig4.png}%

      The proof proceeds by nested induction, firstly on the length of
      the reduction from $a$ to $b$, and then on the length of the
      reduction from $a$ to $c$.}% *)
  
  generalize dependent c. (** %\comm{Before the first induction,
      i.e. induction on $Hrefl1$, the element $c$ needs to be
      generalized so that it can be afterwards instantiated with any
      reduct of $a$.}% *)
  
  induction Hrefl1. (** %\comm{The induction on $Hrefl1$ corresponds to
       induction on the reflexive transitive closure of the relation
       $R$, and since $refltrans$ has two rules, the goal splits in
       two subgoals, one for each possible way of constructing $a
       \tto_R b$.}% *)
  
  - intros c Hrefl2. (** %\comm{In the first case, we have that $b = a$ since
    we are in the reflexive case. This means that we have to prove
    that there exists $d$, such that $a \tto_R d$ and $c \tto_R d$.}% *)
    
    exists c; split. (** %\comm{Taking $d$ as $c$, the proof is simplified to $a
    \tto_R c$ and $c \tto_R c$.}% *)

    + assumption. (** %\comm{The first component is exactly the hypothesis
        $Hrefl2$ and }% *) 

    + apply refl. (** %\comm{$c \tto_R c$ corresponds to an application of
        the $refl$ axiom.}% *)

        (** The interesting part of the proof is then given by the
        inductive case, i.e. when $a\tto_R b$ is generated by the rule
        [(rtrans)]. In this case, the reduction from [a] to [b] is
        done in at least one step, therefore there must exists an
        element $a'$ such that the following diagram holds.

        % \[\xymatrix{ & & a \ar@{->}[dl] \ar@{->>}[dr] & \\ & a'
        \ar@{->>}[dl] & & c \ar@{.>>}[ddll] \\ b \ar@{.>>}[dr] & & &
        \\ & d & & }\] % 

        (* The corresponding proof context is as follows:

        %\includegraphics[scale=0.6]{figs/fig5.png}% *)

        The induction hypothesis states that every divergence from
        $a'$ that reduces to $b$ from one side converges: [IHHrefl1]
        : $\forall c_0 : A, a'\tto_R c_0 \to (\exists d : A, b\tto_R d
        \land c_0\tto_R d$). Now, we'd like apply induction on the
        hypothesis [Hrefl2] (a\tto_R c), but the current proof context has the
        hypothesis [H]: $a\to_R a'$ ([a] reduces to [a'] in one step),
        and hence it is the sole hypothesis depending on [a] in the
        current proof context. If we were to apply induction on [Hrefl2] now, 
        the generated induction hypothesis [IHrefl2] would assume that there is 
        a term $a''$ such that $a \to_R a'' \tto_R c$ and would require that 
        $a'' \to_R a'$, which is generally false. In order to circumvent 
        this problem, we need to discard the hypothesis [H] from our proof 
        context, and replace it by another relevant information derived from 
        the Z property as shown in what follows. *)

  - intros c0 Hrefl2. (** %\comm{Let $c_0$ be a reduct of $a$, and $Hrefl2$
    be the hypothesis $a \tto_R c_0$. So the reduction $a\tto_R c$ in
    the above diagram is now $a\tto_R c_0$ due to a renaming of
    variables automatically done by the Coq system. In addition, the
    reduction $a \to_R a' \tto_R b$ is now $a\to_R b \tto_R c$, as
    shown below:

    \includegraphics[scale=0.5]{figs/fig5-1.png}

    Before applying induction to $Hrefl2$: $a \tto_R c_0$, we will derive 
    $b\tto_R (g\ a)$ and $a\tto_R (g\ a)$ from the proof context so we can
    discard the hypothesis $H$: $a\to_R$.}% *)

    assert (Hbga: refltrans R b (g a)).
    { apply HZ_prop; assumption.  } (** %\comm{We call $Hbga$ the reduction
    $b\tto_R (g\ a)$ that is directly obtained from the Z property.}% *)

    assert (Haga: refltrans R a (g a)).
    { apply rtrans with b; assumption.  } (** %\comm{Call $Haga$ the
        reduction $a\tto_R (g\ a)$, and prove it using the
        transitivity of $\tto_R$, since $a \to_R b$ and $b \tto_R (g\
        a)$. Diagrammatically, we change from the situation on the
        top to the bottomone on the right:

        \xymatrix{ & & a \ar@{->>}[ddrr]_R \ar@{->}[dl]^R & & \\ & b
        \ar@{->>}[dl]^R & & & \\ c \ar@{.>>}[ddrr]_R & & & & c_0
        \ar@{.>>}[ddll]^R \\ & & & & \\ & & d & & } 

        \xymatrix{ & & a \ar@{->>}[ddrr]_R \ar@{->>}[dd]_R & & \\ & b
        \ar@{->>}[dl]^R \ar@{->>}[dr]_R & & & \\ c \ar@{.>>}[ddrr]_R &
        & (g \; a) & & c_0 \ar@{.>>}[ddll]^R \\ & & & & \\ & & d & &} }% *) 

    clear H. generalize dependent b. (** %\comm{At this point we can remove
      the hypothesis $H$ from the context, and generalize $b$. Doing so, 
      we generalize $IHHrefl1$, which, in conjunction with the hypotheses 
      that depend on a (namely, $Hrefl2$, $Hbga$, and $Haga$), will form 
      the four necessary conditions for use of the second inductive 
      hypothesis, $IHHrefl2$.}% *)

    induction Hrefl2. (** %\comm{Now we are ready to start the induction on
    the reduction $a\tto_R c_0$, and we have two subgoals.}% *)
    
    + intros b Hrefl1 IHHrefl1 Hbga. (** %\comm{The first subgoal corresponds
        to the reflexive case that is closed by the induction
        hypothesis $IHHrefl1$:

        \[\xymatrix{ & & a \ar@{->>}[dd]^{H2} & & \\ & b
        \ar@{->>}[dl]_{Hrefl1} \ar@{->>}[dr]^{H1} & & & \\ c
        \ar@{.>>}[dr] & IHHrefl1 & (g \; a) \ar@{.>>}[dl] & & \\ & d &
        &&}\] }% *)
      
      assert (IHHrefl1_ga := IHHrefl1 (g a));
        
        apply IHHrefl1_ga in Hbga. (** %\comm{In order to apply $IHHrefl1$, we instantiate $c_0$ with $(g\
      a)$.}% *)
      
      destruct Hbga. (** %\comm{Therefore, there exists an element, say $x$,
      such that both $c\tto_R x$ and $(g\ a) \tto_R x$.}% *)
      
      exists x; split. (** %\comm{We then take $x$ to show that $c\tto_R x$ and $a
      \tto_R x$.}% *)
      
      * apply H. (** %\comm{Note that $c\tto_R x$ is already an hypothesis,
        and we are done.}% *)
        
      * apply refltrans_composition with (g a);

        [assumption | apply H]. (**
      %\comm{The proof of $a \tto_R x$ is done by the transitivity of
      $\tto_R$ taking $(g\ a)$ as the intermediate step.}% *)
           
    + intros b0 Hrefl1 IHHrefl1 Hb0ga. (** %\comm{The second subgoal corresponds
        to the case in which $a\tto_R c_0$ is generated by the rule
        $(rtrans)$. Therefore, there exists a term $b$ such that
        $a\to_R b$ and $b \tto_R c_0$. The corresponding proof context
        after introducing the universally quantified variable $b0$,
        the hypothesis $Hrefl1$ and the induction hypothesis
        $IHHrefl1$ generated by the first outer induction and the fact
        that $b0 \tto_R (g\ a)$ is given by:

        \includegraphics[scale=0.48]{figs/fig7.png} }% *)

      apply IHHrefl2 with b0. (** %\comm{The second goal, i.e. the inductive case is 
      the consequent on $IHHrefl2$, so we can apply $IHHrefl2$ to prove it. Doing so, 
      we must prove the antecedent of $IHHrefl2$, which consists of four separate 
      hypotheses that we must prove. Those hypotheses are as follows:}% *)
      
      * apply refltrans_composition with (g a);
          
        apply HZ_prop; assumption. (** %\comm{1. $b \tto_R (g\ b)$: This is proved by the transitivity of the
      reflexive transitive closure of $R$ using the
      hypothesis (H: $a\to_R b$) and $HZ\_prop$: $\forall a\
      b: a \to_R b \to (b \tto_R (g\ a) \land (g\ a) \tto_R (g\ b))$.}% *)
        
      * assumption. (** %\comm{2. $b0 \tto_R c$: This is exactly the
          hypothesis $Hrefl1$.}% *)

      * assumption. (** %\comm{3. $\forall c0: b0 \tto_R c0 \to (\exists d:
            c \tto_R d \land c0 \tto_R d)$: This is exactly the
            induction hypothesis $IHHrefl1$.}% *)

      * apply refltrans_composition with (g a);
        [ assumption | apply HZ_prop; assumption]. (** %\comm{4. $b0 \tto_R (g\ b)$: This is proved by the transitivity of
      the reflexive transitive closure of $R$ using the
      hypothesis $H'$: $b0 \tto_R (g\ a)$ and the fact that
      $(g\ a) \tto_R (g\ b)$ that is obtained from the fact that
      $R$ satisfies the Z property (hypothesis
      $HZ\_prop$).}% *)
        
Qed.

Definition SemiConfl {A:Type} (R: Rel A) := forall a b c, R a b -> (refltrans R) a c -> (exists d, (refltrans R) b d /\ (refltrans R) c d).

Theorem Z_prop_implies_SemiConfl {A:Type}: forall R: Rel A, Z_prop R -> SemiConfl R.
(* begin hide *)
Proof.
  intros R HZ_prop.
  unfold Z_prop in HZ_prop.
  unfold SemiConfl.
  destruct HZ_prop.
  intros a b c Hrefl Hrefl'.
  assert (Haxa: refltrans R a (x a)).
  { apply rtrans with b.  - assumption.  - apply H.  assumption.  }
  apply H in Hrefl.
  destruct Hrefl.
  clear H1.
  generalize dependent b.
  induction Hrefl'.
  - intros.
    exists (x a).
    split; assumption.
  - intros.
    destruct IHHrefl' with b0.
    + apply refltrans_composition with (x a); apply H; assumption.
    + apply refltrans_composition with (x b).
      * apply refltrans_composition with (x a).
        ** assumption.
        ** apply H.
           assumption.
      * apply refl.
    + exists x0.
      assumption.
Qed.
(* end hide *)

Theorem Semi_equiv_Confl {A: Type}: forall R: Rel A, Confl R <-> SemiConfl R.
(* begin hide *)
Proof.
  unfold Confl.
  unfold SemiConfl.
  intro R.
  split.
  - intros.
    apply H with a.
    + apply rtrans with b.
      * assumption.
      * apply refl.
    + assumption.
  - intros.
    generalize dependent c.
    induction H0.
    + intros.
      exists c.
      split.
      * assumption.
      * apply refl.
    + intros.
      specialize (H a).
      specialize (H b).
      specialize (H c0).
      apply H in H0.
      * destruct H0.
        destruct H0.
        apply IHrefltrans in H0.
        destruct H0.
        destruct H0.
        exists x0.
        split.
        ** assumption.
        ** apply refltrans_composition with x; assumption.
      * assumption.
Qed.
(* end hide *)

Corollary Zprop_implies_Confl_via_SemiConfl {A:Type}: forall R: Rel A, Z_prop R -> Confl R.
(* begin hide *)
Proof.
  intros R HZ_prop.
  apply Semi_equiv_Confl.
  generalize dependent HZ_prop.
  apply Z_prop_implies_SemiConfl.
Qed.
(* end hide *)

(** * An extension of the Z property: Compositional Z *)

Definition f_is_weak_Z {A} (R R': Rel A) (f: A -> A) := forall a b, R a b -> ((refltrans R') b (f a) /\ (refltrans R') (f a) (f b)).

Definition comp {A} (f1 f2: A -> A) := fun x:A => f1 (f2 x).
Notation "f1 # f2" := (comp f1 f2) (at level 40).

Inductive union {A} (red1 red2: Rel A) : Rel A :=
| union_left: forall a b, red1 a b -> union red1 red2 a b
| union_right: forall a b, red2 a b -> union red1 red2 a b.
Notation "R1 !_! R2" := (union R1 R2) (at level 40).

Lemma union_or {A}: forall (r1 r2: Rel A) (a b: A), (r1 !_! r2) a b <-> (r1 a b) \/ (r2 a b).
(* begin hide *)
Proof.
  intros r1 r2 a b; split.
  - intro Hunion.
    inversion Hunion; subst.
    + left; assumption.
    + right; assumption.
  - intro Hunion.
    inversion Hunion.
    + apply union_left; assumption.
    + apply union_right; assumption.
Qed.
(* end hide *)
Require Import Setoid.
Require Import ZArith.

Lemma equiv_refltrans {A}: forall (R R1 R2: Rel A), (forall x y, R x y <-> (R1 !_! R2) x y) -> forall x y, refltrans (R1 !_! R2) x y -> refltrans R x y.
(* begin hide *)
Proof.
  intros.
  induction H0.
  - apply refl.
  - apply rtrans with b.
    + apply H. assumption.
    + assumption.
  Qed.
(* end hide *)

Definition Z_comp {A:Type} (R :Rel A) := exists (R1 R2: Rel A) (f1 f2: A -> A), (forall x y, R x y <-> (R1 !_! R2) x y) /\ f_is_Z R1 f1 /\ (forall a b, R1 a b -> (refltrans R) ((f2 # f1) a) ((f2 # f1) b)) /\ (forall a b, b = f1 a -> (refltrans R) b (f2 b)) /\ (f_is_weak_Z R2 R (f2 # f1)).

Lemma refltrans_union {A:Type}: forall (R R' :Rel A) (a b: A), refltrans R a b -> refltrans (R !_! R') a b.
(* begin hide *)
Proof.
  intros R R' a b Hrefl.
  induction Hrefl.
  - apply refl.
  - apply rtrans with b.
    + apply union_left. assumption.
    + assumption.
Qed.
(* end hide *)

Require Import Setoid.
Lemma refltrans_union_equiv {A}: forall (R R1 R2 : Rel A), (forall (x y : A), (R x y <-> (R1 !_! R2) x y)) -> forall (x y: A), refltrans (R1 !_! R2) x y -> refltrans R x y.
(* begin hide *)
Proof.
  intros.
  induction H0.
  + apply refl.
  + apply rtrans with b.
    - apply H. assumption.
    - assumption.
Qed.
(* end hide *)

Theorem Z_comp_implies_Z_prop {A:Type}: forall (R :Rel A), Z_comp R -> Z_prop R.
(* begin hide *)
Proof.
  intros R H.
  unfold Z_prop. unfold Z_comp in H. destruct H as
  [ R1 [ R2 [f1 [f2 [Hunion [H1 [H2 [H3 H4]]]]]]]].
  exists (f2 # f1).
  intros a b HR.
  apply Hunion in HR. inversion HR; subst. clear HR.
  - split.
    + apply refltrans_composition with (f1 a).
      * apply H1 in H.
        destruct H as [Hb Hf].
        apply (refltrans_union R1 R2) in Hb.
        apply refltrans_union_equiv with R1 R2.
        ** apply Hunion.
        ** apply Hb.
      * apply H3 with a; reflexivity.
    + apply H2; assumption. 
  - apply H4; assumption.
Qed.
(* end hide *)

(** Now we can use the proofs of the theorems [Z_comp_implies_Z_prop]
and [Z_prop_implies_Confl] to conclude that compositional Z is a
sufficient condition for confluence. *)

Corollary Z_comp_is_Confl {A}: forall (R: Rel A), Z_comp R -> Confl R.
(* begin hide *)
Proof.
  intros R H.
  apply Z_comp_implies_Z_prop in H.
  apply Z_prop_implies_Confl; assumption.
Qed.
(* end hide *)

Theorem Z_comp_thm {A:Type}: forall (R :Rel A) (R1 R2: Rel A) (f1 f2: A -> A), (forall x y, R x y <-> (R1 !_! R2) x y) /\ f_is_Z R1 f1 /\ (forall a b, R1 a b -> (refltrans R) ((f2 # f1) a) ((f2 # f1) b)) /\ (forall a b, b = f1 a -> (refltrans R) b (f2 b)) /\ (f_is_weak_Z R2 R (f2 # f1)) -> f_is_Z R (f2 # f1).
(* begin hide *)
Proof.
  intros R R1 R2 f1 f2 H.
  destruct H as [Hunion [H1 [H2 [H3 H4]]]].
  unfold f_is_Z.
  intros a b Hab.
  apply Hunion in Hab.
  inversion Hab; subst. clear Hab; split.
  - apply refltrans_composition with (f1 a).
    assert (Hbf1a: refltrans (R1 !_! R2) b (f1 a)).
    { apply refltrans_union. apply H1; assumption. }
    apply equiv_refltrans with R1 R2.
    + assumption.
    + assumption.
    + apply H3 with a; reflexivity.
  - unfold comp.
    assert (H' := H).
    apply H1 in H.
    destruct H as [H Hf1].
    clear H.
    apply H2; assumption.
  - apply H4; assumption.
Qed. 
(* end hide *)

Corollary Z_comp_eq_corol {A:Type}: forall (R :Rel A) (R1 R2: Rel A) (f1 f2: A -> A), (forall x y, R x y <-> (R1 !_! R2) x y) /\ (forall a b, R1 a b -> (f1 a) = (f1 b)) /\ (forall a, (refltrans R1) a (f1 a)) /\ (forall b a, a = f1 b -> (refltrans R) a (f2 a)) /\ (f_is_weak_Z R2 R (f2 # f1)) -> f_is_Z R (f2 # f1).
(* begin hide *)
Proof.
  intros R R1 R2 f1 f2 H.
  destruct H as [Hunion [H1 [H2 [H3 H4]]]].
  pose proof (Z_comp_thm := Z_comp_thm R R1 R2 f1 f2).
  apply Z_comp_thm. split.
  - assumption.
  - split.
    + unfold f_is_Z.
      intros a b Hab. split.
      * apply H1 in Hab.
        rewrite Hab.
        apply H2.
      * apply H1 in Hab.
        rewrite Hab.
        apply refl.
    + split.
      * intros a b Hab.
        unfold comp.
        apply H1 in Hab.
        rewrite Hab.
        apply refl.
      * split; assumption.
Qed.
(* end hide *)

Definition Z_comp_eq {A:Type} (R :Rel A) := exists (R1 R2: Rel A) (f1 f2: A -> A), (forall x y, R x y <-> (R1 !_! R2) x y) /\ (forall a b, R1 a b -> (f1 a) = (f1 b)) /\ (forall a, (refltrans R1) a (f1 a)) /\ (forall b a, a = f1 b -> (refltrans R) a (f2 a)) /\ (f_is_weak_Z R2 R (f2 # f1)).

Lemma Z_comp_eq_implies_Z_comp {A:Type}: forall (R : Rel A), Z_comp_eq R -> Z_comp R.
(* begin hide *)
Proof.
  intros R Heq. unfold Z_comp_eq in Heq.
  destruct Heq as [R1 [R2 [f1 [f2 [Hunion [H1 [H2 [H3 H4]]]]]]]].
  unfold Z_comp.
  exists R1, R2, f1, f2.
  split.
  - assumption.
  - split.
    + unfold f_is_Z.
      intros a b H; split.
      * apply H1 in H. rewrite H. apply H2.
      * apply H1 in H. rewrite H. apply refl.
    + split.
      * intros a b H.
        unfold comp.
        apply H1 in H.
        rewrite H.
        apply refl.
      * split; assumption.
Qed.
(* end hide *)

Lemma Z_comp_eq_implies_Z_prop {A:Type}: forall (R : Rel A), Z_comp_eq R -> Z_prop R.
(* begin hide *)
Proof.
  intros R Heq.
  unfold Z_comp_eq in Heq.
  destruct Heq as [R1 [R2 [f1 [f2 [Hunion [H1 [H2 [H3 H4]]]]]]]].
  unfold Z_prop.  exists (f2 # f1).
  intros a b Hab.
  split.
  - apply Hunion in Hab.
    inversion Hab; subst.
    + unfold comp.
      apply H1 in H. rewrite H.
      apply refltrans_composition with (f1 b).
      * assert (H5: refltrans R1 b (f1 b)).
        {
          apply H2.
        }
        apply refltrans_union_equiv with R1 R2.
        ** assumption.
        ** apply refltrans_union. assumption.
      * apply H3 with b. reflexivity.
    + apply H4. assumption.
  - apply Hunion in Hab.
    inversion Hab; subst.
    + unfold comp. apply H1 in H. rewrite H. apply refl.
    + apply H4. assumption.
Qed.
(* end hide *)
