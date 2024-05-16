(**
   Sets are represented by lists, and these lists are built exactly the same way for $\alpha$-equivalent terms. Therefore, the sets [fv_nom t1] and [fv_nom t2] are syntactically equal. This is the content of the following lemma that has a key hole in this formalization.
 *)

Axiom remove_singleton_empty_eq: forall x, remove x (singleton x) = empty.
Axiom remove_empty_empty: forall x, remove x empty = empty. (* ? *)
Axiom remove_singleton_notin: forall x y, x <> y -> remove x (singleton y) = singleton y.
Axiom remove_remove_fv_nom: forall t x, remove x (remove x (fv_nom t)) = remove x (fv_nom t).
Axiom remove_remove_comm_fv_nom: forall t x y, remove x (remove y (fv_nom t)) = remove y (remove x (fv_nom t)).
Axiom remove_union: forall t1 t2 x, remove x (union (fv_nom t1) (fv_nom t2)) = union (remove x (fv_nom t1)) (remove x (fv_nom t2)).
(* Proof.
  induction t as [z | z t1 | t1 IHt1 t2 IHt2 | t1 IHt1 z t2 IHt2].
  - intro x. simpl. case (x == z).
    + intro Heq. subst. rewrite remove_singleton_empty_eq. apply remove_empty_empty.
    + intro Hneq. rewrite remove_singleton_eq.
      * apply remove_singleton_eq. assumption.
      * assumption.
  - intro x. simpl in *. case (x == z).
    + intro Heq. subst. rewrite IHt1. apply IHt1.
    + intro Hneq. Admitted. *)


Corollary remove_singleton_neq: forall x y z, x <> z -> y <> z -> remove x (singleton z) = remove y (singleton z).
Proof.
  intros x y z Hneq1 Hneq2. rewrite remove_singleton_notin.
  - rewrite remove_singleton_notin.
    + reflexivity.
    + assumption.
  - assumption.
Qed.   

(* não usado
Corollary remove_empty_eq: forall x y, remove x (singleton x) = remove y empty.
Proof.
 intros x y. rewrite remove_singleton_empty_eq. rewrite remove_empty_empty. reflexivity.
Qed. *)

Corollary remove_singleton_all: forall x y, remove x (singleton x) = remove y (singleton y).
Proof.
  intros x y. repeat rewrite remove_singleton_empty_eq. reflexivity.
Qed. 

Theorem fv_nom_dec: forall t x, x `in` fv_nom t \/ x `notin` fv_nom t.
Proof.
  induction t as [z | z t1 | t1 IHt1 t2 IHt2 | t1 IHt1 z t2 IHt2].
  - intros x. simpl. case (x == z).
    + intro Heq. subst. left. apply AtomSetImpl.singleton_2. reflexivity.
    + intro Hneq. right. auto.
  - intro x. simpl in *. case (x == z).
    + intro Heq. subst. right. auto.
    + intro Hneq. specialize (IHt1 x). destruct IHt1.
      * left. apply AtomSetImpl.remove_2.
        ** auto.
        ** assumption.
      * right. auto.
  - intros. simpl in *. specialize (IHt1 x). specialize (IHt2 x). destruct IHt1; destruct IHt2; try auto.
  - intros. simpl in *. specialize (IHt1 x). specialize (IHt2 x). destruct (x == z).
   + subst. destruct IHt1.
      * destruct IHt2.
        ** left. auto.
        ** right. auto.
      * destruct IHt2; auto.
   + destruct IHt1; try auto. destruct IHt2.
    * left. auto.
    * right. auto.
Qed.
  
(* virou axioma
Lemma remove_remove_comm_fv_nom: forall t x y, x <> y -> remove x (remove y (fv_nom t)) = remove y (remove x (fv_nom t)).
Proof.
  induction t as [z | t1 z | t1 t2 IHt1 IHt2 | t1 z t2 IHt1 IHt2] using  n_sexp_induction.
  - intros x y Hneq. simpl. case (y == z).
    + intro Heq. subst. rewrite remove_singleton_empty_eq. rewrite remove_empty_empty. symmetry. rewrite remove_singleton_notin.
      * apply remove_singleton_empty_eq.
      * assumption.
    + intro Hneq2. case (x == z).
      * intro Heq. subst. rewrite remove_singleton_notin.
        ** symmetry. rewrite remove_singleton_empty_eq. apply remove_empty_empty.
        ** assumption.
      * intro Hneq3. rewrite remove_singleton_notin.
        ** rewrite remove_singleton_notin.
           *** rewrite remove_singleton_notin.
               **** reflexivity.
               **** assumption.
           *** assumption.             
        ** assumption.
  - intros x y Hneq.  simpl in *. case (y == z).
    + intro Heq. subst. rewrite remove_remove_fv_nom. rewrite H at 2.
      * change (remove x (fv_nom t1)) with (fv_nom (n_abs x t1)). rewrite remove_remove_fv_nom. simpl. apply H.
        ** reflexivity.
        ** assumption.
      * reflexivity.
      * assumption.
    + intro Hneq'. Admitted. *)
  (*
  induction t as [z | z t1 | t1 IHt1 t2 IHt2 | t1 IHt1 z t2 IHt2].
  - intros x y Hneq. simpl. case (y == z).
    + intro Heq. subst. rewrite remove_singleton_empty_eq. rewrite remove_empty_empty. symmetry. rewrite remove_singleton_eq.
      * apply remove_singleton_empty_eq.
      * assumption.
    + intro Hneq2. case (x == z).
      * intro Heq. subst. rewrite remove_singleton_eq.
        ** symmetry. rewrite remove_singleton_empty_eq. apply remove_empty_empty.
        ** assumption.
      * intro Hneq3. rewrite remove_singleton_eq.
        ** rewrite remove_singleton_eq.
           *** rewrite remove_singleton_eq.
               **** reflexivity.
               **** assumption.
           *** assumption.             
        ** assumption.
  - intros x y Hneq. simpl in *. case (y == z).
    + intro Heq. subst. rewrite remove_remove_fv_nom. rewrite IHt1.
      * 
      *
    +
  -
  -
Admitted. *)

Lemma remove_notin: forall t x, x `notin` fv_nom t -> remove x (fv_nom t) = fv_nom t.
Proof.
  induction t as [y | y t1 | t1 IHt1 t2 IHt2 | t1 IHt1 y t2 IHt2].
  - intros x H. simpl in *. apply notin_singleton_1 in H. apply aux_not_equal in H. rewrite remove_singleton_notin.
    + reflexivity.
    + assumption.
  - intros x H. simpl in *. case (x == y).
    + (* x = y *) intro Heq. subst. rewrite remove_remove_fv_nom; reflexivity.
    + (* x <> y *) intro Hneq. apply notin_remove_1 in H. destruct H.
      * subst. contradiction.
      * rewrite remove_remove_comm_fv_nom. rewrite IHt1.
        ** reflexivity.
        ** assumption.
  - intros x H. simpl in *. rewrite remove_union. rewrite IHt1.
    + rewrite IHt2.
      * reflexivity.
      * apply notin_union_2 in H. assumption.
    + apply notin_union_1 in H. assumption.
  - Admitted. (* ok *)

(** errado Lemma fv_nom_swap_eq: forall t x y, x <> y -> fv_nom (swap x y t) = fv_nom t.
Proof.
  induction t as [z | z t1 | t1 IHt1 t2 IHt2 | t1 IHt1 z t2 IHt2].
  - intros x y H. simpl. unfold vswap. destruct (z == x).
    + subst. Admitted. *)
(*
Lemma remove_remove_fv_nom_swap: forall t x y, remove y (remove x (fv_nom (swap y x t))) = remove x (remove y (fv_nom t)). 
Proof.
  intros t x y. case (x == y).
  - intro Heq. subst. rewrite swap_id. reflexivity.
  - intro Hneq. pose proof remove_remove_comm_fv_nom. rewrite <- H. generalize dependent y. generalize dependent x. induction t as [z | z t1 | t1 IHt1 t2 IHt2 | t1 IHt1 z t2 IHt2].
    + intros x y Hneq. simpl. unfold vswap. destruct (z == y).
      * subst. rewrite remove_singleton_empty_eq. rewrite remove_empty_empty. rewrite remove_singleton_notin.
        ** rewrite remove_singleton_empty_eq. reflexivity.
        ** admit. (* ok  *)
      * destruct (z == x).
        ** subst. admit. (* ok *)
        ** reflexivity.
    + intros x y Hneq. f_equal. simpl. unfold vswap. case (z == y).
      * intro Heq. subst. specialize (IHt1 y x). rewrite swap_symmetric. rewrite IHt1.
      *
Admitted. *)
      
(*  induction t as [z | z t1 | t1 IHt1 t2 IHt2 | t1 IHt1 z t2 IHt2].
  - intros x y Hneq. simpl in *. unfold vswap. destruct (z == y).
    + subst. rewrite remove_singleton_neq.
      * rewrite remove_singleton_empty_eq. rewrite remove_singleton_neq.
        ** symmetry. apply remove_singleton_empty_eq.
        ** assumption.
      * apply aux_not_equal. assumption.
    + destruct (z == x).
      * subst. repeat rewrite remove_singleton_empty_eq. rewrite remove_empty. ?? reflexivity.
      * rewrite remove_singleton_neq.
        ** rewrite remove_singleton_neq.
           *** reflexivity.
           *** apply aux_not_equal. assumption.
        ** apply aux_not_equal. assumption.
  - intros x y Hneq. simpl in *. apply notin_remove_1 in Hneq. destruct Hneq as [Hneq | Hneq].
    + subst. unfold vswap. destruct (x == y).
      * subst. rewrite swap_id. reflexivity.
      * destruct (x == x).
        ** rewrite remove_singleton_neq.
           *** rewrite remove_singleton_neq.
               **** reflexivity.
               **** apply aux_not_equal. assumption.
           *** apply aux_not_equal. assumption.
        ** apply aux_not_equal. assumption.
    + unfold vswap. destruct (z == y).
      * subst. rewrite swap_id. reflexivity.
      * destruct (z == x).
        ** subst. rewrite remove_singleton_neq.
           *** rewrite remove_singleton_neq.
               **** reflexivity.
               **** apply aux_not_equal. assumption.
           *** apply aux_not_equal. assumption.
        ** rewrite remove_singleton_neq.
           *** rewrite remove_singleton_neq.
               **** reflexivity.
               **** apply aux_not_equal. assumption.
           *** apply aux_not_equal. assumption.
  - intros x y Hneq. simpl in *. rewrite IHt1.
    + rewrite IHt2.
      * reflexivity.
      * assumption.
    + assumption.
  - intros x y Hneq. simpl in *. apply notin_remove_1 in Hneq. destruct Hneq as [Hneq | Hneq].
    + subst. unfold vswap. destruct (x == y).
      * subst. rewrite swap_id. reflexivity.
      * destruct (x == x).
        ** rewrite remove_singleton_neq.
           *** rewrite remove_singleton_neq.
               **** reflexivity.
               **** apply aux_not_equal. assumption.
           *** apply aux_not_equal. *)

Lemma remove_remove_swap_eq: forall t x y, remove x (remove y (fv_nom t)) = remove x (remove y (fv_nom (swap x y t))). 
Proof.
  induction t as [z | z t1 | t1 IHt1 t2 IHt2 | t1 IHt1 z t2 IHt2].
  - intros x y. simpl. unfold vswap. destruct (z == x).
    + subst. case (x == y).
      * intro Heq. subst. reflexivity.
      * intro Hneq. rewrite remove_singleton_notin.
        ** repeat rewrite remove_singleton_empty_eq. rewrite remove_empty_empty. reflexivity.
        ** apply aux_not_equal. assumption.
    + destruct (z == y).
      * subst. rewrite remove_singleton_empty_eq. rewrite remove_empty_empty. rewrite remove_singleton_notin.
        ** rewrite remove_singleton_empty_eq. reflexivity.
        ** assumption.
      * reflexivity.
  - intros x y. simpl. unfold vswap. destruct (z == y).
    + subst. rewrite remove_remove_fv_nom. rewrite IHt1. destruct (y == x).
      * subst. rewrite swap_id. symmetry. repeat rewrite remove_remove_fv_nom. reflexivity.
      * symmetry. rewrite remove_remove_comm_fv_nom. rewrite remove_remove_fv_nom. reflexivity.
    + destruct (z == x).
      * subst. rewrite remove_remove_fv_nom. rewrite remove_remove_fv_nom. rewrite IHt1. reflexivity.
      * rewrite remove_remove_comm_fv_nom. rewrite IHt1. reflexivity.
        
    

Lemma remove_swap_eq: forall t x y, y `notin` (fv_nom t) -> remove x (fv_nom t) = remove y (fv_nom (swap y x t)). 
Proof.
  induction t as [z | z t1 | t1 IHt1 t2 IHt2 | t1 IHt1 z t2 IHt2].
  - intros x y H. simpl in *. unfold vswap. destruct (z == y).
    + subst. apply notin_singleton_1 in H. contradiction.
    + destruct (z == x).
      * subst. apply remove_singleton_all.
      * apply remove_singleton_neq.
        ** admit. (* ok *)
        ** admit. (* ok *)
  - intros x y H. simpl in *. unfold vswap. destruct (z == y). 
    + subst. apply notin_remove_1 in H. destruct H.
      * rewrite remove_remove_comm_fv_nom. f_equal.
      *
    +
  -
  -

  
 (* intros t x. pose proof fv_nom_dec as H. specialize (H t x). destruct H.
  - intros y Hnotin. generalize dependent y. generalize dependent x. induction t as [z | z t1 | t1 IHt1 t2 IHt2 | t1 IHt1 z t2 IHt2].
    + intros x Hx y Hy. simpl in *. unfold vswap. admit. (* ok *)
    + intros x Hx y Hy. simpl in *. unfold vswap. apply notin_remove_1 in Hy. apply AtomSetProperties.Dec.F.remove_iff in Hx. destruct Hx as [Ht1 Hneq]. destruct (z == y).
      * subst. symmetry. apply remove_remove_fv_nom_swap.
      * destruct Hy as [Heq | Ht1'].
        ** contradiction.
        ** destruct (z == x).
           *** contradiction.
           *** rewrite remove_remove_comm_fv_nom.
               **** specialize (IHt1 x). assert (IH :  forall y : atom, y `notin` fv_nom t1 -> remove x (fv_nom t1) = remove y (fv_nom (swap y x t1))). { apply IHt1. assumption. } rewrite IH with y.
                    ***** apply remove_remove_comm_fv_nom. assumption.
                    ***** assumption.
               **** admit. (* ok *)
    + Admitted. *)

(*      rewrite remove_singleton_empty.

      Instance
      
      
    + destruct (z == x).
      * subst. apply notin_singleton_1 in Hfv. contradiction.
      * rewrite remove_singleton_neq.
        ** rewrite remove_singleton_neq.
           *** reflexivity.
           *** apply aux_not_equal. assumption.
        ** apply aux_not_equal. assumption.
  - intros x y Hfv. simpl in *. apply notin_remove_1 in Hfv. destruct Hfv as [Hfv | Hfv].
    + subst. unfold vswap. destruct (x == y).
      * subst. rewrite swap_id. reflexivity.
      * destruct (x == x).
        **



          rewrite remove_singleton_neq.
           *** reflexivity.
           *** apply aux_not_equal. assumption.
        ** apply aux_not_equal. assumption.
  Admitted. *)

Lemma aeq_fv_nom_eq : forall t1 t2, t1 =a t2 -> fv_nom t1 = fv_nom t2.
Proof.
  induction 1. 
  - reflexivity.
  - simpl. rewrite IHaeq. reflexivity.
  - simpl. rewrite IHaeq. symmetry. rewrite swap_symmetric. apply remove_swap_eq. assumption.
  - simpl. rewrite IHaeq1. rewrite IHaeq2. reflexivity.
  - simpl. rewrite IHaeq1. rewrite IHaeq2. reflexivity.
  - simpl. rewrite IHaeq1. f_equal. rewrite IHaeq2. rewrite swap_symmetric. symmetry. apply remove_swap_eq. assumption.
Qed. 
