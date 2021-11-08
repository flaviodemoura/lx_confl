Require Import lambda_x.
Require Import ZtoConfl.

Fixpoint B (t : n_sexp) := match t with
                           | n_var x => n_var x
                           | n_abs x t1 => n_abs x (B t1)
                           | n_app t1 t2 => match t1 with
                                            | n_abs x t3 => m_subst (B t2) x (B t3)
                                            | _ => n_app (B t1) (B t2)
                                            end
                           | n_sub t1 x t2 => n_sub (B t1) x (B t2)
                           end.

Fixpoint P (t : n_sexp) := match t with
                           | n_var x => n_var x
                           | n_abs x t1 => n_abs x (P t1)
                           | n_app t1 t2 => n_app (P t1) (P t2)
                           | n_sub t1 x t2 => m_subst (P t2) x (P t1)
                           end.

(*Lemma size_m_subst: forall t1 t2 x,
    size (m_subst t2 x t1) = size (n_sub t1 x t2).
Proof.
  induction t1.
  - intros. simpl. unfold m_subst. simpl. case (x == x0)*)

Lemma subst_swap_reduction: forall u t x y z,
    (swap x y (m_subst u z t)) = (m_subst (swap x y u) (swap_var x y z) (swap x y t)).
Proof.
  intros. induction t.
  - unfold m_subst. simpl in *; unfold swap_var. default_simp.
  - unfold m_subst. simpl in *; unfold swap_var.
    case (z == x0); intros; subst.
    -- case (x0 == x); intros; subst.
       --- case (y == y); intros; subst.
           + simpl. unfold swap_var.
             case (x == x); intros; subst.
             ++ reflexivity.
             ++ contradiction.
           + contradiction.
       --- case (x0 == y); intros; subst.
           + case (x == x); intros; subst.
             ++ simpl. unfold swap_var.
                case (y == x); intros; subst.
                +++ contradiction.
                +++ case (y == y); intros; subst.
                    * reflexivity.
                    * contradiction.
             ++ contradiction.
           + case (x0 == x0); intros; subst.
             ++ simpl. unfold swap_var.
                case (x0 == x); intros; subst.
                +++ contradiction.
                +++ case (x0 == y); intros; subst.
                    * contradiction.
                    * reflexivity.
             ++ contradiction.
    -- case (z == x); intros; subst.
       --- case (x0 == x); intros; subst.
           + contradiction.
           + case (x0 == y); intros; subst.
             ++ case (y == x); intros; subst.
                +++ contradiction.
                +++ destruct (atom_fresh
         (Metatheory.union (fv_nom u)
            (Metatheory.union (remove y (fv_nom t)) (singleton x)))).
                    destruct (atom_fresh
       (Metatheory.union (fv_nom (swap x y u))
          (Metatheory.union (remove x (fv_nom (swap x y t)))
                            (singleton y)))).
                    simpl. unfold swap_var.
                    case (x0 == x); intros; subst.
                    * admit.
                    * admit.
             ++ admit.         
       --- admit.
  - unfold m_subst. simpl in *; unfold swap_var. default_simp.
    -- unfold m_subst in *. unfold swap_var in *. default_simp.
       assert (size t1 <= size t1 + size t2). apply le_plus_l.
       rewrite subst_size.
       --- symmetry.
           assert (size (swap x y t1) <= size (swap x y t1) + size (swap x y t2)). apply le_plus_l.
           rewrite subst_size.
           + symmetry. assumption.
           + assumption.
       --- assumption.      
    -- unfold m_subst in *. unfold swap_var in *. default_simp.
       assert (size t2 <= size t1 + size t2). apply le_plus_r.
       rewrite subst_size.
       --- symmetry.
           assert (size (swap x y t2) <= size (swap x y t1) + size (swap x y t2)). apply le_plus_r.
           rewrite subst_size.
           + symmetry. assumption.
           + assumption.
       --- assumption.      
    -- unfold swap_var in *. default_simp. unfold m_subst in *.
       assert (subst_rec (size t1) t1 u y = subst_rec (size t1 + size t2) t1 u y). {
         assert (size t1 <= size t1 + size t2). apply le_plus_l.
         pose proof subst_size.
         specialize (H0 (size t1 + size t2) u y t1).
         apply H0 in H; clear H0. symmetry; assumption.
       }
       rewrite <- H.
       rewrite IHt1.
       assert (size (swap x y t1) <= size (swap x y t1) + size (swap x y t2)). apply le_plus_l.
       pose proof subst_size.
       specialize (H1 (size (swap x y t1) + size (swap x y t2)) (swap x y u) x (swap x y t1)).
       apply H1 in H0; clear H1. rewrite H0. reflexivity.
    -- unfold swap_var in *. default_simp. unfold m_subst in *.
       assert (subst_rec (size t2) t2 u y = subst_rec (size t1 + size t2) t2 u y). {
         assert (size t2 <= size t1 + size t2). apply le_plus_r.
         pose proof subst_size.
         specialize (H0 (size t1 + size t2) u y t2).
         apply H0 in H; clear H0. symmetry; assumption.
       }
       rewrite <- H.
       rewrite IHt2.
       assert (size (swap x y t2) <= size (swap x y t1) + size (swap x y t2)). apply le_plus_r.
       pose proof subst_size.
       specialize (H1 (size (swap x y t1) + size (swap x y t2)) (swap x y u) x (swap x y t2)).
       apply H1 in H0; clear H1. rewrite H0. reflexivity.
    -- unfold swap_var in *. default_simp. unfold m_subst in *.
       assert (subst_rec (size t1) t1 u z = subst_rec (size t1 + size t2) t1 u z). {
         assert (size t1 <= size t1 + size t2). apply le_plus_l.
         pose proof subst_size.
         specialize (H0 (size t1 + size t2) u z t1).
         apply H0 in H; clear H0. symmetry; assumption.
       }
       rewrite <- H.
       rewrite IHt1.
       assert (size (swap x y t1) <= size (swap x y t1) + size (swap x y t2)). apply le_plus_l.
       pose proof subst_size.
       specialize (H1 (size (swap x y t1) + size (swap x y t2)) (swap x y u) z (swap x y t1)).
       apply H1 in H0; clear H1. rewrite H0. reflexivity.
    -- unfold swap_var in *. default_simp. unfold m_subst in *.
       assert (subst_rec (size t2) t2 u z = subst_rec (size t1 + size t2) t2 u z). {
         assert (size t2 <= size t1 + size t2). apply le_plus_r.
         pose proof subst_size.
         specialize (H0 (size t1 + size t2) u z t2).
         apply H0 in H; clear H0. symmetry; assumption.
       }
       rewrite <- H.
       rewrite IHt2.
       assert (size (swap x y t2) <= size (swap x y t1) + size (swap x y t2)). apply le_plus_r.
       pose proof subst_size.
       specialize (H1 (size (swap x y t1) + size (swap x y t2)) (swap x y u) z (swap x y t2)).
       apply H1 in H0; clear H1. rewrite H0. reflexivity.
  - unfold swap_var in *. default_simp. unfold m_subst in *.
    -- unfold swap_var. default_simp.
       --- admit.
       --- admit.
       --- admit.
       --- admit.
       --- admit.
       --- admit.
    -- unfold m_subst. simpl. default_simp.
       --- admit.
       --- admit.
       --- admit.
       --- admit.
       --- admit.
       --- admit.
       --- admit.
       --- admit.
       --- admit.
    -- unfold m_subst. simpl. default_simp.
       --- admit.
       --- admit.
       --- admit.
       --- admit.
       --- admit.
       --- admit.
       --- admit.
       --- admit.
       --- admit.
Admitted.

Lemma aeq_m_subst_1: forall t1 t2 x t3,
    aeq t1 t2 -> aeq (m_subst t3 x t1) (m_subst t3 x t2).
Proof.
  intros. induction H.
  - unfold m_subst. simpl. default_simp. apply aeq_refl.
  - unfold m_subst. simpl. default_simp.
    case (x1 == x2); intros; subst.
    -- apply aeq_abs_same. unfold m_subst in IHaeq.
       pose proof H. apply aeq_size in H0. rewrite H0.
       apply aeq_swap1 with t1 t2 x0 x2 in H.
       case (x0 == x2); intros; subst.
       --- repeat rewrite swap_id in *.
           rewrite H0 in IHaeq. assumption.
       --- apply aeq_swap1 with (subst_rec (size t1) t1 t3 x) (subst_rec (size t2) t2 t3 x) x0 x2 in IHaeq.
           pose proof subst_swap_reduction.
           pose proof H1.
           unfold m_subst in H1; unfold m_subst in H2.
           rewrite H1 in IHaeq; clear H1.
           rewrite H2 in IHaeq; clear H2.
           unfold swap_var in IHaeq.
           destruct (x == x0) in IHaeq; subst.
           + contradiction.
           + admit. 

      
    -- apply aeq_abs_diff.
       --- assumption.
       --- admit.
       --- pose proof subst_swap_reduction.
           unfold m_subst in H0.
           assert (size t2 = size (swap x0 x2 t2)).
           rewrite swap_size_eq; reflexivity.
           rewrite H1. rewrite H0. case (x2 == x1); intros; subst.
           + unfold swap_var. default_simp.
           + admit.
Admitted.

Lemma aeq_m_subst_2: forall t1 t2 t3 x,
    aeq t1 t2 -> aeq (m_subst t1 x t3) (m_subst t2 x t3).
Proof.
Admitted.

Lemma aeq_subst_same: forall t1 t1' x t2 t2',
    aeq t1 t1' -> aeq t2 t2' -> aeq (m_subst t1 x t2) (m_subst t1' x t2').
Proof.
  intros.
  apply aeq_trans with (m_subst t1 x t2').
  - apply aeq_m_subst_1. assumption.
  - apply aeq_m_subst_2. assumption.
Qed.

Lemma aeq_subst_diff: forall t1 t1' x y t2 t2',
    x <> y -> aeq t1 t1' -> aeq t2 (swap x y t2') -> aeq (m_subst t1 x t2) (m_subst t1' y t2').
Proof.
  Admitted.
  
Lemma aeq_swap_P: forall x y t,
    aeq (P (swap x y t)) (swap x y (P t)).
Proof.
  intros; induction t.
  - simpl. apply aeq_refl.
  - simpl. unfold swap_var. default_simp.
  - simpl. apply aeq_app.
    -- assumption.
    -- assumption.
  - simpl. unfold swap_var. default_simp.
    -- case (x == y); intros; subst.
       --- repeat rewrite swap_id. apply aeq_subst_same.
           + apply aeq_refl.
           + apply aeq_refl.
       --- pose proof subst_swap_reduction.
           specialize (H (P t2) (P t1) x y x). rewrite H.
           unfold swap_var; unfold swap_var in H; default_simp.
           apply aeq_subst_same.
           + assumption.
           + assumption. 
    -- pose proof subst_swap_reduction.
       assert ((swap x y (m_subst (P t2) y (P t1)) = (swap y x (m_subst (P t2) y (P t1))))). rewrite swap_symmetric; reflexivity.
       rewrite H0.
       specialize (H (P t2) (P t1) y x y). rewrite H.
       unfold swap_var; unfold swap_var in H; default_simp.
       apply aeq_subst_same.
       --- apply aeq_sym. rewrite swap_symmetric.
           apply aeq_sym. assumption.
       --- apply aeq_sym. rewrite swap_symmetric.
           apply aeq_sym. assumption.
    -- pose proof subst_swap_reduction.
       specialize (H (P t2) (P t1) x y x0).
       unfold swap_var; unfold swap_var in H; default_simp.
       rewrite H. apply aeq_subst_same.
       --- assumption.
       --- assumption.
Qed.

Lemma fv_nom_m_subst: forall t u x,
    fv_nom (m_subst u x t) [=] fv_nom (n_sub t x u).
Proof.
  Admitted.

Lemma notin_P: forall x t,
    x `notin` fv_nom t -> x `notin` fv_nom (P t).
Proof.
  intros. induction t.
  - simpl. simpl in H. assumption.
  - simpl. simpl in H. case (x == x0); intros; subst.
    -- apply notin_remove_3. reflexivity.
    -- apply notin_remove_2. apply IHt. apply notin_remove_1 in H.
       inversion H; subst.
       --- contradiction.
       --- assumption.
  - simpl. apply notin_union; simpl in H.
    -- apply notin_union_1 in H. apply IHt1. assumption.
    -- apply notin_union_2 in H. apply IHt2. assumption.
  - simpl. simpl in H. pose proof H. apply notin_union_1 in H.
    apply notin_union_2 in H0.
             rewrite fv_nom_m_subst. simpl. apply notin_union_3.
    -- case (x == x0); intros; subst.
       --- apply notin_remove_3. reflexivity.
       --- apply notin_remove_2. apply IHt1.
           apply notin_remove_1 in H. inversion H; subst.
           + contradiction.
           + assumption.
    -- apply IHt2. assumption.
Qed.

Lemma notin_P_2: forall x t,
    x `notin` fv_nom (P t) -> x `notin` fv_nom t.
Proof.
  induction t; intros.
  - simpl in H; assumption.
  - simpl in H. case (x == x0); intros; subst.
    -- simpl. apply notin_remove_3. reflexivity.
    -- apply notin_remove_1 in H. inversion H; subst.
       --- contradiction.
       --- simpl. apply notin_remove_2. apply IHt.
           assumption.
  - simpl. simpl in H. apply notin_union_3.
    -- apply notin_union_1 in H. apply IHt1; assumption.
    -- apply notin_union_2 in H. apply IHt2; assumption.
  - simpl in H. rewrite fv_nom_m_subst in H. simpl in H.
    simpl. apply notin_union_3.
    -- case (x == x0); intros; subst.
       --- apply notin_remove_3. reflexivity.
       --- apply notin_union_1 in H. apply notin_remove_1 in H.
           apply notin_remove_2. inversion H; subst.
           + contradiction.
           + apply IHt1; assumption.
    -- apply notin_union_2 in H. apply IHt2; assumption.
Qed.

Lemma aeq_nvar_1: forall t x, aeq t (n_var x) -> t = n_var x.
Proof.
  induction t.
  - intros x' H.
    inversion H; subst.
    reflexivity.
  - intros x' H.
    inversion H.
  - intros x H.
    inversion H.
  - intros x' H.
    inversion H.
Qed.

Lemma aeq_nvar_2: forall t x, t = n_var x -> aeq t (n_var x).
Proof.
  induction t.
  - intros x' H.
    inversion H; subst.
    apply aeq_refl.
  - intros x' H.
    inversion H.
  - intros x H.
    inversion H.
  - intros x' H.
    inversion H.
Qed.

<<<<<<< HEAD
(**)
(*Lemma 1 in Nakazawa*)
Lemma pi_P: forall t1 t2, pix t1 t2 -> P t1 = P t2.
Proof.
  induction 1.
  - simpl.
    unfold m_subst.
    simpl.
    destruct (y == y).
    + reflexivity.
    + contradiction.
  - simpl.
    unfold m_subst.
    simpl.
    destruct (y == x).
    + symmetry in e0.
      contradiction.
    + reflexivity.
  - simpl.
    unfold m_subst.
    simpl.
    destruct (y == y).
    + reflexivity.
    + contradiction.
  - simpl.
    unfold m_subst.
    simpl.
    destruct (y == x).
    + symmetry in e.
      contradiction.
    + destruct (atom_fresh (Metatheory.union (fv_nom (P e2)) (Metatheory.union (remove x (fv_nom (P e1))) (singleton y)))).
      admit.
  - simpl.
    unfold m_subst.
    simpl.
    admit.
Admitted.    

Lemma pi_P': forall t1 t2, ctx pix t1 t2 -> (P t1) = (P t2).
Proof.
  induction 1.
Admitted.
  
Lemma aeq_to_P: forall t1 t2, aeq t1 t2 -> aeq (P t1) (P t2). 
Proof.
Admitted.

Lemma pi_P': forall t1 t2, ctx pix t1 t2 -> aeq (P t1) (P t2).
Proof.
  intros t1 t2 H.
  induction H.
  - apply aeq_to_P; assumption.
  - apply pi_P in H0.
    apply aeq_to_P in H.
    rewrite H0 in H.
    apply aeq_to_P in H1.
    apply aeq_trans with (P e3); assumption.
  - simpl.
    apply aeq_abs_same.
    assumption.
  - simpl.
    apply aeq_app.
    + assumption.
    + apply aeq_refl.
  - simpl.
    apply aeq_app.
    + apply aeq_refl.
    + assumption.
  - simpl.
      
(* 
Lemma pi_P': forall t1 t2, refltrans (ctx pix) t1 t2 -> aeq (P t1) (P t2).
Proof.
  intros t1 t2 H. induction H.
=======
Lemma aeq_P: forall t1 t2, aeq t1 t2 -> aeq (P t1) (P t2).
Proof.
  intros. induction H.
>>>>>>> f4fe749556192fd9e9ebe1a09c448f6bb3c8ee43
  - apply aeq_refl.
  - simpl. apply aeq_abs_same. assumption.
  - simpl. apply aeq_abs_diff.
    -- assumption.
    -- apply notin_P. assumption.
    -- pose proof aeq_swap_P. specialize (H2 y x t2).
       apply aeq_trans with (P (swap y x t2)); assumption. 
  - simpl. apply aeq_app; assumption.
  - simpl. apply aeq_subst_same; assumption.
  - simpl. apply aeq_subst_diff.
    -- assumption.
    -- assumption.
    -- rewrite swap_symmetric.
       pose proof aeq_swap_P. specialize (H3 y x t1').
       apply aeq_trans with (P (swap y x t1')); assumption. 
Qed.
             (**)
(*Lemma 1 in Nakazawa*)    
Lemma pi_P: forall t1 t2, (ctx pix) t1 t2 -> aeq (P t1) (P t2).
Proof.
  intros. induction H.
  - apply aeq_P. assumption.
  - inversion H0; subst.
    -- inversion H; subst.
       --- inversion H5; subst. simpl.
           unfold m_subst. simpl. case (y == y); intros; subst.
           + apply aeq_P.
             apply aeq_trans with e3; assumption.
           + contradiction.
       --- simpl; unfold m_subst. inversion H9; subst.
           simpl. unfold swap_var in *.
           case (y == y); intros; subst.
           + case (x == x); intros; subst.
             ++ apply aeq_P. apply aeq_trans with e3; assumption.
             ++ contradiction.
           + contradiction.
    -- inversion H1; subst. inversion H; subst.
       --- simpl.  unfold m_subst. inversion H6; subst.
           simpl. case (y == x); intros; subst.
           + contradiction.
           + apply aeq_refl.
       --- simpl. simpl in H10. unfold swap_var in H10.
           destruct (x == y) in H10; subst.
           + contradiction.
           + destruct (x == x0) in H10; subst.
             ++ simpl in H9. apply notin_singleton_1 in H9.
                contradiction.
             ++ inversion H10; subst.
                unfold m_subst; simpl.
                case (x0 == x); intros; subst.
                +++ contradiction.
                +++ apply aeq_refl.
    -- inversion H1; subst.
       --- inversion H; subst.
           + simpl; unfold m_subst.
             inversion H6; subst.
             ++ simpl. case (y == y); intros; subst.
                +++ apply aeq_abs_same. apply aeq_P.
                    apply aeq_trans with e0; assumption.
                +++ contradiction.
             ++ simpl. case (y == x); intros; subst.
                +++ contradiction.
                +++ destruct (atom_fresh
         (Metatheory.union (fv_nom (P t0))
            (Metatheory.union (remove x (fv_nom (P t3)))
                              (singleton y)))).
                    case (x0 == y); intros; subst.
                    * apply aeq_abs_same. admit.
                    * apply aeq_abs_diff.
                      ** assumption.
                      ** case (x0 == x); intros; subst.
                         *** apply aeq_fv_nom in H5.
                             rewrite H5 in H9.
                             apply notin_P.
                             assumption.
                         *** apply notin_union_2 in n0.
                             apply notin_union_1 in n0.
                             apply notin_remove_1 in n0.
                             inversion n0; subst.
                         **** contradiction.    
                         **** apply aeq_swap1 with t3 (swap y x e0) y x in H10.
                              rewrite swap_involutive in H10.
                              assert (aeq (swap y x t3) t2).
                              apply aeq_trans with e0; assumption.
                              apply aeq_P in H3.
                              apply aeq_fv_nom in H3.
                              rewrite <- H3.
                              pose proof aeq_swap_P.
                              specialize (H7 y x t3).
                              apply aeq_fv_nom in H7.
                              rewrite H7.
                              apply fv_nom_swap_remove with y x.                             ***** assumption.
                         ***** assumption.
                         ***** rewrite swap_symmetric.
                               rewrite swap_involutive.
                               assumption.
                      ** admit.
           + simpl. admit.
       --- admit.    
    -- admit.   
    -- admit.
  - simpl. apply aeq_abs_same. assumption.
  - simpl. apply aeq_app. 
    -- assumption.
    -- apply aeq_refl.
  - simpl. apply aeq_app. 
    -- apply aeq_refl.
    -- assumption.
  - simpl. apply aeq_subst_same.
    -- apply aeq_refl.
    -- assumption.
  - simpl. apply aeq_subst_same.
    -- assumption.
    -- apply aeq_refl.
Admitted.

(*Lemma 2 in Nakazawa*)
Lemma pure_P: forall e, pure (P e).
Proof.
  induction e.
  - simpl. apply pure_var.
  - simpl. apply pure_abs. assumption.
  - simpl. apply pure_app.
    -- assumption.
    -- assumption.
  - simpl. unfold m_subst. 
    induction (P e1).
    -- simpl. case (x == x0).
       --- intros. assumption.
       --- intros. assumption.
    -- simpl. case (x == x0).
       --- intros. assumption.
       --- intros. destruct (atom_fresh
           (Metatheory.union (fv_nom (P e2))
                             (Metatheory.union (remove x0 (fv_nom n)) (singleton x)))). apply pure_abs. inversion IHe1.
           pose proof pure_m_subst. pose proof pure_swap.
           specialize (H3 x0 x1 n). apply notin_union_2 in n1.
           apply notin_union_1 in n1. 
           case (x0 == x1).
           + intros; subst. apply IHn in H0.
             rewrite swap_id. assumption.
           + intros; subst. pose proof pure_swap.
             specialize (H x0 x1 n). apply H in H0.
             clear H3; clear H. unfold m_subst in H2.
             specialize (H2 (swap x0 x1 n) (P e2) x).
             pose proof swap_size_eq.
             specialize (H x0 x1 n). rewrite <- H.
             apply H2.
             ++ assumption.
             ++ assumption.
    -- simpl. pose proof subst_size. inversion IHe1; subst.
       apply IHn1 in H2; clear IHn1; apply IHn2 in H3; clear IHn2.
       apply pure_app.
       --- specialize (H (size n1 + size n2) (P e2) x n1).
           pose proof le_plus_l.
           specialize (H0 (size n1) (size n2)).
           apply H in H0; clear H. rewrite H0. assumption.
       --- specialize (H (size n1 + size n2) (P e2) x n2).
           pose proof le_plus_r.
           specialize (H0 (size n1) (size n2)).
           apply H in H0; clear H. rewrite H0. assumption.
    -- inversion IHe1.
Qed.

(*lemma 3 in Nakazawa*)
Lemma pure_P_id: forall e, pure e -> P e = e.
Proof.
  induction e.
  - intros. simpl. reflexivity.
  - intros. simpl. inversion H. apply IHe in H1. rewrite H1.
    reflexivity.
  - intros. simpl. inversion H. apply IHe1 in H2; apply IHe2 in H3.
    rewrite H2; rewrite H3. reflexivity.
  - intros. inversion H.
Qed.

(**)

Lemma refltrans_abs (R: Rel n_sexp): forall e1 e2 x ,
    refltrans (ctx R) e1 e2 -> refltrans (ctx R) (n_abs x e1) (n_abs x e2).
Proof.
  intros. induction H.
  - apply refl.
  - induction H.
    -- inversion H0; subst.
       --- apply rtrans with (n_abs x c).
           + apply step_aeq. apply aeq_abs_same. assumption.
           + apply refl.
       --- apply refltrans_composition with (n_abs x e2).
           + apply rtrans with (n_abs x e2).
             ++ apply step_abs_in. apply step_aeq. assumption.
             ++ apply refl.
           + assumption.
    -- apply refltrans_composition with (n_abs x e2).
       --- apply rtrans with (n_abs x e2).
           + apply step_abs_in. apply step_aeq; assumption.
           + apply refl.
       --- apply refltrans_composition with (n_abs x e3).
           + apply rtrans with (n_abs x e3).
             ++ apply step_abs_in. apply step_redex_R; assumption.
             ++ apply refl.
           + apply refltrans_composition with (n_abs x e4).
             ++ apply rtrans with (n_abs x e4).
                +++ apply step_abs_in. apply step_aeq; assumption.
                +++ apply refl.
             ++ assumption.
    -- apply refltrans_composition with (n_abs x (n_abs x0 e')).
       --- apply rtrans with (n_abs x (n_abs x0 e')).
           + repeat apply step_abs_in. assumption.
           + apply refl.
       --- assumption.
    -- apply refltrans_composition with (n_abs x (n_app e1' e2)).
       --- apply rtrans with (n_abs x (n_app e1' e2)).
           + apply step_abs_in. apply step_app_left. assumption.
           + apply refl.
       --- assumption.
    -- apply refltrans_composition with (n_abs x (n_app e1 e2')).
       --- apply rtrans with (n_abs x (n_app e1 e2')).
           + apply step_abs_in. apply step_app_right. assumption.
           + apply refl.
       --- assumption.
    -- apply refltrans_composition with (n_abs x (n_sub e1' x0 e2)).
       --- apply rtrans with (n_abs x (n_sub e1' x0 e2)).
           + apply step_abs_in. apply step_sub_left. assumption.
           + apply refl.
       --- assumption.
    -- apply refltrans_composition with (n_abs x (n_sub e1 x0 e2')).
       --- apply rtrans with (n_abs x (n_sub e1 x0 e2')).
           + apply step_abs_in. apply step_sub_right. assumption.
           + apply refl.
       --- assumption.
Qed.

Lemma refltrans_composition3 (R: Rel n_sexp): forall t u v,
    refltrans R t u -> refltrans R v t -> refltrans R v u.
Proof.
  intros. induction H0.
  - assumption.
  - apply rtrans with b.
    -- assumption.
    -- apply IHrefltrans. assumption.
Qed.
    
Lemma refltrans_app1 (R: Rel n_sexp): forall e1 e2 e3 ,
    refltrans (ctx R) e1 e2 -> refltrans (ctx R) (n_app e1 e3) (n_app e2 e3).
Proof.
  intros e1 e2 e3. intro H. induction H.
  - apply refl.
  - apply refltrans_composition with (n_app b e3).
    -- apply rtrans with (n_app b e3).
       --- apply step_app_left. assumption.
       --- apply refl.
    -- assumption.
Qed.


       
Lemma refltrans_app2 (R: Rel n_sexp): forall e1 e2 e3,
    refltrans (ctx R) e2 e3 -> refltrans (ctx R) (n_app e1 e2) (n_app e1 e3).
Proof.
  intros e1 e2 e3. intro H. induction H.
  - apply refl.
  - apply refltrans_composition with (n_app e1 b).
    -- induction H.
       --- apply rtrans with (n_app e1 e2).
           + apply step_aeq. apply aeq_app.
             ++ apply aeq_refl.
             ++ assumption.
           + apply refl.
       --- apply refltrans_composition with (n_app e1 e2).
           + apply rtrans with (n_app e1 e2).
             ++ apply step_app_right. apply step_aeq. assumption.
             ++ apply refl.
           + apply refltrans_composition with (n_app e1 e3).
             ++ apply rtrans with (n_app e1 e3).
                +++ apply step_app_right. apply step_redex_R.
                    assumption.
                +++ apply refl.
             ++ apply rtrans with (n_app e1 e4).
                +++ apply step_app_right. apply step_aeq.
                    assumption.
                +++ apply refl.
       --- apply rtrans with (n_app e1 (n_abs x e')).
           + apply step_app_right. apply step_abs_in. assumption.
           + apply refl.
       --- apply rtrans with (n_app e1 (n_app e1' e2)).
           + apply step_app_right. apply step_app_left.
             assumption.
           + apply refl.
       --- apply rtrans with (n_app e1 (n_app e0 e2')).
           + repeat apply step_app_right. assumption.
           + apply refl.
       --- apply rtrans with (n_app e1 (n_sub e1' x e2)).
           + apply step_app_right. apply step_sub_left.
             assumption.
           + apply refl.
       --- apply rtrans with (n_app e1 (n_sub e0 x e2')).
           + apply step_app_right. apply step_sub_right.
             assumption.
           + apply refl.
    -- assumption.
Qed.

Lemma refltrans_app3: forall e1 e2 e3 e4,
    refltrans (ctx pix) e1 e2 -> refltrans (ctx pix) e3 e4 -> refltrans (ctx pix) (n_app e1 e3) (n_app e2 e4).
Proof.
  intros. induction H0.
  - induction H.
    -- apply refl.
    -- apply refltrans_app1.
       apply rtrans with b.
       --- assumption.
       --- assumption.
  - apply refltrans_composition with (n_app e1 b).
    -- apply refltrans_app2. apply rtrans with (ctx pix) a b b in H0.
       --- assumption.
       --- apply refl.
    -- assumption.
Qed.

Lemma refltrans_sub1 (R: Rel n_sexp): forall e1 e2 e3 x,
    refltrans R e2 e3 -> refltrans (ctx R) (n_sub e1 x e2) (n_sub e1 x e3).
  intros. induction H.
  - apply refl.
  - apply refltrans_composition with (n_sub e1 x b).
    -- apply rtrans with (n_sub e1 x b).
       --- apply step_sub_right. apply step_redex_R. assumption.
       --- apply refl.
    -- assumption.
Qed.

Lemma refltrans_sub2 (R: Rel n_sexp): forall e1 e2 e3 x,
    refltrans R e2 e3 -> refltrans (ctx R) (n_sub e2 x e1) (n_sub e3 x e1).
Proof.
  intros. induction H.
  - apply refl.
  - apply refltrans_composition with (n_sub b x e1).
    -- apply rtrans with (n_sub b x e1).
       --- apply step_sub_left. apply step_redex_R. assumption.
       --- apply refl.
    -- assumption.
Qed.

(*Lemma 4 in Nakazawa*)
Lemma pure_pix: forall e1 x e2, pure e1 -> refltrans (ctx pix) (n_sub e1 x e2) (m_subst e2 x e1).
Proof.
  induction e1.
  - intros. case (x == x0).
    -- intros; subst. apply rtrans with e2.
       --- apply step_redex_R. apply step_var.
       --- unfold m_subst. simpl. destruct (x0 == x0).
           + apply refl.
           + contradiction.
    -- intros. apply rtrans with (n_var x).
       --- apply step_redex_R. apply step_gc. assumption.
       --- unfold m_subst. simpl. destruct (x0 == x).
           + symmetry in e. contradiction.
           + apply refl.
  - intros. inversion H; subst. specialize (IHe1 x0 e2).
    apply IHe1 in H1. unfold m_subst in H1; unfold m_subst.
    case (x == x0).
    -- intros; subst. apply rtrans with (n_abs x0 e1).
       --- apply step_redex_R. apply step_abs1.
       --- simpl. case (x0 == x0).
           + intros. apply refl.
           + intros; contradiction.
    -- intros. apply rtrans with (n_abs x (n_sub e1 x0 e2)).
       --- apply step_redex_R. apply step_abs2. assumption.
       --- simpl. default_simp.
             apply refltrans_composition with (n_abs x (subst_rec (size e1) e1 e2 x0)).
             ++ apply refltrans_abs. assumption.
             ++ apply rtrans with (n_abs x1 (subst_rec (size e1) (swap x x1 e1) e2 x0)).
                +++ apply step_aeq. case (x == x1); intros; subst.
                    * rewrite swap_id. apply aeq_refl.
                    * apply aeq_abs_diff.
                      ** assumption.
                      ** admit.
                      ** admit.
                +++ apply refl.
  - intros.
    apply refltrans_composition with (n_app (m_subst e2 x e1_1) (m_subst e2 x e1_2)).
    -- apply rtrans with (n_app (n_sub e1_1 x e2) (n_sub e1_2 x e2)).
       --- apply step_redex_R. apply step_app.
       --- inversion H; subst.
           specialize (IHe1_1 x e2).
           specialize (IHe1_2 x e2).
           apply IHe1_1 in H2; clear IHe1_1.
           apply IHe1_2 in H3; clear IHe1_2. apply refltrans_app3.
           + assumption.
           + assumption.
    -- apply refltrans_composition with (m_subst e2 x (n_app e1_1 e1_2)).
       --- unfold m_subst. simpl. pose proof subst_size.
           pose proof H0.
           specialize (H0 (size e1_1 + size e1_2) e2 x e1_1).
           specialize (H1 (size e1_1 + size e1_2) e2 x e1_2).
           assert (size e1_1 <= size e1_1 + size e1_2). {
             apply le_plus_l.
           }
           assert (size e1_2 <= size e1_1 + size e1_2). {
             apply le_plus_r.
           }
           apply H0 in H2; clear H0. apply H1 in H3; clear H1.
           rewrite H2; rewrite H3. apply refl.         
       --- apply refl.
  - intros. inversion H.
Admitted.

Lemma lambda_x_Z_comp_eq: Z_comp_eq lx.
Proof.
  unfold Z_comp_eq.
  exists (ctx pix), (ctx betax), P, B.
  split.
  - intros x y. split.
    + intros. unfold lx in H. admit.
    + intros. apply union_or in H. inversion H.
      ++ admit.
      ++ admit.        
  - split.
    + intros. induction H.
      ++ inversion H.
         +++ simpl. unfold m_subst. simpl. default_simp.
         +++ simpl. unfold m_subst. simpl. default_simp. admit.
         +++ simpl. unfold m_subst. simpl. admit.
         +++ simpl. unfold m_subst. simpl. admit.
         +++ simpl. unfold m_subst. simpl. admit.
         +++ simpl. unfold m_subst. simpl. admit.
      ++ admit.
      ++ admit.
      ++ admit.
      ++ admit.
      ++ admit.
    ++ admit.
    + split.
      * admit.
      * split.
        ** admit.
        ** unfold f_is_weak_Z. admit.
Admitted.
  
Theorem lambda_x_is_confluent: Confl lx.
Proof.
  apply Z_prop_implies_Confl.
  apply Z_comp_eq_implies_Z_prop.
  apply lambda_x_Z_comp_eq.
Qed.
