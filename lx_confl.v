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

Lemma size_m_subst: forall t1 t2 x,
    size (m_subst t2 x t1) = size (n_sub t1 x t2).
Proof.
  induction t1.
  - intros. simpl. unfold m_subst. simpl. case (x == x0)

Lemma subst_swap_reduction: forall u t x y z,
    (swap x y (m_subst u z t)) = (m_subst (swap x y u) (swap_var x y z) (swap x y t)).
Proof.
  intros. induction t.
  - unfold m_subst. simpl in *; unfold swap_var. default_simp.
  - unfold m_subst. simpl in *; unfold swap_var. admit.
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
    -- admit.
Admitted.

Lemma aeq_size: forall t1 t2,
    aeq t1 t2 -> size t1 = size t2.
Proof.
  intros. induction H.
  - simpl. reflexivity.
  - simpl. rewrite IHaeq. reflexivity.
  - simpl. rewrite IHaeq. rewrite swap_size_eq. reflexivity.
  - simpl. rewrite IHaeq1; rewrite IHaeq2. reflexivity.
  - simpl. rewrite IHaeq1; rewrite IHaeq2. reflexivity.
  - simpl. rewrite swap_size_eq in IHaeq2.
    rewrite IHaeq1; rewrite IHaeq2. reflexivity.
Qed.

Lemma aeq_m_subst_1: forall t1 t2 x t3,
    aeq t1 t2 -> aeq (m_subst t3 x t1) (m_subst t3 x t2).
Proof.
  intros. induction H.
  - unfold m_subst. simpl. default_simp. apply aeq_refl.
  - unfold m_subst. simpl. default_simp.
    case (x1 == x2); intros; subst.
    -- apply aeq_abs_same. unfold m_subst in IHaeq.
       pose proof H. apply aeq_size in H0. rewrite H0.
       apply aeq_swap1 with t1 t2 x0 x2 in H. admit.
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

Lemma aeq_subst: forall t1 t1' x t2 t2',
    aeq t1 t1' -> aeq t2 t2' -> aeq (m_subst t1 x t2) (m_subst t1' x t2').
Proof.
  intros.
  apply aeq_trans with (m_subst t1 x t2').
  - apply aeq_m_subst_1. assumption.
  - apply aeq_m_subst_2. assumption.
Qed.

Lemma subst_notin: forall x u t,
    x `notin` fv_nom u -> x `notin` fv_nom t -> x `notin` fv_nom (m_subst u x t).
Proof.
  intros. induction t.
  - unfold m_subst; simpl. default_simp.
  - unfold m_subst; simpl. default_simp.
    unfold m_subst in IHt. apply notin_remove_1 in H0.
    inversion H0.
    -- symmetry in H1; contradiction.
    -- apply IHt in H1. case (x == x1); intros.
       --- apply notin_remove_3; symmetry; assumption.
       --- apply notin_remove_2. admit.
  - unfold m_subst in *; simpl in *. apply notin_union_3.
    -- apply notin_union_1 in H0.
       assert (size t1 <= size t1 + size t2). apply le_plus_l.
       apply subst_size with (size t1 + size t2) u x t1 in H1.
       rewrite H1. apply IHt1. assumption.
    -- apply notin_union_2 in H0.
       assert (size t2 <= size t1 + size t2). apply le_plus_r.
       apply subst_size with (size t1 + size t2) u x t2 in H1.
       rewrite H1. apply IHt2. assumption.
  - unfold m_subst in *; simpl in *. default_simp.
    apply notin_union_3.
    -- case (x == x1); intros; subst.
       --- apply notin_remove_3. reflexivity.
       --- apply notin_remove_2. apply notin_union_1 in H0.
           apply notin_remove_1 in H0. inversion H0.
           + symmetry in H1; contradiction.
           + admit.
    -- apply notin_union_2 in H0.
       assert (size t2 <= size t1 + size t2). apply le_plus_r.
       apply subst_size with (size t1 + size t2) u x t2 in H1.
       rewrite H1. apply IHt2. assumption.
Admitted.

Lemma size_P: forall t, size (P t) = size t.
Proof.
  intros; induction t.
  - simpl; reflexivity.
  - simpl. rewrite IHt; reflexivity.
  - simpl. rewrite IHt1; rewrite IHt2. reflexivity.
  - simpl. unfold m_subst; simpl. admit. (*rever definição*)
Admitted.

(*t = n_app x y*)
Lemma subst_swap: forall u t x y,
    m_subst u x (swap x y t) = m_subst u y t.
Proof.
  intros. induction t.
  - simpl; unfold swap_var; unfold m_subst; simpl. default_simp.
    admit.
    (*rever definição*)
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
       --- repeat rewrite swap_id. apply aeq_subst.
           + apply aeq_refl.
           + apply aeq_refl.
       --- pose proof subst_swap_reduction.
           specialize (H (P t2) (P t1) x y x). rewrite H.
           unfold swap_var; unfold swap_var in H; default_simp.
           apply aeq_subst.
           + assumption.
           + assumption. 
    -- pose proof subst_swap_reduction.
       assert ((swap x y (m_subst (P t2) y (P t1)) = (swap y x (m_subst (P t2) y (P t1))))). rewrite swap_symmetric; reflexivity.
       rewrite H0.
       specialize (H (P t2) (P t1) y x y). rewrite H.
       unfold swap_var; unfold swap_var in H; default_simp.
       apply aeq_subst.
       --- apply aeq_sym. rewrite swap_symmetric.
           apply aeq_sym. assumption.
       --- apply aeq_sym. rewrite swap_symmetric.
           apply aeq_sym. assumption.
    -- pose proof subst_swap_reduction.
       specialize (H (P t2) (P t1) x y x0).
       unfold swap_var; unfold swap_var in H; default_simp.
       rewrite H. apply aeq_subst.
       --- assumption.
       --- assumption.
Qed.           

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
  - admit.
Admitted.

Lemma aeq_P: forall t1 t2, aeq t1 t2 -> aeq (P t1) (P t2).
Proof.
  intros t1 t2 H.
  induction H.
  - simpl.
    apply aeq_refl.
  - simpl; apply aeq_abs_same. assumption.
  - simpl. apply aeq_abs_diff.
    -- assumption.
    -- apply notin_P. assumption.
    -- pose proof aeq_swap_P. specialize (H2 y x t2).
       pose proof aeq_trans.
       specialize (H3 (P t1) (P (swap y x t2)) (swap y x (P t2))).
       apply H3 in IHaeq; assumption.
  - simpl. apply aeq_app.
    -- assumption.
    -- assumption.
  - simpl. apply aeq_subst.
    -- assumption.
    -- assumption.
  - simpl. pose proof subst_swap.
    specialize (H3 (P t2') (P t1') x y). rewrite <- H3.
    apply aeq_subst.
    -- assumption.
    -- rewrite swap_symmetric. pose proof aeq_swap_P.
       specialize (H4 y x t1').
       apply aeq_trans with (P t1) (P (swap y x t1')) (swap y x (P t1')) in IHaeq2.
       --- assumption.
       --- assumption.
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

(**)
    
Lemma pi_P: forall t1 t2, refltrans (ctx pix) t1 t2 -> aeq (P t1) (P t2).
Proof.
  intros t1 t2 H. induction H.
  - apply aeq_refl.
  - apply refltrans_composition with (ctx pix) a b c in H0.
    -- inversion H; subst.
       --- apply aeq_P in H1. apply aeq_trans with (P b).
           + assumption.
           + assumption.
               inversion H2; subst.
           + inversion H1; subst.
             ++ simpl. apply aeq_P in H7. simpl in H7.
                inversion H7; subst. rewrite subst_eq_var.
                apply aeq_P in H3; apply aeq_P in H9.
                apply aeq_trans with (P e3).
                +++ assumption.
                +++ apply aeq_trans with (P b).
                    * assumption.
                    * assumption.
             ++ simpl. simpl in H11. unfold swap_var in H11.
                default_simp. rewrite subst_eq_var.
                apply aeq_P in H3; apply aeq_P in H7.
                apply aeq_trans with (P e3).
                +++ assumption.
                +++ apply aeq_trans with (P b).
                    * assumption.
                    * assumption.
           + apply aeq_P in H1. simpl in H1.
             unfold m_subst in H1. simpl in H1. default_simp.
             apply aeq_trans with (n_var x).
             ++ assumption.
             ++ assumption.
           + apply aeq_P in H1. simpl in H1.
             unfold m_subst in H1. simpl in H1. default_simp.
             apply aeq_P in H3. simpl in H3.
             apply aeq_trans with (n_abs y (P e1)).
             ++ assumption.
             ++ apply aeq_trans with (P b).
                +++ assumption.
                +++ assumption.
           + apply aeq_P in H1. simpl in H1.
             unfold m_subst in H1. simpl in H1. default_simp.
             apply aeq_P in H3. simpl in H3.
             assert (n_abs x0
                           (subst_rec (size (P e1)) (swap x x0 (P e1)) (P e0) y) = n_abs x (m_subst (P e0) y (P e1))). admit.
             rewrite H5 in H1.
             apply aeq_trans with (n_abs x (m_subst (P e0) y (P e1))).
             ++ assumption.
             ++ apply aeq_trans with (P b).
                +++ assumption.
                +++ assumption.
           + apply aeq_P in H1. simpl in H1.
             unfold m_subst in H1. simpl in H1. default_simp.
             apply aeq_P in H6; apply aeq_P in H8.
             simpl in H6; simpl in H8. unfold m_subst in *.
             inversion H1; subst.
             assert (aeq t1 (P t1')). {
               apply aeq_trans with (subst_rec (size (P e1) + size (P e0)) (P e1) (P e4) y).
               ++ assumption.
               ++ assert (size (P e1) <= size (P e1) + size (P e0)).
                  apply le_plus_l.
                  pose proof subst_size.
                  specialize (H4 (size (P e1) + size (P e0)) (P e4) y (P e1)). apply H4 in H3; rewrite H3. assumption.
             }
             assert (aeq t2 (P t2')). {
               apply aeq_trans with (subst_rec (size (P e1) + size (P e0)) (P e0) (P e4) y).
               ++ assumption.
               ++ assert (size (P e0) <= size (P e1) + size (P e0)).
                  apply le_plus_r.
                  pose proof subst_size.
                  specialize (H9 (size (P e1) + size (P e0)) (P e4) y (P e0)). apply H9 in H4; rewrite H4. assumption.
             }
             assert (aeq (n_app t1 t2) (n_app (P t1') (P t2'))). {
               apply aeq_app; assumption.
             }
             apply aeq_trans with (n_app (P t1') (P t2')).
             ++ assumption.
             ++ assumption.
       --- simpl in *. inversion H1; subst.
           + apply aeq_P in H2.
             apply aeq_abs_same with x (P e) (P e') in H2.
             apply aeq_trans with (n_abs x (P e')).
             ++ assumption.
             ++ assumption.
           + inversion H3; subst.
             ++ apply aeq_P in H2. simpl in H2.
                rewrite subst_eq_var in H2.
                apply aeq_P in H4.
                apply aeq_abs_same with x (P e) (P e3) in H2.
                apply aeq_abs_same with x (P e3) (P e') in H4.
                apply aeq_trans with (n_abs x (P e')).
                +++ apply aeq_trans with (n_abs x (P e3)).
                    * assumption.
                    * assumption.
                +++ assumption.
             ++ apply aeq_P in H2. simpl in H2.
                rewrite subst_neq_var in H2.
                +++ apply aeq_P in H4. simpl in H4.
                    apply aeq_abs_same with x (P e) (n_var x0) in H2.
                    apply aeq_abs_same with x (n_var x0) (P e') in H4.
                    apply aeq_trans with (n_abs x (n_var x0)).
                    * assumption.
                    * apply aeq_trans with (n_abs x (P e')).
                      ** assumption.
                      ** assumption.
                +++ apply aux_not_equal; assumption.
             ++ apply aeq_P in H2. simpl in H2.
                rewrite subst_abs in H2.
                default_simp. apply aeq_P in H4. simpl in H4.
                apply aeq_abs_same with x (P e) (n_abs y (P e1)) in H2.
                apply aeq_abs_same with x (n_abs y (P e1)) (P e') in H4.
                apply aeq_trans with (n_abs x (n_abs y (P e1))).
                    * assumption.
                    * apply aeq_trans with (n_abs x (P e')).
                      ** assumption.
                      ** assumption.
             ++ apply aeq_P in H2. simpl in H2.
                rewrite subst_abs in H2.
                default_simp. apply aeq_P in H4. simpl in H4.
                assert (n_abs x1 (m_subst (P e0) y (swap x0 x1 (P e1))) = n_abs x0 (m_subst (P e0) y (P e1))). admit.
                rewrite H6 in H2.
                apply aeq_abs_same with x (P e) (n_abs x0 (m_subst (P e0) y (P e1))) in H2.
                apply aeq_abs_same with x (n_abs x0 (m_subst (P e0) y (P e1))) (P e') in H4.
                
                apply aeq_trans with (n_abs x (n_abs x0 (m_subst (P e0) y (P e1)))).
                    * assumption.
                    * apply aeq_trans with (n_abs x (P e')).
                      ** assumption.
                      ** assumption.
             ++ apply aeq_P in H2. simpl in H2.
                rewrite subst_app in H2. apply aeq_P in H4.
                simpl in H4.
                apply aeq_abs_same with x (P e) (n_app (m_subst (P e4) y (P e1))
            (m_subst (P e4) y (P e0))) in H2.
                apply aeq_abs_same with x (n_app (m_subst (P e4) y (P e1))
            (m_subst (P e4) y (P e0))) (P e') in H4.
                apply aeq_trans with (n_abs x
            (n_app (m_subst (P e4) y (P e1))
               (m_subst (P e4) y (P e0)))).
                    * assumption.
                    * apply aeq_trans with (n_abs x (P e')).
                      ** assumption.
                      ** assumption.
           + simpl in *. inversion H2; subst.
             ++ apply aeq_abs_same with x0 e0 e'0 in H3.
                apply aeq_abs_same with x (n_abs x0 e0) (n_abs x0 e'0) in H3.
                apply aeq_P in H3. simpl in H3.
                apply aeq_trans with (n_abs x (n_abs x0 (P e'0))).
                +++ assumption.
                +++ assumption.
             ++ inversion H4; subst.
                +++ admit.
                +++ admit.
                +++ admit.
                +++ admit.
                +++ admit.
             ++ admit.
             ++ admit.
             ++ admit.
             ++ admit.
             ++ admit.
           + admit.  
           + admit.
           + admit.
           + admit.
       --- admit.
       --- admit.
       --- admit.
       --- admit.
    -- apply rtrans with b.
       --- assumption.
       --- apply refl.
Admitted.      
(*      induction H.
       --- apply aeq_P in H. assumption.
       --- inversion H1; subst.
           + inversion H; subst.
             ++ simpl. inversion H6; subst. simpl.
                rewrite subst_eq_var.
                apply aeq_trans with t2 e3 e4 in H8.
                +++ apply aeq_P in H8. assumption.
                +++ assumption.
             ++ simpl. simpl in H10. unfold swap_var in H10.
                default_simp. rewrite subst_eq_var.
                apply aeq_trans with t2 e3 e4 in H6.
                +++ apply aeq_P in H6. assumption.
                +++ assumption.
           + inversion H; subst.
             ++ simpl. inversion H7; subst. simpl.
                rewrite subst_neq_var.
                +++ inversion H2; subst. simpl. apply aeq_refl.
                +++ apply aux_not_equal. assumption.
             ++ simpl. simpl in H11. unfold swap_var in H11.
                default_simp.
                +++ apply notin_singleton_1 in H10. contradiction.
                +++ rewrite subst_neq_var.
                    * apply aeq_refl.
                    * apply notin_singleton_1 in H10.
                      apply aux_not_equal. assumption.
           + inversion H; subst.
             ++ simpl. apply aeq_P in H6; simpl in H6.
                inversion H6; subst.
                +++ unfold m_subst; simpl. default_simp.
                    apply aeq_P in H2; simpl in H2.
                    apply aeq_sym in H2.
                    apply aeq_trans with (n_abs y (P e0)).
                    * apply aeq_abs_same; assumption.
                    * apply aeq_sym; assumption.
                +++ unfold m_subst. simpl. default_simp.
                    apply aeq_P in H2; simpl in H2.
                    apply aeq_trans with (n_abs y (P e0)).
                    * case (x0 == y); intros; subst.
                      ** repeat apply notin_union_2 in n.
                         apply notin_singleton_1 in n.
                         contradiction.
                      ** apply aeq_abs_diff.
                         *** assumption.
                         *** admit. (*aeq_abs_diff*)
                         *** admit. (*aeq_abs_diff*)
                    * assumption.
             ++ simpl. apply aeq_P in H2; simpl in H2.
                apply aeq_trans with (n_abs y (P e0)).
                +++ apply aeq_P in H; simpl in H. apply aeq_sym.
                    apply aeq_trans with (m_subst (P e5) y (n_abs y (P e0))).
                    * unfold m_subst; simpl.
                      clear H9; default_simp. apply aeq_refl.
                    * apply aeq_sym; assumption.
                +++ assumption.
           + apply aeq_P in H; apply aeq_P in H2.
             simpl in H; unfold m_subst in H; simpl in H.
             simpl in H2; unfold m_subst in H2; simpl in H2.
             default_simp. case (x == x0); intros; subst.
             ++ rewrite swap_id in H.
                apply aeq_trans with (n_abs x0 (subst_rec (size (P e0)) (P e0) (P e5) y)).
                +++ assumption.
                +++ assumption.
             ++ apply aeq_trans with (n_abs x0
           (subst_rec (size (P e0)) (swap x x0 (P e0)) (P e5) y)).
                +++ assumption.
                +++ apply aeq_sym in H2.
                    apply aeq_trans with (P e4) (n_abs x (subst_rec (size (P e0)) (P e0) (P e5) y)) (n_abs x0
       (subst_rec (size (P e0)) (swap x x0 (P e0)) (P e5) y)) in H2.
                    * apply aeq_sym; assumption.
                    * apply aeq_abs_diff.
                      ** assumption.
                      ** admit. (*aeq_abs_diff*)
                      ** admit. (*aeq_abs_diff*)                    
           + inversion H; subst.
             ++ simpl. apply aeq_P in H2. simpl in H2.
                apply aeq_P in H. simpl in H.
                unfold m_subst in H; unfold m_subst in H2.
                simpl in H.
                pose proof subst_size; pose proof subst_size.
                specialize (H3 (size (P e0) + size (P e5)) (P e6) y (P e0)).
                specialize (H4 (size (P e0) + size (P e5)) (P e6) y (P e5)).
                assert (size (P e0) <= size (P e0) + size (P e5)). {
                  apply le_plus_l.
                }
                assert (size (P e5) <= size (P e0) + size (P e5)). {
                  apply le_plus_r.
                }
                apply H3 in H5; clear H3.
                apply H4 in H7; clear H4.
                rewrite H5 in H; rewrite H7 in H.
                unfold m_subst.
                apply aeq_trans with (subst_rec (size (P t1)) (P t1) (P t2) y) (n_app (subst_rec (size (P e0)) (P e0) (P e6) y)
           (subst_rec (size (P e5)) (P e5) (P e6) y)) (P e4) in H.
                +++ assumption.
                +++ assumption.
             ++ simpl. apply aeq_P in H2. simpl in H2.
                inversion H2; subst. apply aeq_P in H.
                simpl in H. unfold m_subst in H. simpl in H.
                unfold m_subst in H2.
                pose proof subst_size; pose proof subst_size.
                specialize (H3 (size (P e0) + size (P e5)) (P e6) y (P e0)).
                specialize (H4 (size (P e0) + size (P e5)) (P e6) y (P e5)).
                assert (size (P e0) <= size (P e0) + size (P e5)). {
                  apply le_plus_l.
                }
                assert (size (P e5) <= size (P e0) + size (P e5)). {
                  apply le_plus_r.
                }
                apply H3 in H12; clear H3.
                apply H4 in H13; clear H4.
                rewrite H12 in H; rewrite H13 in H.
                rewrite H5. unfold m_subst.
                apply aeq_trans with (subst_rec (size (P t1)) (P t1) (P t2) x) (n_app (subst_rec (size (P e0)) (P e0) (P e6) y)
           (subst_rec (size (P e5)) (P e5) (P e6) y)) (P e4) in H.
                +++ assumption.
                +++ assumption.
       --- simpl. apply aeq_abs_same. simpl in IHrefltrans.
           inversion IHrefltrans; subst.
           + apply IHctx.
             ++ admit.
             ++ admit.
           + admit.

       --- admit.
       --- simpl. apply aeq_app.
           + apply aeq_refl.
           + apply IHctx.
             ++ admit.
             ++ admit.
       --- admit.
       --- admit.
     -- assumption. 
Admitted.*)

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
Admitted.

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
    -- admit.
    -- assumption.
Admitted.

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
    refltrans R e2 e3 -> refltrans R (n_sub e1 x e2) (n_sub e1 x e3).
Admitted.

Lemma refltrans_sub2 (R: Rel n_sexp): forall e1 e2 e3 x,
    refltrans R e2 e3 -> refltrans R (n_sub e1 x e2) (n_sub e1 x e3).
Admitted.

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
       --- simpl. default_simp. intros.
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
    + intros. unfold lx in H. inversion H; subst.
      ++ admit.
      ++ inversion H1; subst.
         +++ apply union_right. admit.
         +++ admit.
      ++ subst. admit.
      ++ subst. admit.
      ++ subst. admit.
      ++ subst. admit.
      ++ admit.
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
        ** Admitted.
  
Theorem lambda_x_is_confluent: Confl lx.
Proof.
  apply Z_prop_implies_Confl.
  apply Z_comp_eq_implies_Z_prop.
  apply lambda_x_Z_comp_eq.
Qed.
