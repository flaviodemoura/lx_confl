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
       --- repeat rewrite swap_id. apply aeq_refl.
       --- induction t1.
           + simpl. unfold swap_var. default_simp.
             ++ repeat rewrite subst_eq_var. assumption.
             ++ repeat rewrite subst_neq_var.
                +++ simpl. unfold swap_var. default_simp.
                +++ assumption.
                +++ assumption.
             ++ repeat rewrite subst_neq_var.
                +++ simpl. unfold swap_var. default_simp.
                +++ apply aux_not_equal; assumption.
                +++ apply aux_not_equal; assumption.
           + simpl. unfold swap_var. default_simp.
             ++ repeat rewrite subst_abs. default_simp.
                unfold swap_var. default_simp. unfold swap_var in IHt1.
                default_simp.
             ++ repeat rewrite subst_abs. default_simp.
                unfold swap_var. default_simp.
                +++ case (x0 == y); intros; subst.
                    * apply aeq_abs_same. admit.
                    * apply aeq_abs_diff.
                      ** assumption.
                      ** admit.
                      ** admit.
                +++ repeat rewrite swap_id. 
                    case (x == x0); intros; subst.
                    * repeat rewrite swap_id. apply aeq_abs_same.
                      apply IHt0. unfold swap_var in IHt1.
                      default_simp. admit.
                    * admit.
                +++ case (x0 == x1); intros; subst.
                    * apply aeq_abs_same. admit.
                    * apply aeq_abs_diff.
                      ** assumption.
                      ** admit.
                      ** admit.
              ++ repeat rewrite subst_abs. default_simp.
                unfold swap_var. default_simp.
                +++ case (x1 == y); intros; subst.
                    * apply aeq_abs_same. admit.
                    * apply aeq_abs_diff.
                      ** assumption.
                      ** admit.
                      ** admit.
                +++ repeat rewrite swap_id. 
                    case (x == x1); intros; subst.
                    * repeat rewrite swap_id. apply aeq_abs_same.
                      admit.
                    * admit.
                +++ case (x1 == x2); intros; subst.
                    * apply aeq_abs_same. admit.
                    * apply aeq_abs_diff.
                      ** assumption.
                      ** admit.
                      ** admit.
           + simpl. rewrite subst_app. apply aeq_app.
             ++ unfold m_subst in IHt1_1.
                assert (size (P t1_1) <= (size (P t1_1) + size (P t1_2))). {
                  apply le_plus_l.
      }
                apply subst_size with (size (P t1_1) + size (P t1_2)) (P t2) x (P t1_1) in H. rewrite H. apply IHt1_1. simpl in IHt1.
                admit.
             ++ unfold m_subst in IHt1_2.
                assert (size (P t1_2) <= (size (P t1_1) + size (P t1_2))). {
                  apply le_plus_r.
      }
                apply subst_size with (size (P t1_1) + size (P t1_2)) (P t2) x (P t1_2) in H. rewrite H. apply IHt1_2. simpl in IHt2.
                admit. 
           + simpl. unfold swap_var. default_simp.
             ++ admit.
             ++ admit.
             ++ admit.
    -- induction t1.
       --- simpl. unfold swap_var. default_simp.
           + admit.
           + repeat rewrite subst_eq_var. assumption.
           + admit.
       --- simpl. unfold swap_var. default_simp.
           + unfold swap_var in IHt1. default_simp.
             repeat rewrite subst_abs. default_simp.
             unfold swap_var. default_simp.
             ++ rewrite swap_id. admit.
             ++ admit.
             ++ admit.
           + unfold swap_var in IHt1. default_simp.
             repeat rewrite subst_abs. default_simp.
             unfold swap_var. default_simp.
           + unfold swap_var in IHt1. default_simp.
             repeat rewrite subst_abs. default_simp.
             unfold swap_var. default_simp.
             ++ admit.
             ++ admit.
             ++ admit.
       --- simpl in IHt1. simpl. admit.
       --- admit.    


    -- admit.
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
  - simpl. induction t1.
    -- simpl. simpl in IHaeq1. inversion IHaeq1; subst.
       case (x == x0). intros; subst.
       --- repeat rewrite subst_eq_var. assumption.
       --- admit.
    -- simpl. simpl in IHaeq1.
       unfold m_subst; unfold m_subst in IHt1.
       simpl. default_simp.
       --- admit.
       --- admit.
    -- simpl. simpl in IHaeq1.
       unfold m_subst; unfold m_subst in IHt1_1; unfold m_subst in IHt1_2.
       simpl. admit.
    -- simpl. admit.
  - admit.
Admitted.

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

Lemma double_P: forall t, P (P t) = P t.
Proof.
  intros; induction t.
  - simpl. reflexivity.
  - simpl. rewrite IHt. reflexivity.
  - simpl. rewrite IHt1; rewrite IHt2. reflexivity.
  - admit.
Admitted.
(**)

Lemma pi_P: forall t1 t2, refltrans (ctx pix) t1 t2 -> aeq (P t1) (P t2).
Proof.
  intros t1 t2 H. induction H.
  - apply aeq_refl.
  - apply aeq_trans with (P b).
    -- induction H.
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
             ++ simpl. inversion H6; subst.
                +++ inversion H2; subst.
                    * unfold m_subst. simpl. default_simp.
                      apply aeq_abs_same.
                      apply aeq_trans with t0 e0 t3 in H5.
                      *** apply aeq_P in H5; assumption.
                      *** assumption.
                    * unfold m_subst. simpl. default_simp.
                      apply aeq_abs_diff.
                      ** assumption.
                      ** apply notin_P. assumption.
                      ** apply aeq_trans with t0 e0 (swap y0 y t3) in H5.
                         *** apply aeq_P in H5.
                             pose proof aeq_swap_P.
                             specialize (H3 y0 y t3).
                             apply aeq_trans with (P t0) (P (swap y0 y t3)) (swap y0 y (P t3)) in H5.
                         **** assumption.
                         **** assumption.
                         *** assumption.
                +++ simpl. unfold m_subst. simpl. default_simp.
                    inversion H2; subst.
                    * simpl. case (x0 == y); intros; subst.
                      ** apply aeq_abs_same.
                         rewrite swap_symmetric in H10.
                         apply aeq_swap1 with t0 (swap x y e0) x y in H10.
                         rewrite swap_involutive in H10.
                         apply aeq_trans with (swap x y t0) e0 t3 in H10.
                         *** apply aeq_P in H10.
                             pose proof aeq_swap_P.
                             specialize (H3 x y t0).
                             apply aeq_sym in H3.
                             apply aeq_sym in H10.
                             apply aeq_trans with (P t3) (P (swap x y t0)) (swap x y (P t0)) in H10.
                         **** pose proof swap_size_eq. 
                              specialize (H4 x y (P t0)).
                              rewrite <- H4.
                              pose proof subst_fresh_eq_aux.
                              specialize (H7 (size (swap x y (P t0))) y (swap x y (P t0)) (P t2)).
                              unfold m_subst in H7.
                              assert (size (swap x y (P t0)) <= size (swap x y (P t0))). {
                                default_simp.
                     }
                              apply H7 in H12; clear H7.
                              apply aeq_sym in H12.
                              apply aeq_trans with (P t3) (swap x y (P t0)) (subst_rec (size (swap x y (P t0))) 
             (swap x y (P t0)) (P t2) y) in H10.
                         ***** apply aeq_sym. assumption.
                         ***** assumption.
                         ***** apply notin_union_2 in n.
                               apply notin_union_2 in n.
                               apply notin_singleton_1 in n.
                               contradiction. 
                         **** apply aeq_sym. assumption.
                         *** assumption.
                      ** apply aeq_abs_diff.
                         *** assumption.
                         *** admit.
                         *** apply aeq_swap1 with e0 t3 y x0 in H11.
                             admit.
                    * simpl. case (x0 == y0); intros; subst.
                      ** apply aeq_abs_same.
                         apply aeq_swap1 with t0 (swap y x e0) y x in H10.
                         rewrite swap_involutive in H10.
                         apply aeq_trans with (swap y x t0) e0 (swap y0 y t3) in H10.
                         *** apply aeq_swap1 with (swap y x t0) (swap y0 y t3) y0 y in H10.
                             rewrite swap_involutive in H10.
                             apply aeq_P in H10.
                             assert ((P (swap y0 y (swap y x t0)) = (swap y0 y (swap y x (P t0))))). admit. (*esta definido com aeq nao como igualdade sintatica*)
                             rewrite H3 in H10.
                             assert (swap y x (P t0) = (swap x y (P t0))). apply swap_symmetric; reflexivity.
                             rewrite H4 in H10.
                             assert ((swap y0 y (swap x y (P t0))) = (swap y y0 (swap x y (P t0)))). apply swap_symmetric; reflexivity.
                             rewrite H12 in H10.
                             rewrite swap_comp in H10.
                             pose proof subst_fresh_eq_aux.
                             specialize (H14 (size (swap x y0 (P t0))) y (swap x y0 (P t0)) (P t2)).
                             pose proof swap_size_eq.
                             specialize (H15 x y0 (P t0)).
                             rewrite <- H15.
                             assert (size (swap x y0 (P t0)) <= size (swap x y0 (P t0))). default_simp.
                             apply H14 in H16; clear H14.
                             unfold m_subst in H16.
                             apply aeq_sym in H10.
                             apply aeq_sym in H16.
                             apply aeq_sym.
                             apply aeq_trans with (P t3) (swap x y0 (P t0)) (subst_rec (size (swap x y0 (P t0))) (swap x y0 (P t0)) (P t2) y) in H10.
                         **** assumption.
                         **** assumption.
                         **** admit.

                         *** assumption.
                      ** apply aeq_abs_diff.
                         *** assumption.
                         *** admit.
                         *** admit.    
             ++ simpl. admit.
           + simpl. inversion H2; subst.
             +++ apply aeq_P in H. apply aeq_P in H2.
                 simpl in H2. simpl in H.
                 unfold m_subst in H; unfold m_subst in H2.
                 simpl in H. default_simp.
                 case (x == x0); intros; subst.
                 * rewrite swap_id in H.
                   apply aeq_trans with (P e1) (n_abs x0 (subst_rec (size (P e0)) (P e0) (P e5) y)) (n_abs x0 (P t2)) in H.
                   ** assumption.
                   ** assumption.
                 * pose proof subst_fresh_eq.
                   unfold m_subst in H4. inversion H7; subst.
                   ** simpl. simpl in H2. admit.
                   ** simpl. simpl in H2. admit. (*Igual a de cima*)
             +++ simpl. apply aeq_P in H9.
                 assert (P (swap y0 x t2) = swap y0 x (P t2)).
                 admit.
                 rewrite H4 in H9. simpl in H9.
                 apply aeq_P in H. simpl in H.
                 apply notin_P in H7. admit.
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
Admitted.      
  (*- induction H0.
    -- inversion H; subst.
       --- apply aeq_nvar_1 in H4; subst.
           simpl.
           unfold m_subst.
           simpl.
           destruct (y == y).
           ---- apply aeq_P.
                apply aeq_trans with e; assumption.
           ---- contradiction.
       --- replace (swap y x (n_var y)) with (n_var x) in H8.
           ---- apply aeq_nvar_1 in H8; subst.
                simpl.
                unfold m_subst.
                simpl.
                destruct (x == x).
                ----- apply aeq_P.
                      apply aeq_trans with e; assumption.
                ----- contradiction.
           ---- simpl.
                unfold swap_var.
                destruct (y == y).
                ----- reflexivity.
                ----- contradiction.
    -- apply aeq_P in H. simpl in H. unfold m_subst in H.
       simpl in H. case (y == x) in H.
       --- symmetry in e0; contradiction.
       --- apply aeq_trans with (n_var x).
           ---- assumption.
           ---- apply aeq_P in H1. simpl in H1. assumption.
    -- apply aeq_P in H. simpl in H. unfold m_subst in H.
       simpl in H. case (y == y) in H.
       --- apply aeq_P in H1. simpl in H1. pose proof aeq_trans.
           specialize (H0 (P e1) (n_abs y (P e0)) (P e4)).
           apply H0 in H.
           ---- assumption.
           ---- apply H0 in H.
                ----- assumption.
                ----- apply H1.
       --- contradiction.
    -- apply aeq_P in H. simpl in H. unfold m_subst in H.
       simpl in H. case (y == x) in H.
       --- symmetry in e; contradiction.
       --- destruct (atom_fresh
             (Metatheory.union (fv_nom (P e2))
                (Metatheory.union (remove x (fv_nom (P e0)))
                                  (singleton y)))).
           apply aeq_trans with (n_abs x0
                                       (subst_rec (size (P e0)) (swap x x0 (P e0)) (P e2) y)).
           ---- assumption.
           ---- apply aeq_P in H1. simpl in H1.
                unfold m_subst in H1. simpl in H1. admit.
    -- apply aeq_P in H. simpl in H. unfold m_subst in H.
       simpl in H.
       apply aeq_P in H1. simpl in H1. unfold m_subst in H1.
       simpl in H1. pose proof subst_size; pose proof H0.
       specialize (H0 (size (P e0) + size (P e2)) (P e3) y (P e0)).
       specialize (H2 (size (P e0) + size (P e2)) (P e3) y (P e2)).
       pose proof le_plus_l. pose proof le_plus_r.
       specialize (H3 (size (P e0)) (size (P e2))).
       specialize (H4 (size (P e0)) (size (P e2))).
       apply H0 in H3; clear H0. apply H2 in H4; clear H2.
       rewrite H3 in H; clear H3. rewrite H4 in H; clear H4.
       apply aeq_trans with (n_app (subst_rec (size (P e0)) (P e0) (P e3) y)
                                   (subst_rec (size (P e2)) (P e2) (P e3) y)).
       --- assumption.
       --- assumption.
  - simpl. apply aeq_abs_same. assumption.
  - simpl. apply aeq_app.
    -- assumption.
    -- apply aeq_refl.
  - simpl. apply aeq_app.
    -- apply aeq_refl.
    -- assumption.
  - admit.
  - admit.
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

(*Lemma refltrans_aeq (R: Rel n_sexp): forall a b,
    aeq a b -> refltrans (ctx R) a b.
Admitted.*)

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
       --- apply step_redex_R. apply step_abs2.
           + assumption.
       --- simpl. case (x0 == x).
           + intro Hneq; symmetry in Hneq; contradiction.
           + intros. destruct (atom_fresh
         (Metatheory.union (fv_nom e2)
            (Metatheory.union (remove x (fv_nom e1))
                              (singleton x0)))).
             apply refltrans_composition with (n_abs x (subst_rec (size e1) e1 e2 x0)).
             ++ apply refltrans_abs. assumption.
             ++ apply rtrans with (n_abs x1 (subst_rec (size e1) (swap x x1 e1) e2 x0)).
                +++ admit.
                  (*assert (aeq (n_abs x (subst_rec (size e1) e1 e2 x0))
                                (n_abs x1 (subst_rec (size e1) (swap x x1 e1) e2 x0))). {
                      apply aeq_abs_diff.
                      - admit.
                      - pose proof n1.
                        apply notin_union_2 in n1.
                        apply notin_union_1 in n1.
                        apply notin_remove_1 in n1.
                        inversion n1; subst.
                        -- admit.
                        -- pose proof fv_nom_abs_subst_aux.
                           specialize (H3 e1 e2 x0).
                   }*)
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

    (*inversion H.
      ++ subst. inversion H0.
         +++ simpl. unfold m_subst. simpl. case (y == y).
         ++++ intros; reflexivity.
         ++++ intros; contradiction.

         +++ simpl. unfold m_subst. simpl. case (y == x).
         ++++ intros; subst. contradiction.
         ++++ intros; reflexivity.

         +++ simpl. unfold m_subst. simpl. case (y == y).
         ++++ intros; reflexivity.
         ++++ intros; contradiction.

         +++ simpl. unfold m_subst. simpl. case (y == x).
         ++++ intros; subst. contradiction.
         ++++ intros. destruct  (atom_fresh
       (Metatheory.union (fv_nom (P e2))
          (Metatheory.union (remove x (fv_nom (P e1)))
                            (singleton y)))).
              admit.

         +++ simpl. unfold m_subst. simpl.
             assert (size (P e1) <= size (P e1) + size (P e2)). {
               apply le_plus_l.
             }
             assert (size (P e2) <= size (P e1) + size (P e2)). {
               apply le_plus_r.
             }
             pose proof subst_size. pose proof H5.
             specialize (H5 (size (P e1) + size (P e2)) (P e3) y (P e1)).
             specialize (H6 (size (P e1) + size (P e2)) (P e3) y (P e2)).
             apply H5 in H3; clear H5; apply H6 in H4; clear H6.
             rewrite H3; rewrite H4. reflexivity.*)


             
      (*++ subst. inversion H0.
         +++ simpl. unfold m_subst. simpl. case (y == y).
         ++++ intros; reflexivity.
         ++++ intros; contradiction.

         +++ simpl. unfold m_subst. simpl. case (y == x).
         ++++ intros; subst. contradiction.
         ++++ intros; reflexivity.

         +++ simpl. unfold m_subst. simpl. case (y == y).
         ++++ intros; reflexivity.
         ++++ intros; contradiction.

         +++ simpl. unfold m_subst. simpl. case (y == x).
         ++++ intros; subst. contradiction.
         ++++ intros. destruct  (atom_fresh
       (Metatheory.union (fv_nom (P e2))
          (Metatheory.union (remove x (fv_nom (P e1)))
                            (singleton y)))).
              admit.

         +++ simpl. unfold m_subst. simpl.
             assert (size (P e1) <= size (P e1) + size (P e2)). {
               apply le_plus_l.
             }
             assert (size (P e2) <= size (P e1) + size (P e2)). {
               apply le_plus_r.
             }
             pose proof subst_size. pose proof H5.
             specialize (H5 (size (P e1) + size (P e2)) (P e3) y (P e1)).
             specialize (H6 (size (P e1) + size (P e2)) (P e3) y (P e2)).
             apply H5 in H3; clear H5; apply H6 in H4; clear H6.
             rewrite H3; rewrite H4. reflexivity.

      ++ subst. simpl. inversion H0.
         +++ subst. inversion H1.
         ++++ subst. simpl. unfold m_subst; simpl. case (y == y).
         +++++ intros; reflexivity.
         +++++ intros; contradiction.
         ++++ simpl. unfold m_subst. simpl. case (y == x0).
         +++++ intros. subst; contradiction.
         +++++ intros; reflexivity.
         ++++ simpl. unfold m_subst. simpl. case (y == y).
         +++++ intros; reflexivity.
         +++++ intros; contradiction.
         ++++ simpl. unfold m_subst. simpl. case (y == x0).
         +++++ intros. symmetry in e0; contradiction.
         +++++ intros. destruct (atom_fresh
         (Metatheory.union (fv_nom (P e2))
            (Metatheory.union (remove x0 (fv_nom (P e1)))
                              (singleton y)))). admit.
         ++++ simpl. unfold m_subst. simpl.
              assert (size (P e1) <= size (P e1) + size (P e2)). {
               apply le_plus_l.
             }
             assert (size (P e2) <= size (P e1) + size (P e2)). {
               apply le_plus_r.
             }
             pose proof subst_size. pose proof H6.
             specialize (H6 (size (P e1) + size (P e2)) (P e3) y (P e1)).
             specialize (H7 (size (P e1) + size (P e2)) (P e3) y (P e2)).
             apply H6 in H4; clear H6; apply H7 in H5; clear H7.
             rewrite H4; rewrite H5. reflexivity.

        +++ simpl. subst. inversion H1.
        ++++ subst.*)
        


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
