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

Lemma aeq_P: forall t1 t2, aeq t1 t2 -> aeq (P t1) (P t2).
Proof.
  intros t1 t2 H.
  induction H.
  - simpl.
    apply aeq_refl.
  - simpl; apply aeq_abs_same. assumption.
  - simpl. apply aeq_abs_diff.
    -- assumption.
    -- admit.           
    -- admit.
  - simpl. apply aeq_app.
    -- assumption.
    -- assumption.
  - admit.
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

(**)

Lemma pi_P: forall t1 t2, refltrans (ctx pix) t1 t2 -> aeq (P t1) (P t2).
Proof.
  intros t1 t2 H. induction H.
  - apply aeq_refl.
  - apply aeq_trans with (P b).
    -- induction H.
       --- inversion H1; subst.
           + apply aeq_P in H. simpl in H.
             apply aeq_P in H2.
             assert (aeq (m_subst (P e3) y (n_var y)) (P e3)). {
               admit.
             }
             admit.
           + admit.
           + apply aeq_P in H. simpl in H.
             assert (aeq (m_subst (P e5) y (n_abs y (P e0))) (n_abs y (P e0))). {
             admit.  
             }
             admit.
           + admit.
           + admit.
       --- admit.
       --- admit.
       --- admit.
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
    refltrans R e2 e3 -> refltrans R (n_app e1 e2) (n_app e1 e3).
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
    + intros. inversion H.
      ++ subst. apply union_right. admit.
      ++ subst. apply union_left. admit.
      ++ subst. admit.
      ++ subst. admit.
      ++ subst. admit.
      ++ subst. admit.
    + intros. apply union_or in H. inversion H.
      ++ admit.
      ++ admit.        
  - split.
    + intros. induction H.
      ++ inversion H.
         +++ simpl. unfold m_subst. simpl. default_simp.
         +++ simpl. unfold m_subst. simpl. default_simp.
         +++ simpl. unfold m_subst. simpl. default_simp.
         +++ simpl. unfold m_subst. simpl. default_simp.
         +++ simpl. unfold m_subst. simpl. default_simp. admit.
         +++ simpl. unfold m_subst. simpl. default_simp. admit.
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
