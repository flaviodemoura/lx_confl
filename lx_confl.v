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

(**
Lemma pi_P: forall t1 t2, ctx pix t1 t2 -> P t1 = P t2.

\x. t = \y. (x y)t
*)

Lemma fv_nom_subst_rec: forall t1 t2 x n, fv_nom (subst_rec (size n) t1 t2 x) = (remove x (fv_nom t1)) `union` (fv_nom t2).
Proof.
  Admitted.

Lemma swap_m_subst: forall t1 t2 x1 x2 y, (swap x1 x2 (m_subst t1 y t2)) = (m_subst  (swap x1 x2 t1) (swap_var x1 x2 y) (swap x1 x2 t2)).
Proof.
Admitted.
  
Lemma pi_P: forall t1 t2, ctx pix t1 t2 -> aeq (P t1) (P t2).
Proof.
  induction 1.
  - inversion H; subst.
    -- simpl. unfold m_subst. simpl. case (y == y).
       --- intros. apply aeq_refl.
       --- contradiction.
    -- simpl. unfold m_subst. simpl. case (y == x).
       --- intros. symmetry in e0. contradiction.
       --- intros. apply aeq_refl.
    -- simpl. unfold m_subst. simpl. case (y == y).
       --- intros. apply aeq_refl.
       --- contradiction.
    -- simpl. unfold m_subst. simpl. case (y == x).
       --- intros. symmetry in e. contradiction.
       --- intros. destruct (atom_fresh
           (Metatheory.union (fv_nom (P e3))
                             (Metatheory.union (remove x (fv_nom (P e0))) (singleton y)))). apply notin_union_2 in n0.
           apply notin_union_1 in n0. apply notin_remove_1 in n0.
           inversion n0.
           + subst. rewrite swap_id. apply aeq_refl.
           + clear n0.
             apply aeq_abs_diff.
             * admit.
             * rewrite fv_nom_subst_rec.
               admit.
             * simpl.
Admitted.
             



(*




                        
    -- subst. simpl. unfold m_subst. simpl.
       assert (subst_rec (size (P e0) + size (P e3)) (P e0) (P e4) y = subst_rec (size (P e0)) (P e0) (P e4) y). {
         apply subst_size. apply le_plus_l.       
       }
       assert ((subst_rec (size (P e0) + size (P e3)) (P e3) (P e4) y = subst_rec (size (P e3)) (P e3) (P e4) y)). {
         apply subst_size. apply le_plus_r.
       }
       rewrite H0; rewrite H1. apply aeq_refl.
  - inversion H.
    -- subst. simpl. simpl in IHstep. apply aeq_abs_same. apply IHstep.
    -- subst. simpl. simpl in IHstep. apply aeq_abs_same. apply IHstep.
    -- subst. simpl. simpl in IHstep. apply aeq_abs_same. apply IHstep.
    -- subst. simpl. simpl in IHstep. apply aeq_abs_same. apply IHstep.
    -- subst. simpl. simpl in IHstep. apply aeq_abs_same. apply IHstep.
    -- subst. simpl. simpl in IHstep. apply aeq_abs_same. apply IHstep.
  - inversion H.
    -- subst. simpl. simpl in IHstep. apply aeq_app.
       --- apply IHstep.
       --- apply aeq_refl.
    -- subst. simpl. simpl in IHstep. apply aeq_app.
       --- apply IHstep.
       --- apply aeq_refl.
    -- subst. simpl. simpl in IHstep. apply aeq_app.
       --- apply IHstep.
       --- apply aeq_refl.
    -- subst. simpl. simpl in IHstep. apply aeq_app.
       --- apply IHstep.
       --- apply aeq_refl.
    -- subst. simpl. simpl in IHstep. apply aeq_app.
       --- apply IHstep.
       --- apply aeq_refl.
    -- subst. simpl. simpl in IHstep. apply aeq_app.
       --- apply IHstep.
       --- apply aeq_refl.
  - inversion H.
    -- subst. simpl. simpl in IHstep. apply aeq_app.
       --- apply aeq_refl.
       --- apply IHstep.
    -- subst. simpl. simpl in IHstep. apply aeq_app.
       --- apply aeq_refl.
       --- apply IHstep.
    -- subst. simpl. simpl in IHstep. apply aeq_app.
       --- apply aeq_refl.
       --- apply IHstep.
    -- subst. simpl. simpl in IHstep. apply aeq_app.
       --- apply aeq_refl.
       --- apply IHstep.
    -- subst. simpl. simpl in IHstep. apply aeq_app.
       --- apply aeq_refl.
       --- apply IHstep.
    -- subst. simpl. simpl in IHstep. apply aeq_app.
       --- apply aeq_refl.
       --- apply IHstep.
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
           specialize (H3 x0 x1 n). apply H3 in H0.
           Admitted.
(*           specialize (H2 (P e2) x (swap x0 x1 n)).
           apply H2 in H0. unfold m_subst in H0.
           + rewrite swap_size_eq in H0. assumption.
           + assumption.
    -- simpl. apply pure_app.
       --- inversion IHe1. apply IHn1 in H1. pose proof le_plus_l.
           specialize (H3 (size n1) (size n2)).
           pose proof subst_size.
           specialize (H4 (size n1 + size n2) (P e2) x n1).
           apply H4 in H3. rewrite H3. assumption.
       --- inversion IHe1. apply IHn2 in H2. pose proof le_plus_r.
           specialize (H3 (size n1) (size n2)).
           pose proof subst_size.
           specialize (H4 (size n1 + size n2) (P e2) x n2).
           apply H4 in H3. rewrite H3. assumption.
    -- simpl. case (x == x0).
       --- intros. assumption.
       --- intros. destruct (atom_fresh
           (Metatheory.union (fv_nom (P e2))
                             (Metatheory.union (Metatheory.union (remove x0 (fv_nom n1)) (fv_nom n2)) (singleton x)))). inversion IHe1.
Qed. *)

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

  Lemma pure_pix: forall e1 x e2, pure e1 -> refltrans (ctx pix) (n_sub e1 x e2) (m_subst e2 x e1).
Proof.
  induction e1.
  - intros. case (x == x0).
    -- intros; subst. apply rtrans with e2.
       --- apply step_redex. apply step_var.
       --- unfold m_subst. simpl. destruct (x0 == x0).
           + apply refl.
           + contradiction.
    -- intros. apply rtrans with (n_var x).
       --- apply step_redex. apply step_gc. assumption.
       --- unfold m_subst. simpl. destruct (x0 == x).
           + symmetry in e. contradiction.
           + apply refl.
  - intros. inversion H. subst. specialize (IHe1 x0 e2).
    apply IHe1 in H1. unfold m_subst in H1; unfold m_subst.
    inversion H1.
    -- subst. simpl. default_simp.
       --- admit.
Admitted.

Lemma lambda_x_Z_comp_eq: Z_comp_eq lx.
Proof.
  unfold Z_comp_eq.
  exists (ctx pix), (ctx betax), P, B.
  split.
  - intros x y. split.
    + intros. inversion H.
      ++ subst. apply union_right. assumption.
      ++ subst. apply union_left. assumption.
    + intros. apply union_or in H. inversion H.
      ++ apply x_ctx_rule. assumption.
      ++ apply b_ctx_rule. assumption.        
  - split.
    + intros. induction H.
      ++ inversion H.
         +++ simpl. unfold m_subst. simpl. default_simp.
         +++ simpl. unfold m_subst. simpl. default_simp.
         +++ simpl. unfold m_subst. simpl. default_simp.
         +++ simpl. unfold m_subst. simpl. default_simp.
         ++++ inversion H.
         +++++ subst. apply notin_union_2 in n.
               apply notin_union_1 in n.
               apply notin_remove_1 in n. inversion n.
         ++++++ contradiction.
         ++++++ contradiction.
         +++++ subst. apply notin_union_2 in n.
               apply notin_union_1 in n.
               apply notin_remove_1 in n. inversion n.
         ++++++ symmetry in H1; assumption.
         ++++++ admit.
         ++++ case (x == x0).
         +++++ intros. subst. rewrite swap_id. reflexivity.
         +++++ intros. apply notin_union_2 in n.
               apply notin_union_1 in n.
               apply notin_remove_1 in n. inversion n.
         ++++++ contradiction.
         ++++++ admit.

         +++ admit.
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
