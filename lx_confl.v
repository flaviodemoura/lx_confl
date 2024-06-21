Require Import lambda_es lambda_x.
Require Import ZtoConfl_nom. 

Fixpoint B (t : n_sexp) := match t with
                           | n_var x => n_var x
                           | n_abs x t1 => n_abs x (B t1)
                           | n_app t1 t2 => match t1 with
                                            | n_abs x t3 => {x := (B t2)}(B t3)
                                            | _ => n_app (B t1) (B t2)
                                            end
                           | n_sub t1 x t2 => n_sub (B t1) x (B t2)
                           end.

Fixpoint P (t : n_sexp) := match t with
                           | n_var x => n_var x
                           | n_abs x t1 => n_abs x (P t1)
                           | n_app t1 t2 => n_app (P t1) (P t2)
                           | n_sub t1 x t2 => {x := (P t2)}(P t1)
                           end.
     
Lemma notin_P: forall x t, x `notin` fv_nom t -> x `notin` fv_nom (P t).
Proof.
  intros x t Hnot. induction t.
  - simpl in *. assumption.
  - simpl in *. case (x == x0); intros; subst.
    + apply notin_remove_3; reflexivity.
    + apply notin_remove_2. apply IHt. apply notin_remove_1 in Hnot. inversion Hnot; subst.
      * contradiction.
      * assumption.
  - simpl in *. apply notin_union.
    + apply notin_union_1 in Hnot. apply IHt1; assumption.
    + apply notin_union_2 in Hnot. apply IHt2; assumption.
  - simpl in *. pose proof Hnot as H. apply notin_union_1 in Hnot. apply notin_union_2 in H. unfold m_subst. pose proof in_or_notin as H0. specialize (H0 x0 (fv_nom (P t1))). destruct H0.
    + apply fv_nom_remove.
      * apply IHt2; assumption.
      * case (x == x0); intros; subst.
        ** apply notin_remove_3; reflexivity.
        ** apply notin_remove_1 in Hnot. destruct Hnot.
           *** symmetry in H1. contradiction.
           *** apply notin_remove_2. apply IHt1. assumption.
    + apply fv_nom_remove.
      * apply IHt2; assumption.
      * case (x == x0); intros; subst.
        ** apply notin_remove_3; reflexivity.
        ** apply notin_remove_1 in Hnot. destruct Hnot.
           *** symmetry in H1. contradiction.
           *** apply notin_remove_2. apply IHt1. assumption.
Qed.

Lemma aeq_swap_P: forall t x y, (P (swap x y t)) =a (swap x y (P t)).
Proof.
  induction t.
  - intros x' y. default_simp.
  - intros x' y. simpl. apply aeq_abs_same. apply IHt.
  - intros x y. default_simp.
  - intros x' y. simpl. apply (aeq_trans _ (m_subst (swap x' y (P t2)) (vswap x' y x) (swap x' y (P t1)))).
    + apply (aeq_trans _ (m_subst (swap x' y (P t2)) (vswap x' y x) (P (swap x' y t1)))).
      * apply aeq_m_subst_in. apply IHt2.
      * apply aeq_m_subst_out. apply IHt1.
    + apply aeq_sym. apply aeq_swap_m_subst.
Qed.
(*                                                                                            
Lemma notin_swap_P_1: forall t x y z, x `notin` fv_nom (P (swap y z t)) ->  x `notin` fv_nom (swap y z(P t)).
Proof.
  induction t;intros.
  - simpl in *. assumption.
  - simpl in *. case (x0 == (swap_var y z x));intros.
    -- rewrite e. default_simp.
    -- apply (diff_remove _ _ _ n). apply (diff_remove_2 _ _ _ n) in H.
       apply IHt. assumption.
  - simpl in *. apply notin_union_3.
    -- apply notin_union_1 in H. apply IHt1. assumption.
    -- apply notin_union_2 in H. apply IHt2. assumption.
  - simpl in *. pose proof aeq_swap_m_subst.
    specialize (H0 (P t1) (P t2) y z x). apply aeq_fv_nom in H0.
    rewrite H0. pose proof in_or_notin. specialize (H1 (swap_var y z x)
    (fv_nom (swap y z (P t1)))). pose proof in_or_notin.
    specialize (H2 (swap_var y z x) (fv_nom (P (swap y z t1)))).
    destruct H1;destruct H2.
    -- apply (fv_nom_m_subst_in _ (swap y z (P t2))) in H1.
       apply (fv_nom_m_subst_in _ (P (swap y z t2))) in H2.
       rewrite H1. rewrite H2 in H. simpl in *. apply notin_union_3.
       --- apply notin_union_1 in H. case (x0 == (swap_var y z x));intros.
           ---- rewrite e. default_simp.
           ---- apply (diff_remove _ _ _ n). apply (diff_remove_2 _ _ _ n) in H.
                apply IHt1. assumption.
       --- apply notin_union_2 in H. apply IHt2. assumption.
    -- apply IHt1 in H2. default_simp.
    -- pose proof aeq_swap_P. specialize (H3 t1 y z).
       apply aeq_fv_nom in H3. rewrite H3 in H2. default_simp.
    -- apply (fv_nom_m_subst_notin _ (swap y z (P t2))) in H1.
       apply (fv_nom_m_subst_notin _ (P (swap y z t2))) in H2.
       rewrite H1. rewrite H2 in H. case (x0 == (swap_var y z x));intros.
       --- rewrite e. default_simp.
       --- apply (diff_remove _ _ _ n). apply (diff_remove_2 _ _ _ n) in H.
           apply IHt1. assumption.
Qed.

Lemma notin_swap_P_2: forall t x y z, x `notin` fv_nom (swap y z(P t)) -> x `notin` fv_nom (P (swap y z t)).
Proof.
  induction t;intros;simpl in *.
  - assumption.
  - case (x0 == (swap_var y z x));intros.
    -- rewrite e. default_simp.
    -- apply (diff_remove _ _ _ n). apply (diff_remove_2 _ _ _ n) in H.
       apply IHt. assumption.
  - apply notin_union_3.
    -- apply notin_union_1 in H. apply IHt1. assumption.
    -- apply notin_union_2 in H. apply IHt2. assumption.
  - pose proof aeq_swap_m_subst.
    specialize (H0 (P t1) (P t2) y z x). apply aeq_fv_nom in H0.
    rewrite H0 in H. pose proof in_or_notin. specialize (H1 (swap_var y z x)
    (fv_nom (swap y z (P t1)))). pose proof in_or_notin.
    specialize (H2 (swap_var y z x) (fv_nom (P (swap y z t1)))).
    destruct H1;destruct H2.
    -- apply (fv_nom_m_subst_in _ (swap y z (P t2))) in H1.
       apply (fv_nom_m_subst_in _ (P (swap y z t2))) in H2.
       rewrite H2. rewrite H1 in H. simpl in *. apply notin_union_3.
       --- case (x0 == (swap_var y z x));intros.
           ---- rewrite e. default_simp.
           ---- apply notin_union_1 in H. apply (diff_remove_2 _ _ _ n) in H.
                apply (diff_remove _ _ _ n). apply IHt1. assumption.
       --- apply IHt2. apply notin_union_2 in H. assumption.
    -- pose proof aeq_swap_P. specialize (H3 t1 y z).
       apply aeq_fv_nom in H3. rewrite H3 in H2. default_simp.
    -- apply IHt1 in H1. default_simp.
    -- apply (fv_nom_m_subst_notin _ (swap y z (P t2))) in H1.
       apply (fv_nom_m_subst_notin _ (P (swap y z t2))) in H2.
       rewrite H2. rewrite H1 in H. case (x0 == (swap_var y z x));intros.
       --- rewrite e. default_simp.
       --- apply (diff_remove_2 _ _ _ n) in H.
           apply (diff_remove _ _ _ n). apply IHt1. assumption.
Qed.

Lemma notin_swap_P: forall t x y z, x `notin` fv_nom (swap y z(P t)) <-> x `notin` fv_nom (P (swap y z t)).
Proof.
  split.
  - apply notin_swap_P_2.
  - apply notin_swap_P_1.
Qed.
*)

Lemma aeq_P: forall t1 t2, t1 =a t2 -> (P t1) =a (P t2).
Proof.
  induction t1 as [x | t11 x IH | t11 t12 IH1 IH2 | t11 t12 x IH1 IH2] using n_sexp_induction.
  - intros t2 H. inversion H; subst. apply aeq_refl.
  - intros t2 H'. inversion H'; subst.
    + simpl. apply aeq_abs_same. rewrite <- (swap_id t11 x). rewrite <- (swap_id t11 x) in H2. apply IH.
      * apply swap_size_eq.
      * assumption.
    + simpl. apply aeq_abs_diff.
      * assumption.
      * apply notin_P. assumption.
      * apply aeq_trans with (P (swap y x t0)).
        ** symmetry. apply IH.
           *** apply aeq_size in H4. symmetry. assumption.
           *** apply aeq_sym. assumption.
        ** apply aeq_swap_P.
  - intros t2 H. inversion H; subst. simpl. apply aeq_app.
    + apply IH1. assumption.
    + apply IH2. assumption.
  - intros t2 H. inversion H; subst; simpl.
    + apply (aeq_trans _ ({x := (P t12)}(P t1'))).
      * apply aeq_m_subst_out. apply IH2.
        ** reflexivity.
        ** assumption.
      * apply aeq_m_subst_in. apply IH1. assumption.
    + apply (aeq_trans _ ({x := P t2'} P t11)).
       * apply aeq_m_subst_in. apply IH1. assumption.
       * apply aeq_m_subst_out_neq.
          ** assumption.
          ** apply notin_P. assumption.
          ** apply aeq_trans with (P (swap x y t1')).
            *** apply IH2.
              **** reflexivity.
              **** rewrite swap_symmetric. assumption.
              *** apply aeq_swap_P.
Qed.

Lemma notin_abs: forall x y e, x <> y -> x `notin` fv_nom (n_abs y e) -> x `notin` fv_nom e.
Proof.
  intros. pose proof in_or_notin. specialize (H1 x (fv_nom e)). destruct H1.
    - simpl in H0. apply notin_remove_1 in H0. destruct H0.
      + subst. contradiction.
      + assumption.
    - assumption.
Qed.


(*Lemma 5.3(1) in Nakazawa*)    
Lemma pi_P: forall t1 t2, (ctx pix) t1 t2 -> (P t1) =a (P t2).
Proof.
  intros t1 t2 H. induction H.
  - apply aeq_P. assumption.
  - inversion H0; subst.
    + apply aeq_trans with (P e3).
       * apply aeq_P in H. simpl in H. unfold m_subst in H. rewrite subst_rec_fun_equation in H. destruct (y == y).
           ** assumption.
           ** contradiction.
       * apply aeq_P; assumption.
    + apply aeq_P in H. simpl in H. unfold m_subst in H. rewrite subst_rec_fun_equation in H. destruct (y == x).
       * symmetry in e0. contradiction.
       * apply aeq_trans with (n_var x).
           ** assumption.
           ** apply aeq_P in H1. simpl in H1. assumption.
    + apply aeq_P in H. simpl in H. unfold m_subst in H. rewrite subst_rec_fun_equation in H. destruct (y == y).
       * apply aeq_P in H1. simpl in H1. apply (aeq_trans _ _ _ H H1).
       * contradiction.
    + apply aeq_P in H. simpl in H. unfold m_subst in H. rewrite subst_rec_fun_equation in H. destruct (y == x).
       * symmetry in e. contradiction.
       * destruct (atom_fresh(Metatheory.union (fv_nom (P e5))(Metatheory.union (fv_nom (n_abs x (P e0))) (singleton y)))) in H.
           apply aeq_trans with (n_abs x0 (subst_rec_fun (swap x x0 (P e0)) (P e5) y)).
           ** assumption.
           ** apply aeq_P in H1. apply aeq_trans with (P (n_abs x ([y := e5] e0))).
                *** simpl. unfold m_subst. destruct (x == x0).
                  **** subst. rewrite swap_id. apply aeq_refl.
                  **** apply aeq_abs_diff.
                    ***** apply aux_not_equal. assumption.
                    ***** apply fv_nom_remove. 
                      ****** apply notin_union_1 in n0. assumption.
                      ****** apply notin_remove_2. apply notin_union_2 in n0. apply notin_union_1 in n0. apply (notin_abs x0 x (P e0)).
                        ******* apply aux_not_equal. assumption.
                        ******* assumption.
                    ***** apply aeq_trans with (subst_rec_fun (swap x x0 (P e0)) (swap x x0 (P e5)) (vswap x x0 y)).
                      ****** unfold vswap. destruct (y == x).
                        ******* subst. contradiction.
                        ******* destruct (y == x0).
                          ******** subst. repeat apply notin_union_2 in n0. apply notin_singleton_1 in n0. contradiction.
                          ******** apply aeq_m_subst_in. rewrite swap_reduction.
                            ********* apply aeq_refl.
                            ********* apply notin_P in H3. assumption.
                            *********  apply notin_union_1 in n0. assumption.  
                      ****** apply aeq_sym. apply aeq_swap_m_subst.
                *** assumption.
    + apply aeq_P in H. apply aeq_trans with (P([y := e5] n_abs x e0)).
      * assumption.
      * apply aeq_trans with (P(n_abs z ([y := e5] swap x z e0))).
        ** simpl. apply aeq_trans with (n_abs z ({y := P e5} (swap x z (P e0)))).
          *** apply m_subst_abs_neq.
            **** apply aux_not_equal. assumption.
            **** apply notin_union_3.
              ***** apply notin_P. assumption.
              ***** apply notin_union_3.
                ****** pose proof notin_abs. specialize (H8 z x e0). simpl. apply notin_remove_2. apply notin_P. assumption.
                ****** apply notin_singleton. apply aux_not_equal. assumption.
          *** apply aeq_abs_same. apply aeq_m_subst_out. apply aeq_sym. apply aeq_swap_P.
        ** apply aeq_P. assumption.
    + apply aeq_P in H. apply aeq_trans with (P([y := e6] n_app e0 e5)).
      * assumption.
      * apply aeq_P in H1. apply aeq_trans with (P(n_app ([y := e6] e0) ([y := e6] e5))).
        ** simpl. rewrite m_subst_app. apply aeq_refl.
        ** assumption.
  - simpl. apply aeq_abs_same. assumption.
  - simpl. apply aeq_app.
    + assumption.
    + apply aeq_refl.
  - simpl. apply aeq_app.
    + apply aeq_refl.
    + assumption.
  - simpl. apply aeq_m_subst_eq.
    + assumption.
    + apply aeq_refl.
  - simpl. apply aeq_m_subst_eq.
    + apply aeq_refl.
    + assumption.
Qed.
 

(*Lemma 2 in Nakazawa - Jose Roberto para 14/5/2024 *)
Lemma pure_P: forall t, pure (P t).
Proof.
  induction t.
  - simpl. apply pure_var.
  - simpl. apply pure_abs. assumption.
  - simpl. apply pure_app.
    -- assumption.
    -- assumption.
  - simpl. apply pure_m_subst.
    -- assumption.
    -- assumption.
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

Lemma ctx_betapi_iff_lx:  forall e1 e2,
  refltrans lx e1 e2 <-> refltrans (ctx betapi) e1 e2.
Proof.
  intros. split; default_simp.
Qed.

(**)

Lemma refltrans_abs (R: Rel n_sexp): forall e1 e2 x, refltrans (ctx R) e1 e2 -> refltrans (ctx R) (n_abs x e1) (n_abs x e2).
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
       --- apply refltrans_composition with (n_abs x e2).
           + apply rtrans with (n_abs x e2).
             ++ apply step_abs_in. apply step_aeq. assumption.
             ++ apply refl.
           + assumption.
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
   - inversion H.
      -- apply refl.
      -- subst. apply rtrans with (n_abs x (n_abs x0 t2)).
         --- repeat apply step_abs_in. apply step_aeq. assumption.
         --- apply refl.
      -- subst. apply rtrans with (n_abs x (n_abs y t2)).
        --- apply step_abs_in. apply step_aeq. assumption.
        --- apply refl.
      -- subst. apply rtrans with (n_abs x (n_app t1' t2')).
        --- apply step_abs_in. apply step_aeq. assumption.
        --- apply refl.
      -- subst. apply rtrans with (n_abs x ([x0 := t2'] t1')).
        --- apply step_abs_in. apply step_aeq. assumption.
        --- apply refl.
      -- subst. apply rtrans with (n_abs x ([y := t2'] t1')).
        --- apply step_abs_in. apply step_aeq. assumption.
        --- apply refl.
   - inversion IHrefltrans.
    -- subst. apply rtrans with (n_abs x c).
      --- apply step_abs_in. apply step_aeq. assumption.
      --- apply refl.
    -- subst. apply refltrans_composition with (n_abs x b).
       --- apply rtrans with (n_abs x b).
          + apply step_abs_in. apply step_aeq. assumption.
          + apply refl.
       --- assumption.  
    -- subst. apply refltrans_composition with (n_abs x b).
       --- apply rtrans with (n_abs x b).
          + apply step_abs_in. apply step_aeq. assumption.
          + apply refl.
       --- assumption.  
    -- subst. apply refltrans_composition with (n_abs x b).
       --- apply rtrans with (n_abs x b).
          + apply step_abs_in. apply step_aeq. assumption.
          + apply refl.
       --- assumption.  
Qed.
    
Lemma refltrans_abs_diff (R: Rel n_sexp): forall e1 e2 x y, x <> y -> x `notin` fv_nom e2 -> refltrans (ctx R) e1 (swap x y e2) -> refltrans (ctx R) (n_abs x e1) (n_abs y e2).
Proof.
  intros. inversion H1;subst.
    - apply refl_aeq. apply aeq_abs_diff.
      + assumption.
      + assumption.
      + rewrite swap_symmetric. apply aeq_refl.
    - apply refltrans_composition with (n_abs x b).
      + apply rtrans with (n_abs x b).
        * apply step_abs_in. assumption.
        * apply refl.
      + apply refltrans_composition with (n_abs x (swap x y e2)).
        * apply refltrans_abs. assumption.
        * apply refl_aeq. apply aeq_abs_diff.
          ** assumption.
          ** assumption.
          ** rewrite swap_symmetric. apply aeq_refl.
    - apply refltrans_composition with (n_abs x (swap x y e2)).
      + apply refl_aeq. apply aeq_abs_same. assumption.
      + apply refl_aeq. apply aeq_abs_diff.
          * assumption.
          * assumption.
          * rewrite swap_symmetric. apply aeq_refl.
    - apply refltrans_composition with (n_abs x (swap x y e2)).
      + apply refltrans_abs. assumption.
      + apply refl_aeq. apply aeq_abs_diff.
          * assumption.
          * assumption.
          * rewrite swap_symmetric. apply aeq_refl.
Qed.

Lemma refltrans_app1 (R: Rel n_sexp): forall e1 e2 e3, refltrans (ctx R) e1 e2 -> refltrans (ctx R) (n_app e1 e3) (n_app e2 e3).
Proof.
  intros e1 e2 e3. intro H. induction H.
  - apply refl.
  - apply refltrans_composition with (n_app b e3).
    -- apply rtrans with (n_app b e3).
       --- apply step_app_left. assumption.
       --- apply refl.
    -- assumption.
   - apply refltrans_composition with (n_app b e3).
    -- apply rtrans with (n_app b e3).
       --- apply step_app_left. apply step_aeq. assumption.
       --- apply refl.
    -- apply refl.
   - apply refltrans_composition with (n_app b e3).
    -- apply rtrans with (n_app b e3).
       --- apply step_app_left. apply step_aeq. assumption.
       --- apply refl.
    -- assumption.
Qed.
       
Lemma refltrans_app2 (R: Rel n_sexp): forall e1 e2 e3, refltrans (ctx R) e2 e3 -> refltrans (ctx R) (n_app e1 e2) (n_app e1 e3).
Proof.
  intros e1 e2 e3. intro H. induction H.
  - apply refl.
  - apply refltrans_composition with (n_app e1 b).
    -- apply rtrans with (n_app e1 b).
      --- apply step_app_right. assumption.
      --- apply refl.
    -- assumption.
  - apply refltrans_composition with (n_app e1 b).
    -- apply rtrans with (n_app e1 b).
       --- apply step_app_right. apply step_aeq. assumption.
       --- apply refl.
    -- apply refl.
  - apply refltrans_composition with (n_app e1 b).
    -- apply rtrans with (n_app e1 b).
       --- apply step_app_right. apply step_aeq. assumption.
       --- apply refl.
    -- assumption.
Qed.

Lemma refltrans_app3 (R: Rel n_sexp): forall e1 e2 e3 e4, refltrans (ctx R) e1 e2 -> refltrans (ctx R) e3 e4 -> refltrans (ctx R) (n_app e1 e3) (n_app e2 e4).
Proof.

  intros. apply refltrans_composition with (n_app e2 e3).
    - apply refltrans_app1. assumption.
    - apply refltrans_app2. assumption.
Qed.

Lemma refltrans_sub1 (R: Rel n_sexp): forall e1 e2 e3 x, refltrans (ctx R) e2 e3 -> refltrans (ctx R) (n_sub e1 x e2) (n_sub e1 x e3).
Proof.
  intros. induction H.
  - apply refl.
  - apply refltrans_composition with (n_sub e1 x b).
    -- apply rtrans with (n_sub e1 x b).
       --- apply step_sub_right. assumption.
       --- apply refl.
    -- assumption.
  - pose proof aeq_sub_same. specialize (H0 e1 a e1 b x). apply refl_aeq. apply H0.
    -- apply aeq_refl.
    -- assumption.
  - apply refltrans_composition with (n_sub e1 x b).
    -- apply refl_aeq. apply aeq_sub_same.
      --- apply aeq_refl.
      --- assumption.
    -- assumption.
Qed.

Lemma refltrans_sub2 (R: Rel n_sexp): forall e1 e2 e3 x, refltrans (ctx R) e2 e3 -> refltrans (ctx R) (n_sub e2 x e1) (n_sub e3 x e1).
Proof.
  intros. induction H.
  - apply refl.
  - apply refltrans_composition with (n_sub b x e1).
    -- apply rtrans with (n_sub b x e1).
       --- apply step_sub_left. assumption.
       --- apply refl.
    -- assumption.
  - apply refl_aeq. apply aeq_sub_same.
    -- assumption.
    -- apply aeq_refl.
  - apply refltrans_composition with (n_sub b x e1).
    -- apply refl_aeq. apply aeq_sub_same.
      --- assumption.
      --- apply aeq_refl.
    -- assumption.
Qed.

Lemma refltrans_sub3 (R: Rel n_sexp): forall e1 e2 e3 e4 x, refltrans (ctx R) e1 e3 -> refltrans (ctx R) e2 e4 -> refltrans (ctx R) (n_sub e1 x e2) (n_sub e3 x e4).
Proof.
  intros. apply refltrans_composition with (n_sub e3 x e2).
  - apply refltrans_sub2. assumption.
  - apply refltrans_sub1. assumption.
Qed.

Lemma var_diff: forall e1 x y, x`notin` fv_nom e1 -> y `in` fv_nom e1 -> x <> y.
Proof.
  intros. destruct (x == y).
   - subst. contradiction.
   - assumption. 
Qed.

(*Lemma 4 in Nakazawa*)
Lemma pure_pix: forall e1 x e2, pure e1 -> refltrans (ctx pix) (n_sub e1 x e2) ({x := e2}e1).
Proof.
  induction e1 using n_sexp_induction.
  - intros. case (x == x0).
    -- intros; subst. apply rtrans with ({x0 := e2} n_var x0).
       ---  apply step_redex_R. rewrite m_subst_var_eq. apply step_var.
       --- apply refl.
    -- intros. apply rtrans with ({x0 := e2} n_var x).
       --- apply step_redex_R. rewrite m_subst_var_neq. 
            ---- apply step_gc. assumption.
            ---- assumption.
       --- apply refl.  
  - intros. inversion H0; subst. destruct (x == z).
    -- subst. apply rtrans with ({z := e2} n_abs z e1).
       --- apply step_redex_R. rewrite m_subst_abs_eq. apply step_abs1.
       --- apply refl.
    -- pose proof in_or_notin. specialize (H1 z (fv_nom(e2))). destruct H1. 
        --- apply rtrans with (let (z',_) := (atom_fresh (Metatheory.union (singleton z) (Metatheory.union (singleton x) 
            (Metatheory.union (fv_nom e2) (fv_nom e1))))) in (n_abs z' ([x := e2] (swap z z' e1)))).
            ---- apply step_redex_R. destruct (atom_fresh (Metatheory.union (singleton z) (Metatheory.union (singleton x) 
                 (Metatheory.union (fv_nom e2) (fv_nom e1))))). apply step_abs3.
              ----- apply aux_not_equal in n. assumption.
              ----- apply notin_union_1 in n0. apply notin_singleton_1 in n0. apply aux_not_equal in n0. assumption.
              ----- apply notin_union_2 in n0. apply notin_union_1 in n0. apply notin_singleton_1 in n0. apply aux_not_equal in n0. assumption.
              ----- assumption.
              ----- apply notin_union_2 in n0. apply notin_union_2 in n0. apply notin_union_2 in n0. assumption.
              ----- apply notin_union_2 in n0. apply notin_union_2 in n0. apply notin_union_1 in n0. assumption.
            ---- destruct (atom_fresh (Metatheory.union (singleton z) (Metatheory.union (singleton x) (Metatheory.union (fv_nom e2) (fv_nom e1))))).
                unfold m_subst. rewrite subst_rec_fun_equation. destruct (x==z).
                ----- subst. contradiction.
                ----- destruct (atom_fresh (Metatheory.union (fv_nom e2) (Metatheory.union (fv_nom (n_abs z e1)) (singleton x)))). 
                    simpl in n2. case (x0 == x1).
                    ------ intro. subst. apply refltrans_abs. apply H.
                      ------- apply swap_size_eq.
                      ------- apply pure_swap. assumption.
                    ------ intro. apply refltrans_abs_diff.
                      ------- assumption.
                      ------- apply fv_nom_remove. 
                        -------- apply notin_union_2 in n0. apply notin_union_2 in n0. apply notin_union_1 in n0. apply n0.
                        -------- apply notin_remove_2. assert (n0Copy:= n0). repeat apply notin_union_2 in n0. apply notin_union_1 in n0Copy. apply notin_singleton_1' in n0Copy. 
                                  apply aux_not_equal in n0Copy. apply fv_nom_remove_swap; assumption.
                      ------- specialize (H (swap z x0 e1)). apply refltrans_composition with ({x := e2} swap z x0 e1).
                        -------- apply H. apply swap_size_eq. apply pure_swap. assumption.
                        -------- apply refl_aeq. apply aeq_sym. apply aeq_trans with (subst_rec_fun (swap x0 x1 (swap z x1 e1)) (swap x0 x1 e2) (vswap x0 x1 x)).
                          --------- apply aeq_swap_m_subst.
                          --------- rewrite vswap_neq; try auto. assert (Hneq: x1 <> z).
                                        { apply notin_union_1 in n2. apply (var_diff e2 x1 z); assumption. } 
                                         unfold m_subst. apply aeq_m_subst_eq.
                            ---------- rewrite (swap_symmetric _ z x1). rewrite (swap_symmetric _ z x0). apply aeq_swap_swap. 
                              ----------- repeat apply notin_union_2 in n0. assumption.
                              ----------- auto.
                            ---------- apply swap_reduction; auto.
        --- apply rtrans with (n_abs z ([x := e2]e1)).
          ---- apply step_redex_R. apply step_abs2.
            ----- apply aux_not_equal in n. assumption.
            ----- assumption.
          ---- unfold m_subst. rewrite subst_rec_fun_equation. destruct (x==z).
            ----- contradiction.
            ----- destruct (atom_fresh (Metatheory.union (fv_nom e2)(Metatheory.union (fv_nom (n_abs z e1))(singleton x)))). case (x0 == z).
              ------ intro. subst. rewrite swap_id. apply refltrans_abs. apply H.
                ------- reflexivity.
                ------- assumption.
              ------ intro. apply refltrans_abs_diff.
                ------- apply aux_not_equal. assumption.
                ------- apply fv_nom_remove.
                  -------- assumption.
                  -------- apply notin_remove_2. apply fv_nom_swap. apply notin_union_2 in n1. apply notin_union_1 in n1. simpl in n1. apply notin_remove_1 in n1. destruct n1.
                    --------- subst. contradiction.
                    --------- assumption.
                ------- apply refltrans_composition with (subst_rec_fun (swap z x0(swap z x0 e1)) (swap z x0 e2) (vswap z x0 x)).
                  -------- rewrite vswap_neq.
                    --------- apply refltrans_composition with (subst_rec_fun (swap z x0 (swap z x0 e1)) e2 x).
                      ---------- rewrite swap_involutive. apply H.
                        ----------- reflexivity.
                        ----------- assumption.
                      ---------- rewrite swap_involutive. apply refl_aeq. apply aeq_m_subst_in. apply aeq_sym. apply swap_reduction.
                        ----------- assumption.
                        ----------- apply notin_union_1 in n1. assumption.
                       --------- apply aux_not_equal. assumption.
                       --------- repeat apply notin_union_2 in n1. apply notin_singleton_1 in n1. apply aux_not_equal. assumption.
                  -------- apply refl_aeq. apply aeq_sym. apply aeq_swap_m_subst.
  - intros. apply refltrans_composition with (n_app (m_subst e2 x e1_1) (m_subst e2 x e1_2)).
    -- apply rtrans with (n_app (n_sub e1_1 x e2) (n_sub e1_2 x e2)).
       --- apply step_redex_R. apply step_app.
       --- inversion H; subst. specialize (IHe1_1 x e2). specialize (IHe1_2 x e2). apply IHe1_1 in H2. apply IHe1_2 in H3. apply refltrans_app3; assumption.
    -- apply refltrans_composition with (m_subst e2 x (n_app e1_1 e1_2)).
       --- rewrite m_subst_app. apply refl.
       --- apply refl.
  - intros. inversion H0.
Qed.

Lemma ctx_betax_beta_pix: forall x y, ctx betapi x y <-> (ctx pix !_! ctx betax) x y.
Proof.
  intros x y. unfold lx in *. split.
    - intros. apply union_or.  induction H.
       -- left. constructor. assumption.
       -- inversion H0.
           --- right. apply (step_redex _ e1 e2 e3 e4);assumption.
           --- left. apply (step_redex _ e1 e2 e3 e4);assumption.
       -- destruct IHctx.
           --- left. apply step_abs_in. assumption.
           --- right. apply step_abs_in. assumption.
       -- destruct IHctx.
           --- left. apply step_app_left. assumption.
           --- right. apply step_app_left. assumption.
       -- destruct IHctx.
           --- left. apply step_app_right. assumption.
           --- right. apply step_app_right. assumption.
       -- destruct IHctx.
           --- left. apply step_sub_left. assumption.
           --- right. apply step_sub_left. assumption.
       -- destruct IHctx.
           --- left. apply step_sub_right. assumption.
           --- right. apply step_sub_right. assumption.
    - intros. apply union_or in H. destruct H.
       -- induction H.
           --- apply step_aeq. assumption.
           --- apply (step_redex _ e1 e2 e3 e4);try assumption.
                apply x_rule. assumption.
           --- apply step_abs_in. assumption.
           --- apply step_app_left. assumption.
           --- apply step_app_right. assumption.
           --- apply step_sub_left. assumption.
           --- apply step_sub_right. assumption.
       -- induction H.
           --- apply step_aeq. assumption.
           --- apply (step_redex _ e1 e2 e3 e4);try assumption.
                apply b_rule. assumption.
           --- apply step_abs_in. assumption.
           --- apply step_app_left. assumption.
           --- apply step_app_right. assumption.
           --- apply step_sub_left. assumption.
           --- apply step_sub_right. assumption.
Qed.

Lemma pure_pix_2: forall e1 x e2, pure e1 -> refltrans (ctx betapi) (n_sub e1 x e2) ({x := e2}e1).
Proof.
  intros. apply (pure_pix _ x e2) in H. induction H.
  - apply refl.
  - apply (rtrans _ _ b).
    -- apply ctx_betax_beta_pix. apply union_or. left. assumption.
    -- assumption.
  - apply refl_aeq. assumption.
  - apply (rtrans _ _ b).
    -- apply step_aeq. assumption.
    -- assumption.
Qed.  

Lemma pure_B: forall e, pure e -> pure (B e).
Proof.
  intros. induction H.
  - simpl. apply pure_var.
  - simpl. destruct e1.
    + simpl in *. apply pure_app;assumption.
    + apply pure_m_subst.
       * simpl in IHpure1. inversion IHpure1. assumption.
       * assumption.
    + apply pure_app;assumption.
    + simpl in IHpure1. inversion IHpure1.
  - simpl. apply pure_abs. assumption.
Qed.

Lemma swap_B: forall x1 x2 t, aeq (swap x1 x2 (B t)) (B (swap x1 x2 t)).
Proof.
  intros. induction t.
  - simpl. apply aeq_refl.
  - simpl. apply aeq_abs_same. assumption.
  - simpl. destruct t1;default_simp. inversion IHt1.
    + apply aeq_trans with (m_subst (swap x1 x2 (B t2)) (vswap x1 x2 x) (swap x1 x2 (B t1))).
       * apply aeq_swap_m_subst.
       * apply (aeq_trans _ (m_subst (swap x1 x2 (B t2)) (vswap x1 x2 x) (B (swap x1 x2 t1)))).
           ** apply aeq_m_subst_out. assumption.
           ** apply aeq_m_subst_in. assumption.
    + default_simp.
  - simpl. apply aeq_sub_same;assumption.
Qed.

Lemma pure_refltrans_B: forall e, pure e -> refltrans lx e (B e).
Proof.
  induction e using n_sexp_induction;intros.
  - simpl. apply refl.
  - simpl. apply refltrans_abs. apply H.
    + reflexivity.
    + inversion H0; subst. assumption.
  - simpl. destruct e1 eqn:H'.
    + simpl. apply refltrans_app2. apply IHe2. inversion H. assumption.
    + inversion H. apply refltrans_composition with (n_app (B (n_abs x n)) e2).
      * apply refltrans_app1. apply IHe1. assumption.
      * simpl. apply (rtrans _ _ (n_sub (B n) x e2)).
        ** apply step_redex_R. apply b_rule. apply step_betax.
        ** apply refltrans_composition with (n_sub (B n) x (B e2)).
          *** apply refltrans_sub1. apply IHe2. assumption.
          *** apply pure_pix_2. apply pure_B. inversion H2. assumption.
    + apply refltrans_app3.
      * apply IHe1. inversion H. assumption.
      * apply IHe2. inversion H. assumption.
    + inversion H. inversion H2.
 - inversion H0.
Qed.

Lemma refltrans_P: forall a, refltrans (ctx pix) a (P a).
Proof.
  induction a.
  - simpl. apply refl.
  - simpl. apply refltrans_abs. assumption.
  - simpl. apply refltrans_app3;assumption.
  - simpl. apply (refltrans_composition3 _ (n_sub (P a1) x a2)).
    + apply (refltrans_composition3 _ (n_sub (P a1) x (P a2))).
       * apply pure_pix. apply pure_P.
       * apply refltrans_sub1. assumption.
    + apply refltrans_sub2. assumption.
Qed.

Lemma refltrans_lx_pix: forall a b, refltrans (ctx pix) a b -> refltrans lx a b.
Proof.
  intros. induction H.
  - apply refl.
  - apply (rtrans _ a b c).
    + apply ctx_betax_beta_pix. apply union_or. left. assumption.
    + assumption.
  - apply refl_aeq. assumption.
  - apply (refltrans_composition _ b c).
    + apply refl_aeq. assumption.
    + assumption.
Qed.

Lemma refltrans_lx_betax: forall a b, refltrans (ctx betax) a b -> refltrans lx a b.
Proof.
  intros. induction H.
  - apply refl.
  - apply (rtrans _ a b c).
    + apply ctx_betax_beta_pix. apply union_or. right. assumption.
    + assumption.
  - apply refl_aeq. assumption.
  - apply (refltrans_composition _ b c).
    + apply refl_aeq. assumption.
    + assumption.
Qed.

(*
Lemma refltrans_abs2: forall e1 e2 x ,
  refltrans lx e1 e2 -> refltrans lx (n_abs x e1) (n_abs x e2).
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
*)
Lemma notin_B: forall e x, x `notin` (fv_nom e) -> x `notin` (fv_nom (B e)).
Proof.
  induction e;intros.
  - simpl in *. assumption.
  - simpl in *. case (x0 == x);intros.
    -- rewrite e0. default_simp.
    -- apply diff_remove;default_simp.
  - simpl in *. destruct e1;simpl in *;try(apply notin_union_3).
    -- apply notin_union_1 in H. assumption.
    -- apply notin_union_2 in H. apply IHe2. assumption.
    -- pose proof in_or_notin. specialize (H0 x0 (fv_nom (B e1))). destruct H0.
       --- apply (fv_nom_m_subst_in _ (B e2)) in H0. rewrite H0. simpl. apply notin_union_3.
           ---- apply notin_union_1 in H. apply IHe1. assumption.
           ---- apply IHe2. apply notin_union_2 in H. assumption.
       --- apply (fv_nom_m_subst_notin _ (B e2)) in H0. rewrite H0. apply IHe1.
           apply notin_union_1 in H. assumption.
    -- apply IHe1. apply notin_union_1 in H. assumption.
    -- apply IHe2. apply notin_union_2 in H. assumption.
    -- apply IHe1. apply notin_union_1 in H. assumption.
    -- apply IHe2. apply notin_union_2 in H. assumption.
  - simpl in *. apply notin_union_3.
    -- case (x0 == x);intros.
       --- rewrite e. default_simp.
       --- apply diff_remove;default_simp.
    -- apply notin_union_2 in H. apply IHe2. default_simp.
Qed.

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

Lemma in_swap: forall  e x y z, x <> y -> x <> z -> x `in` fv_nom e <-> 
  x `in` fv_nom (swap y z e).
Proof.
  induction e;intros;split.
  - intros. simpl. unfold swap_var. simpl in H1. apply AtomSetImpl.singleton_1 in H1.
    rewrite H1. default_simp.
  - intros. simpl in *. unfold swap_var in H1. default_simp;apply AtomSetImpl.singleton_1 in H1;default_simp.
  - intros. simpl in *. unfold swap_var. case (x0 == x);intros.
    -- rewrite e0 in *. apply remove_iff in H1. destruct H1. default_simp.
    -- apply AtomSetImpl.remove_2.
       --- default_simp.
       --- apply AtomSetImpl.remove_3 in H1. apply IHe;default_simp.
  - intros. simpl in *. case (x == x0);intros.
    --  rewrite e0 in *. apply remove_iff in H1. destruct H1. unfold swap_var in H2.
        default_simp.
    -- apply AtomSetImpl.remove_3 in H1. apply AtomSetImpl.remove_2.
       --- assumption.
       --- specialize (IHe x0 y z H H0). destruct IHe. apply H3. assumption.
  - intros. simpl in *. apply AtomSetImpl.union_1 in H1. destruct H1.
    -- apply AtomSetImpl.union_2. apply IHe1;default_simp.
    -- apply AtomSetImpl.union_3. apply IHe2;default_simp.
  - intros. simpl in *. apply AtomSetImpl.union_1 in H1. destruct H1.
    -- apply AtomSetImpl.union_2. specialize (IHe1 x y z H H0). destruct IHe1.
       apply H3. assumption.
    -- apply AtomSetImpl.union_3. specialize (IHe2 x y z H H0). destruct IHe2.
       apply H3. assumption.
  - intros. simpl in *. apply AtomSetImpl.union_1 in H1. destruct H1.
    -- apply AtomSetImpl.union_2. case (x == x0);intros.
       --- rewrite e in *. apply remove_iff in H1. destruct H1. default_simp.
       --- apply AtomSetImpl.remove_2.
           ---- unfold swap_var. default_simp.
           ---- apply AtomSetImpl.remove_3 in H1. apply IHe1;default_simp.
    -- apply AtomSetImpl.union_3. apply IHe2;default_simp.
  - intros. simpl in *. apply AtomSetImpl.union_1 in H1. destruct H1.
    -- case (x == x0);intros. 
       --- rewrite e in *. unfold swap_var in H1. default_simp. apply remove_iff in H1.
           destruct H1. default_simp.
       --- apply AtomSetImpl.remove_3 in H1. apply AtomSetImpl.union_2.
           apply AtomSetImpl.remove_2.
           ---- assumption.
           ---- specialize (IHe1 x0 y z H H0). destruct IHe1. apply H3. assumption.
    -- apply AtomSetImpl.union_3. specialize (IHe2 x0 y z H H0). destruct IHe2. apply H3. assumption.
Qed.

Lemma in_swap_2: forall e x a b c d, x <> a -> x <> b -> x <> c -> x <> d ->
  x `in` fv_nom (swap a b e) <-> x `in` fv_nom (swap c d e).
Proof.
  intros. split;intros;apply in_swap in H3;try assumption;
  apply in_swap;assumption.
Qed.

Lemma lx_fv_nom: forall e1 e2 x, lx e1 e2 -> x `notin` (fv_nom e1) -> x `notin` (fv_nom e2).
  intros. induction H.
  - apply aeq_fv_nom in H. rewrite <- H. assumption.
  - apply aeq_fv_nom in H. apply aeq_fv_nom in H2.
    rewrite <- H2. rewrite H in H0. inversion H1.
    -- inversion H3. rewrite <- H6 in H0. simpl in *. assumption.
    -- inversion H3.
       --- rewrite <- H7. rewrite <- H6 in H0. simpl in H0.
           apply notin_union_2 in H0. assumption.
       --- rewrite <- H7 in H0. simpl in H0. apply notin_union_1 in H0.
           simpl. case (x == x0);intros;default_simp.
       --- rewrite <- H6 in H0. simpl in *. apply notin_union_1 in H0.
           rewrite double_remove in H0. assumption.
       --- rewrite <- H8 in H0. simpl in *. case (x == x0);intros.
           ---- rewrite e in *. default_simp.
           ---- apply diff_remove;default_simp.
       --- rewrite <- H11 in H0. simpl in *. case (x == z);intros.
           ---- rewrite e in *. default_simp.
           ---- apply diff_remove;default_simp. apply notin_union_3.
                ----- case (x == y);intros.
                      ------ rewrite e. default_simp.
                      ------  apply diff_remove;default_simp. case (x == x0);intros.
                              ------- rewrite e. apply fv_nom_swap;default_simp.
                              ------- apply fv_nom_remove_swap;default_simp.
                ----- apply notin_union_2 in H0. assumption.
       --- rewrite <- H6 in H0. simpl in *. default_simp.
  - simpl in *. default_simp.
  - default_simp.
  - default_simp.
  - default_simp.
  - default_simp.
Qed.

Lemma refltrans_fv_nom: forall e1 e2 x, refltrans lx e1 e2 -> x `notin` (fv_nom e1) -> x `notin` (fv_nom e2).
Proof.
  intros. induction H.
  - assumption.
  - apply IHrefltrans. apply (lx_fv_nom _ _ x) in H;assumption. 
Qed.

Lemma refltrans_m_subst_1: forall e1 e2 e3 x,
  refltrans lx e1 e2 -> refltrans lx ({x := e1}e3) ({x := e2}e3).
Proof.
  induction e3 using n_sexp_induction;intros;unfold m_subst in *.
  - simpl. default_simp. apply refl.
  - simpl. default_simp.
    -- apply refl.
    -- case (x1 == x0);intros.
       --- rewrite e in *. apply refltrans_abs. rewrite <- (swap_size_eq z x0). apply H.
           ---- reflexivity.
           ---- assumption.
       --- rewrite <- (swap_size_eq z x0) at 1. rewrite <- (swap_size_eq z x1 e3).
           apply (refltrans_composition _ _ (n_abs x0 (subst_rec (size (swap z x0 e3)) (swap z x0 e3) e2 x))).
           ---- apply refltrans_abs. apply H;default_simp.
           ---- apply (rtrans _ _ (n_abs x1 (subst_rec (size (swap z x1 e3)) (swap z x1 e3) e2 x))).
                ----- apply step_aeq. apply aeq_abs_diff.
                      ------ default_simp.
                      ------ pose proof in_or_notin. specialize (H1 x (fv_nom (swap z x1 e3))).
                             destruct H1.
                             ------- apply (fv_nom_m_subst_in _ e2) in H1. rewrite H1. simpl. apply notin_union_3.
                                     -------- apply diff_remove;default_simp. case (x0 == z);intros.
                                              * rewrite e. apply fv_nom_swap. default_simp.
                                              * apply fv_nom_remove_swap;default_simp.
                                     -------- apply notin_union_1 in n. apply (refltrans_fv_nom _ _ _ H0 n).
                             ------- apply (fv_nom_m_subst_notin _ e2) in H1. rewrite H1.
                                     apply diff_remove;default_simp. case (x0 == z);intros.
                                     * rewrite e. apply fv_nom_swap. default_simp.
                                     * apply fv_nom_remove_swap;default_simp.
                      ------ apply (aeq_trans _ (subst_rec (size (swap x1 x0 (swap z x1 e3)))
                             (swap x1 x0 (swap z x1 e3)) e2 (swap_var x1 x0 x))).
                             ------- unfold swap_var. pose proof n. pose proof n0. repeat apply notin_union_2 in H1.
                                     repeat apply notin_union_2 in H2. apply notin_singleton_1 in H1.
                                     apply notin_singleton_1 in H2. default_simp.
                                     rewrite (swap_symmetric _ z x1). rewrite (swap_symmetric _ x1 x0).
                                     case (x0 == z);intros.
                                     * rewrite e in *. rewrite (swap_symmetric _ z x1).
                                       rewrite swap_involutive. rewrite swap_id. apply aeq_refl.
                                     * case (x1 == z);intros.
                                       ** rewrite e in *. rewrite swap_id. rewrite (swap_symmetric _ x0 z).
                                          apply aeq_refl.
                                       ** rewrite shuffle_swap;default_simp. rewrite (swap_symmetric _ x0 z).
                                          rewrite shuffle_swap;default_simp. apply aeq_m_subst_2.
                                          apply aeq_swap0.
                                          *** apply fv_nom_swap. default_simp.
                                          *** apply fv_nom_remove_swap;default_simp.
                             ------- apply (aeq_trans _ (subst_rec (size (swap x1 x0 (swap z x1 e3))) (swap x1 x0 (swap z x1 e3))
                                     (swap x1 x0 e2) (swap_var x1 x0 x))).
                                     * apply aeq_m_subst_1. apply aeq_swap0.
                                       ** default_simp.
                                       ** apply (refltrans_fv_nom e1 e2 x0);default_simp.
                                     * apply aeq_sym. apply aeq_swap_m_subst.
                ----- apply refl.
  - pose proof subst_app. unfold m_subst in H0. rewrite H0. rewrite H0. apply refltrans_app3.
    -- apply IHe3_1. assumption.
    -- apply IHe3_2. assumption.
  - pose proof subst_sub. unfold m_subst in H1. repeat rewrite H1. case (x == z);intros.
    -- apply refltrans_sub3.
       --- apply refl.
       --- apply IHe3_1. assumption.
    -- default_simp. case (x0 == x1);intros.
       --- rewrite e in *. apply refltrans_sub3.
           ---- apply H;default_simp.
           ---- apply IHe3_1. assumption.
       --- apply (refltrans_composition _ _ (n_sub (subst_rec (size (swap z x0 e3_1)) (swap z x0 e3_1) e2 x) x0
           (subst_rec (size e3_2) e3_2 e2 x))).
           ---- apply refltrans_sub3.
                ----- apply H;default_simp.
                ----- apply IHe3_1. assumption.
           ---- apply (rtrans _ _ (n_sub (subst_rec (size (swap z x1 e3_1)) (swap z x1 e3_1) e2 x) x1
                (subst_rec (size e3_2) e3_2 e2 x))).
                ----- apply step_aeq. apply aeq_sub_diff.
                      * apply aeq_refl.
                      * assumption.
                      * pose proof in_or_notin. specialize (H2  x (fv_nom (swap z x1 e3_1))).
                        destruct H2.
                        ** apply (fv_nom_m_subst_in _ e2) in H2. rewrite H2. simpl.
                           apply notin_union_3.
                           *** apply diff_remove;default_simp. case (x0 == z);intros.
                               **** rewrite e in *. apply fv_nom_swap.  default_simp.
                               **** apply fv_nom_remove_swap;default_simp.
                           *** apply (refltrans_fv_nom e1 e2 x0);default_simp.
                        ** apply (fv_nom_m_subst_notin _ e2) in H2. rewrite H2.
                           apply diff_remove;default_simp. case (x0 == z);intros.
                           *** rewrite e in *. apply fv_nom_swap.  default_simp.
                           *** apply fv_nom_remove_swap;default_simp.
                      * apply (aeq_trans _ (subst_rec (size (swap x1 x0 (swap z x1 e3_1))) (swap x1 x0 (swap z x1 e3_1))
                        e2 (swap_var x1 x0 x))).
                        ** pose proof n1. pose proof n0. repeat apply notin_union_2 in H3.
                           repeat apply notin_union_2 in H2. apply notin_singleton_1 in H3.
                           apply notin_singleton_1 in H2. unfold swap_var. default_simp.
                           apply aeq_m_subst_2. case (x1 == z);intros.
                           *** rewrite e in *. rewrite swap_id. apply aeq_refl.
                           *** case (x0 == z);intros.
                               **** rewrite e in *. rewrite swap_id. rewrite swap_symmetric.
                                    rewrite swap_involutive. apply aeq_refl.
                               **** rewrite (swap_symmetric _ x1 x0).
                                    rewrite (swap_symmetric _ z x1). rewrite shuffle_swap;default_simp.
                                    rewrite (swap_symmetric _ x0 z). rewrite shuffle_swap;default_simp.
                                    apply aeq_swap0.
                                    ***** apply fv_nom_swap. default_simp.
                                    ***** apply fv_nom_remove_swap;default_simp.
                        ** apply (aeq_trans _ (subst_rec (size (swap x1 x0 (swap z x1 e3_1)))
                           (swap x1 x0 (swap z x1 e3_1)) (swap x1 x0 e2) (swap_var x1 x0 x))).
                           *** apply aeq_m_subst_1. apply aeq_swap0.
                               **** default_simp.
                               **** apply (refltrans_fv_nom e1 e2 x0);default_simp.
                           *** apply aeq_sym. apply aeq_swap_m_subst. 
                ----- apply refl. 
Qed.

Lemma refltrans_subst_fresh_1: forall e1 e2 x, x `notin` (fv_nom e1) -> 
  refltrans lx e1 ({x := e2}e1).
Proof.
  intros. apply (rtrans _ _ (m_subst e2 x e1)).
  - apply step_aeq. apply aeq_sym. apply subst_fresh_eq. assumption.
  - apply refl.
Qed.

Lemma refltrans_subst_fresh_2: forall e1 e2 x, x `notin` (fv_nom e1) -> 
  refltrans lx ({x := e2}e1) e1.
Proof.
  intros. apply (rtrans _ _ e1).
  - apply step_aeq. apply subst_fresh_eq. assumption.
  - apply refl.
Qed.

Lemma refltrans_m_subst1 (R: Rel n_sexp): forall e1 e2 e3 x, refltrans (ctx R) e1 e2 -> 
  refltrans (ctx R) ({x := e1}e3) ({x := e2}e3).
Admitted.

Lemma refltrans_m_subst2 (R: Rel n_sexp): forall e1 e2 e3 x, refltrans (ctx R) e1 e2 -> 
  refltrans (ctx R) ({x := e3}e1) ({x := e3}e2).
Admitted.

Lemma aeq_double_m_subst: forall e1 e2 e3 x, {x := e1}({x := e2}e3) =a {x := ({x := e1}e2)}e3.
Proof.
  intros e1 e2 e3. generalize dependent e1. generalize dependent e2. induction e3 using n_sexp_induction;intros.
  - unfold m_subst. default_simp. apply aeq_refl.
  - pose proof subst_abs. rewrite H0. rewrite H0. case (x == z);intros.
    -- rewrite e. rewrite H0. default_simp. apply aeq_refl.
    -- simpl. destruct (atom_fresh (Metatheory.union (fv_nom e2)
       (Metatheory.union (remove z (fv_nom e3)) (singleton x)))).
       destruct (atom_fresh (Metatheory.union (fv_nom (m_subst e1 x e2))
       (Metatheory.union (remove z (fv_nom e3)) (singleton x)))). rewrite H0. pose proof n0.
       repeat apply notin_union_2 in H1. apply notin_singleton_1 in H1. default_simp.
       case (x2 == x1);intros.
       --- rewrite e in *. apply aeq_abs_same. apply (aeq_trans _ (m_subst e1 x ((m_subst e2 (swap_var x0 x1 x)
           (swap x0 x1 (swap z x0 e3)))))).
           ---- apply aeq_m_subst_2. apply (aeq_trans _ (m_subst (swap x0 x1 e2) (swap_var x0 x1 x)
                (swap x0 x1 (swap z x0 e3)))).
                ----- apply aeq_swap_m_subst.
                ----- apply aeq_m_subst_1. apply aeq_sym. apply aeq_swap0.
                      ------ default_simp.
                      ------ pose proof n1. apply notin_union_1 in H2. pose proof in_or_notin.
                             specialize (H3 x (fv_nom e2)). destruct H3.
                             * apply (fv_nom_m_subst_in _ e1) in H3. rewrite H3 in H2. simpl in H2.
                               apply notin_union_1 in H2. apply diff_remove_2 in H2;default_simp.
                             * apply (fv_nom_m_subst_notin _ e1) in H3. rewrite H3 in H2.
                               apply diff_remove_2 in H2;default_simp.
           ---- unfold swap_var. pose proof n1. repeat apply notin_union_2 in H2. apply notin_singleton_1 in H2.
                default_simp. rewrite swap_symmetric. rewrite (swap_symmetric _ z x0). case (x1 == z);intros.
                ----- rewrite e in *. rewrite swap_symmetric. rewrite swap_involutive.
                      rewrite <- (swap_id e3 z) at 1. apply H. reflexivity.
                ----- case (x0 == z);intros.
                      ------ rewrite e in *. rewrite swap_symmetric. rewrite swap_id. apply H. reflexivity.
                      ------ rewrite shuffle_swap;default_simp. rewrite swap_symmetric.
                             case (x1 == x0);intros.
                             ------- rewrite e in *. rewrite swap_id. apply H. reflexivity.
                             ------- rewrite shuffle_swap;default_simp. apply (aeq_trans _ 
                                     (m_subst e1 x (m_subst e2 x (swap z x1 e3)))).
                                     * repeat apply aeq_m_subst_2. apply aeq_sym. apply aeq_swap0.
                                       ** apply fv_nom_swap. default_simp.
                                       ** apply fv_nom_remove_swap;default_simp.
                                     * apply H. reflexivity.
       --- apply aeq_abs_diff.
           ---- assumption.
           ---- pose proof in_or_notin. specialize (H2 x (fv_nom (swap z x1 e3))). destruct H2.
                ----- pose proof H2 as H'. apply (fv_nom_m_subst_in _ (m_subst e1 x e2)) in H2. rewrite H2.
                      simpl. apply notin_union_3.
                      ------ apply diff_remove;default_simp. case (x2 == z);intros.
                             * rewrite e in *. apply fv_nom_swap. default_simp.
                             * apply fv_nom_remove_swap;default_simp. pose proof n2. apply notin_union_2 in H3.
                               apply notin_union_1 in H3. case (x2 == x0);intros.
                               ** rewrite e in *. default_simp.
                               ** apply diff_remove_2 in H3;default_simp. pose proof in_or_notin.
                                  specialize (H4 x (fv_nom (swap z x0 e3))). destruct H4.
                                  *** apply (fv_nom_m_subst_in _ e2) in H4. rewrite H4 in H3. simpl in H3.
                                      apply notin_union_1 in H3. apply diff_remove_2 in H3.
                                      **** apply fv_nom_swap_remove in H3;default_simp.
                                      **** default_simp.
                                  *** apply (fv_nom_m_subst_notin _ e2) in H4. rewrite H4 in H3. simpl in H3.
                                      apply diff_remove_2 in H3.
                                      **** apply fv_nom_swap_remove in H3;default_simp.
                                      **** default_simp.
                      ------ pose proof in_or_notin. specialize (H3 x (fv_nom e2)).
                             assert (H'': x `in` fv_nom (swap z x0 e3)).
                             * pose proof in_swap_2. specialize (H4 e3 x z x1 z x0).
                               apply H4;default_simp.
                             * apply (fv_nom_m_subst_in _ e2) in H''. rewrite H'' in n2.
                               destruct H3.
                               ** apply (fv_nom_m_subst_in _ e1) in H3. rewrite H3.
                                  simpl in *. apply notin_union_3.
                                  *** case (x0 == x2);intros.
                                      **** rewrite e in *. apply diff_remove;default_simp.
                                      **** apply notin_union_2 in n2. apply notin_union_1 in n2.
                                           apply diff_remove_2 in n2;default_simp.
                                  *** default_simp.
                               ** apply (fv_nom_m_subst_notin _ e1) in H3. rewrite H3.
                                  simpl in *. case (x0 == x2);intros.
                                  *** rewrite e in *. apply diff_remove;default_simp.
                                  *** apply notin_union_2 in n2. apply notin_union_1 in n2.
                                      apply diff_remove_2 in n2;default_simp.
                ----- pose proof H2 as H'. apply (fv_nom_m_subst_notin _ (m_subst e1 x e2)) in H2. rewrite H2.
                      apply diff_remove;default_simp. case (x2 == z);intros.
                      * rewrite e in *. apply fv_nom_swap. default_simp.
                      * apply fv_nom_remove_swap;default_simp. pose proof n2. apply notin_union_2 in H3.
                        apply notin_union_1 in H3. case (x2 == x0);intros.
                        ** rewrite e in *. default_simp.
                        ** apply diff_remove_2 in H3;default_simp. pose proof in_or_notin.
                           specialize (H4 x (fv_nom (swap z x0 e3))). destruct H4.
                           *** apply (fv_nom_m_subst_in _ e2) in H4. rewrite H4 in H3. simpl in H3.
                               apply notin_union_1 in H3. apply diff_remove_2 in H3.
                               **** apply fv_nom_swap_remove in H3;default_simp.
                               **** default_simp.
                           *** apply (fv_nom_m_subst_notin _ e2) in H4. rewrite H4 in H3. simpl in H3.
                               apply diff_remove_2 in H3.
                               **** apply fv_nom_swap_remove in H3;default_simp.
                               **** default_simp.
           ---- case (x2 == x0);intros.
                ----- rewrite e in *. rewrite swap_id. apply (aeq_trans _ (m_subst (m_subst e1 x e2)
                      (swap_var x1 x0 x) (swap x1 x0 (swap z x1 e3)))).
                      * unfold swap_var. pose proof n1. repeat apply notin_union_2 in H2. apply notin_singleton_1 in H2.
                        default_simp. rewrite (swap_symmetric _ x1 x0). rewrite (swap_symmetric _ z x1).
                        case (x0 == z);intros.
                        ** rewrite e in *. rewrite (swap_symmetric _ x1 z). rewrite swap_involutive.
                           rewrite <- (swap_id e3 z) at 2. apply H. reflexivity.
                        ** case (x1 == z);intros.
                           *** rewrite e. rewrite swap_symmetric. rewrite swap_id. apply H. reflexivity.
                           *** rewrite shuffle_swap;default_simp. rewrite (swap_symmetric _ x0 z).
                               rewrite shuffle_swap;default_simp. apply (aeq_trans _ 
                               (m_subst (m_subst e1 x e2) x (swap z x0 e3))).
                               **** apply H. reflexivity.
                               **** apply aeq_m_subst_2. apply aeq_swap0.
                                    ***** apply fv_nom_swap. default_simp.
                                    ***** apply fv_nom_remove_swap;default_simp.
                      * apply (aeq_trans _ (m_subst (swap x1 x0 (m_subst e1 x e2)) (swap_var x1 x0 x)
                        (swap x1 x0 (swap z x1 e3)))).
                        ** apply aeq_m_subst_1. apply aeq_swap0.
                           *** default_simp.
                           *** pose proof in_or_notin. specialize (H2 x (fv_nom e2)). destruct H2.
                               **** apply (fv_nom_m_subst_in _ e1) in H2. rewrite H2.
                                    simpl. apply notin_union_3.
                                    ***** apply diff_remove;default_simp.
                                    ***** default_simp.
                               **** apply (fv_nom_m_subst_notin _ e1) in H2. rewrite H2.
                                    apply diff_remove;default_simp.
                        ** apply aeq_sym. apply aeq_swap_m_subst.
                ----- pose proof in_or_notin. specialize (H2 x (fv_nom (swap z x0 e3))).
                      destruct H2.
                      ------  apply (aeq_trans _ (m_subst e1 x (m_subst e2 (swap_var x0 x2 x) (swap x0 x2 (swap z x0 e3))))).
                             * apply aeq_m_subst_2. pose proof n2. repeat apply notin_union_2 in H3.
                               apply notin_singleton_1 in H3. apply (aeq_trans _ (m_subst (swap x0 x2 e2) (swap_var x0 x2 x)
                               (swap x0 x2 (swap z x0 e3)))).
                               ** apply aeq_swap_m_subst.
                               ** apply aeq_m_subst_1. apply aeq_sym. apply aeq_swap0.
                                  *** default_simp.
                                  *** apply notin_union_2 in n2. apply notin_union_1 in n2.
                                      apply (fv_nom_m_subst_in _ e2) in H2. rewrite H2 in n2.
                                      simpl in n2. apply diff_remove_2 in n2;default_simp.
                             * rewrite (swap_symmetric _ x0 x2). rewrite (swap_symmetric _ z x0).
                               unfold swap_var. pose proof n2. repeat apply notin_union_2 in H3.
                               apply notin_singleton_1 in H3. default_simp. case (x2 == z);intros.
                               ** rewrite e in *. rewrite swap_symmetric. rewrite swap_involutive.
                                  apply (aeq_trans _ (m_subst (m_subst e1 x e2) (swap_var x1 z x)
                                  (swap x1 z (swap z x1 e3)))).
                                  *** unfold swap_var. pose proof n1. repeat apply notin_union_2 in H4.
                                      apply notin_singleton_1 in H4. default_simp. rewrite swap_symmetric.
                                      rewrite swap_involutive. rewrite <- (swap_id e3 z). apply H. reflexivity.
                                  *** apply (aeq_trans _ (m_subst (swap x1 z (m_subst e1 x e2)) (swap_var x1 z x)
                                      (swap x1 z (swap z x1 e3)))).
                                      **** apply aeq_m_subst_1. apply aeq_swap0.
                                           ***** default_simp.
                                           ***** apply (fv_nom_m_subst_in _ e2) in H2. rewrite H2 in n2. simpl in n2.
                                                 pose proof in_or_notin. specialize (H4 x (fv_nom e2)). destruct H4.
                                                 ****** apply (fv_nom_m_subst_in _ e1) in H4. rewrite H4.
                                                        simpl. apply notin_union_3.
                                                        ******* apply diff_remove;default_simp.
                                                        ******* default_simp.
                                                 ****** apply (fv_nom_m_subst_notin _ e1) in H4. rewrite H4. 
                                                        apply diff_remove;default_simp.
                                      **** apply aeq_sym. apply aeq_swap_m_subst.
                               ** case (x0 == z);intros.
                                  *** rewrite e in *. rewrite swap_id. apply (aeq_trans _ 
                                      (m_subst (m_subst e1 x e2) (swap_var x1 x2 x) (swap x1 x2 (swap z x1 e3)))).
                                      **** rewrite (swap_symmetric _ x1 x2). rewrite (swap_symmetric _ z x1).
                                           case (x1 == z);intros.
                                           ***** rewrite e0 in *. rewrite swap_id. unfold swap_var.
                                                 default_simp.
                                           ***** rewrite shuffle_swap;default_simp. rewrite (swap_symmetric _ x2 z).
                                                 rewrite (swap_symmetric _ x2 z). rewrite shuffle_swap;default_simp.
                                                 apply (aeq_trans _ (m_subst (m_subst e1 x e2) (swap_var x1 x2 x) (swap z x2 e3))).
                                                 ****** unfold swap_var. repeat apply notin_union_2 in n1.
                                                        apply notin_singleton_1 in n1. default_simp.
                                                 ****** apply aeq_m_subst_2. apply aeq_swap0.
                                                        ******* apply fv_nom_swap. rewrite swap_id in *.
                                                                apply (fv_nom_m_subst_in _ e2) in H2.
                                                                rewrite H2 in n2. simpl in n2. default_simp.
                                                        ******* apply fv_nom_remove_swap;default_simp.
                                      **** apply (aeq_trans _ (m_subst (swap x1 x2 (m_subst e1 x e2)) (swap_var x1 x2 x)
                                           (swap x1 x2 (swap z x1 e3)))).
                                           ***** apply aeq_m_subst_1. apply aeq_swap0.
                                                 ****** default_simp.
                                                 ****** rewrite swap_id in *. apply (fv_nom_m_subst_in _ e2) in H2. rewrite H2 in n2. simpl in n2.
                                                        pose proof in_or_notin. specialize (H4 x (fv_nom e2)). destruct H4.
                                                        ******* apply (fv_nom_m_subst_in _ e1) in H4. rewrite H4.
                                                                simpl. apply notin_union_3.
                                                                ******** apply diff_remove;default_simp.
                                                                ******** default_simp.
                                                        ******* apply (fv_nom_m_subst_notin _ e1) in H4. rewrite H4. 
                                                                apply diff_remove;default_simp.
                                           ***** apply aeq_sym. apply aeq_swap_m_subst.
                                  *** rewrite shuffle_swap;default_simp. rewrite swap_symmetric.
                                      rewrite shuffle_swap;default_simp. apply  (aeq_trans _ (m_subst e1 x (m_subst e2 x
                                      (swap z x2 e3)))).
                                      **** apply aeq_m_subst_2. apply aeq_m_subst_2. apply aeq_sym. apply aeq_swap0.
                                           ***** apply fv_nom_swap. apply (fv_nom_m_subst_in _ e2) in H2.
                                                 rewrite H2 in n2. simpl in n2. apply notin_union_2 in n2.
                                                 apply notin_union_1 in n2. apply diff_remove_2 in n2.
                                                 ****** apply notin_union_1 in n2. apply diff_remove_2 in n2;default_simp.
                                                        apply fv_nom_swap_remove in n2;default_simp.
                                                 ****** assumption.
                                           ***** apply fv_nom_remove_swap;default_simp.
                                      **** apply (aeq_trans _ (m_subst (m_subst e1 x e2) (swap_var x1 x2 x) 
                                           (swap x1 x2 (swap z x1 e3)))).
                                           ***** unfold swap_var. pose proof n1. repeat apply notin_union_2 in H4.
                                                 apply notin_singleton_1 in H4. default_simp.
                                                 rewrite (swap_symmetric _ x1 x2). rewrite (swap_symmetric _ z x1).
                                                 case (x1 == z);intros.
                                                 ****** rewrite e in *. rewrite swap_id. rewrite swap_symmetric.
                                                        apply H. reflexivity.
                                                 ****** rewrite shuffle_swap;default_simp. rewrite (swap_symmetric _ x2 z).
                                                        rewrite shuffle_swap;default_simp. apply (aeq_trans _ 
                                                        (m_subst (m_subst e1 x e2) x (swap z x2 e3))).
                                                        ******* apply H. reflexivity.
                                                        ******* apply aeq_m_subst_2. apply aeq_swap0.
                                                                ******** apply fv_nom_swap. apply (fv_nom_m_subst_in _ e2) in H2.
                                                                         rewrite H2 in n2. simpl in n2. apply notin_union_2 in n2.
                                                                         apply notin_union_1 in n2. apply diff_remove_2 in n2.
                                                                         + apply notin_union_1 in n2. apply diff_remove_2 in n2;
                                                                           default_simp. apply fv_nom_swap_remove in n2;default_simp.
                                                                         + assumption.
                                                                ******** apply fv_nom_remove_swap;default_simp.
                                           ***** apply (aeq_trans _ (m_subst (swap x1 x2 (m_subst e1 x e2)) (swap_var x1 x2 x)
                                                 (swap x1 x2 (swap z x1 e3)))).
                                                 ****** apply aeq_m_subst_1. apply aeq_swap0.
                                                        ******* default_simp.
                                                        ******* apply (fv_nom_m_subst_in _ e2) in H2. pose proof n2.
                                                                rewrite H2 in n2. simpl in n2. apply notin_union_2 in n2.
                                                                apply notin_union_1 in n2. apply diff_remove_2 in n2.
                                                                + apply notin_union_2 in n2. pose proof in_or_notin.
                                                                  specialize (H5 x (fv_nom e2)). destruct H5.
                                                                  ++ apply (fv_nom_m_subst_in _ e1) in H5. rewrite H5.
                                                                     simpl. apply notin_union_3;default_simp.
                                                                  ++ apply (fv_nom_m_subst_notin _ e1) in H5. rewrite H5.
                                                                     apply diff_remove;default_simp.
                                                                + assumption.
                                                 ****** apply aeq_sym. apply aeq_swap_m_subst.
                      ------ apply (aeq_trans _ (m_subst e1 x (swap x0 x2 (swap z x0 e3)))).
                             ------- apply aeq_m_subst_2. apply aeq_swap. apply subst_fresh_eq. assumption.
                             ------- apply (aeq_trans _ (swap x1 x2 (swap z x1 e3))).
                                     * apply (aeq_trans _ (swap x0 x2 (swap z x0 e3))).
                                       ** apply subst_fresh_eq. apply fv_nom_remove_swap;default_simp.
                                       ** case (z == x1);intros.
                                          *** rewrite e in *. rewrite swap_id. rewrite swap_symmetric.
                                              rewrite (swap_symmetric _ x1 x0).
                                              case (x0 == x1);intros.
                                              **** rewrite e0 in *. rewrite swap_id. rewrite swap_symmetric.
                                                   apply aeq_refl.
                                              **** rewrite shuffle_swap;default_simp. rewrite swap_symmetric.
                                                   rewrite shuffle_swap;default_simp.
                                                   apply aeq_sym. apply aeq_swap0.
                                                   ***** apply fv_nom_swap. apply (fv_nom_m_subst_notin _ e2) in H2.
                                                         rewrite H2 in n2. pose proof n2. apply notin_union_2 in n2.
                                                         apply notin_union_1 in n2. apply diff_remove_2 in n2;try assumption.
                                                         apply diff_remove_2 in n2;default_simp.
                                                         apply fv_nom_swap_remove in n2;default_simp.
                                                   ***** apply fv_nom_remove_swap;default_simp.
                                          *** case (z == x0);intros.
                                              **** rewrite e in *. rewrite swap_id. rewrite (swap_symmetric _ x1 x2).
                                                   rewrite (swap_symmetric _ x0 x1). rewrite shuffle_swap;default_simp.
                                                   rewrite swap_symmetric. apply aeq_swap. apply aeq_swap0.
                                                   ***** rewrite swap_id in *. apply (fv_nom_m_subst_notin _ e2) in H2.
                                                         rewrite H2 in n2. pose proof n2. apply notin_union_2 in n2.
                                                         apply notin_union_1 in n2. apply diff_remove_2 in n2;try assumption.
                                                         apply diff_remove_2 in n2;default_simp.
                                                   ***** default_simp.
                                              **** case (z == x2);intros.
                                                   ***** rewrite e in *. rewrite swap_symmetric. rewrite swap_involutive.
                                                         rewrite swap_symmetric. rewrite swap_involutive. apply aeq_refl.
                                                   ***** rewrite swap_symmetric. rewrite (swap_symmetric _ z x0).
                                                         rewrite shuffle_swap;default_simp.
                                                         rewrite (swap_symmetric _ x1 x2).
                                                         rewrite (swap_symmetric _ z x1).
                                                         rewrite shuffle_swap;default_simp. apply aeq_swap.
                                                         apply (aeq_trans _ e3).
                                                         ****** apply aeq_sym. apply aeq_swap0.
                                                                ******* apply (fv_nom_m_subst_notin _ e2) in H2.
                                                                        rewrite H2 in n2. pose proof n2.
                                                                        apply notin_union_2 in n2.
                                                                        apply notin_union_1 in n2.
                                                                        apply diff_remove_2 in n2;try assumption.
                                                                        apply diff_remove_2 in n2;default_simp.
                                                                        apply fv_nom_swap_remove in n2;default_simp.
                                                                ******* default_simp.
                                                         ****** apply aeq_swap0.
                                                                ******* apply (fv_nom_m_subst_notin _ e2) in H2.
                                                                        rewrite H2 in n2. pose proof n2.
                                                                        apply notin_union_2 in n2.
                                                                        apply notin_union_1 in n2.
                                                                        apply diff_remove_2 in n2;try assumption.
                                                                        apply diff_remove_2 in n2;default_simp.
                                                                        apply fv_nom_swap_remove in n2;default_simp.
                                                                ******* default_simp.
                                     * apply aeq_swap. apply aeq_sym. apply subst_fresh_eq.
                                       apply fv_nom_remove_swap;default_simp.
                                       apply fv_nom_swap_remove in H2;default_simp. 
 - pose proof subst_app. rewrite H. rewrite H. rewrite H. apply aeq_app.
   -- apply IHe3_1.
   -- apply IHe3_2.
 - pose proof subst_sub. rewrite H0. rewrite H0. case (x == z);intros.
   -- rewrite e in *. rewrite H0. default_simp. apply aeq_sub_same.
      --- apply aeq_refl.
      --- apply IHe3_1.
   -- default_simp. rewrite H0. pose proof n0. repeat apply notin_union_2 in H1. apply notin_singleton_1 in H1.
      default_simp. case (x1 == x2);intros.
      --- rewrite e in *. apply aeq_sub_same.
          ---- apply (aeq_trans _ (m_subst e1 x (m_subst e2 x (swap x0 x2 (swap z x0 e3_1))))).
               ----- apply aeq_m_subst_2. apply (aeq_trans _ (m_subst (swap x0 x2 e2) (swap_var x0 x2 x)
                     (swap x0 x2 (swap z x0 e3_1)))).
                     ------ apply aeq_swap_m_subst.
                     ------ unfold swap_var. pose proof n0. pose proof n1. repeat apply notin_union_2 in n1.
                            repeat apply notin_union_2 in n0. apply notin_singleton_1 in n0.
                            apply notin_singleton_1 in n1. default_simp. apply aeq_m_subst_1.
                            apply aeq_sym. apply aeq_swap0.
                            * default_simp.
                            * pose proof in_or_notin. specialize (H4 x (fv_nom e2)). destruct H4.
                              ** apply (fv_nom_m_subst_in _ e1) in H4. rewrite H4 in H3. simpl in H3.
                                 default_simp.
                              ** apply (fv_nom_m_subst_notin _ e1) in H4. rewrite H4 in H3. default_simp.
               ----- rewrite swap_symmetric. rewrite (swap_symmetric _ z x0). case (x2 == z);intros.
                     ------ rewrite e0 in *. rewrite swap_symmetric. rewrite swap_involutive.
                            rewrite <- (swap_id e3_1 z) at 1. apply H. reflexivity.
                     ------ case (x0 == z);intros.
                            * rewrite e0 in *. rewrite swap_id. rewrite swap_symmetric. apply H. reflexivity.
                            * rewrite shuffle_swap;default_simp. rewrite swap_symmetric.
                              case (x2 == x0);intros.
                              ** rewrite e in *. rewrite swap_id. apply H. reflexivity.
                              ** rewrite shuffle_swap;default_simp. apply (aeq_trans _ (m_subst e1 x
                                 (m_subst e2 x (swap z x2 e3_1)))).
                                 *** apply aeq_m_subst_2. apply aeq_m_subst_2. apply aeq_sym.
                                     apply aeq_swap0.
                                     **** apply fv_nom_swap. default_simp.
                                     **** apply fv_nom_remove_swap;default_simp.
                                 *** apply H. reflexivity.
          ---- apply IHe3_1.
      --- apply aeq_sub_diff.
          ---- apply IHe3_1.
          ---- default_simp.
          ---- pose proof in_or_notin. specialize (H2 x (fv_nom (swap z x0 e3_1))). destruct H2.
               ----- pose proof H2. pose proof n2. apply (fv_nom_m_subst_in _ e2) in H2. rewrite H2 in n2. simpl in n2.
                     apply notin_union_2 in n2. apply notin_union_1 in n2.
                     apply notin_union_1 in n2. apply in_swap in H3.
                     * pose proof H3. apply (in_swap _ _ z x1) in H3.
                       ** apply (fv_nom_m_subst_in _ (m_subst e1 x e2)) in H3. rewrite H3. simpl.
                          apply notin_union_3.
                          *** apply diff_remove.
                              **** default_simp.
                              **** case (x2 == x0);intros.
                                   ***** rewrite e in *. case (x0 == z);intros.
                                         ****** rewrite e0 in *. apply fv_nom_swap. apply notin_union_2 in n1.
                                                repeat apply notin_union_1 in n1. apply diff_remove_2 in n1;default_simp.
                                         ****** apply notin_union_2 in n0. repeat apply notin_union_1 in n0.
                                                apply fv_nom_remove_swap.
                                                ******* default_simp.
                                                ******* assumption.
                                                ******* apply diff_remove_2 in n0;default_simp.
                                   ***** apply diff_remove_2 in n2;try assumption. apply notin_union_1 in n2.
                                         apply diff_remove_2 in n2;default_simp. case (x2 == z);intros.
                                         ****** rewrite e in *. apply fv_nom_swap. default_simp.
                                         ****** apply fv_nom_remove_swap;default_simp.
                                                apply fv_nom_swap_remove in n2;default_simp.
                          *** pose proof in_or_notin. specialize (H6 x (fv_nom e2)). destruct H6.
                              **** apply (fv_nom_m_subst_in _ e1) in H6. rewrite H6.
                                   simpl. apply notin_union_3.
                                   ***** apply diff_remove.
                                         ****** repeat apply notin_union_2 in H4. apply notin_singleton_1 in H4.
                                                default_simp.
                                         ****** case (x2 == x0);intros.
                                                ******* rewrite e in *. default_simp.
                                                ******* apply diff_remove_2 in n2;default_simp.
                                   ***** default_simp.
                              **** apply (fv_nom_m_subst_notin _ e1) in H6. rewrite H6.
                                   apply diff_remove.
                                   ***** repeat apply notin_union_2 in H4. apply notin_singleton_1 in H4.
                                         default_simp.
                                   ***** case (x2 == x0);intros.
                                         ****** rewrite e in *. default_simp.
                                         ****** apply diff_remove_2 in n2;default_simp.             
                       ** assumption.
                       ** default_simp.
                     * assumption.
                     * assumption.
               ----- assert (H': x `notin` fv_nom (swap z x1 e3_1)).
                     * apply fv_nom_remove_swap;default_simp. apply fv_nom_swap_remove in H2;default_simp.
                     * apply (fv_nom_m_subst_notin _ e2) in H2. apply (fv_nom_m_subst_notin _ (m_subst e1 x e2)) in H'.
                       rewrite H'. pose proof n2. rewrite H2 in n2. apply notin_union_2 in n2. apply notin_union_1 in n2.
                       apply notin_union_1 in n2. case (x2 == x0);intros.
                       ** rewrite e in *. apply diff_remove.
                          *** default_simp.
                          *** case (x0 == z);intros.
                              **** rewrite e0 in *. apply fv_nom_swap. apply notin_union_2 in n1.
                                   repeat apply notin_union_1 in n1. apply diff_remove_2 in n1;default_simp.
                              **** apply fv_nom_remove_swap.
                                   ***** default_simp.
                                   ***** assumption.
                                   ***** apply notin_union_2 in n0.
                                         repeat apply notin_union_1 in n0. apply diff_remove_2 in n0;default_simp.
                       ** apply diff_remove.
                          *** default_simp.
                          *** apply diff_remove_2 in n2;try assumption. apply diff_remove_2 in n2;default_simp.
                              case (x2 == z);intros.
                              **** rewrite e in *. apply fv_nom_swap. default_simp.
                              **** apply fv_nom_remove_swap;default_simp.
                                   apply fv_nom_swap_remove in n2;default_simp.
          ---- pose proof in_or_notin. specialize (H2 x (fv_nom (swap z x0 e3_1))). destruct H2.
               ----- apply (fv_nom_m_subst_in _ e2) in H2. rewrite H2 in n2. simpl in n2.
                     case (x0 == x2);intros.
                     ------ rewrite e in *. rewrite swap_id. apply (aeq_trans _
                            (m_subst (m_subst e1 x e2) x (swap x1 x2 (swap z x1 e3_1)))).
                            * rewrite (swap_symmetric _ x1 x2). rewrite (swap_symmetric _ z x1).
                              case (x1 == z);intros.
                              ** rewrite e0 in *. rewrite swap_symmetric. rewrite swap_id. apply H. reflexivity.
                              ** case (x2 == z);intros.
                                 *** rewrite e0 in *. rewrite (swap_symmetric _ z x1). rewrite swap_involutive.
                                     rewrite <- (swap_id e3_1 z) at 2. apply H. reflexivity.
                                 *** rewrite shuffle_swap;default_simp. rewrite (swap_symmetric _ x2 z).
                                     rewrite shuffle_swap;default_simp. apply (aeq_trans _
                                     (m_subst (m_subst e1 x e2) x (swap z x2 e3_1))).
                                     **** apply H. reflexivity.
                                     **** apply aeq_m_subst_2. apply aeq_swap0.
                                          ***** apply fv_nom_swap. default_simp.
                                          ***** apply fv_nom_remove_swap;default_simp.
                            * apply (aeq_trans _ (m_subst (swap x1 x2 (m_subst e1 x e2)) (swap_var x1 x2 x)
                              (swap x1 x2 (swap z x1 e3_1)))).
                              ** unfold swap_var. pose proof n1. repeat apply notin_union_2 in H3. apply notin_singleton_1 in H3.
                                 default_simp. apply aeq_m_subst_1. apply aeq_swap0.
                                 *** default_simp.
                                 *** pose proof in_or_notin. specialize (H4 x (fv_nom e2)). destruct H4.
                                     **** apply (fv_nom_m_subst_in _ e1) in H4. rewrite H4. simpl.
                                          apply notin_union_3;default_simp.
                                     **** apply (fv_nom_m_subst_notin _ e1) in H4. rewrite H4. default_simp.
                              ** apply aeq_sym. apply aeq_swap_m_subst.
                     ------ apply (aeq_trans _ (m_subst e1 x (m_subst e2 x (swap x0 x2 (swap z x0 e3_1))))).
                            * apply aeq_m_subst_2. apply (aeq_trans _ (m_subst (swap x0 x2 e2) (swap_var x0 x2 x)
                              (swap x0 x2 (swap z x0 e3_1)))).
                              ** apply aeq_swap_m_subst.
                              ** unfold swap_var. pose proof n2. repeat apply notin_union_2 in n2. apply notin_singleton_1 in n2.
                                 default_simp. apply aeq_m_subst_1. apply aeq_sym. apply aeq_swap0.
                                 *** default_simp.
                                 *** default_simp.
                            * apply (aeq_trans _ (m_subst (m_subst e1 x e2) x (swap x1 x2 (swap z x1 e3_1)))).
                              ** case (x0 == x1);intros.
                                 *** rewrite e in *. apply H. rewrite swap_size_eq. reflexivity.
                                 *** rewrite swap_symmetric. rewrite (swap_symmetric _ z x0).
                                     case (x2 == z);intros.
                                     **** rewrite e in *. rewrite swap_symmetric. rewrite swap_involutive.
                                          rewrite swap_symmetric. rewrite swap_involutive.
                                          rewrite <- (swap_id e3_1 z). apply H. reflexivity.
                                     **** case (x0 == z);intros.
                                          ***** rewrite e in *. rewrite swap_id. rewrite (swap_symmetric _ x1 x2).
                                                rewrite (swap_symmetric _ z x1). rewrite shuffle_swap;default_simp.
                                                apply (aeq_trans _ (m_subst (m_subst e1 x e2) x (swap x2 z e3_1))).
                                                ****** apply H. reflexivity.
                                                ****** apply aeq_m_subst_2. apply aeq_swap. apply aeq_swap0.
                                                       ******* rewrite swap_id in n2. default_simp.
                                                       ******* default_simp.
                                          ***** rewrite shuffle_swap;default_simp. apply (aeq_trans _ 
                                                (m_subst e1 x (m_subst e2 x (swap x2 z e3_1)))).
                                                ****** apply aeq_m_subst_2. apply aeq_m_subst_2. apply aeq_swap.
                                                       apply aeq_sym. apply aeq_swap0.
                                                       ******* pose proof n2. apply notin_union_2 in n2.
                                                               repeat apply notin_union_1 in n2.
                                                               apply diff_remove_2 in n2.
                                                               ******** apply notin_union_1 in n2. apply diff_remove_2 in n2.
                                                                        ********* apply fv_nom_swap_remove in n2;default_simp.
                                                                        ********* default_simp.
                                                               ******** default_simp.
                                                       ******* apply notin_union_2 in n0. repeat apply notin_union_1 in n0.
                                                               apply diff_remove_2 in n0;default_simp.
                                                ****** rewrite (swap_symmetric _ x1 x2).
                                                       rewrite (swap_symmetric _ z x1). case (z == x1);intros.
                                                       ******* rewrite e in *. rewrite swap_id. apply H. reflexivity.
                                                       ******* rewrite shuffle_swap;default_simp. apply (aeq_trans _ 
                                                               (m_subst (m_subst e1 x e2) x (swap x2 z e3_1))).
                                                               ******** apply H. reflexivity.
                                                               ******** apply aeq_m_subst_2. apply aeq_swap.
                                                                        apply aeq_swap0.
                                                                        ********* pose proof n2. apply notin_union_2 in n2.
                                                                                  repeat apply notin_union_1 in n2.
                                                                                  apply diff_remove_2 in n2.
                                                                                  + apply notin_union_1 in n2.
                                                                                    apply diff_remove_2 in n2.
                                                                                    ++ apply fv_nom_swap_remove in n2;default_simp.
                                                                                    ++ default_simp.
                                                                                  + default_simp.
                                                                        ********* default_simp.
                              ** apply (aeq_trans _ (m_subst (swap x1 x2 (m_subst e1 x e2)) (swap_var x1 x2 x)
                                 (swap x1 x2 (swap z x1 e3_1)))).
                                 *** unfold swap_var. pose proof n1. pose proof n2. repeat apply notin_union_2 in H3.
                                     repeat apply notin_union_2 in H4. apply notin_singleton_1 in H3.
                                     apply notin_singleton_1 in H4. default_simp. apply aeq_m_subst_1. apply aeq_swap0.
                                     **** default_simp.
                                     **** pose proof in_or_notin. specialize (H5 x (fv_nom e2)). destruct H5.
                                          ***** apply (fv_nom_m_subst_in _ e1) in H5. rewrite H5. simpl.
                                                apply notin_union_3;default_simp.
                                          ***** apply (fv_nom_m_subst_notin _ e1) in H5. rewrite H5. default_simp.
                                 *** apply aeq_sym. apply aeq_swap_m_subst.
               ----- assert (H': x `notin` fv_nom (swap z x1 e3_1)).
                     ------- apply fv_nom_remove_swap;default_simp. apply fv_nom_swap_remove in H2;default_simp.
                     ------- apply (aeq_trans _ (m_subst e1 x (swap x0 x2 (swap z x0 e3_1)))).
                             * apply aeq_m_subst_2. apply aeq_swap. apply subst_fresh_eq. assumption.
                             * apply (aeq_trans _ (swap x1 x2 (swap z x1 e3_1))).
                               ** apply (aeq_trans _ (swap x0 x2 (swap z x0 e3_1))).
                                  *** apply subst_fresh_eq. apply fv_nom_remove_swap;default_simp.
                                  *** case (z == x0);intros.
                                      **** rewrite e in *. rewrite swap_id. case (x0 == x1);intros.
                                           ***** rewrite e0 in *. rewrite swap_id. apply aeq_refl.
                                           ***** rewrite (swap_symmetric _ x1 x2). rewrite (swap_symmetric _ x0 x1).
                                                 case (x2 == x0);intros.
                                                 ****** rewrite e0 in *. rewrite swap_id. rewrite swap_symmetric.
                                                        rewrite swap_involutive. apply aeq_refl.
                                                 ****** rewrite shuffle_swap;default_simp. rewrite swap_symmetric.
                                                        apply aeq_swap. apply aeq_swap0.
                                                        + pose proof n2. apply notin_union_2 in n2. repeat apply notin_union_1 in n2.
                                                          apply (fv_nom_m_subst_notin _ e2) in H2. rewrite H2 in n2.
                                                          simpl in n2. apply diff_remove_2 in n2.
                                                          ++ rewrite swap_id in n2. apply diff_remove_2 in n2;default_simp.
                                                          ++ assumption.
                                                        + default_simp.
                                      **** case (z == x2);intros.
                                           ***** rewrite e in *. rewrite swap_symmetric. rewrite swap_involutive.
                                                 rewrite swap_symmetric. rewrite swap_involutive. apply aeq_refl.
                                           ***** rewrite swap_symmetric. rewrite (swap_symmetric _ z x0).
                                                 rewrite shuffle_swap;default_simp. case(z == x1);intros.
                                                 ****** rewrite e in *. rewrite swap_id. rewrite swap_symmetric.
                                                        apply aeq_swap. apply aeq_sym. case (x2 == x0);intros.
                                                        + rewrite e0. rewrite swap_id. apply aeq_refl. 
                                                        + apply aeq_swap0.
                                                          ++ pose proof n2. apply notin_union_2 in n2.
                                                             repeat apply notin_union_1 in n2. apply diff_remove_2 in n2.
                                                             +++ apply (fv_nom_m_subst_notin _ e2) in H2. rewrite H2 in n2.
                                                                 apply diff_remove_2 in n2.
                                                                 ++++ apply fv_nom_swap_remove in n2;default_simp.
                                                                 ++++ default_simp.
                                                             +++ default_simp.
                                                          ++ default_simp.
                                                 ****** rewrite (swap_symmetric _ x1 x2). rewrite (swap_symmetric _ z x1).
                                                        rewrite shuffle_swap;default_simp. apply aeq_swap.
                                                        apply (aeq_trans _ e3_1).
                                                        + apply aeq_sym. apply aeq_swap0.
                                                          ++ case (x2 == x0);intros.
                                                             +++ rewrite e in *. default_simp.
                                                             +++ pose proof n2. apply notin_union_2 in n2.
                                                                 repeat apply notin_union_1 in n2. apply diff_remove_2 in n2.
                                                                 ++++ apply (fv_nom_m_subst_notin _ e2) in H2. rewrite H2 in n2.
                                                                      apply diff_remove_2 in n2.
                                                                      +++++ apply fv_nom_swap_remove in n2;default_simp.
                                                                      +++++ default_simp.
                                                                 ++++ default_simp.
                                                          ++ default_simp.
                                                        + apply aeq_swap0.
                                                          ++ case (x2 == x0);intros.
                                                             +++ rewrite e in *. default_simp.
                                                             +++ pose proof n2. apply notin_union_2 in n2.
                                                                 repeat apply notin_union_1 in n2. apply diff_remove_2 in n2.
                                                                 ++++ apply (fv_nom_m_subst_notin _ e2) in H2. rewrite H2 in n2.
                                                                      apply diff_remove_2 in n2.
                                                                      +++++ apply fv_nom_swap_remove in n2;default_simp.
                                                                      +++++ default_simp.
                                                                 ++++ default_simp.
                                                          ++ default_simp.
                               ** apply aeq_swap. apply aeq_sym. apply subst_fresh_eq. assumption.
Qed.

Lemma aeq_swap_B: forall e1 x1 x2, aeq (B (swap x1 x2 e1)) (swap x1 x2 (B e1)).
Proof.
  induction e1 using n_sexp_size_induction;intros;destruct e1 eqn:He1.
  - simpl. apply aeq_refl.
  - simpl. apply aeq_abs_same. apply H. simpl. lia.
  - destruct n1.
    -- simpl. apply aeq_app;try apply aeq_refl. apply H. simpl. lia.
    -- default_simp. apply (aeq_trans _ (m_subst (swap x1 x2 (B n2)) (swap_var x1 x2 x) (swap x1 x2 (B n1)))).
       --- apply (aeq_trans _ (m_subst (B (swap x1 x2 n2)) (swap_var x1 x2 x) (swap x1 x2 (B n1)))).
           ---- apply aeq_m_subst_2. apply H. lia.
           ---- apply aeq_m_subst_1. apply H. lia.
       --- apply aeq_sym. apply aeq_swap_m_subst.
    -- assert (H': (B (swap x1 x2 (n_app (n_app n1_1 n1_2) n2))) = (n_app (B (swap x1 x2 (n_app n1_1 n1_2))) (B (swap x1 x2 n2)))).
       default_simp. assert (H'': (swap x1 x2 (B (n_app (n_app n1_1 n1_2) n2))) = (n_app (swap x1 x2 (B (n_app n1_1 n1_2)))
       (swap x1 x2 (B n2)))). default_simp. rewrite H'. rewrite H''. apply aeq_app;apply H; simpl; lia.
    -- simpl. apply aeq_app.
       --- apply aeq_sub_same;apply H;simpl;lia.
       --- apply H. simpl. lia.
  - simpl. apply aeq_sub_same;apply H;simpl;lia.
Qed.
 
Lemma aeq_B: forall e1 e2, e1 =a e2 -> (B e1) =a (B e2).
Proof.
  induction e1 using n_sexp_induction;intros.
  - inversion H. simpl. apply aeq_refl.
  - inversion H0.
    -- subst. simpl. apply aeq_abs_same. rewrite <- (swap_id e1 z). apply H.
       --- reflexivity.
       --- rewrite swap_id. assumption.
    -- subst. simpl. apply aeq_abs_diff.
       --- assumption.
       --- apply notin_B. assumption.
       --- apply (aeq_trans _ (B (swap y z t2))).
           ---- rewrite <- (swap_id e1 z). apply H.
                * reflexivity.
                * rewrite swap_id. assumption.
           ---- apply aeq_swap_B.
  - destruct e1_1;inversion H.
    -- simpl. inversion H2. simpl. apply aeq_app.
       --- apply aeq_refl.
       ---  apply IHe1_2. assumption.
    -- simpl. inversion H2;subst.
       --- apply (aeq_trans _ (m_subst (B t2') x (B e1_1))).
           ---- apply aeq_m_subst_1. apply IHe1_2. assumption.
           ---- apply aeq_m_subst_2. apply IHe1_1 in H2. simpl in H2. inversion H2.
                * assumption.
                * default_simp.
       --- apply (aeq_trans _ (m_subst (B t2') x (B e1_1))).
           ---- apply aeq_m_subst_1. apply IHe1_2. assumption.
           ---- apply aeq_m_subst_3.
                * assumption.
                * apply notin_B. assumption.
                * apply IHe1_1 in H2. simpl in H2. inversion H2.
                  ** default_simp.
                  ** rewrite swap_symmetric. assumption.
    -- inversion H2. assert (H': (B (n_app (n_app e1_1_1 e1_1_2) e1_2)) = n_app (B (n_app e1_1_1 e1_1_2)) (B e1_2)).
       default_simp. assert (H'': (B (n_app (n_app t1'0 t2'0) t2')) = n_app (B (n_app t1'0 t2'0)) (B t2')).
       default_simp. rewrite H'. rewrite H''. apply aeq_app.
       --- apply IHe1_1. subst. assumption.
       --- apply IHe1_2. assumption.
    -- inversion H2;subst.
       --- simpl. apply aeq_app.
           ---- simpl in IHe1_1. apply IHe1_1 in H2. simpl in H2. assumption.
           ---- apply IHe1_2. assumption.
       --- simpl. apply aeq_app.
           ---- apply IHe1_1 in H2. simpl in H2. assumption.
           ---- apply IHe1_2. assumption.
  - inversion H0;subst.
    -- simpl. apply aeq_sub_same.
       --- rewrite <- (swap_id e1_1 z). apply H.
           ---- reflexivity.
           ---- rewrite swap_id. assumption.
       --- apply IHe1_1. assumption.
    -- simpl. apply aeq_sub_diff.
       --- apply IHe1_1. assumption.
       --- assumption.
       --- apply notin_B. assumption.
       --- rewrite <- (swap_id e1_1 z) in H8. apply H in H8.
           ---- rewrite swap_id in H8. apply (aeq_trans _ (B (swap y z t1'))).
                ----- assumption.
                ----- apply aeq_swap_B.
           ---- reflexivity.
Qed.

Lemma refltrans_rtrans_reduction (R: Rel n_sexp): forall e1 e2, (ctx R) e1 e2 -> refltrans (ctx R) e1 e2.
Proof.
  intros. apply (rtrans _ _ e2).
  - assumption.
  - apply refl.
Qed.

Lemma refltrans_m_subst_B: forall e1 e2 x, pure e1 -> pure e2 -> refltrans lx ({x := (B e2)}(B e1)) (B ({x := e2}e1)).
Proof.
  induction e1 using n_sexp_size_induction;intros.
  destruct e1 eqn:He.
  - simpl. unfold m_subst;default_simp;apply refl.
  - pose proof subst_abs. simpl. rewrite H2. rewrite H2. case (x == x0);intros.
    -- simpl. apply refltrans_abs. apply refl.
    -- default_simp. case (x1 == x2);intros.
       --- rewrite e in *. apply refltrans_abs. apply (rtrans _ _ (m_subst (B e2) x (B (swap x0 x2 n)))).
           ---- apply step_aeq. apply aeq_m_subst_2. apply swap_B.
           ---- apply H.
                ----- rewrite swap_size_eq. default_simp.
                ----- apply pure_swap. assumption.
                ----- assumption.
       --- apply (rtrans _ _ (n_abs x2 (swap x1 x2 (m_subst (B e2) x (swap x0 x1 (B n)))))).
           ---- apply step_aeq. apply aeq_abs_diff.
                ----- assumption.
                ----- apply fv_nom_swap. pose proof in_or_notin. specialize (H0 x (fv_nom (swap x0 x1 (B n)))).
                      destruct H0.
                      ------ apply (fv_nom_m_subst_in _ (B e2)) in H0. rewrite H0. simpl. apply notin_union_3.
                             * apply diff_remove;default_simp. case (x2 == x0);intros.
                               ** rewrite e in *. apply fv_nom_swap. default_simp.
                               ** apply fv_nom_remove_swap;default_simp. apply notin_B. default_simp.
                             * apply notin_B. default_simp.
                      ------ apply (fv_nom_m_subst_notin _ (B e2)) in H0. rewrite H0.
                             apply diff_remove;default_simp. case (x2 == x0);intros.
                             * rewrite e in *. apply fv_nom_swap. default_simp.
                             * apply fv_nom_remove_swap;default_simp. apply notin_B. default_simp.
                ----- rewrite (swap_symmetric _ x2 x1). rewrite swap_involutive. apply aeq_refl.
           ---- apply refltrans_abs. apply (rtrans _ _ (m_subst (B e2) x (swap x1 x2 (swap x0 x1 (B n))))).
                ----- apply step_aeq. apply (aeq_trans _ (m_subst (swap x1 x2 (B e2)) (swap_var x1 x2 x)
                      (swap x1 x2 (swap x0 x1 (B n))))).
                      ------ apply aeq_swap_m_subst.
                      ------ unfold swap_var. pose proof n1. pose proof n2. repeat apply notin_union_2 in n1.
                             repeat apply notin_union_2 in n2. apply notin_singleton_1 in n1. apply notin_singleton_1 in n2.
                             default_simp. apply aeq_m_subst_1. apply aeq_sym. apply aeq_swap0.
                             * default_simp.
                             * apply notin_B. default_simp.
                ----- case (x1 == x0);intros.
                      ------ rewrite e in *. rewrite swap_id. apply (rtrans _ _ (m_subst (B e2) x (B (swap x0 x2 n)))).
                             * apply step_aeq. apply aeq_m_subst_2. apply aeq_sym. apply aeq_swap_B.
                             * apply H.
                               ** rewrite swap_size_eq. lia.
                               ** apply pure_swap. assumption.
                               ** assumption.
                      ------ case (x2 == x0);intros.
                             * rewrite e in *. rewrite swap_symmetric. rewrite swap_involutive. rewrite swap_id.
                               apply H.
                               ** lia.
                               ** assumption.
                               ** assumption.
                             * rewrite swap_symmetric. rewrite (swap_symmetric _ x0 x1). rewrite shuffle_swap;default_simp.
                               rewrite swap_symmetric. apply (rtrans _ _ (m_subst (B e2) x (B (swap x0 x2 n)))).
                               ** apply step_aeq. apply aeq_m_subst_2. apply (aeq_trans _ (swap x0 x2 (B n))).
                                  *** apply aeq_swap. apply aeq_sym. apply aeq_swap0.
                                      **** apply notin_B. default_simp.
                                      **** default_simp.
                                  *** apply aeq_sym. apply aeq_swap_B.
                               ** apply H.
                                  *** rewrite swap_size_eq. lia.
                                  *** apply pure_swap. assumption.
                                  *** assumption.
  - pose proof subst_app. rewrite H2. destruct n1.
    -- simpl. case (x0 == x);intros.
       --- rewrite e in *. unfold m_subst at 2. default_simp. pose proof subst_app. destruct e2 eqn:He2.
           ---- rewrite H0. apply refltrans_app3.
                ----- assert (H': n_var x = (B (n_var x))). default_simp. rewrite H'. apply H.
                      * simpl. lia.
                      * simpl. apply pure_var.
                      * apply pure_var.
                ----- apply H.
                      * lia.
                      * assumption.
                      * apply pure_var.
           ---- simpl. rewrite H0. unfold m_subst at 1. default_simp.
                apply (rtrans _ _ (n_sub (B n) x0 (m_subst (n_abs x0 (B n)) x (B n2)))).
                ----- apply step_redex_R. apply b_rule. apply step_betax.
                ----- apply (refltrans_composition _ _ (n_sub (B n) x0 (B (m_subst (n_abs x0 n) x n2)))).
                      * apply refltrans_sub1. assert (H': n_abs x0 (B n) = B (n_abs x0 n)). default_simp. rewrite H'. apply H.
                        ** lia.
                        ** assumption.
                        ** assumption.
                      * apply refltrans_lx_pix. apply pure_pix. apply pure_B. inversion H1. assumption.
           ---- rewrite H0. apply refltrans_app3.
                ----- assert (H': n_var x = B (n_var x)). default_simp. rewrite H'. apply H.
                      * simpl. lia.
                      * simpl. apply pure_var.
                      * assumption.
                ----- apply H.
                      * lia.
                      * assumption.
                      * assumption.
           ---- inversion H1.
       --- unfold m_subst at 2. default_simp. pose proof subst_app. rewrite H0. apply refltrans_app3.
           ---- assert (H': n_var x0 = B (n_var x0)). default_simp. rewrite H'. apply H.
                ----- simpl. lia.
                ----- simpl. apply pure_var.
                ----- assumption.
           ---- apply H.
                ----- lia.
                ----- assumption.
                ----- assumption. 
    -- case (x == x0);intros.
       --- rewrite e in *. simpl. pose proof subst_abs. rewrite H3. default_simp.
           apply (rtrans _ _ (m_subst (m_subst (B e2) x0 (B n2)) x0 (B n1))).
           ---- apply step_aeq. apply aeq_double_m_subst.
           ---- apply refltrans_m_subst1. apply H.
                * lia.
                * assumption.
                * assumption.
       --- remember (B (n_app (m_subst e2 x (n_abs x0 n1)) (m_subst e2 x n2))) as expression.
           simpl. remember ( let (z,_) := (atom_fresh (Metatheory.union (fv_nom e2)
           (Metatheory.union (fv_nom n2) (Metatheory.union (fv_nom n1)
           (Metatheory.union (singleton x0) (singleton x)))))) in z) as x2. destruct (atom_fresh
           (Metatheory.union (fv_nom e2) (Metatheory.union (fv_nom n2)
           (Metatheory.union (fv_nom n1) (Metatheory.union (singleton x0) (singleton x)))))).
           apply (rtrans _ _ (m_subst (B e2) x (m_subst (B n2) x1 (swap x0 x1 (B n1)))) ).
           ---- apply step_aeq. apply aeq_m_subst_2. apply aeq_m_subst_3.
                ----- default_simp.
                ----- apply fv_nom_swap. apply notin_B. default_simp.
                ----- rewrite swap_involutive. apply aeq_refl.
           ---- apply (rtrans _ _ (m_subst (m_subst (B e2) x (B n2)) x1 (m_subst (B e2) x (swap x0 x1 (B n1))))).
                ----- apply step_aeq. apply m_subst_lemma.
                      * default_simp.
                      * apply notin_B. default_simp.
                ----- apply (refltrans_composition _ _ (m_subst (B (m_subst e2 x n2)) x1 (m_subst (B e2) x (swap x0 x1 (B n1))))).
                      * apply refltrans_m_subst1. inversion H0. apply H;try assumption. simpl. lia.
                      * apply (refltrans_composition _ _ (m_subst (B (m_subst e2 x n2)) x1 (B (m_subst e2 x (swap x0 x1 n1))))).
                        ** apply refltrans_m_subst2. inversion H0. inversion H5.
                           apply (rtrans _ _ (m_subst (B e2) x (B (swap x0 x1 n1)))).
                           *** apply step_aeq. apply aeq_m_subst_2. apply aeq_sym. apply aeq_swap_B.
                           *** apply H.
                               **** simpl. rewrite swap_size_eq. lia.
                               **** apply pure_swap. assumption.
                               **** assumption.
                        ** assert (H': (m_subst (B (m_subst e2 x n2)) x1 (B (m_subst e2 x (swap x0 x1 n1)))) = 
                          B (n_app (n_abs x1 (m_subst e2 x (swap x0 x1 n1))) (m_subst e2 x n2))).
                          *** simpl. reflexivity.
                          *** rewrite H'. rewrite Heqexpression. apply refltrans_rtrans_reduction. apply step_aeq.
                              apply aeq_B. apply aeq_app.
                              **** pose proof subst_abs. rewrite H3. default_simp. case (x1 == x2);intros.
                                   ***** rewrite e in *. apply aeq_refl.
                                   ***** apply aeq_abs_diff.
                                         ****** assumption.
                                         ****** pose proof in_or_notin. specialize (H4 x (fv_nom (swap x0 x2 n1))).
                                                destruct H4.
                                                + apply (fv_nom_m_subst_in _ e2) in H4. rewrite H4. simpl.
                                                  apply notin_union_3.
                                                  ++ apply diff_remove;default_simp. apply fv_nom_remove_swap;default_simp.
                                                  ++ default_simp.
                                                + apply (fv_nom_m_subst_notin _ e2) in H4. rewrite H4.
                                                  apply diff_remove;default_simp. apply fv_nom_remove_swap;default_simp.
                                         ****** apply (aeq_trans _ (m_subst e2 x (swap x2 x1 (swap x0 x2 n1)))).
                                                + rewrite (swap_symmetric _ x2 x1). rewrite (swap_symmetric _ x0 x2).
                                                  case (x2 == x0);intros.
                                                  ++ rewrite e in *. rewrite swap_symmetric. rewrite swap_id. apply aeq_refl.
                                                  ++ rewrite shuffle_swap;default_simp. rewrite swap_symmetric.
                                                     apply aeq_m_subst_2. apply aeq_swap. apply aeq_swap0;default_simp.
                                                + apply (aeq_trans _ (m_subst (swap x2 x1 e2) (swap_var x2 x1 x)
                                                  (swap x2 x1 (swap x0 x2 n1)))).
                                                  ++ unfold swap_var. pose proof n0. pose proof n3.
                                                     repeat apply notin_union_2 in n0. repeat apply notin_union_2 in n3.
                                                     apply notin_singleton_1 in n0. apply notin_singleton_1 in n3.
                                                     default_simp. apply aeq_m_subst_1. apply aeq_swap0;default_simp.
                                                  ++ apply aeq_sym. apply aeq_swap_m_subst.
                              **** apply aeq_refl. 
    -- assert (H': (B (n_app (n_app n1_1 n1_2) n2)) = n_app (B (n_app n1_1 n1_2)) (B n2)). default_simp.
       assert (H'': (B (n_app (m_subst e2 x (n_app n1_1 n1_2)) (m_subst e2 x n2))) = 
       n_app (B (m_subst e2 x (n_app n1_1 n1_2))) (B (m_subst e2 x n2))). default_simp.
       rewrite H'. rewrite H''. rewrite H2. apply refltrans_app3.
       --- apply H.
           ---- simpl. lia.
           ---- inversion H0. assumption.
           ---- assumption.
       --- apply H.
           ---- simpl. lia.
           ---- inversion H0. assumption.
           ---- assumption.
    -- inversion H0. inversion H5.
  - inversion H0.
Qed.

Lemma refltrans_m_subst (R: Rel n_sexp): forall e1 e2 e3 e4 x, refltrans (ctx R) e1 e2 -> 
  refltrans (ctx R) e3 e4 -> refltrans (ctx R) ({x := e3}e1) ({x := e4}e2).
Proof.
  intros. apply (refltrans_composition _ _ (m_subst e3 x e2)).
  - apply refltrans_m_subst2. assumption.
  - apply refltrans_m_subst1. assumption.
Qed.

Lemma pure_swap_2: forall x y t, pure (swap x y t) -> pure t.
Proof.
  intros. induction t.
  - apply pure_var.
  - apply pure_abs. simpl in H. inversion H. apply IHt. assumption.
  - apply pure_app.
    -- simpl in H. inversion H. apply IHt1. assumption.
    -- simpl in H. inversion H. apply IHt2. assumption.
  - inversion H.
Qed.

Lemma aeq_pure: forall e1 e2, e1 =a e2 -> pure e1 -> pure e2.
Proof.
  induction e1;intros.
  - inversion H. apply pure_var.
  - inversion H.
    -- apply pure_abs. inversion H0. apply IHe1 in H4;assumption.
    -- apply pure_abs. inversion H0. apply (pure_swap_2 y x). apply IHe1 in H6;assumption.
  - inversion H0. inversion H. apply pure_app.
    -- apply IHe1_1;assumption.
    -- apply IHe1_2;assumption.
  - inversion H0.
Qed.

(* 5.4.1 Nakazawa*)
Lemma refltrans_P_beta: forall e1 e2, lx e1 e2 -> refltrans (ctx beta) (P e1) (P e2).
Proof.
  intros. induction H.
  - apply (rtrans _ _ (P e2)).
    -- apply step_aeq. apply aeq_P. assumption.
    -- apply refl.
  - inversion H0.
    -- inversion H2. subst. inversion H. inversion H6.
       --- inversion H1.
           ---- simpl. apply (rtrans _ _ (m_subst (P t2) x (P t0))).
                ----- apply step_redex_R. apply step_beta.
                ----- apply refltrans_m_subst.
                      * apply (rtrans _ _ (P t1'0)).
                        ** apply step_aeq. apply aeq_P. apply (aeq_trans _ e0);assumption.
                        ** apply refl.
                      * apply (rtrans _ _ (P t2'0)).
                        ** apply step_aeq. apply aeq_P. apply (aeq_trans _ e5);assumption.
                        ** apply refl.
           ---- simpl. apply (rtrans _ _ (m_subst (P t2) x (P t0))).
                ----- apply step_redex_R. apply step_beta.
                ----- apply (refltrans_composition _ _ (m_subst (P t2'0) x (P (swap x y t1'0)))).
                      * apply refltrans_m_subst.
                        ** apply (rtrans _ _ (P (swap x y t1'0))).
                           *** apply step_aeq. apply aeq_P. rewrite swap_symmetric. apply (aeq_trans _ e0);assumption.
                           *** apply refl.
                        ** apply (rtrans _ _ (P t2'0)).
                           *** apply step_aeq. apply aeq_P. apply (aeq_trans _ e5);assumption.
                           *** apply refl.
                      * apply (rtrans _ _ (m_subst (P t2'0) y (P t1'0))).
                        ** apply step_aeq. apply aeq_m_subst_3.
                           *** assumption.
                           *** apply notin_P. assumption.
                           *** apply aeq_swap_P.
                        ** apply refl.
       --- simpl. apply (rtrans  _ _ (n_app (n_abs x (P (swap x x0 t0))) (P t2))).
           ---- apply step_aeq. apply aeq_app.
                * apply aeq_abs_diff.
                  ** assumption.
                  ** apply notin_P. apply (aeq_swap _ _ x x0) in H13. rewrite swap_involutive in H13.
                     apply aeq_fv_nom in H13. rewrite H13. assumption.
                  ** apply (aeq_swap _ _ x x0). rewrite swap_involutive. apply aeq_sym. apply aeq_swap_P.
                * apply aeq_refl.
           ---- inversion H1.
                ----- simpl. apply (rtrans _ _ (m_subst (P t2) x (P (swap x x0 t0)))).
                      ------ apply step_redex_R. apply step_beta.
                      ------ apply refltrans_m_subst.
                             * apply (rtrans _ _ (P t1'0)).
                               ** apply step_aeq. apply aeq_P.
                                  apply (aeq_swap _ _ x x0) in H13. rewrite swap_involutive in H13.
                                  apply (aeq_trans _ e0);assumption.
                               ** apply refl.
                             * apply (rtrans _ _ (P t2'0)).
                               ** apply step_aeq. apply aeq_P. apply (aeq_trans _ e5);assumption.
                               ** apply refl.
                ----- simpl. apply (rtrans _ _ (m_subst (P t2) x (P (swap x x0 t0)))).
                      ------ apply step_redex_R. apply step_beta.
                      ------ apply (refltrans_composition _ _ (m_subst (P t2'0) x (P (swap x y0 t1'0)))).
                             * apply refltrans_m_subst.
                               ** apply (rtrans _ _ (P (swap x y0 t1'0))).
                                  *** apply step_aeq. apply aeq_P. rewrite swap_symmetric.
                                      apply (aeq_swap _ _ x x0) in H13. rewrite swap_involutive in H13.
                                      rewrite swap_symmetric in H13. rewrite swap_symmetric in H21.
                                      apply (aeq_trans _ e0);assumption.
                                  *** apply refl.
                               ** apply (rtrans _ _ (P t2'0)).
                                  *** apply step_aeq. apply aeq_P. apply (aeq_trans _ e5);assumption.
                                  *** apply refl.
                             * apply (rtrans _ _ (m_subst (P t2'0) y0 (P t1'0))).
                               ** apply step_aeq. apply aeq_m_subst_3.
                                  *** assumption.
                                  *** apply notin_P. assumption.
                                  *** apply aeq_swap_P.
                               ** apply refl.
    -- inversion H2.
       --- subst. inversion H.
           ---- inversion H6. subst. simpl. unfold m_subst. simpl. default_simp.
                apply (rtrans _ _ (P e4)).
                ----- apply step_aeq. apply aeq_P. apply (aeq_trans _ e3);assumption.
                ----- apply refl.
           ---- simpl in H10. inversion H10. subst. unfold swap_var in *. default_simp.
                unfold m_subst. simpl. default_simp. apply (rtrans _ _ (P e4)).
                ----- apply step_aeq. apply aeq_P. apply (aeq_trans _ e3);assumption.
                ----- apply refl.
       --- subst. inversion H1. inversion H.
           ---- inversion H9. subst. simpl. unfold m_subst. simpl. default_simp. apply refl.
           ---- simpl in H13. inversion H13. subst. unfold swap_var. simpl in H12. apply notin_singleton_1 in H12.
                default_simp. unfold m_subst. default_simp. apply refl.
       --- subst. apply (rtrans _ _ (P (n_sub (n_abs y e0) y e5))).
           ---- apply step_aeq. apply aeq_P. assumption.
           ---- apply (refltrans_composition _ _ (P (n_abs y e0))).
                ----- simpl. unfold m_subst. default_simp. apply refl.
                ----- apply refltrans_rtrans_reduction. apply step_aeq. apply aeq_P. assumption.
       --- subst. apply (rtrans _ _ (P (n_sub (n_abs x e0) y e5))).
           ---- apply step_aeq. apply aeq_P. assumption.
           ---- apply (refltrans_composition _ _ (P (n_abs x (n_sub e0 y e5)))).
                ----- simpl. pose proof subst_abs. rewrite H3. default_simp.
                      apply (rtrans _ _ (n_abs x (swap x x0 (m_subst (P e5) y (swap x x0 (P e0)))))).
                      * apply step_aeq. case (x0 == x);intros.
                        ** rewrite e in *. repeat rewrite swap_id. apply aeq_refl.
                        ** apply aeq_abs_diff.
                          *** assumption.
                          *** rewrite swap_symmetric. apply fv_nom_swap. pose proof in_or_notin.
                              specialize (H4 y (fv_nom (swap x x0 (P e0)))). destruct H4.
                              **** apply (fv_nom_m_subst_in _ (P e5)) in H4. rewrite H4. simpl.
                                   apply notin_union_3.
                                   ***** apply diff_remove;try(assumption). apply fv_nom_swap.
                                         default_simp.
                                   ***** apply notin_P. assumption.
                              **** apply (fv_nom_m_subst_notin _ (P e5)) in H4. rewrite H4.
                                    apply diff_remove;try(assumption). apply fv_nom_swap.
                                    default_simp.
                          *** rewrite swap_involutive. apply aeq_refl.
                      * apply refltrans_rtrans_reduction. apply step_aeq. apply aeq_abs_same.
                        apply (aeq_trans _ (m_subst (swap x x0 (P e5)) (swap_var x x0 y)
                        (swap x x0 (swap x x0 (P e0))))).
                        ** apply aeq_swap_m_subst.
                        ** rewrite swap_involutive.  unfold swap_var. pose proof n. repeat apply notin_union_2 in H4.
                           apply notin_singleton_1 in H4. default_simp. apply (aeq_trans _
                           (m_subst (P e5) y (P e0))).
                           *** apply aeq_m_subst_1. apply aeq_sym. apply aeq_swap0.
                               **** apply notin_P. assumption.
                               **** default_simp.
                           *** apply aeq_refl.
                ----- apply refltrans_rtrans_reduction. apply step_aeq.
                      apply aeq_P. assumption.
       --- subst. apply (rtrans _ _ (P (n_sub (n_abs x e0) y e5))).
           ---- apply step_aeq. apply aeq_P. assumption.
           ---- apply (refltrans_composition _ _ (P (n_abs z (n_sub (swap x z e0) y e5)))).
                ----- simpl. pose proof subst_abs. rewrite H3. default_simp. case (z == x0);intros.
                      * rewrite e in *. apply refltrans_abs. apply refltrans_m_subst2.
                        apply refltrans_rtrans_reduction. apply step_aeq. apply aeq_sym.
                        apply aeq_swap_P.
                      * apply refltrans_rtrans_reduction. apply step_aeq. apply aeq_sym.
                        apply aeq_abs_diff.
                        ** assumption.
                        ** pose proof in_or_notin. specialize (H4 y (fv_nom (swap x x0 (P e0)))).
                           destruct H4.
                           *** apply (fv_nom_m_subst_in _ (P e5)) in H4. rewrite H4. simpl. apply notin_union_3.
                               **** apply diff_remove;try(assumption). case (z == x);intros.
                                    ***** rewrite e in *. apply fv_nom_swap. default_simp.
                                    ***** apply fv_nom_remove_swap;default_simp.
                                          apply notin_P. assumption.
                               **** apply notin_P. assumption.
                           *** apply (fv_nom_m_subst_notin _ (P e5)) in H4. rewrite H4.
                               apply diff_remove;try(assumption). case (z == x);intros.
                               **** rewrite e in *. apply fv_nom_swap. default_simp.
                               **** apply fv_nom_remove_swap;default_simp.
                                    apply notin_P. assumption.
                        ** apply (aeq_trans _ (m_subst (P e5) y (swap x0 z (swap x x0 (P e0))))).
                           *** apply aeq_m_subst_2. case (z == x);intros.
                               **** rewrite e in *. rewrite swap_id. rewrite swap_symmetric. 
                                    rewrite swap_involutive. apply aeq_refl.
                               **** case (x0 == x);intros.
                                    ***** rewrite e in *. rewrite swap_id. apply aeq_swap_P.
                                    ***** rewrite (swap_symmetric _ x0 z).
                                          rewrite (swap_symmetric _ x x0).
                                          rewrite shuffle_swap;default_simp.
                                          apply (aeq_trans _ (swap z x (P e0))).
                                          ****** rewrite swap_symmetric. apply aeq_swap_P.
                                          ****** apply aeq_swap. apply aeq_swap0.
                                                 ******* apply notin_P. assumption.
                                                 ******* default_simp.
                           *** apply (aeq_trans _ (m_subst (swap x0 z (P e5)) (swap_var x0 z y)
                               (swap x0 z (swap x x0 (P e0))))).
                               **** unfold swap_var. pose proof n. repeat apply notin_union_2 in H4.
                                    apply notin_singleton_1 in H4. default_simp.
                                    apply aeq_m_subst_1. apply aeq_swap0.
                                    ***** default_simp.
                                    ***** apply notin_P. assumption.
                               **** apply aeq_sym. apply aeq_swap_m_subst.                     
                ----- apply refltrans_rtrans_reduction. apply step_aeq. apply aeq_P. assumption.
       --- subst. apply (rtrans _ _ (P (n_sub (n_app e0 e5) y e6))).
           ---- apply step_aeq. apply aeq_P. assumption.
           ---- apply (refltrans_composition _ _ (P (n_app (n_sub e0 y e6) (n_sub e5 y e6)))).
                ----- simpl. pose proof subst_app. rewrite H3. apply refl. 
                ----- apply refltrans_rtrans_reduction. apply step_aeq. apply aeq_P. assumption.
  - simpl. apply refltrans_abs. assumption.
  - simpl. apply refltrans_app1. assumption.
  - simpl. apply refltrans_app2. assumption.
  - simpl. apply refltrans_m_subst2. assumption.
  - simpl. apply refltrans_m_subst1. assumption.
Qed.

(* 5.4.2 Nakazawa*)
Lemma refltrans_pure_beta: forall e1 e2, pure e1 -> pure e2 -> (ctx beta) e1 e2 ->
  refltrans lx e1 e2.
Proof.
  intros. induction H1.
  - apply refltrans_rtrans_reduction. apply step_aeq. assumption.
  - inversion H2. subst. inversion H1. inversion H7;subst.
    -- apply (rtrans _ _ (n_sub t0 x t2)).
       --- apply step_redex_R. apply b_rule. apply step_betax.
       --- apply (refltrans_composition _ _ (m_subst e5 x e0)).
           ----- apply (rtrans _ _ (n_sub e0 x e5)).
                 * apply step_aeq. apply aeq_sub_same;assumption.
                 * apply refltrans_lx_pix. apply pure_pix. inversion H.
                   inversion H6. apply aeq_pure in H11;assumption.
           ----- apply refltrans_rtrans_reduction. apply step_aeq. assumption.
    -- apply (refltrans_composition _ _ (n_app (n_abs x (swap x x0 t0)) t2)).
       --- apply refltrans_app1. apply refltrans_rtrans_reduction. apply step_aeq.
           apply aeq_abs_diff.
           ---- assumption.
           ---- apply (aeq_swap _ _ x x0) in H14. rewrite swap_involutive in H14.
                apply aeq_fv_nom in H14. rewrite H14. assumption.
           ---- rewrite swap_involutive. apply aeq_refl.
       --- apply (rtrans _ _ (n_sub (swap x x0 t0) x t2)).
           ---- apply step_redex_R. apply b_rule. apply step_betax.
           ---- apply (refltrans_composition _ _ (m_subst e5 x e0)).
                ------ apply (rtrans _ _ (n_sub e0 x e5)).
                       ** apply step_aeq. apply (aeq_swap _ _ x x0) in H14. rewrite swap_involutive in H14.
                          apply aeq_sub_same;assumption.
                       ** apply refltrans_lx_pix. apply pure_pix. inversion H.
                          inversion H6. apply (pure_swap_2 x x0). apply aeq_pure in H14;assumption.
                ------ apply refltrans_rtrans_reduction. apply step_aeq. assumption.
  - apply refltrans_abs. inversion H. inversion H0. apply IHctx;assumption.
  - apply refltrans_app1. inversion H. inversion H0. apply IHctx;assumption.
  - apply refltrans_app2. inversion H. inversion H0. apply IHctx;assumption.
  - inversion H.
  - inversion H.
Qed.

Lemma pure_beta_trans: forall e1 e2, pure e1 -> (ctx beta) e1 e2 -> pure e2.
Proof.
  intros. induction H0.
  - apply aeq_pure in H0;assumption.
  - inversion H1. subst. assert (H': pure (n_app (n_abs x e0) e5)).
    -- apply aeq_pure in H0;assumption.
    -- inversion H'. inversion H5. apply aeq_pure in H2;try assumption.
       apply pure_m_subst;assumption.
  - inversion H. apply pure_abs. apply IHctx. assumption.
  - inversion H. apply pure_app.
    -- apply IHctx. assumption.
    -- assumption.
  - inversion H. apply pure_app.
    -- assumption.
    -- apply IHctx. assumption.
  - inversion H.
  - inversion H.
Qed.

Lemma ctx_abs_beta: forall e1 e2 x, ctx beta (n_abs x e1) (n_abs x e2) -> 
  ctx beta e1 e2.
Proof.
  intros. inversion H.
  - inversion H0.
    -- apply step_aeq. assumption.
    -- default_simp.
  - inversion H0;subst;inversion H1.
  - assumption.
Qed.

Lemma Z_property_B_beta: forall e1 e2, pure e1 -> pure e2 -> (ctx beta) e1 e2 -> refltrans (ctx beta) e2 (B e1) /\ refltrans (ctx beta) (B e1) (B e2).
Proof.
Admitted.

Lemma refltrans_beta_imply_B: forall e1 e2, pure e1 -> pure e2 -> refltrans (ctx beta) e1 e2 -> refltrans (ctx beta) (B e1) (B e2). 
Proof.
  induction 3.
  - apply refl.
  - apply (refltrans_composition _ _ (B b)).
    -- pose proof H1. apply Z_property_B_beta in H1.
       --- destruct H1. assumption.
       --- assumption.
       --- apply (pure_beta_trans _ _ H H1);assumption.
    -- apply IHrefltrans.
       --- apply (pure_beta_trans _ _ H H1);assumption.
       --- assumption.
Qed.

Lemma refltrans_beta_to_lx: forall e1 e2, pure e1 -> pure e2 -> refltrans (ctx beta) e1 e2 -> refltrans lx e1 e2.
Proof.
  intros. induction H1.
  - apply refl.
  - pose proof H1. apply (refltrans_composition _ _ b).
    -- apply refltrans_pure_beta.
       --- assumption.
       --- apply (pure_beta_trans _ _ H H1);assumption.
       --- assumption.
    -- apply IHrefltrans.
       --- apply (pure_beta_trans _ _ H H1);assumption.
       --- assumption.
Qed.

Lemma lambda_x_Z_comp_eq: Z_comp_eq lx.
Proof.
  unfold Z_comp_eq.
  exists (ctx pix), (ctx betax), P, B.
  split.
  - apply ctx_betax_beta_pix. 
  - split.
    -- admit.
    -- split.
       --- apply refltrans_P.
       --- split.
           ---- intros. apply pure_refltrans_B. rewrite H. apply pure_P.
           ---- unfold f_is_weak_Z. unfold comp. intros.
                split.
                ----- induction H.
                      ------ apply (rtrans _ _ e1).
                             * apply step_aeq. apply aeq_sym. assumption.
                             * apply (refltrans_composition _ _ (P e1)).
                               ** apply refltrans_lx_pix. apply refltrans_P.
                               ** apply pure_refltrans_B. apply pure_P.
                      ------ inversion H0. apply (rtrans _ _ e3). apply step_aeq.
                             apply aeq_sym. assumption.
                             rewrite <- H2 in *. rewrite <- H3 in *.
                             inversion H. inversion H7.
                             * simpl. apply (refltrans_composition _ _ (n_sub t0 x t2)).
                               ** apply (refltrans_sub3).
                                  *** apply (rtrans _ _ t0).
                                      **** apply step_aeq. apply aeq_sym. assumption.
                                      **** apply refl.
                                  *** apply (rtrans _ _ t2).
                                      **** apply step_aeq. apply aeq_sym. assumption.
                                      **** apply refl.
                               ** apply (refltrans_composition _ _ (n_sub (P t0) x (P t2))).
                                  *** apply refltrans_sub3;apply refltrans_lx_pix;apply refltrans_P.
                                  *** apply (refltrans_composition _ _ (n_sub (B (P t0)) x (B (P t2)))).
                                      **** apply refltrans_sub3;apply pure_refltrans_B;apply pure_P.
                                      **** apply pure_pix_2. apply pure_B. apply pure_P.
                             * apply (rtrans _ _ (n_sub t0 x0 e5)).
                               ** apply step_aeq. apply aeq_sym. apply aeq_sub_diff;default_simp. apply aeq_refl.
                               ** simpl. apply (refltrans_composition _ _ (n_sub t0 x0 t2)).
                                  *** apply (refltrans_sub1). apply (rtrans _ _ t2).
                                      **** apply step_aeq. apply aeq_sym. assumption.
                                      **** apply refl.
                                  *** apply (refltrans_composition _ _ (n_sub (P t0) x0 (P t2))).
                                      **** apply refltrans_sub3;apply refltrans_lx_pix;apply refltrans_P.
                                      **** apply (refltrans_composition _ _ (n_sub (B (P t0)) x0 (B (P t2)))).
                                           ***** apply refltrans_sub3;apply pure_refltrans_B;apply pure_P.
                                           ***** apply pure_pix_2. apply pure_B. apply pure_P.
                      ------ simpl. apply refltrans_abs. assumption.
                      ------ apply (refltrans_composition _ _ (n_app e1' (P e2))).
                             * apply refltrans_app2. apply refltrans_lx_pix. apply refltrans_P.
                             * apply (refltrans_composition _ _ (n_app e1' (B (P e2)))).
                               ** apply refltrans_app2. apply pure_refltrans_B. apply pure_P.
                               ** simpl. destruct (P e1) eqn:Hp.
                                  *** apply refltrans_app1. assumption.
                                  *** simpl in *. apply (refltrans_composition _ _ (n_app (n_abs x (B n)) (B (P e2)))).
                                      **** apply refltrans_app1. assumption.
                                      **** apply (refltrans_composition _ _ (n_sub (B n) x (B (P e2)))).
                                           ***** apply (rtrans _ _ (n_sub (B n) x (B (P e2)))).
                                                 ****** apply step_redex_R. apply b_rule. apply step_betax.
                                                 ****** apply refl.
                                           ***** apply pure_pix_2. apply pure_B. assert (H': pure (P e1)).
                                                 ****** apply pure_P.
                                                 ****** rewrite Hp in H'. inversion H'. assumption.
                                  *** apply refltrans_app1. assumption.
                                  *** apply refltrans_app1. assumption.
                      ------ apply (refltrans_composition _ _ (n_app (P e1) e2')).
                             * apply refltrans_app1. apply refltrans_lx_pix. apply refltrans_P.
                             * apply (refltrans_composition _ _ (n_app (B (P e1)) e2')).
                               ** apply refltrans_app1. apply pure_refltrans_B. apply pure_P.
                               ** simpl. destruct (P e1) eqn:Hp.
                                  *** simpl. apply refltrans_app2. assumption.
                                  *** simpl. apply (refltrans_composition _ _ (n_sub (B n) x e2')).
                                      **** apply (rtrans _ _ (n_sub (B n) x e2')).
                                           ***** apply step_redex_R. apply b_rule. apply step_betax.
                                           ***** apply refl.
                                      **** apply (refltrans_composition _ _ (n_sub (B n) x (B (P e2)))).
                                           ***** apply refltrans_sub1. assumption.
                                           ***** apply pure_pix_2. apply pure_B. assert (H': pure (P e1)).
                                                 ****** apply pure_P.
                                                 ****** rewrite Hp in H'. inversion H'. assumption.
                                  *** apply refltrans_app2. assumption.
                                  *** apply refltrans_app2. assumption.
                      ------ simpl. apply (refltrans_composition _ _ (n_sub (B (P e1)) x (B (P e2)))).
                             * apply refltrans_sub3.
                               ** assumption.
                               ** apply (refltrans_composition _ _ (P e2)).
                                  *** apply refltrans_lx_pix. apply refltrans_P.
                                  *** apply pure_refltrans_B. apply pure_P.
                             * apply (refltrans_composition _ _ (m_subst (B (P e2)) x (B (P e1)))).
                               ** apply pure_pix_2. apply pure_B. apply pure_P.
                               ** apply refltrans_m_subst_B;apply pure_P.
                      ------ simpl. apply (refltrans_composition _ _ (n_sub (B (P e1)) x (B (P e2)))).
                             * apply refltrans_sub3.
                               ** apply (refltrans_composition _ _ (P e1)).
                                  *** apply refltrans_lx_pix. apply refltrans_P.
                                  *** apply pure_refltrans_B. apply pure_P.
                               ** assumption.
                             * apply (refltrans_composition _ _ (m_subst (B (P e2)) x (B (P e1)))).
                               ** apply pure_pix_2. apply pure_B. apply pure_P.
                               ** apply refltrans_m_subst_B;apply pure_P.
                ----- pose proof ctx_betax_beta_pix. specialize (H0 a b). destruct H0.
                      assert (H': (ctx pix !_! ctx betax) a b).
                      * apply union_or. right. assumption.
                      * apply H1 in H'. apply refltrans_P_beta in H'. pose proof refltrans_beta_imply_B.
                        specialize (H2 (P a) (P b)). apply H2 in H'.
                        ** apply refltrans_beta_to_lx.
                           *** apply pure_B. apply pure_P.
                           *** apply pure_B. apply pure_P.
                           *** assumption.
                        ** apply pure_P.
                        ** apply pure_P.
Admitted.
  
Theorem lambda_x_is_confluent: Confl lx.
Proof.
  apply Z_prop_implies_Confl.
  apply Z_comp_eq_implies_Z_prop.
  apply lambda_x_Z_comp_eq.
Qed.
