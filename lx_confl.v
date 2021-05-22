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

Lemma pi_P: forall t1 t2, step pix t1 t2 -> P t1 = P t2.
Proof.
  intros t1 t2 H. induction H.
  - inversion H.
    -- subst. simpl. unfold m_subst. simpl. case (y == y).
       --- intros. reflexivity.
       --- contradiction.
    -- subst. simpl. unfold m_subst. simpl. case (y == x).
       --- intros. symmetry in e0. contradiction.
       --- intros. reflexivity.
    -- subst. simpl. unfold m_subst. simpl. case (y == y).
       --- intros. reflexivity.
       --- contradiction.
    -- subst. simpl. unfold m_subst. simpl. case (y == x).
       --- intros. symmetry in e. contradiction.
       --- intros. admit.
    -- subst. simpl. unfold m_subst. simpl.
       assert (subst_rec (size (P e0) + size (P e3)) (P e0) (P e4) y = subst_rec (size (P e0)) (P e0) (P e4) y). {
         apply subst_size. apply le_plus_l.       
       }
       assert ((subst_rec (size (P e0) + size (P e3)) (P e3) (P e4) y = subst_rec (size (P e3)) (P e3) (P e4) y)). {
         apply subst_size. apply le_plus_r.
       }
       rewrite H0; rewrite H1. reflexivity.
  - inversion H.
    -- subst. simpl. simpl in IHstep. rewrite IHstep. reflexivity.
    -- subst. simpl. simpl in IHstep. rewrite IHstep. reflexivity.
    -- subst. simpl. simpl in IHstep. rewrite IHstep. reflexivity.
    -- subst. simpl. simpl in IHstep. rewrite IHstep. reflexivity.
    -- subst. simpl. simpl in IHstep. rewrite IHstep. reflexivity.
    -- subst. simpl. simpl in IHstep. rewrite IHstep. reflexivity.
  - inversion H.
    -- subst. simpl. simpl in IHstep. rewrite IHstep. reflexivity.
    -- subst. simpl. simpl in IHstep. rewrite IHstep. reflexivity.
    -- subst. simpl. simpl in IHstep. rewrite IHstep. reflexivity.
    -- subst. simpl. simpl in IHstep. rewrite IHstep. reflexivity.
    -- subst. simpl. simpl in IHstep. rewrite IHstep. reflexivity.
    -- subst. simpl. simpl in IHstep. rewrite IHstep. reflexivity.
  - inversion H.
    -- subst. simpl. simpl in IHstep. rewrite IHstep. reflexivity.
    -- subst. simpl. simpl in IHstep. rewrite IHstep. reflexivity.
    -- subst. simpl. simpl in IHstep. rewrite IHstep. reflexivity.
    -- subst. simpl. simpl in IHstep. rewrite IHstep. reflexivity.
    -- subst. simpl. simpl in IHstep. rewrite IHstep. reflexivity.
    -- subst. simpl. simpl in IHstep. rewrite IHstep. reflexivity.
  - inversion H.
    -- subst. simpl. simpl in IHstep. rewrite IHstep. reflexivity.
    -- subst. simpl. simpl in IHstep. rewrite IHstep. reflexivity.
    -- subst. simpl. simpl in IHstep. rewrite IHstep. reflexivity.
    -- subst. simpl. simpl in IHstep. rewrite IHstep. reflexivity.
    -- subst. simpl. simpl in IHstep. rewrite IHstep. reflexivity.
    -- subst. simpl. simpl in IHstep. rewrite IHstep. reflexivity.
  - inversion H.
    -- subst. simpl. simpl in IHstep. rewrite IHstep. reflexivity.
    -- subst. simpl. simpl in IHstep. rewrite IHstep. reflexivity.
    -- subst. simpl. simpl in IHstep. rewrite IHstep. reflexivity.
    -- subst. simpl. simpl in IHstep. rewrite IHstep. reflexivity.
    -- subst. simpl. simpl in IHstep. rewrite IHstep. reflexivity.
    -- subst. simpl. simpl in IHstep. rewrite IHstep. reflexivity. 
Admitted.

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
                             (Metatheory.union (remove x0 (fv_nom n)) (singleton x)))). apply pure_abs. 
           admit.
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
       --- intros. admit.                
Admitted.

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

  Lemma pure_pix: forall e1 x e2, pure e1 -> refltrans (step pix) (n_sub e1 x e2) (m_subst e2 x e1).
Proof.
Admitted.
    
