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
Admitted.

Lemma pure_P: forall e, pure (P e).
Proof.
  Admitted.

Lemma pure_P_id: forall e, pure e -> P e = e.
  Proof.
  Admitted.

  Lemma pure_pix: forall e1 x e2, pure e1 -> refltrans (step pix) (n_sub e1 x e2) (m_subst e2 x e1).
  Proof.
    Admitted.
    
