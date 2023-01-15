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

Axiom Eq_implies_equality: forall s s': atoms, s [=] s' -> s = s'.

Lemma swap_var_in: forall x y z,  swap_var x y z = x \/ swap_var x y z = y \/  swap_var x y z = z.
Proof.
  intros x y z.
  unfold swap_var.
  default_simp.
Qed.

Lemma swap_var_neq: forall x y z, x <> z -> y <> z -> swap_var x y z = z.
Proof.
  intros x y z H1 H2.
  unfold swap_var.
  default_simp.
Qed.

Axiom atoms_set_eq: forall s1 s2: atoms, s1 [=] s2 -> s1 =s2.

Lemma eq_aeq: forall t u, t = u -> aeq t u.
Proof.
  intros t u H; rewrite H; apply aeq_refl.
Qed.

Lemma abs_swap: forall t x y, y `notin` fv_nom t -> aeq (n_abs y (swap x y t)) (n_abs x t). 
Proof.
  intros. destruct (y == x).
  - rewrite e. rewrite swap_id. apply aeq_refl.
  - apply (aeq_abs_diff _ _ _ _ n H). apply aeq_refl.
Qed.
     
Lemma fv_nom_m_subst_notin: forall t u x, x `notin` fv_nom t ->
    fv_nom (m_subst u x t) [=] remove x (fv_nom t).
Proof.
  (* sugestão: indução no tamanho de t. *)
  induction t using n_sexp_induction.
  - intros. unfold m_subst. simpl in *.
    apply notin_singleton_1 in H. default_simp.
    rewrite (remove_singleton_neq _ _ H). reflexivity.
  - intros. unfold m_subst in *. simpl in *.
    case (x == z).
    -- intro; subst. simpl. rewrite double_remove.
        reflexivity.
    -- intro Hneq. destruct (atom_fresh
        (Metatheory.union (fv_nom u) (Metatheory.union (remove z (fv_nom t))
        (singleton x)))). simpl. assert
        (H': size (swap z x0 t) = size t). apply swap_size_eq.
        assert (H'': size t = size t). reflexivity.
        apply (diff_remove_2 _ _ _ Hneq) in H0.
        pose proof n. apply notin_union_2 in n.
        apply notin_union_2 in n. apply notin_singleton_1 in n.
        apply (fv_nom_remove_swap _ _ _ _ n Hneq) in H0.
        apply (H t z x0 H'' u x) in H0. rewrite H' in H0.
        rewrite H0. rewrite remove_symmetric.
        apply notin_union_2 in H1. apply notin_union_1 in H1.
        case (x0 == z);intros.
        --- rewrite e. rewrite swap_id. reflexivity.
        --- apply (diff_remove_2 _ _ _ n0) in H1.
            rewrite (remove_fv_swap _ _ _ H1). reflexivity.
  - intros. unfold m_subst in *. simpl. simpl in H.
    assert (H1: size t1 <= size t1 + size t2). lia.
    assert (H2: size t2 <= size t1 + size t2). lia.
    rewrite (subst_size _ _ _ _ H1). pose proof H.
    rewrite (subst_size _ _ _ _ H2).
    apply notin_union_2 in H. apply notin_union_1 in H0.
    apply (IHt1 u) in H0. apply (IHt2 u) in H. rewrite H.
    rewrite H0. rewrite remove_union_distrib. reflexivity.
  - intros. unfold m_subst in *. assert (Ht1: size t1 = size t1).
    reflexivity. simpl. destruct (x == z).
    -- simpl. assert (H': size t2 <= size t1 + size t2).
        lia. rewrite (subst_size _ _ _ _ H'). simpl in H0.
        apply notin_union_2 in H0. pose proof H0.
        apply (IHt1 u) in H0. rewrite H0. rewrite e.
        rewrite remove_union_distrib. rewrite double_remove.
        reflexivity.
    -- destruct (atom_fresh (Metatheory.union (fv_nom u)
        (Metatheory.union (Metatheory.union (remove z (fv_nom t1))
        (fv_nom t2)) (singleton x)))). simpl.
        assert (Hs: size (swap z x0 t1) <= size t1 + size t2).
        --- rewrite swap_size_eq. lia.
        --- rewrite (subst_size _ _ _ _ Hs).
            simpl in H0. pose proof H0. apply notin_union_1 in H0.
            apply (diff_remove_2 _ _ _ n) in H0.
            apply notin_union_2 in n0. pose proof n0.
            apply notin_union_2 in n0. apply notin_singleton_1 in n0.
            apply (fv_nom_remove_swap _ _ _ _ n0 n) in H0.
            apply (H t1 z x0 Ht1 u x) in H0. rewrite H0.
            assert (H': size t2 <= size t1 + size t2). lia.
            rewrite (subst_size _ _ _ _ H').
            apply notin_union_2 in H1. apply (IHt1 u) in H1.
            rewrite H1. case (x0 == z);intros.
        ---- rewrite e. rewrite swap_id.
              rewrite remove_union_distrib.
              rewrite remove_symmetric. reflexivity.
        ---- rewrite remove_symmetric. apply notin_union_1 in H2.
              apply notin_union_1 in H2.
              apply (diff_remove_2 _ _ _ n1) in H2.
              rewrite (remove_fv_swap _ _ _ H2).
              rewrite remove_union_distrib. reflexivity.
Qed.

Lemma fv_nom_m_subst_in: forall t u x, x `in` fv_nom t ->
    fv_nom (m_subst u x t) [=] fv_nom (n_sub t x u). 
Proof.
  induction t using n_sexp_induction.
  - intros. unfold m_subst. simpl.
    apply AtomSetImpl.singleton_1 in H. rewrite H.
    destruct (x0 == x0).
    -- rewrite remove_singleton_empty.
        rewrite AtomSetProperties.empty_union_1.
        reflexivity. apply AtomSetImpl.empty_1.
    -- contradiction.
  - intros. unfold m_subst in *. simpl. case (x == z);intros.
    -- simpl in H0. rewrite e in H0. apply remove_iff in H0.
        destruct H0. contradiction.
    -- destruct (atom_fresh (Metatheory.union (fv_nom u)
        (Metatheory.union (remove z (fv_nom t)) (singleton x)))).
        simpl. assert (Ht: size t = size t). reflexivity.
        simpl in H0. apply AtomSetImpl.remove_3 in H0.
        pose proof n0.
        apply notin_union_2 in n0. pose proof n0.
        apply notin_union_2 in n0. apply notin_singleton_1 in n0.
        assert (n': z <> x). auto.
        assert (H': x `in` remove z (fv_nom t)).
        apply (AtomSetImpl.remove_2 n' H0).
        assert (n'': x0 <> x). auto.
        assert (H'': x `in` remove x0 (remove z (fv_nom t))).
        apply (AtomSetImpl.remove_2 n'' H').
        rewrite <- swap_remove_reduction in H''.
        apply AtomSetImpl.remove_3 in H''.
        apply AtomSetImpl.remove_3 in H''.
        apply (H t z x0 Ht u x) in H''. rewrite swap_size_eq in H''.
        rewrite H''. simpl. rewrite remove_union_distrib.
        rewrite remove_symmetric. apply notin_union_1 in H2.
        case (x0 == z);intros.
      --- rewrite e. rewrite swap_id. apply notin_union_1 in H1.
          rewrite e in H1.
          rewrite (AtomSetProperties.remove_equal H1).
          reflexivity.
      --- apply (diff_remove_2 _ _ _ n1) in H2.
          rewrite (remove_fv_swap _ _ _ H2).
          apply notin_union_1 in H1.
          rewrite (AtomSetProperties.remove_equal H1). reflexivity.
  - unfold m_subst in *. intros. simpl.
    assert (Ht1: size t1 <= size t1 + size t2). lia.
    assert (Ht2: size t2 <= size t1 + size t2). lia.
    rewrite (subst_size _ _ _ _ Ht1). simpl in H.
    rewrite (subst_size _ _ _ _ Ht2).
    assert (H': forall a s, a `in` s \/ a `notin` s).
    apply in_or_notin.
    assert (H'': forall a b c, Metatheory.union (Metatheory.union a b)
    (Metatheory.union c b) [=] Metatheory.union (Metatheory.union a c) b).
    { intros. rewrite AtomSetProperties.union_assoc.
      rewrite (AtomSetProperties.union_sym b _). 
      rewrite AtomSetProperties.union_assoc.
      rewrite <- (AtomSetProperties.union_assoc a).
      apply AtomSetProperties.union_equal_2.
      rewrite (AtomSetProperties.union_subset_equal);reflexivity. }
    apply AtomSetImpl.union_1 in H. destruct H.
    -- apply (IHt1 u) in H. rewrite H. specialize (H' x (fv_nom t2)).
        destruct H'.
      --- apply (IHt2 u) in H0. rewrite H0. simpl.
          rewrite H''. rewrite remove_union_distrib. reflexivity.
      --- apply (fv_nom_m_subst_notin t2 u) in H0. rewrite H0. simpl.
          rewrite AtomSetProperties.union_sym.
          rewrite <- AtomSetProperties.union_assoc.
          rewrite remove_union_distrib.
          rewrite (AtomSetProperties.union_sym (remove x (fv_nom t2))).
          reflexivity.
    -- apply (IHt2 u) in H. rewrite H. specialize (H' x (fv_nom t1)).
        destruct H'.
      --- apply (IHt1 u) in H0. rewrite H0. simpl.
          rewrite H''. rewrite remove_union_distrib. reflexivity.
      --- apply (fv_nom_m_subst_notin t1 u) in H0. rewrite H0. simpl.
          rewrite <- AtomSetProperties.union_assoc.
          rewrite remove_union_distrib.
          reflexivity.
  - intros. unfold m_subst in *. simpl. case (x == z);intros.
    -- rewrite e. simpl. assert (H1: size t2 <= size t1 + size t2).
        lia. rewrite (subst_size _ _ _ _ H1). simpl in H0.
        apply AtomSetImpl.union_1 in H0. rewrite e in H0. destruct H0.
        --- apply AtomSetNotin.D.F.remove_iff in H0.
            destruct H0. contradiction.
        --- apply (IHt1 u z) in H0. rewrite H0. simpl.
            rewrite <- AtomSetProperties.union_assoc.
            rewrite remove_union_distrib. 
            rewrite double_remove. reflexivity.
    -- destruct (atom_fresh (Metatheory.union (fv_nom u)
        (Metatheory.union (Metatheory.union (remove z (fv_nom t1))
        (fv_nom t2)) (singleton x)))). assert (H1:
        size t1 <= size t1 + size t2 /\ size t2 <= size t1 + size t2).
        split;lia. destruct H1. rewrite (subst_size _ _ _ _ H2).
        assert (H': size (swap z x0 t1) = size t1). apply swap_size_eq.
        rewrite <- H' in H1 at 1. rewrite (subst_size _ _ _ _ H1).
        simpl in H0. pose proof in_or_notin. apply AtomSetImpl.union_1 in H0.
        assert (H'''': forall a b c, Metatheory.union (Metatheory.union a b)
      (Metatheory.union c b) [=] Metatheory.union (Metatheory.union a c) b).
      { intros. rewrite AtomSetProperties.union_assoc.
        rewrite (AtomSetProperties.union_sym b _). 
        rewrite AtomSetProperties.union_assoc.
        rewrite <- (AtomSetProperties.union_assoc a).
        apply AtomSetProperties.union_equal_2.
        rewrite (AtomSetProperties.union_subset_equal);reflexivity. }
        destruct H0.
        --- apply AtomSetImpl.remove_3 in H0. 
            apply (in_fv_nom_equivariance z x0) in H0.
            assert (H'': swap_var z x0 x = x).
            { apply notin_union_2 in n0. apply notin_union_2 in n0.
              apply notin_singleton_1 in n0. unfold swap_var.
              default_simp. } rewrite H'' in H0.
            assert (H''': size t1 = size t1). reflexivity. simpl.
            rewrite (H t1 z x0 H''' u x H0).
            specialize (H3 x (fv_nom t2)). destruct H3.
            ---- rewrite (IHt1 u x H3). simpl. rewrite remove_union_distrib.
                rewrite remove_symmetric. case (x0 == z);intros.
                ----- rewrite e. rewrite swap_id. apply notin_union_1 in n0.
                      rewrite e in n0. apply AtomSetProperties.remove_equal in n0.
                      rewrite n0.
                      rewrite H''''. rewrite remove_union_distrib. reflexivity.
                ----- pose proof n0. apply notin_union_2 in n0.
                      apply notin_union_1 in n0. apply notin_union_1 in n0.
                      apply (diff_remove_2 _ _ _ n1) in n0.
                      rewrite (remove_fv_swap _ z _ n0). apply notin_union_1 in H4.
                      rewrite (AtomSetProperties.remove_equal H4). rewrite H''''.
                      rewrite remove_union_distrib. reflexivity.
            ---- rewrite (fv_nom_m_subst_notin _ u _ H3). simpl. 
                rewrite remove_union_distrib.
                rewrite remove_symmetric. case (x0 == z);intros.
                ----- rewrite e. rewrite swap_id. rewrite AtomSetProperties.union_assoc.
                      rewrite (AtomSetProperties.union_sym (remove z (fv_nom u))).
                      rewrite <- AtomSetProperties.union_assoc. rewrite remove_union_distrib.
                      apply notin_union_1 in n0. rewrite e in n0. 
                      apply AtomSetProperties.remove_equal in n0. rewrite n0.
                      reflexivity.
                ----- pose proof n0. apply notin_union_2 in n0.
                      apply notin_union_1 in n0. apply notin_union_1 in n0.
                      apply (diff_remove_2 _ _ _ n1) in n0.
                      rewrite (remove_fv_swap _ z _ n0). apply notin_union_1 in H4.
                      rewrite (AtomSetProperties.remove_equal H4).
                      rewrite AtomSetProperties.union_assoc.
                      rewrite (AtomSetProperties.union_sym (fv_nom u)).
                      rewrite <- AtomSetProperties.union_assoc.
                      rewrite remove_union_distrib. reflexivity.
      --- apply (IHt1 u) in H0. simpl. rewrite H0. specialize (H3 x (fv_nom t1)).
          destruct H3.
          ---- apply (in_fv_nom_equivariance z x0) in H3.
                assert (H'': swap_var z x0 x = x).
                { apply notin_union_2 in n0. apply notin_union_2 in n0.
                  apply notin_singleton_1 in n0. unfold swap_var.
                  default_simp. } rewrite H'' in H3.
                assert (H''': size t1 = size t1). reflexivity. simpl.
                rewrite (H t1 z x0 H''' u x H3). simpl.
                rewrite remove_union_distrib.
                rewrite remove_symmetric. case (x0 == z);intros.
                ----- rewrite e. rewrite swap_id. apply notin_union_1 in n0.
                      rewrite e in n0. apply AtomSetProperties.remove_equal in n0.
                      rewrite n0.
                      rewrite H''''. rewrite remove_union_distrib. reflexivity.
                ----- pose proof n0. apply notin_union_2 in n0.
                      apply notin_union_1 in n0. apply notin_union_1 in n0.
                      apply (diff_remove_2 _ _ _ n1) in n0.
                      rewrite (remove_fv_swap _ z _ n0). apply notin_union_1 in H4.
                      rewrite (AtomSetProperties.remove_equal H4). rewrite H''''.
                      rewrite remove_union_distrib. reflexivity.
          ---- pose proof n0. apply notin_union_2 in n0. apply notin_union_2 in n0.
                apply notin_singleton_1 in n0.
                apply (fv_nom_remove_swap _ _ _ _ n0 n) in H3.
                apply (fv_nom_m_subst_notin _ u) in H3. unfold m_subst in H3.
                rewrite H3. rewrite remove_symmetric. case (x0 == z);intros.
                ----- rewrite e. rewrite swap_id. simpl. 
                      rewrite <- AtomSetProperties.union_assoc.
                      rewrite remove_union_distrib. reflexivity.
                ----- apply notin_union_2 in H4. apply notin_union_1 in H4.
                      apply notin_union_1 in H4. apply (diff_remove_2 _ _ _ n1) in H4.
                      rewrite (remove_fv_swap _ z _ H4). simpl.
                      rewrite <- AtomSetProperties.union_assoc.
                      rewrite remove_union_distrib. reflexivity.
Qed.

Lemma notin_P: forall x t,
    x `notin` fv_nom t -> x `notin` fv_nom (P t).
Proof.
  intros x t Hnot.
  induction t.
  - simpl in *.
    assumption.
  - simpl in *.
    case (x == x0); intros; subst.
    -- apply notin_remove_3; reflexivity.
    -- apply notin_remove_2.
       apply IHt.
       apply notin_remove_1 in Hnot.
       inversion Hnot; subst.
       --- contradiction.
       --- assumption.
  - simpl in *.
    apply notin_union.
    -- apply notin_union_1 in Hnot.
       apply IHt1; assumption.
    -- apply notin_union_2 in Hnot.
       apply IHt2; assumption.
  - simpl in *.
    pose proof Hnot.
    apply notin_union_1 in Hnot.
    apply notin_union_2 in H.
    unfold m_subst. pose proof in_or_notin.
    specialize (H0 x0 (fv_nom (P t1))).
    destruct H0.
    -- pose proof fv_nom_m_subst_in. unfold m_subst in H1.
       rewrite (H1 _ (P t2) _ H0). simpl. apply IHt2 in H.
       apply notin_union.
       --- case (x == x0);intros.
           ---- rewrite e. default_simp.
           ---- apply (diff_remove _ _ _ n). apply IHt1.
                apply (diff_remove_2 _ _ _ n) in Hnot. assumption.
       --- assumption.
    -- pose proof fv_nom_m_subst_notin. unfold m_subst in H1.
       rewrite (H1 _ (P t2) x0 H0). case (x == x0);intros.
       --- rewrite e. default_simp.
       --- apply (diff_remove _ _ _ n). apply IHt1.
            apply (diff_remove_2 _ _ _ n) in Hnot. assumption.
Qed.

Lemma aeq_m_subst_1: forall t t1 t1' x,
  aeq t1 t1' -> aeq (m_subst t1 x t) (m_subst t1' x t).
Proof.
  intros. unfold m_subst.
  induction t using n_sexp_induction.
  - default_simp.
  - simpl. pose proof H. apply aeq_fv_nom in H1. apply Eq_implies_equality in H1.
    rewrite H1. default_simp.
    -- apply aeq_refl.
    -- apply aeq_abs_same. rewrite <- (swap_size_eq z x0).
       apply H0. reflexivity.
  - simpl. apply aeq_app.
    -- assert (size t2 <= size t2 + size t3). lia.
       repeat rewrite (subst_size _ _ _ _ H0). assumption.
    -- assert (size t3 <= size t2 + size t3). lia.
       repeat rewrite (subst_size _ _ _ _ H0). assumption.
  - simpl. pose proof H. apply aeq_fv_nom in H1. apply Eq_implies_equality in H1.
    rewrite H1. default_simp.
    -- assert (H': size t3 <= size t2 + size t3). lia.
       repeat rewrite (subst_size _ _ _ _ H'). apply aeq_sub_same.
       --- apply aeq_refl.
       --- assumption.
    -- apply aeq_sub_same.
       --- assert (H': size (swap z x0 t2) <= size t2 + size t3). rewrite swap_size_eq.
           lia. repeat rewrite (subst_size _ _ _ _ H'). apply H0. reflexivity.
       --- assert (H': size t3 <= size t2 + size t3).
           lia. repeat rewrite (subst_size _ _ _ _ H'). assumption.
Qed.

Lemma aeq_m_subst_2: forall t t1 t1' x,
  aeq t1 t1' -> aeq (m_subst t x t1) (m_subst t x t1').
Proof.
  intros t t1. unfold m_subst.
  induction t1 using n_sexp_induction;intros.
  - default_simp. apply aeq_refl.
  - inversion H0.
    -- simpl. pose proof H0. rewrite <- H2 in H0. apply aeq_fv_nom in H0. apply Eq_implies_equality in H0.
       simpl in H0. rewrite H0. default_simp. apply aeq_abs_same.
       rewrite <- (swap_size_eq z x0 t1). rewrite <- (swap_size_eq z x0 t2).
       apply H. 
       --- reflexivity.
       --- apply aeq_swap1. assumption.
    -- simpl. assert (H': remove z (fv_nom t1) [=] remove y (fv_nom t2)).
       --- apply (remove_fv_swap _ y) in H4. apply aeq_fv_nom in H6.
           rewrite <- H6 in H4. assumption.
       --- apply Eq_implies_equality in H'. rewrite H'. default_simp.
           ---- pose proof n. repeat apply notin_union_2 in H1. apply notin_singleton_1 in H1.
                apply aeq_abs_diff.
                ----- assumption.
                ----- apply (fv_nom_remove_swap _ _ _ _ H1 H3) in H4.
                      apply (fv_nom_m_subst_notin _ t) in H4.
                      rewrite <- (swap_size_eq y x0 t2). unfold m_subst in H4.
                      rewrite H4. default_simp.
                ----- rewrite <- (swap_size_eq y x0). apply (aeq_trans _ 
                      (swap x0 z (swap y x0 t2))).
                      ------ case (x0 == y); intros.
                             ------- rewrite e. rewrite swap_id. assumption.
                             ------- rewrite (swap_symmetric _ x0 z). rewrite (swap_symmetric _ y x0).
                                     rewrite (shuffle_swap' _ _ _ _ n0 n1). apply (aeq_trans _ 
                                     (swap y z t2)).
                                     -------- assumption.
                                     -------- apply aeq_swap. apply notin_union_2 in n.
                                              apply notin_union_1 in n. apply (diff_remove_2 _ _ _ n1) in n.
                                              apply (aeq_swap0 _ _ _ n H4).
                      ------ apply aeq_swap1. pose proof subst_fresh_eq.
                             unfold m_subst in H2. apply aeq_sym. apply H2.
                             apply (fv_nom_remove_swap _ _ _ _ H1 n0 H4).
           ---- pose proof n. repeat apply notin_union_2 in H1. apply notin_singleton_1 in H1.
                apply aeq_sym. assert (H''': y `notin` fv_nom t1).
                ----- pose proof in_or_notin. specialize (H2 y (fv_nom t1)). destruct H2.
                      ------ apply (aeq_swap1 _ _ y z) in H6. rewrite swap_involutive in H6.
                             apply aeq_fv_nom in H6. rewrite <- H6 in H4.
                             apply fv_nom_swap_2 in H4. contradiction.
                      ------ assumption.
                ----- apply aeq_abs_diff.
                      ------ assumption.
                      ------ apply (fv_nom_remove_swap _ _ _ _ H1 n0) in H'''.
                             apply (fv_nom_m_subst_notin _ t) in H'''.
                             rewrite <- (swap_size_eq z x0 t1). unfold m_subst in H'''.
                             rewrite H'''. default_simp.
                      ------ rewrite <- (swap_size_eq z x0). apply (aeq_trans _ 
                             (swap x0 y (swap z x0 t1))).
                             ------- case (x0 == z); intros.
                                     -------- rewrite e. rewrite swap_id. rewrite swap_symmetric.
                                              apply (aeq_swap _ _ y z). rewrite swap_involutive.
                                              apply aeq_sym. assumption.
                                     -------- rewrite (swap_symmetric _ z x0). rewrite (swap_symmetric _ x0 y).
                                              rewrite (shuffle_swap' _ _ _ _ n0 n1).
                                              apply (aeq_trans _ (swap z y t1)). 
                                              --------- rewrite swap_symmetric.
                                                        apply (aeq_swap _ _ y z). rewrite swap_involutive.
                                                        apply aeq_sym. assumption.
                                              --------- apply aeq_swap. apply notin_union_2 in n.
                                                        apply notin_union_1 in n. rewrite <- H' in n. 
                                                        apply (diff_remove_2 _ _ _ n1) in n.
                                                        apply (aeq_swap0 _ _ _ n H''').
                             ------- apply aeq_swap. pose proof subst_fresh_eq.
                                     unfold m_subst in H2. apply aeq_sym. apply H2.
                                     apply (fv_nom_remove_swap _ _ _ _ H1 n0 H''').
           ---- apply aeq_abs_same. apply aeq_sym. rewrite <- (swap_size_eq y x0 t2).
                rewrite <- (swap_size_eq z x0 t1). apply H.
                ----- apply aeq_size in H6. rewrite swap_size_eq in H6. rewrite H6. reflexivity.
                ----- case (x0 == z); intros.
                      ------ rewrite e. rewrite swap_id. apply aeq_sym. assumption.
                      ------ case (x0 == y);intros.
                             ------- rewrite e. rewrite swap_id. apply (aeq_swap _ _ z y).
                                     rewrite swap_involutive. apply aeq_sym.
                                     rewrite swap_symmetric. assumption.
                             ------- apply (aeq_swap _ _ z x0). rewrite swap_involutive.
                                     rewrite (swap_symmetric _ y x0).
                                     rewrite (shuffle_swap' _ _ _ _ H3 n3).
                                     apply (aeq_trans _ (swap y z t2)).
                                     -------- apply aeq_swap. apply aeq_sym.
                                              apply notin_union_2 in n. apply notin_union_1 in n.
                                              apply (diff_remove_2 _ _ _ n3) in n.
                                              apply (aeq_swap0 _ _ _ n H4).
                                     -------- apply aeq_sym. assumption.
  - inversion H. simpl. apply aeq_app.
    -- assert (H': size t1_1 <= size t1_1 + size t1_2). lia.
       assert (H'': size t1'0 <= size t1'0 + size t2'). lia.
       rewrite (subst_size _ _ _ _ H'). rewrite (subst_size _ _ _ _ H''). apply IHt1_1. assumption.
    -- assert (H': size t1_2 <= size t1_1 + size t1_2). lia.
       assert (H'': size t2' <= size t1'0 + size t2'). lia.
       rewrite (subst_size _ _ _ _ H'). rewrite (subst_size _ _ _ _ H''). apply IHt1_2. assumption.
  - inversion H0.
    -- simpl. assert (H': Metatheory.union (remove z (fv_nom t1_1)) (fv_nom t1_2) [=]
       Metatheory.union (remove z (fv_nom t1'0)) (fv_nom t2')).
       --- apply aeq_fv_nom in H5. rewrite H5. apply aeq_fv_nom in H6. rewrite H6.
           reflexivity.
       --- apply Eq_implies_equality in H'. rewrite H'. default_simp.
           ---- assert (H'1: size t1_2 <= size t1_1 + size t1_2). lia.
                assert (H'2: size t2' <= size t1'0 + size t2'). lia.
                rewrite (subst_size _ _ _ _ H'1). rewrite (subst_size _ _ _ _ H'2).
                apply aeq_sub_same.
                ----- assumption.
                ----- apply IHt1_1. assumption.
           ---- assert (H'1: size (swap z x0 t1_1) <= size t1_1 + size t1_2). rewrite swap_size_eq. lia.
                assert (H'2: size (swap z x0 t1'0) <= size t1'0 + size t2'). rewrite swap_size_eq. lia.
                assert (H'3: size t1_2 <= size t1_1 + size t1_2). lia.
                assert (H'4: size t2' <= size t1'0 + size t2'). lia.
                rewrite (subst_size _ _ _ _ H'1). rewrite (subst_size _ _ _ _ H'2).
                rewrite (subst_size _ _ _ _ H'3). rewrite (subst_size _ _ _ _ H'4).
                apply aeq_sub_same.
                ----- apply H.
                      ------ reflexivity.
                      ------ apply aeq_swap. assumption.
                ----- apply IHt1_1. assumption.
    -- simpl. assert (H': Metatheory.union (remove z (fv_nom t1_1)) (fv_nom t1_2) [=]
       Metatheory.union (remove y (fv_nom t1'0)) (fv_nom t2')).
       --- apply aeq_fv_nom in H4. rewrite H4. apply aeq_fv_nom in H8. rewrite H8.
           rewrite (remove_fv_swap _ _ _ H7). reflexivity.
       --- apply Eq_implies_equality in H'. rewrite H'. default_simp.
           ---- assert (H'1: size (swap y x0 t1'0) <= size t1'0 + size t2'). rewrite swap_size_eq. lia.
                assert (H'2: size t2' <= size t1'0 + size t2'). lia.
                assert (H'3: size t1_2 <= size t1_1 + size t1_2). lia.
                rewrite (subst_size _ _ _ _ H'1). rewrite (subst_size _ _ _ _ H'2).
                rewrite (subst_size _ _ _ _ H'3).
                pose proof n. repeat apply notin_union_2 in H1. apply notin_singleton_1 in H1.
                apply aeq_sub_diff.
                ----- apply IHt1_1. assumption.
                ----- assumption.
                ----- apply (fv_nom_remove_swap _ _ _ _ H1 n0) in H7.
                      apply (fv_nom_m_subst_notin _ t) in H7. unfold m_subst in H7.
                      rewrite H7. default_simp.
                ----- case (x0 == y);intros.
                      ------ rewrite e. rewrite swap_id. apply (aeq_trans _ (
                             (swap y z t1'0))). assumption.
                             apply aeq_swap. apply aeq_sym. apply subst_fresh_eq.
                             assumption.
                      ------ apply (aeq_trans _ (swap x0 z (swap y x0 t1'0))).
                             ------- rewrite swap_symmetric. rewrite (swap_symmetric _ y x0).
                                     rewrite (shuffle_swap' _ _ _ _ n0 n1). apply (aeq_trans _
                                     (swap y z t1'0)). assumption. apply aeq_swap.
                                     apply aeq_swap0.
                                     * apply notin_union_2 in n. repeat apply notin_union_1 in n.
                                       apply (diff_remove_2 _ _ _ n1 n).
                                     * assumption.
                             ------- apply aeq_swap. apply aeq_sym. apply subst_fresh_eq.
                                     repeat apply notin_union_2 in n. apply notin_singleton_1 in n.        
                                     apply fv_nom_remove_swap;assumption.
           ---- assert (H'1: size (swap z x0 t1_1) <= size t1_1 + size t1_2). rewrite swap_size_eq. lia.
                assert (H'2: size t2' <= size t1'0 + size t2'). lia.
                assert (H'3: size t1_2 <= size t1_1 + size t1_2). lia.
                rewrite (subst_size _ _ _ _ H'1). rewrite (subst_size _ _ _ _ H'2).
                rewrite (subst_size _ _ _ _ H'3). apply aeq_sym.
                pose proof n. repeat apply notin_union_2 in H1. apply notin_singleton_1 in H1.
                assert (H''': y `notin` fv_nom t1_1).
                { apply aeq_fv_nom in H8. rewrite H8. apply fv_nom_swap. assumption. }
                apply aeq_sub_diff.
                ----- apply aeq_sym. apply IHt1_1. assumption.
                ----- assumption.
                ----- apply (fv_nom_remove_swap _ _ _ _ H1 n0) in H'''.
                      apply (fv_nom_m_subst_notin _ t) in H'''. unfold m_subst in H'''.
                      rewrite H'''. default_simp.
                ----- case (x0 == z);intros.
                      ------ rewrite e. rewrite swap_id. apply (aeq_trans _ (
                             (swap y z t1_1))).
                             ------- apply (aeq_swap _ _ y z). rewrite swap_involutive.
                                     apply aeq_sym. assumption.
                             ------- rewrite (swap_symmetric _ z y).
                                     apply aeq_swap. apply aeq_sym. apply subst_fresh_eq.
                                     assumption.
                      ------ apply (aeq_trans _ (swap x0 y (swap z x0 t1_1))).
                              ------- rewrite swap_symmetric. rewrite (swap_symmetric _ z x0).
                                      rewrite (shuffle_swap' _ _ _ _ n0 n1). rewrite swap_symmetric.
                                      apply (aeq_trans _ (swap y z t1_1)). 
                                      -------- apply (aeq_swap _  _ y z). rewrite swap_involutive.
                                               apply aeq_sym. assumption.
                                      -------- apply aeq_swap.
                                               apply aeq_swap0.
                                               * apply notin_union_2 in n. repeat apply notin_union_1 in n.
                                                 apply aeq_fv_nom in H8. rewrite H8.
                                                 assert(H'''': x0 <> y). default_simp.
                                                 apply (fv_nom_remove_swap _ _ _ _ n1 H''''). 
                                                 apply (diff_remove_2 _ _ _ H'''' n). 
                                               * assumption.
                              ------- apply aeq_swap. apply aeq_sym. apply subst_fresh_eq.
                                      repeat apply notin_union_2 in n. apply notin_singleton_1 in n.        
                                      apply fv_nom_remove_swap;assumption.
           ---- assert (H'1: size (swap z x0 t1_1) <= size t1_1 + size t1_2). rewrite swap_size_eq. lia.
                assert (H'2: size (swap y x0 t1'0) <= size t1'0 + size t2'). rewrite swap_size_eq. lia.
                assert (H'3: size t1_2 <= size t1_1 + size t1_2). lia.
                assert (H'4: size t2' <= size t1'0 + size t2'). lia.
                rewrite (subst_size _ _ _ _ H'1). rewrite (subst_size _ _ _ _ H'2).
                rewrite (subst_size _ _ _ _ H'3). rewrite (subst_size _ _ _ _ H'4).
                apply aeq_sub_same.
                ----- apply H. reflexivity. case (x0 == z);intros.
                      ------ rewrite e. rewrite swap_id. assumption.
                      ------ case (x0 == y);intros.
                             ------- rewrite e. rewrite swap_id. rewrite swap_symmetric.
                                     apply (aeq_swap _ _ y z). rewrite swap_involutive. assumption.
                             ------- apply (aeq_swap _ _ z x0). rewrite swap_involutive.
                                     rewrite (swap_symmetric _ y x0). rewrite (shuffle_swap' _ _ _ _ H5 n3).
                                     apply (aeq_trans _ (swap y z t1'0)).
                                     -------- assumption.
                                     -------- apply aeq_swap. apply notin_union_2 in n.
                                              repeat apply notin_union_1 in n.
                                              apply (diff_remove_2 _ _ _ n3) in n.
                                              apply (aeq_swap0 _ _ _ n H7).
                ----- apply IHt1_1. assumption.
Qed.

Corollary aeq_m_subst: forall t1 t1' t2 t2' x, aeq t1 t1' ->
  aeq t2 t2' -> aeq (m_subst t2 x t1) (m_subst t2' x t1').
Proof.
 intros t1 t1' t2 t2' x H1 H2.  
  apply aeq_trans with (m_subst t2 x t1').
  - apply aeq_m_subst_2; assumption.
  - apply aeq_m_subst_1; assumption.
Qed.

Lemma swap_var_eq: forall x y z w, swap_var x y z = swap_var x y w <-> z = w.
Proof.
  intros x y z w; split.
  - unfold swap_var.
    default_simp.
  - intro H; subst.
    reflexivity.
Qed.
                  
Lemma aeq_swap_m_subst: forall t u x y z, aeq (swap x y (m_subst u z t)) (m_subst (swap x y u) (swap_var x y z) (swap x y t)).
Proof.
  intros t u x y z. case (x == y).
  - intro Heq; subst. repeat rewrite swap_id. rewrite swap_var_id. apply aeq_refl.
  - generalize dependent z. generalize dependent y. generalize dependent x. generalize dependent u.
    induction t using n_sexp_induction.
    -- intros u x' y z Hneq. unfold m_subst. simpl in *. default_simp.
       --- apply aeq_refl.
       --- apply swap_var_eq in e. contradiction.
    -- intros u x y z' Hneq. simpl in *. destruct (z' == z) eqn:Heq.
       --- subst. unfold m_subst in *. simpl. rewrite Heq.
           destruct (swap_var x y z == swap_var x y z).
           ---- simpl. apply aeq_refl.
           ---- apply False_ind. apply n; reflexivity.
       --- unfold m_subst in *. (*
           replace (n_abs (swap_var x y z) (swap x y t)) with (swap x y (n_abs z t)). *)
           simpl. rewrite Heq.
           destruct (swap_var x y z' == swap_var x y z).
           ---- apply False_ind. apply n. apply swap_var_eq in e. assumption.
           ---- destruct (atom_fresh
            (Metatheory.union (fv_nom u)
               (Metatheory.union (remove z (fv_nom t)) (singleton z')))).
                simpl. replace (size t) with (size (swap z x0 t)). (* a *)
                ----- destruct (atom_fresh
                                  (Metatheory.union (fv_nom (swap x y u))
                                     (Metatheory.union
                                        (remove (swap_var x y z) (fv_nom (swap x y t)))
                                        (singleton (swap_var x y z'))))).
                case (x1 == swap_var x y x0).
                ------ intro H'. rewrite H'. apply aeq_abs_same.
                       replace (size (swap x y t)) with (size (swap (swap_var x y z) (swap_var x y x0) (swap x y t))).
                       ------- apply aeq_trans with (subst_rec (size (swap x y (swap z x0 t))) (swap x y (swap z x0 t)) (swap x y u) (swap_var x y z')).
                       -------- apply H.
                       --------- reflexivity.
                       --------- assumption.
                       -------- pose proof aeq_m_subst_2 as H''. unfold m_subst in H''. apply H''. rewrite swap_equivariance. apply aeq_refl.
                       ------- repeat rewrite swap_size_eq; reflexivity.  
                       ------ intro Hneq'. apply aeq_abs_diff.
                       ------- apply aux_not_equal; assumption.
                         ------- admit. (* Danilo ok *)
                         ------- (* b *) apply aeq_trans with (subst_rec (size (swap x1 (swap_var x y x0) (swap (swap_var x y z) x1 (swap x y t))))
         (swap x1 (swap_var x y x0) (swap (swap_var x y z) x1 (swap x y t))) 
         (swap x y u) (swap_var x y z')).
                         --------- (* c *) apply aeq_trans with (subst_rec (size (swap x y (swap z x0 t))) (swap x y (swap z x0 t)) (swap x y u) (swap_var x y z')).
                         ---------- apply H.
                         ----------- reflexivity.
                         ----------- assumption.
                         ---------- apply aeq_m_subst_2. replace
                           (swap (swap_var x y z) x1 (swap x y t)) with  (swap x1 (swap_var x y z) (swap x y t)).
                         ----------- replace (swap x1 (swap_var x y x0)
       (swap x1 (swap_var x y z) (swap x y t))) with (swap (swap_var x y x0) x1
       (swap x1 (swap_var x y z) (swap x y t))).
                         ------------ rewrite swap_equivariance. rewrite swap_symmetric. apply aeq_sym. apply aeq_swap_swap.
                         ------------- admit. (* ok *)
                         ------------- admit. (* ok *)
                           ------------ apply swap_symmetric.
                           ----------- apply swap_symmetric.
                           --------- (* d *) assert (swap_var x y z' = swap_var x1 (swap_var x y x0) (swap_var x y z')). { rewrite swap_var_neq with  x1 (swap_var x y x0) (swap_var x y z').
                                                                                                                           - reflexivity.
                                                                                                                           - admit. (* ok *)
                                                                                                                           - admit. (* ok *) } rewrite H0 at 1.
                           assert (aeq (swap x y u) (swap x1 (swap_var x y x0) (swap x y u))). { admit. } apply aeq_trans with (subst_rec (size (swap x1 (swap_var x y x0) (swap (swap_var x y z) x1 (swap x y t))))
       (swap x1 (swap_var x y x0) (swap (swap_var x y z) x1 (swap x y t))) 
       (swap x1 (swap_var x y x0) (swap x y u)) (swap_var x1 (swap_var x y x0) (swap_var x y z'))).
                           ---------- admit. (* ok *)
                           ---------- apply aeq_sym.
                           assert (size (swap x y t) = size (swap (swap_var x y z) x1 (swap x y t))). { repeat rewrite swap_size_eq; reflexivity. } rewrite H2 at 1. apply H.
                           -----------  rewrite swap_size_eq; reflexivity.
                           ----------- assumption.
                           ----- rewrite swap_size_eq; reflexivity.
    -- admit.
    -- Admitted.                            

Lemma aeq_swap_P: forall t x y,
    aeq (P (swap x y t)) (swap x y (P t)).
Proof.
  intros t. induction t;intros.
  - default_simp.
  - simpl. apply aeq_abs_same. apply IHt.
  - default_simp.
  - simpl. apply (aeq_trans _ (m_subst (swap x0 y (P t2)) (swap_var x0 y x) (swap x0 y (P t1)))).
    -- apply (aeq_trans _ (m_subst (swap x0 y (P t2)) (swap_var x0 y x) (P (swap x0 y t1)))).
       --- apply aeq_m_subst_1. apply IHt2.
       --- apply aeq_m_subst_2. apply IHt1.
    -- apply aeq_sym. apply aeq_swap_m_subst.
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

Lemma swap_inverse: forall x y t1 t2,
  t1 = swap x y t2 -> t2 = swap x y t1.
Proof.
  intros. rewrite H. rewrite swap_involutive. reflexivity.
Qed.

Lemma aeq_m_subst_3: forall t1 t1' t2 x y, x <> y -> 
  x `notin` (fv_nom t1') -> aeq t1 (swap x y t1') ->
  aeq (m_subst t2 x t1) (m_subst t2 y t1').
Proof.
  intros t1 t1'. generalize dependent t1.   
  induction t1' using n_sexp_induction; intros.
  - inversion H1. unfold m_subst. simpl. unfold swap_var.
    default_simp.
    -- apply aeq_refl.
    -- apply notin_singleton_1 in H0. contradiction.
  - inversion H2.
    -- unfold m_subst in *. simpl. unfold swap_var. case (y == z);intros.
       --- rewrite e. default_simp. apply aeq_abs_diff.
           * assumption.
           * default_simp.
           * rewrite swap_symmetric. assumption.
       --- default_simp.
           ---- case (x0 == x1);intros.
                ----- rewrite e. apply aeq_abs_same.
                      rewrite <- (swap_size_eq x x1 t1'). rewrite <- (swap_size_eq y x1 t0).
                      assert (H': size t1' = size t1'). reflexivity.
                      specialize (H t1' x x1 H'). apply H.
                      * assumption.
                      * apply fv_nom_swap. apply notin_union_2 in n1.
                        apply notin_union_1 in n1. repeat apply notin_union_2 in n0.
                        apply notin_singleton_1 in n0. rewrite e in n0.
                        assert (H'': x1 <> x). default_simp.
                        apply (diff_remove_2 _ _ _ H'' n1).
                      * rewrite (swap_symmetric _ x y).
                        repeat apply notin_union_2 in n1.
                        repeat apply notin_union_2 in n0.
                        apply notin_singleton_1 in n0. rewrite e in n0.
                        apply notin_singleton_1 in n1.
                        rewrite (shuffle_swap _ _ _ _ n1 n0).
                        apply aeq_swap. rewrite swap_symmetric. assumption.
                ----- apply aeq_abs_diff.
                      ------ assumption.
                      ------ pose proof in_or_notin. specialize (H3 y (fv_nom (swap x x1 t1'))).
                             rewrite <- (swap_size_eq x x1).
                             destruct H3.
                             ------- apply (fv_nom_m_subst_in _ t2) in H3. unfold m_subst in H3.
                                     rewrite H3. simpl. apply notin_union_3.
                                     -------- repeat apply notin_union_2 in n1. apply notin_singleton_1 in n1.
                                              case (x0 == y);intros.
                                              * rewrite e. default_simp.
                                              * apply (diff_remove _ _ _ n4).
                                                pose proof n0. repeat apply notin_union_2 in H4.
                                                apply notin_singleton_1 in H4.
                                                assert (H': x0 <> x). default_simp.
                                                apply (fv_nom_remove_swap _ _ _ _ n3 H').
                                                apply notin_union_2 in n0. apply notin_union_1 in n0.
                                                apply aeq_fv_nom in H5. rewrite H5 in n0.
                                                rewrite swap_symmetric in n0.
                                                apply (diff_remove_2 _ _ _ n4) in n0.
                                                apply fv_nom_swap_remove in n0;assumption.
                                     -------- apply notin_union_1 in n0. assumption.
                             ------- apply (fv_nom_m_subst_notin _ t2) in H3. unfold m_subst in H3.
                                     rewrite H3. repeat apply notin_union_2 in n1. apply notin_singleton_1 in n1.
                                     case (x0 == y);intros.
                                     * rewrite e. default_simp.
                                     * apply (diff_remove _ _ _ n4).
                                       pose proof n0. repeat apply notin_union_2 in H4.
                                       apply notin_singleton_1 in H4.
                                       assert (H': x0 <> x). default_simp.
                                       apply (fv_nom_remove_swap _ _ _ _ n3 H').
                                       apply notin_union_2 in n0. apply notin_union_1 in n0.
                                       apply aeq_fv_nom in H5. rewrite H5 in n0.
                                       rewrite swap_symmetric in n0.
                                       apply (diff_remove_2 _ _ _ n4) in n0.
                                       apply fv_nom_swap_remove in n0;assumption.
                      ------ rewrite <- (swap_size_eq y x0 t0). rewrite <- (swap_size_eq x x1 t1').    
                             apply (aeq_trans _ (subst_rec (size (swap x1 x0 (swap x x1 t1')))
                             (swap x1 x0 (swap x x1 t1')) t2 (swap_var x1 x0 y))).
                             ------- unfold swap_var. default_simp.
                                     -------- repeat apply notin_union_2 in n1. apply notin_singleton_1 in n1. contradiction.
                                     -------- rewrite swap_id. case (x1 == x);intros.
                                              --------- rewrite e. rewrite swap_id. apply aeq_m_subst_2. assumption.
                                              --------- rewrite (swap_symmetric _ x1 x0). rewrite (swap_symmetric _ x x1).
                                                        rewrite (shuffle_swap _ _ _ _ n n5).  rewrite (swap_symmetric _ x0 x).
                                                        assert (H': x <> x1). default_simp.
                                                        rewrite (shuffle_swap _ _ _ _ H' n3). apply H.
                                                        * rewrite swap_size_eq. reflexivity.
                                                        * assumption.
                                                        * apply fv_nom_swap. assert (H'': x1 <> x0).
                                                          default_simp. apply (fv_nom_remove_swap _ _ _ _ H'' n5).
                                                          apply notin_union_2 in n1. apply notin_union_1 in n1.
                                                          apply diff_remove_2 in n1;assumption.
                                                        * rewrite swap_involutive. assumption.
                                     -------- apply H.
                                              --------- rewrite swap_size_eq. reflexivity.
                                              --------- assumption.
                                              --------- case (x == x1);intros.
                                                        ---------- rewrite e. rewrite swap_id. apply fv_nom_swap.
                                                                   apply (aeq_swap1 _ _ x y) in H5.
                                                                   rewrite swap_involutive in H5.
                                                                   apply aeq_fv_nom in H5. rewrite <- H5. rewrite <- e in n3.
                                                                   assert (H': x0 <> y). default_simp.
                                                                   apply (fv_nom_remove_swap _ _ _ _ H' n3).
                                                                   apply notin_union_2 in n0. apply notin_union_1 in n0.
                                                                   apply (diff_remove_2  _ y);assumption.
                                                        ---------- repeat apply notin_union_2 in n0. apply notin_singleton_1 in n0.
                                                                   apply (fv_nom_remove_swap _ _ _ _ n0 n6).
                                                                   apply fv_nom_swap. apply notin_union_2 in n1.
                                                                   apply notin_union_1 in n1. apply (diff_remove_2 _ x).
                                                                   * default_simp.
                                                                   * assumption.
                                              --------- case (x1 == x);intros.
                                                        ---------- rewrite e. rewrite swap_id. rewrite (swap_symmetric _ x y).
                                                                   rewrite shuffle_swap.
                                                                   * apply aeq_swap. rewrite swap_symmetric. assumption.
                                                                   * assumption.
                                                                   * repeat apply notin_union_2 in n0. apply notin_singleton_1.
                                                                     assumption.
                                                        ---------- rewrite (swap_symmetric _ x1 x0). rewrite (swap_symmetric _ x x1).
                                                                   pose proof n0. repeat apply notin_union_2 in n0.
                                                                   apply notin_singleton_1 in n0.
                                                                   assert (H': x0 <> x). default_simp.
                                                                   rewrite (shuffle_swap _ _ _ _ H' n6). rewrite (swap_symmetric _ x0 x).
                                                                   rewrite (swap_symmetric _ x y). rewrite (shuffle_swap _ _ _ _ n5 n0).
                                                                   apply aeq_swap. assert (H'': x <> x1). default_simp.
                                                                   rewrite swap_symmetric_2;try assumption.
                                                                   rewrite (swap_symmetric _ y x).
                                                                   apply (aeq_trans _ (swap x y t1') _ H5).
                                                                   apply aeq_swap0.
                                                                   * apply notin_union_2 in H3. apply notin_union_1 in H3.
                                                                     assert (H''': x0 <> y). default_simp.
                                                                     apply (diff_remove_2 _ _ _ H''') in H3.
                                                                     apply aeq_fv_nom in H5. rewrite H5 in H3.
                                                                     assumption.
                                                                   * apply notin_union_2 in n1. apply notin_union_1 in n1.
                                                                     apply (diff_remove_2 _ _ _ n6) in n1.
                                                                     assert (H''': x1 <> y). default_simp.
                                                                     apply fv_nom_remove_swap;assumption.
                             ------- apply (aeq_trans _ (subst_rec (size (swap x1 x0 (swap x x1 t1'))) (swap x1 x0 (swap x x1 t1'))
                                     (swap x1 x0 t2) (swap_var x1 x0 y))).
                                     -------- apply aeq_m_subst_1. apply notin_union_1 in n0. apply notin_union_1 in n1.
                                              apply aeq_swap0;assumption.
                                     -------- pose proof aeq_swap_m_subst. unfold m_subst in H3. apply aeq_sym. apply H3.
           ---- case (x1 == x0);intros.
                ----- rewrite e. apply aeq_abs_same. rewrite <- (swap_size_eq z x0). rewrite <- (swap_size_eq z x0 t1').
                      apply H.
                      ------ reflexivity.
                      ------ assumption.
                      ------ apply (diff_remove_2 _ _ _ n2) in H1. repeat apply notin_union_2 in n0. apply notin_singleton_1 in n0.
                             apply fv_nom_remove_swap;assumption.
                      ------ case (z == x0);intros.
                             * rewrite e0. rewrite swap_id. rewrite swap_id. assumption.
                             * repeat apply notin_union_2 in n0. repeat apply notin_union_2 in n1.
                               apply notin_singleton_1 in n0. apply notin_singleton_1 in n1. rewrite e in n1.
                               rewrite swap_symmetric_2;try assumption. apply aeq_swap. assumption.
                ----- apply aeq_abs_diff.
                      ------ default_simp.
                      ------ pose proof in_or_notin. specialize (H3 y (fv_nom (swap z x1 t1'))).
                             rewrite <- (swap_size_eq z x1). destruct H3.
                             ------- apply (fv_nom_m_subst_in _ t2) in H3. unfold m_subst in H3. rewrite H3. simpl.
                                     apply notin_union_3.
                                     -------- case (x0 == y);intros.
                                              --------- rewrite e. default_simp.
                                              --------- apply (diff_remove _ _ _ n6). case (x0 == z);intros.
                                                        * rewrite e. apply fv_nom_swap. apply notin_union_2 in n1.
                                                          apply notin_union_1 in n1. rewrite e in n5.
                                                          apply diff_remove_2 in n1;assumption.
                                                        * assert (H': x0 <> x1). default_simp.
                                                          apply fv_nom_remove_swap;try assumption.
                                                          pose proof n0. repeat apply notin_union_2 in n0. apply notin_singleton_1 in n0.
                                                          apply notin_union_2 in H4. apply notin_union_1 in H4.
                                                          apply (diff_remove_2 _ _ _ n7) in H4. apply aeq_fv_nom in H5.
                                                          assert (H'': x0 <> x). default_simp.
                                                          rewrite H5 in H4. apply fv_nom_swap_remove in H4;assumption.
                                     -------- apply notin_union_1 in n0. assumption.
                             ------- apply (fv_nom_m_subst_notin _ t2) in H3. unfold m_subst in H3. rewrite H3.
                                     case (x0 == y);intros.
                                     -------- rewrite e. default_simp.
                                     -------- apply (diff_remove _ _ _ n6). case (x0 == z);intros.
                                              * rewrite e. apply fv_nom_swap. apply notin_union_2 in n1.
                                                apply notin_union_1 in n1. rewrite e in n5.
                                                apply diff_remove_2 in n1;assumption.
                                              * assert (H': x0 <> x1). default_simp.
                                                apply fv_nom_remove_swap;try assumption.
                                                pose proof n0. repeat apply notin_union_2 in n0. apply notin_singleton_1 in n0.
                                                apply notin_union_2 in H4. apply notin_union_1 in H4.
                                                apply (diff_remove_2 _ _ _ n7) in H4. apply aeq_fv_nom in H5.
                                                assert (H'': x0 <> x). default_simp.
                                                rewrite H5 in H4. apply fv_nom_swap_remove in H4;assumption.
                      ------ rewrite <- (swap_size_eq z x0). rewrite <- (swap_size_eq z x1 t1').
                             apply (aeq_trans _ (subst_rec (size (swap x1 x0 (swap z x1 t1'))) (swap x1 x0 (swap z x1 t1'))
                             t2 (swap_var x1 x0 y))).
                             ------- unfold swap_var. pose proof n1. repeat apply notin_union_2 in H3. apply notin_singleton_1 in H3.
                                     default_simp.
                                     -------- case (x == x1);intros.
                                              --------- rewrite e. apply aeq_m_subst_2.
                                                        rewrite (swap_symmetric _ x1 x0). rewrite (swap_symmetric _ z x1).
                                                        rewrite shuffle_swap.
                                                        * rewrite (swap_symmetric _ z x0). apply aeq_swap.
                                                          rewrite e in H5. rewrite swap_symmetric. assumption.
                                                        * assumption.
                                                        * default_simp.
                                              --------- apply H.
                                                        ---------- rewrite swap_size_eq. reflexivity.
                                                        ---------- assumption.
                                                        ---------- apply fv_nom_remove_swap;try assumption.
                                                                   apply (diff_remove_2 _ _ _ n2) in H1.
                                                                   apply fv_nom_remove_swap;assumption.
                                                        ---------- rewrite (swap_symmetric _ z x1). rewrite (swap_symmetric _ x1 x0).
                                                                   case (x1 == z); intros.
                                                                   ----------- rewrite e. rewrite swap_id.
                                                                               rewrite (swap_symmetric _ x0 z).
                                                                               rewrite shuffle_swap;try assumption.
                                                                               rewrite (swap_symmetric _ x x0).
                                                                               rewrite shuffle_swap;try assumption.
                                                                               rewrite (swap_symmetric _ z x0).
                                                                               apply aeq_swap. rewrite (swap_symmetric _ x0 x).
                                                                               assumption.
                                                                   ----------- rewrite shuffle_swap;try assumption.
                                                                               rewrite (swap_symmetric _ x0 z).
                                                                               assert (H'': z <> x1). default_simp.
                                                                               rewrite shuffle_swap;try assumption.
                                                                               rewrite (swap_symmetric _ z x1).
                                                                               rewrite shuffle_swap;try assumption.
                                                                               rewrite (swap_symmetric _ x z).
                                                                               rewrite shuffle_swap;try assumption.
                                                                               rewrite (swap_symmetric _ z x).
                                                                               rewrite shuffle_swap;try assumption.
                                                                               rewrite (swap_symmetric _ x x0).
                                                                               rewrite shuffle_swap;try assumption.
                                                                               rewrite (swap_symmetric _ z x1).
                                                                               rewrite (swap_symmetric _ x0 z).
                                                                               rewrite shuffle_swap;try assumption.
                                                                               rewrite (swap_symmetric _ x1 x0).
                                                                               rewrite shuffle_swap;try assumption.
                                                                               rewrite (swap_symmetric _ z x0).
                                                                               apply aeq_swap. apply (aeq_swap _ _ x0 x1).
                                                                               rewrite swap_involutive.
                                                                               apply (aeq_trans _ t0).
                                                                               ------------ apply aeq_sym.
                                                                                            apply aeq_swap0.
                                                                                            * apply notin_union_2 in n0.
                                                                                              apply notin_union_1 in n0.
                                                                                              apply (diff_remove_2 _ _ _ n) in n0.
                                                                                              assumption.
                                                                                            * apply notin_union_2 in n1.
                                                                                              apply notin_union_1 in n1.
                                                                                              apply (diff_remove_2 _ _ _ n8) in n1.
                                                                                              apply aeq_fv_nom in H5. rewrite H5.
                                                                                              apply fv_nom_remove_swap;default_simp.
                                                                               ------------ rewrite swap_symmetric. assumption.
                                     -------- apply H.
                                              --------- rewrite swap_size_eq. reflexivity.
                                              --------- assumption.
                                              --------- case (x == x1);intros.
                                                        ---------- rewrite e in *. apply fv_nom_swap. case (x0 == z);intros.
                                                                   ----------- rewrite e0 in *. apply fv_nom_swap.
                                                                               apply notin_union_2 in n1. apply notin_union_1 in n1.
                                                                               apply diff_remove_2 in n1;assumption.
                                                                   ----------- apply notin_union_2 in n0. apply notin_union_1 in n0.
                                                                               apply (diff_remove_2 _ _ _ n8) in n0.
                                                                               apply aeq_fv_nom in H5. rewrite H5 in n0.
                                                                               apply fv_nom_swap_remove in n0.
                                                                               * apply fv_nom_remove_swap;default_simp.
                                                                               * default_simp.
                                                                               * default_simp.
                                                        ---------- pose proof n0. repeat apply notin_union_2 in H4.
                                                                   apply notin_singleton_1 in H4.
                                                                   apply fv_nom_remove_swap;try assumption.
                                                                   apply fv_nom_remove_swap;try assumption.
                                                                   apply diff_remove_2 in H1;assumption.
                                              --------- pose proof n0. repeat apply notin_union_2 in H4. apply notin_singleton_1 in H4.
                                                        case (x == x1);intros.
                                                        ---------- rewrite e in *. case (x0 == z);intros.
                                                                   ----------- rewrite e0 in *. rewrite swap_id.
                                                                               rewrite (swap_symmetric _ z x1).
                                                                               rewrite swap_involutive. assumption.
                                                                   ----------- rewrite (swap_symmetric _ z x1).
                                                                               rewrite (swap_symmetric _ x1 x0).
                                                                               rewrite shuffle_swap;try assumption.
                                                                               rewrite swap_symmetric_2;try default_simp.
                                                                               rewrite swap_symmetric. apply aeq_swap.
                                                                               rewrite (swap_symmetric _ x1 y).
                                                                               rewrite (swap_symmetric _ x0 x1).
                                                                               rewrite shuffle_swap;try assumption.
                                                                               apply (aeq_swap _ _ y x0). rewrite swap_involutive.
                                                                               apply (aeq_trans _ t0).
                                                                               ------------ apply aeq_sym. apply aeq_swap0.
                                                                                            * apply aeq_fv_nom in H5. rewrite H5.
                                                                                              rewrite swap_symmetric.
                                                                                              apply fv_nom_swap.
                                                                                              apply diff_remove_2 in H1;assumption.
                                                                                            * apply notin_union_2 in n0.
                                                                                              apply notin_union_1 in n0.
                                                                                              apply diff_remove_2 in n0;assumption.
                                                                               ------------ rewrite swap_symmetric. assumption.
                                                        ---------- rewrite swap_symmetric_2;try assumption.
                                                                   rewrite (swap_symmetric_2 x y);try assumption.
                                                                   rewrite (swap_symmetric _ x1 x0). rewrite (swap_symmetric _ z x1).
                                                                   case (x0 == z);intros.
                                                                   ----------- rewrite e. rewrite swap_id. rewrite swap_symmetric.
                                                                               rewrite swap_involutive. assumption.
                                                                   ----------- case (x1 == z);intros.
                                                                               ------------ rewrite e in *. rewrite swap_id.
                                                                                            rewrite swap_symmetric.
                                                                                            apply aeq_swap. assumption.
                                                                               ------------ rewrite shuffle_swap;try assumption.
                                                                                            rewrite swap_symmetric. apply aeq_swap.
                                                                                            apply (aeq_swap _ _ x0 x1).
                                                                                            rewrite swap_involutive.
                                                                                            apply (aeq_trans _ t0).
                                                                                            ------------- apply aeq_sym.
                                                                                                          apply aeq_swap0.
                                                                                                          * apply notin_union_2 in n0.
                                                                                                            apply notin_union_1 in n0.
                                                                                                            apply diff_remove_2 in n0;assumption.
                                                                                                          * apply notin_union_2 in n1.
                                                                                                            apply notin_union_1 in n1.
                                                                                                            apply aeq_fv_nom in H5.
                                                                                                            rewrite H5.
                                                                                                            apply fv_nom_remove_swap.
                                                                                                            ** default_simp.
                                                                                                            ** default_simp.
                                                                                                            ** apply diff_remove_2 in n1;assumption.
                                                                                            ------------- assumption.
                             ------- apply (aeq_trans _ (subst_rec (size (swap x1 x0 (swap z x1 t1')))
                                     (swap x1 x0 (swap z x1 t1')) (swap x1 x0 t2) (swap_var x1 x0 y))).
                                     -------- apply aeq_m_subst_1. apply aeq_swap0.
                                              * apply notin_union_1 in n1. assumption.
                                              * apply notin_union_1 in n0. assumption.
                                     -------- pose proof aeq_swap_m_subst. unfold m_subst in H3. apply aeq_sym.
                                              apply H3.
    -- unfold m_subst in *. simpl. unfold swap_var in *. default_simp.
       --- case (x0 == x2);intros.
           ---- rewrite e in *. apply aeq_abs_same. rewrite swap_id. apply (aeq_trans _ t1').
                ----- rewrite swap_symmetric in H8. rewrite swap_involutive in H8. assumption.
                ----- pose proof subst_fresh_eq. unfold m_subst in H3. apply aeq_sym. apply H3.
                      rewrite swap_symmetric in H7. apply fv_nom_swap_2 in H7. assumption.
           ---- apply aeq_abs_diff.
                ----- assumption.
                ----- pose proof in_or_notin. specialize (H3 y (fv_nom (swap x0 x2 t1'))).
                      rewrite <- (swap_size_eq x0 x2). destruct H3.
                      ------ rewrite swap_symmetric in H7. apply fv_nom_swap_2 in H7.
                             apply (fv_nom_remove_swap _ _ x2 x0) in H7.
                             ------- default_simp.
                             ------- repeat apply notin_union_2 in n0. apply notin_singleton_1 in n0. assumption.
                             ------- assumption.
                      ------ apply (fv_nom_m_subst_notin _ t2) in H3. unfold m_subst in H3. rewrite H3.
                             apply diff_remove;try assumption. apply fv_nom_swap. apply notin_union_2 in n0.
                             apply notin_union_1 in n0. apply diff_remove_2 in n0;try default_simp.
                ----- apply (aeq_trans _ (swap x2 x0 (swap x0 x2 t1'))).
                      ------ rewrite swap_symmetric. rewrite swap_involutive.
                             rewrite swap_symmetric in H8. rewrite swap_involutive in H8. assumption.
                      ------ apply aeq_swap. pose proof subst_fresh_eq. unfold m_subst in H3. apply aeq_sym.
                             rewrite <- (swap_size_eq x0 x2). apply H3. apply fv_nom_remove_swap.
                             * repeat apply notin_union_2 in n0. apply notin_singleton_1 in n0. assumption.
                             * assumption.
                             * rewrite swap_symmetric in H7. apply fv_nom_swap_2 in H7. assumption.
     --- case (x0 == x2);intros.
         ---- rewrite e in *. apply aeq_abs_same. rewrite <- (swap_size_eq z x2).
              apply (aeq_trans _ (swap z x2 t1')).
              ----- apply (aeq_trans _ (swap z x2 (swap x2 y t1'))).
                    ------ assumption.
                    ------ apply aeq_swap. apply aeq_sym. apply aeq_swap0.
                           ------- apply notin_union_2 in n0. apply notin_union_1 in n0.
                                   apply diff_remove_2 in n0;assumption.
                           ------- rewrite swap_symmetric in H7. apply fv_nom_swap_2 in H7. assumption.
              ----- pose proof subst_fresh_eq. unfold m_subst in H3. apply aeq_sym. apply H3.
                    rewrite swap_symmetric in H7. apply fv_nom_swap_2 in H7.
                    apply fv_nom_remove_swap;default_simp.
         ---- apply aeq_abs_diff.
              ----- assumption.
              ----- pose proof in_or_notin. specialize (H3 y (fv_nom (swap z x2 t1'))).
                    rewrite <- (swap_size_eq z x2). destruct H3.
                    ------ rewrite swap_symmetric in H7. apply fv_nom_swap_2 in H7.
                            apply (fv_nom_remove_swap _ _ x2 z) in H7.
                            ------- default_simp.
                            ------- repeat apply notin_union_2 in n0. apply notin_singleton_1 in n0. assumption.
                            ------- assumption.
                    ------ apply (fv_nom_m_subst_notin _ t2) in H3. unfold m_subst in H3. rewrite H3.
                            apply diff_remove;try assumption. apply (diff_remove_2 _ _ _ H5) in H1.
                            apply fv_nom_remove_swap;assumption.
              ----- apply (aeq_trans _ (swap x2 x0 (swap z x2 t1'))).
                    ------ rewrite swap_symmetric. rewrite (swap_symmetric _ z x2).
                           case (x2 == z);intros.
                           ------- rewrite e in *. rewrite swap_id. rewrite swap_symmetric.
                                   apply (aeq_trans _ (swap z x0 (swap x0 y t1'))).
                                   -------- assumption.
                                   -------- apply aeq_swap. apply aeq_sym. apply aeq_swap0.
                                            * apply diff_remove_2 in H1;default_simp.
                                            * rewrite swap_symmetric in H7. apply fv_nom_swap_2 in H7. assumption.
                           ------- rewrite shuffle_swap;try assumption. apply (aeq_trans _ (swap z x0 (swap x0 y t1'))).
                                   -------- assumption.
                                   -------- rewrite swap_symmetric. apply aeq_swap. apply (diff_remove_2 _ _ _ H5) in H1.
                                            apply notin_union_2 in n0. apply notin_union_1 in n0.
                                            apply (diff_remove_2 _ _ _ n5) in n0.
                                            rewrite swap_symmetric in H7. apply fv_nom_swap_2 in H7.
                                            apply (aeq_trans _ t1').
                                            * apply aeq_sym. apply aeq_swap0;assumption.
                                            * apply aeq_swap0;assumption.
                    ------ apply aeq_swap. pose proof subst_fresh_eq. unfold m_subst in H3. apply aeq_sym.
                            rewrite <- (swap_size_eq z x2). apply H3. apply fv_nom_remove_swap.
                            * repeat apply notin_union_2 in n0. apply notin_singleton_1 in n0. assumption.
                            * assumption.
                            * rewrite swap_symmetric in H7. apply fv_nom_swap_2 in H7. assumption.
     --- case (x1 == z);intros.
         ---- rewrite e0 in *. apply aeq_abs_same. rewrite <- (swap_size_eq x0 z). case (x0 == z);intros.
              ----- rewrite e1 in *. rewrite swap_id. apply (diff_remove_2 _ _ _ H0) in H1.
                    rewrite swap_involutive in H8. apply (aeq_trans _ t0).
                    ------ pose proof subst_fresh_eq. unfold m_subst in H3. apply H3. apply aeq_fv_nom in H8.
                           rewrite H8. assumption.
                    ------ assumption.
              ----- apply (aeq_trans _ (swap x0 z t0)).
                    ------ pose proof subst_fresh_eq. unfold m_subst in H3. apply H3.
                           apply fv_nom_remove_swap;try assumption. apply aeq_fv_nom in H8. rewrite H8.
                           apply fv_nom_swap. assumption.
                    ------ rewrite swap_symmetric in H8. rewrite shuffle_swap in H8;try assumption.
                           apply (aeq_swap _ _ x0 z). rewrite swap_involutive. apply (aeq_trans _
                           (swap x0 z (swap x0 x t1'))).
                           ------- assumption.
                           ------- apply aeq_swap. apply aeq_sym. apply aeq_swap0.
                                   -------- apply fv_nom_swap_remove in H7;default_simp.
                                   -------- apply diff_remove_2 in H1; assumption.
         ---- apply aeq_abs_diff.
              ----- assumption.
              ----- case (x1 == x0);intros.
                    ------ rewrite e0 in *. apply fv_nom_swap_remove in H7;assumption.
                    ------ pose proof n. repeat apply notin_union_2 in H3. apply notin_singleton_1 in H3.
                           apply notin_union_2 in n. apply notin_union_1 in n. apply aeq_fv_nom in H8.
                           rewrite H8 in n. apply diff_remove_2 in n;try assumption.
                           apply fv_nom_swap_remove in n;try default_simp.
                           apply fv_nom_swap_remove in n;try default_simp.
              ----- rewrite <- (swap_size_eq x0 x1). apply (aeq_trans _ (swap x0 x1 t0)).
                    ------ pose proof subst_fresh_eq. unfold m_subst in H3. apply H3.
                           apply (aeq_swap _ _ x x0) in H8. rewrite swap_involutive in H8.
                           apply aeq_fv_nom in H8. rewrite <- H8 in H7. apply fv_nom_swap_2 in H7.
                           repeat apply notin_union_2 in n. apply notin_singleton_1 in n.
                           apply fv_nom_remove_swap;assumption.
                    ------ apply (aeq_swap _ _ x0 x1). rewrite swap_involutive. rewrite (swap_symmetric _ z x1).
                           case (x0 == z);intro.
                           ------- rewrite e0 in *. rewrite swap_symmetric. rewrite swap_involutive in *.
                                   assumption.
                           ------- rewrite shuffle_swap;try assumption. rewrite swap_symmetric.
                                   case (x0 == x1);intros.
                                   -------- rewrite e0 in *. rewrite swap_id. rewrite swap_symmetric in H8.
                                            rewrite shuffle_swap in H8;try assumption. apply (aeq_trans _ (swap x1 z (swap x1 x t1'))).
                                            --------- assumption.
                                            --------- rewrite swap_symmetric. apply aeq_swap. apply aeq_sym. apply aeq_swap0.
                                                      * apply fv_nom_swap_remove in H7;assumption.
                                                      * apply diff_remove_2 in H1;assumption.
                                   -------- rewrite shuffle_swap;try default_simp. apply (aeq_trans _ (swap z x1 t0)).
                                            --------- apply aeq_swap0.
                                                      * apply (aeq_swap _ _ x x0) in H8. apply (aeq_swap _ _ x z) in H8.
                                                        repeat rewrite swap_involutive in H8. apply aeq_fv_nom in H8.
                                                        rewrite <- H8 in H1. apply (diff_remove_2 _ _ _ H0) in H1.
                                                        rewrite swap_symmetric in H1. apply fv_nom_swap_2 in H1.
                                                        apply fv_nom_swap_remove in H1;default_simp.
                                                      * apply notin_union_2 in n. apply notin_union_1 in n.
                                                        apply diff_remove_2 in n;default_simp.
                                            --------- apply aeq_swap. rewrite swap_symmetric in H8.
                                                      rewrite shuffle_swap in H8;try assumption.
                                                      rewrite swap_symmetric. apply (aeq_trans _ (swap x0 z (swap x0 x t1'))).
                                                      ---------- assumption.
                                                      ---------- apply aeq_swap. apply aeq_sym. apply aeq_swap0.
                                                                 * apply fv_nom_swap_remove in H7;assumption.
                                                                 * apply diff_remove_2 in H1;assumption.
     --- rewrite <- (swap_size_eq x0 x1 t0). rewrite <- (swap_size_eq x x2 t1'). case (x1 == x2);intros.
         ---- rewrite e in *. apply aeq_abs_same. apply H.
              ------ reflexivity.
              ------ assumption.
              ------ apply fv_nom_swap. apply notin_union_2 in n0. apply notin_union_1 in n0.
                     repeat apply notin_union_2 in n. apply notin_singleton_1 in n.
                     apply diff_remove_2 in n0;default_simp.
              ------ case (x0 == x2);intros.
                     ------- rewrite e0 in *. rewrite swap_id. rewrite swap_symmetric.
                             rewrite shuffle_swap.
                             * rewrite (swap_symmetric _ y x). assumption.
                             * repeat apply notin_union_2 in n0. apply notin_singleton_1 in n0. assumption.
                             * assumption.
                     ------- assert (H': y <> x2). repeat apply notin_union_2 in n0. apply notin_singleton_1 in n0. assumption.
                             assert (H'': x <> x2). repeat apply notin_union_2 in n. apply notin_singleton_1 in n. assumption.
                             rewrite (swap_symmetric _ x y). rewrite shuffle_swap;try assumption.
                             apply (aeq_swap _ _ x0 x2). rewrite swap_involutive.
                             rewrite (swap_symmetric _ y x2). rewrite shuffle_swap;try default_simp.
                             rewrite swap_symmetric. rewrite shuffle_swap;try assumption.
                             apply (aeq_trans _ (swap y x2 t0)).
                             -------- apply aeq_swap0.
                                      * apply (aeq_swap _ _ y x0) in H8. rewrite swap_involutive in H8.
                                        apply aeq_fv_nom in H8. rewrite <- H8 in H7.
                                        apply fv_nom_swap_2 in H7. assumption.
                                      * apply notin_union_2 in n. apply notin_union_1 in n.
                                        apply diff_remove_2 in n;default_simp.
                             -------- apply aeq_swap. rewrite (swap_symmetric _ y x). assumption.
         ---- apply aeq_abs_diff.
              ----- assumption.
              ----- pose proof in_or_notin. specialize (H3 y (fv_nom (swap x x2 t1'))).
                    destruct H3.
                    ------ apply (fv_nom_m_subst_in _ t2) in H3. unfold m_subst in H3. rewrite H3.
                           simpl. apply notin_union_3.
                           ------- case (x1 == y);intros.
                                   -------- rewrite e. default_simp.
                                   -------- apply diff_remove;try assumption. pose proof n.
                                            repeat apply notin_union_2 in H4. apply notin_singleton_1 in H4.
                                            apply fv_nom_remove_swap;try default_simp.
                                            apply (aeq_swap _ _ y x0) in H8.
                                            apply (aeq_swap _ _ x y) in H8.
                                            repeat rewrite swap_involutive in H8. apply aeq_fv_nom in H8.
                                            rewrite <- H8. apply fv_nom_remove_swap;try default_simp.
                                            case (x1 == x0);intros.
                                            --------- rewrite e in *. rewrite swap_symmetric.
                                                      apply fv_nom_swap. apply fv_nom_swap_remove in H7;try default_simp.
                                                      rewrite <- H8 in H7. apply fv_nom_swap_remove in H7;
                                                      try default_simp. apply fv_nom_swap_2 in H7. assumption.
                                            --------- apply fv_nom_remove_swap;try assumption. apply notin_union_2 in n.
                                                      apply notin_union_1 in n. apply diff_remove_2 in n;assumption.
                           ------- apply notin_union_1 in n. assumption.
                    ------ apply (fv_nom_m_subst_notin _ t2) in H3. unfold m_subst in H3. rewrite H3.
                           case (x1 == y);intros.
                           ------- rewrite e. default_simp.
                           ------- apply diff_remove;try assumption. pose proof n.
                                   repeat apply notin_union_2 in H4. apply notin_singleton_1 in H4.
                                   apply fv_nom_remove_swap;try default_simp.
                                   apply (aeq_swap _ _ y x0) in H8.
                                   apply (aeq_swap _ _ x y) in H8.
                                   repeat rewrite swap_involutive in H8. apply aeq_fv_nom in H8.
                                   rewrite <- H8. apply fv_nom_remove_swap;try default_simp.
                                   case (x1 == x0);intros.
                                   -------- rewrite e in *. rewrite swap_symmetric.
                                            apply fv_nom_swap. apply fv_nom_swap_remove in H7;try default_simp.
                                            rewrite <- H8 in H7. apply fv_nom_swap_remove in H7;
                                            try default_simp. apply fv_nom_swap_2 in H7. assumption.
                                   -------- apply fv_nom_remove_swap;try assumption. apply notin_union_2 in n.
                                            apply notin_union_1 in n. apply diff_remove_2 in n;assumption.
              ----- apply (aeq_trans _ (subst_rec (size (swap x2 x1 (swap x x2 t1'))) (swap x2 x1 (swap x x2 t1'))
                    t2 (swap_var x2 x1 y))).
                    ------ unfold swap_var. pose proof n0. repeat apply notin_union_2 in H3. apply notin_singleton_1 in H3.
                           default_simp.
                           ------- case (x == x2);intros.
                                   -------- rewrite e in *. apply aeq_m_subst_2. rewrite swap_id.
                                            rewrite swap_symmetric. apply (aeq_swap _ _ x1 x0).
                                            rewrite swap_involutive. assumption.
                                   -------- apply H.
                                            --------- rewrite swap_size_eq. reflexivity.
                                            --------- assumption.
                                            --------- apply fv_nom_remove_swap;try assumption.
                                                      apply fv_nom_swap. apply notin_union_2 in n0.
                                                      apply notin_union_1 in n0. apply diff_remove_2 in n0;
                                                      default_simp.
                                            --------- rewrite (swap_symmetric _ x2 x1).
                                                      rewrite (swap_symmetric t1' x x2).
                                                      rewrite shuffle_swap;try default_simp.
                                                      rewrite (swap_symmetric _ x1 x). rewrite shuffle_swap;
                                                      try assumption. rewrite swap_involutive.
                                                      apply (aeq_swap _ _ x0 x1). rewrite swap_involutive.
                                                      rewrite swap_symmetric. apply H8.
                           ------- apply H.
                                   -------- rewrite swap_size_eq. reflexivity.
                                   -------- assumption.
                                   -------- case (x == x2);intros.
                                            --------- rewrite e in *. apply fv_nom_swap. rewrite swap_id.
                                                      case (x1 == x0);intros.
                                                      ---------- rewrite e0 in *. apply fv_nom_swap_remove in H7;
                                                                 assumption.
                                                      ---------- apply notin_union_2 in n. apply notin_union_1 in n.
                                                                 apply (diff_remove_2 _ _ _ n6) in n.
                                                                 apply aeq_fv_nom in H8. rewrite H8 in n.
                                                                 apply fv_nom_swap_remove in n;try default_simp.
                                                                 apply fv_nom_swap_remove in n;try default_simp.
                                            --------- pose proof n. repeat apply notin_union_2 in H4.
                                                      apply notin_singleton_1 in H4. apply fv_nom_remove_swap;try assumption.
                                                      apply fv_nom_swap. apply notin_union_2 in n0.
                                                      apply notin_union_1 in n0. apply diff_remove_2 in n0;default_simp.
                                   -------- pose proof n. repeat apply notin_union_2 in H4. apply notin_singleton_1 in H4.
                                            case (x2 == x);intros.
                                            --------- rewrite e in *. rewrite swap_id.
                                                      rewrite (swap_symmetric _ x y).
                                                      rewrite shuffle_swap;try assumption.
                                                      apply (aeq_swap _ _ x0 x1). rewrite swap_involutive.
                                                      rewrite (swap_symmetric _ y x1).
                                                      rewrite shuffle_swap;try default_simp. rewrite swap_symmetric.
                                                      case (x0 == x1);intros.
                                                      ---------- rewrite e in *. rewrite swap_id.
                                                                 rewrite (swap_symmetric _ y x). assumption.
                                                      ---------- rewrite shuffle_swap;try assumption.
                                                                 apply (aeq_trans _ (swap y x1 t0)).
                                                                 ----------- apply aeq_swap0.
                                                                             * apply (aeq_swap _ _ y x0) in H8.
                                                                               rewrite swap_involutive in H8. apply aeq_fv_nom in H8.
                                                                               rewrite <- H8 in H7. apply fv_nom_swap_2 in H7.
                                                                               assumption.
                                                                             * apply notin_union_2 in n.
                                                                               apply notin_union_1 in n.
                                                                               apply diff_remove_2 in n;default_simp.
                                                                 ----------- apply aeq_swap. rewrite (swap_symmetric _ y x).
                                                                             assumption.
                                            --------- rewrite (swap_symmetric _ x2 x1). rewrite (swap_symmetric _ x x2).
                                                      rewrite shuffle_swap;try default_simp.
                                                      rewrite (swap_symmetric _ x1 x). rewrite (swap_symmetric _ x y).
                                                      rewrite shuffle_swap;try assumption. apply (aeq_swap _ _ x0 x1).
                                                      rewrite swap_involutive. rewrite (swap_symmetric _ y x1).
                                                      rewrite shuffle_swap;try default_simp. rewrite swap_symmetric.
                                                      case (x0 == x1);intros.
                                                      ---------- rewrite e in *. rewrite swap_id.
                                                                 apply (aeq_trans _ (swap y x1 (swap y x t1'))).
                                                                 ----------- rewrite (swap_symmetric _ y x). assumption.
                                                                 ----------- repeat apply aeq_swap. apply aeq_swap0.
                                                                             * apply fv_nom_swap_remove in H7;default_simp.
                                                                             * apply notin_union_2 in n0.
                                                                               apply notin_union_1 in n0.
                                                                               apply diff_remove_2 in n0;assumption.
                                                      ---------- rewrite shuffle_swap;try assumption.
                                                                 apply (aeq_trans _ (swap y x1 t0)).
                                                                 ----------- apply aeq_swap0.
                                                                             * apply (aeq_swap _ _ y x0) in H8.
                                                                               rewrite swap_involutive in H8.
                                                                               apply aeq_fv_nom in H8. rewrite <- H8 in H7.
                                                                               apply fv_nom_swap_2 in H7. assumption.
                                                                             * apply notin_union_2 in n. apply notin_union_1 in n.
                                                                               apply diff_remove_2 in n;default_simp.
                                                                 ----------- apply aeq_swap. apply (aeq_trans _ 
                                                                             (swap y x0 (swap y x t1'))).
                                                                             ------------ rewrite (swap_symmetric _ y x). assumption.
                                                                             ------------ repeat apply aeq_swap. apply aeq_swap0.
                                                                                          * apply (aeq_swap _ _ y x0) in H8.
                                                                                            apply (aeq_swap _ _ x y) in H8.
                                                                                            repeat rewrite swap_involutive in H8.
                                                                                            apply aeq_fv_nom in H8.
                                                                                            rewrite <- H8.
                                                                                            apply fv_nom_remove_swap;try default_simp.
                                                                                            apply fv_nom_remove_swap;try default_simp.
                                                                                          * default_simp.
                    ------ apply (aeq_trans _ (subst_rec (size (swap x2 x1 (swap x x2 t1'))) (swap x2 x1 (swap x x2 t1'))
                           (swap x2 x1 t2) (swap_var x2 x1 y))).
                           ------- apply aeq_m_subst_1. apply aeq_swap0;default_simp.
                           ------- apply aeq_sym. apply aeq_swap_m_subst.
     --- rewrite <- (swap_size_eq x0 x1). rewrite <- (swap_size_eq z x2 t1'). case (x1 == x2);intros.
         ---- rewrite e in *. apply aeq_abs_same. apply H.
              ----- reflexivity.
              ----- assumption.
              ----- repeat apply notin_union_2 in n. apply notin_singleton_1 in n.
                    apply diff_remove_2 in H1;try default_simp. apply fv_nom_remove_swap; default_simp.
              ----- case (x0 == x2);intros.
                    ------ rewrite e0 in *. rewrite swap_id. repeat apply notin_union_2 in n0.
                           apply notin_singleton_1 in n0. rewrite swap_symmetric_2;try default_simp.
                    ------ rewrite swap_symmetric_2;default_simp. apply (aeq_swap _ _ x0 x2).
                           rewrite swap_involutive. rewrite (swap_symmetric _ z x2).
                           case (x2 == z);intros.
                           ------- rewrite e in *. rewrite swap_id.
                                   rewrite swap_symmetric. assumption.
                           ------- rewrite shuffle_swap;default_simp.
                                   case (x0 == y);intros.
                                   -------- rewrite e in *. rewrite (swap_symmetric _ y x2).
                                            rewrite (swap_symmetric _ x y). rewrite shuffle_swap;try default_simp.
                                            rewrite (swap_symmetric _ x2 x). rewrite shuffle_swap;try default_simp.
                                            apply (aeq_trans _ (swap y z (swap x y t1'))).
                                            --------- rewrite swap_symmetric. assumption.
                                            --------- repeat apply aeq_swap. apply aeq_swap0.
                                                      * apply fv_nom_swap_2 in H7. assumption.
                                                      * default_simp. 
                                   -------- rewrite (swap_symmetric_2 x0 x2 x y);try default_simp.
                                            apply (aeq_trans _ (swap x0 z (swap x y t1'))).
                                            --------- rewrite swap_symmetric. assumption.
                                            --------- repeat apply aeq_swap. apply aeq_swap0.
                                                      * apply fv_nom_swap_remove in H7;default_simp.
                                                      * default_simp.
         ---- apply aeq_abs_diff.
              ----- assumption.
              ----- pose proof in_or_notin. specialize (H3 y (fv_nom (swap z x2 t1'))).
                    destruct H3.
                    ------ apply (fv_nom_m_subst_in _ t2) in H3. unfold m_subst in H3. rewrite H3.
                           simpl. apply notin_union_3.
                           ------- case (x1 == y);intros.
                                   -------- rewrite e. default_simp.
                                   -------- apply diff_remove;try assumption. case (x1 == z);intros.
                                            --------- rewrite e in *. apply fv_nom_swap. default_simp.
                                            --------- apply fv_nom_remove_swap;try assumption.
                                                      apply (aeq_swap _ _ z x0) in H8. pose proof H8.
                                                      apply (aeq_swap _ _ x y) in H8.
                                                      repeat rewrite swap_involutive in H8. apply aeq_fv_nom in H8.
                                                      rewrite <- H8. pose proof n. repeat apply notin_union_2 in H6.
                                                      apply notin_singleton_1 in H6. apply fv_nom_remove_swap;try default_simp.
                                                      case (x1 == x0);intros.
                                                      ---------- rewrite e in *. rewrite swap_symmetric.
                                                                 apply fv_nom_swap. rewrite swap_involutive in H4.
                                                                 apply aeq_fv_nom in H4. rewrite <- H4 in H7.
                                                                 apply fv_nom_swap_2 in H7. assumption.
                                                      ---------- apply fv_nom_remove_swap;default_simp.
                           ------- default_simp.
                    ------ apply (fv_nom_m_subst_notin _ t2) in H3. unfold m_subst in H3. rewrite H3.
                           case (x1 == y);intros.
                           ------- rewrite e. default_simp.
                           ------- apply diff_remove;try assumption. case (x1 == z);intros.
                                   -------- rewrite e in *. apply fv_nom_swap. default_simp.
                                   -------- apply fv_nom_remove_swap;try assumption.
                                            apply (aeq_swap _ _ z x0) in H8. pose proof H8.
                                            apply (aeq_swap _ _ x y) in H8.
                                            repeat rewrite swap_involutive in H8. apply aeq_fv_nom in H8.
                                            rewrite <- H8. pose proof n. repeat apply notin_union_2 in H6.
                                            apply notin_singleton_1 in H6. apply fv_nom_remove_swap;try default_simp.
                                            case (x1 == x0);intros.
                                            --------- rewrite e in *. rewrite swap_symmetric.
                                                      apply fv_nom_swap. rewrite swap_involutive in H4.
                                                      apply aeq_fv_nom in H4. rewrite <- H4 in H7.
                                                      apply fv_nom_swap_2 in H7. assumption.
                                            --------- apply fv_nom_remove_swap;default_simp.
              ----- apply (aeq_trans _ (subst_rec (size (swap x2 x1 (swap z x2 t1'))) (swap x2 x1 (swap z x2 t1'))
                    t2 (swap_var x2 x1 y))).
                    ------ unfold swap_var. pose proof n. pose proof n0. repeat apply notin_union_2 in H3.
                           repeat apply notin_union_2 in H4. apply notin_singleton_1 in H3. apply notin_singleton_1 in H4.
                           default_simp.
                           ------- case (x == x2);intros.
                                   -------- rewrite e in *. apply aeq_m_subst_2. rewrite (swap_symmetric _ z x2).
                                            rewrite (swap_symmetric _ x2 x1). rewrite shuffle_swap;try default_simp.
                                            case (x1 == x0);intros.
                                            --------- rewrite e in *. rewrite swap_id.
                                                      rewrite swap_symmetric. rewrite (swap_symmetric _ x0 x2).
                                                      assumption.
                                            --------- apply (aeq_swap _ _ x0 x1). rewrite swap_involutive.
                                                      rewrite shuffle_swap;try default_simp. rewrite swap_symmetric.
                                                      rewrite shuffle_swap;try default_simp.
                                                      apply (aeq_trans _ (swap z x1 t0)).
                                                      ---------- apply aeq_swap0.
                                                                 * apply (aeq_swap _ _ z x0) in H8. rewrite swap_involutive in H8.
                                                                   apply aeq_fv_nom in H8. rewrite <- H8 in H7.
                                                                   apply fv_nom_swap_2 in H7. assumption.
                                                                 * default_simp.
                                                      ---------- apply aeq_swap. rewrite (swap_symmetric _ x1 x2). assumption.
                                   -------- apply H.
                                            --------- rewrite swap_size_eq. reflexivity.
                                            --------- assumption.
                                            --------- apply fv_nom_remove_swap;try assumption.
                                                      apply fv_nom_remove_swap;try default_simp.
                                            --------- case (x0 == x1);intros.
                                                      ---------- rewrite e in *. rewrite swap_id.
                                                                 rewrite (swap_symmetric _ x2 x1). rewrite (swap_symmetric _ z x2).
                                                                 case (x2 == z);intros.
                                                                 ----------- rewrite e0 in *. rewrite swap_id.
                                                                             rewrite (swap_symmetric _ x1 z).
                                                                             rewrite shuffle_swap;try assumption.
                                                                             rewrite swap_symmetric. rewrite shuffle_swap;
                                                                             try assumption. rewrite swap_symmetric.
                                                                             rewrite (swap_symmetric _ x1 x). assumption.
                                                                 ----------- rewrite (swap_symmetric _ x1 x2).
                                                                             rewrite shuffle_swap;default_simp.
                                                                             rewrite swap_symmetric.
                                                                             rewrite shuffle_swap;try assumption.
                                                                             rewrite (swap_symmetric_2 x1 x);default_simp.
                                                                             rewrite shuffle_swap;default_simp.
                                                                             rewrite swap_symmetric.
                                                                             rewrite shuffle_swap;default_simp.
                                                                             rewrite (swap_symmetric _ x1 x).
                                                                             apply (aeq_trans _ (swap z x2 t0)).
                                                                             ------------ apply aeq_swap0.
                                                                                          * apply (aeq_swap _ _ z x1) in H8.
                                                                                            rewrite swap_involutive in H8.
                                                                                            apply aeq_fv_nom in H8.
                                                                                            rewrite <- H8 in H7.
                                                                                            apply fv_nom_swap_2 in H7. assumption.
                                                                                          * apply notin_union_2 in n0.
                                                                                            apply notin_union_1 in n0.
                                                                                            apply (diff_remove_2 _ _ _ n8) in n0.
                                                                                            apply (aeq_swap _ _ z x1) in H8.
                                                                                            apply (aeq_swap _ _ x x1) in H8.
                                                                                            repeat rewrite swap_involutive in H8.
                                                                                            apply aeq_fv_nom in H8.
                                                                                            rewrite <- H8 in n0.
                                                                                            apply fv_nom_swap_remove in n0;default_simp.
                                                                                            apply fv_nom_swap_remove in n0;default_simp.
                                                                             ------------ apply aeq_swap. assumption.
                                                      ---------- rewrite shuffle_swap;default_simp.
                                                                 rewrite (swap_symmetric _ x x1). rewrite shuffle_swap;default_simp.
                                                                 rewrite (swap_symmetric _ x1 x). rewrite (swap_symmetric_2 x x1);default_simp.
                                                                 apply (aeq_swap _ _ x0 x1). rewrite swap_involutive.
                                                                 case (x0 == x2);intros.
                                                                 ----------- rewrite e in *. rewrite swap_symmetric. rewrite swap_involutive.
                                                                             assumption.
                                                                 ----------- rewrite shuffle_swap;default_simp.
                                                                             rewrite swap_symmetric. rewrite shuffle_swap;default_simp.
                                                                             rewrite (swap_symmetric _ x2 x0).
                                                                             rewrite (swap_symmetric _ z x2).
                                                                             case (x2 == z);intros.
                                                                             ------------ rewrite e in *.
                                                                                          rewrite swap_id.
                                                                                          apply (aeq_trans _ (swap z x1 t0)).
                                                                                          * apply aeq_swap0.
                                                                                            ** apply (aeq_swap _ _ z x0) in H8.
                                                                                               rewrite swap_involutive in H8.
                                                                                               apply aeq_fv_nom in H8.
                                                                                               rewrite <- H8 in H7.
                                                                                               apply fv_nom_swap_2 in H7.
                                                                                               assumption.
                                                                                            ** default_simp.
                                                                                          * apply aeq_swap. rewrite swap_symmetric.
                                                                                            assumption.
                                                                             ------------ rewrite shuffle_swap;default_simp.
                                                                                          rewrite (swap_symmetric _ x0 z).
                                                                                          rewrite shuffle_swap;default_simp.
                                                                                          apply notin_union_2 in n0.
                                                                                          apply notin_union_1 in n0.
                                                                                          apply (diff_remove_2 _ _ _ n10) in n0.
                                                                                          pose proof H8.
                                                                                          apply (aeq_swap _ _ z x0) in H8.
                                                                                          rewrite swap_involutive in H8.
                                                                                          pose proof H8.
                                                                                          apply (aeq_swap _ _ x x1) in H8.
                                                                                          rewrite swap_involutive in H8.
                                                                                          apply aeq_fv_nom in H8.
                                                                                          rewrite <- H8 in n0.
                                                                                          repeat (apply fv_nom_swap_remove in n0;default_simp).
                                                                                          apply (aeq_trans _ (swap x2 x1 t0)). 
                                                                                          * apply aeq_swap0;default_simp.
                                                                                          * apply aeq_swap.
                                                                                            apply (aeq_trans _ (swap z x2 t0)).
                                                                                            ** apply aeq_fv_nom in H9.
                                                                                               rewrite <- H9 in H7.
                                                                                               apply fv_nom_swap_2 in H7.
                                                                                               apply aeq_swap0;default_simp.
                                                                                            ** apply aeq_swap. assumption.
                           ------- apply H.
                                   -------- rewrite swap_size_eq. reflexivity.
                                   -------- assumption. 
                                   -------- case (x == x2);intros.
                                            --------- rewrite e in *.
                                                      apply fv_nom_swap. case (x1 == z);intros.
                                                      ---------- rewrite e0 in *. apply fv_nom_swap. default_simp.
                                                      ---------- apply fv_nom_remove_swap;default_simp.
                                                                 apply (aeq_swap _ _ z x0) in H8.
                                                                 pose proof H8.
                                                                 apply (aeq_swap _ _ x2 y) in H8.
                                                                 repeat rewrite swap_involutive in H8.
                                                                 apply aeq_fv_nom in H8. rewrite <- H8.
                                                                 apply fv_nom_remove_swap;default_simp.
                                                                 case (x1 == x0);intros.
                                                                 ----------- rewrite e in *. rewrite swap_symmetric.
                                                                             apply fv_nom_swap.
                                                                             rewrite swap_involutive in H6.
                                                                             apply aeq_fv_nom in H6.
                                                                             rewrite <- H6 in H7.
                                                                             apply fv_nom_swap_2 in H7.
                                                                             assumption.
                                                                 ----------- apply fv_nom_remove_swap;default_simp.
                                            --------- repeat apply fv_nom_remove_swap;default_simp.
                                   -------- case (x == x2);intros.
                                            --------- rewrite e in *. rewrite (swap_symmetric _ x2 y).
                                                      rewrite shuffle_swap;default_simp.
                                                      rewrite (swap_symmetric _ z x2).
                                                      rewrite shuffle_swap;default_simp.
                                                      rewrite (swap_symmetric _ y x1).
                                                      case (x1 == z);intros.
                                                      ---------- rewrite e in *. rewrite (swap_symmetric _ z y).
                                                                 rewrite swap_involutive. rewrite swap_symmetric.
                                                                 rewrite (swap_symmetric _ y x2).
                                                                 apply (aeq_swap _ _ z x0). rewrite swap_involutive.
                                                                 assumption.
                                                      ---------- rewrite shuffle_swap;default_simp.
                                                                 apply (aeq_swap _ _ x0 x1). rewrite swap_involutive.
                                                                 rewrite shuffle_swap;default_simp.
                                                                 rewrite swap_symmetric.
                                                                 case (x0 == x1);intros.
                                                                 ----------- rewrite e in *. rewrite swap_id.
                                                                             rewrite shuffle_swap;default_simp.
                                                                             apply (aeq_trans _ (swap z y t0)).
                                                                             ------------ apply aeq_swap0.
                                                                                          * apply (aeq_swap _ _ z x1) in H8.
                                                                                            rewrite swap_involutive in H8.
                                                                                            apply aeq_fv_nom in H8.
                                                                                            rewrite <- H8 in H7.
                                                                                            apply fv_nom_swap_2 in H7.
                                                                                            assumption.
                                                                                          * apply (aeq_swap _ _ z x1) in H8.
                                                                                            rewrite swap_involutive in H8.
                                                                                            apply (aeq_swap _ _ x2 y) in H8.
                                                                                            rewrite swap_involutive in H8.
                                                                                            apply aeq_fv_nom in H8.
                                                                                            rewrite <- H8 in H1.
                                                                                            apply diff_remove_2 in H1; default_simp.
                                                                                            rewrite swap_symmetric in H1.
                                                                                            apply fv_nom_swap_2 in H1.
                                                                                            apply fv_nom_swap_remove in H1;default_simp.
                                                                             ------------ apply aeq_swap. rewrite (swap_symmetric _ y x2).
                                                                                          assumption.
                                                                 ----------- rewrite shuffle_swap;default_simp.
                                                                             case (x0 == y);intros.
                                                                             * rewrite e in *.
                                                                               rewrite (swap_symmetric _ x1 y).
                                                                               rewrite shuffle_swap;default_simp.
                                                                               rewrite swap_involutive.
                                                                               rewrite (swap_symmetric _ y x2).
                                                                               assumption.
                                                                             * rewrite (swap_symmetric_2 z x0);default_simp.
                                                                               apply (aeq_trans _ (swap z x1 t0)).
                                                                               ** apply aeq_swap0.
                                                                                  *** apply (aeq_swap _ _ z x0) in H8.
                                                                                      rewrite swap_involutive in H8.
                                                                                      apply aeq_fv_nom in H8.
                                                                                      rewrite <- H8 in H7.
                                                                                      apply fv_nom_swap_2 in H7.
                                                                                      assumption.
                                                                                  *** default_simp.
                                                                               ** apply aeq_swap. apply (aeq_trans _ (swap x1 y t0)).
                                                                                  *** apply aeq_swap0.
                                                                                      **** default_simp.
                                                                                      **** apply (aeq_swap _ _ z x0) in H8.
                                                                                           rewrite swap_involutive in H8.
                                                                                           apply (aeq_swap _ _ x2 y) in H8.
                                                                                           rewrite swap_involutive in H8.
                                                                                           apply aeq_fv_nom in H8.
                                                                                           rewrite <- H8 in H1.
                                                                                           apply diff_remove_2 in H1; default_simp.
                                                                                           rewrite swap_symmetric in H1.
                                                                                           apply fv_nom_swap_2 in H1.
                                                                                           apply fv_nom_swap_remove in H1;default_simp.
                                                                                  *** apply aeq_swap. rewrite (swap_symmetric _ y x2).
                                                                                      assumption.
                                            --------- repeat rewrite (swap_symmetric_2 x y);default_simp. apply (aeq_swap _ _ x0 x1).
                                                      rewrite swap_involutive. rewrite (swap_symmetric _ x2 x1).
                                                      case (x0 == x2);intros.
                                                      ---------- rewrite e in *. rewrite swap_symmetric. rewrite swap_involutive.
                                                                 assumption.
                                                      ---------- rewrite shuffle_swap;default_simp. rewrite swap_symmetric.
                                                                 case (x1 == z);intros.
                                                                 * rewrite e in *. rewrite shuffle_swap;default_simp.
                                                                   rewrite swap_symmetric. rewrite shuffle_swap;default_simp.
                                                                   rewrite swap_involutive. assumption.
                                                                 * rewrite (swap_symmetric_2 x0 x1);default_simp.
                                                                   rewrite swap_symmetric. rewrite (swap_symmetric _ z x2).
                                                                   case (x2 == z);intros.
                                                                   ** rewrite e in *. rewrite swap_id.
                                                                      rewrite swap_symmetric.
                                                                      case (x0 == x1);intros.
                                                                      *** rewrite e0 in *. rewrite swap_id. assumption.
                                                                      *** rewrite shuffle_swap;default_simp.
                                                                          apply (aeq_trans _ (swap z x1 t0)).
                                                                          **** apply aeq_swap0.
                                                                               ***** apply (aeq_swap _ _ z x0) in H8.
                                                                                     rewrite swap_involutive in H8.
                                                                                     apply aeq_fv_nom in H8.
                                                                                     rewrite <- H8 in H7.
                                                                                     apply fv_nom_swap_2 in H7.
                                                                                     assumption.
                                                                               ***** default_simp.
                                                                          **** apply aeq_swap. assumption.
                                                                   ** rewrite shuffle_swap;default_simp.
                                                                      rewrite swap_symmetric. rewrite shuffle_swap;default_simp.
                                                                      case (x0 == x1);intros.
                                                                      *** rewrite e in *. rewrite swap_id.
                                                                          apply (aeq_trans _ (swap z x2 t0)).
                                                                          **** apply aeq_swap0.
                                                                               ***** apply (aeq_swap _ _ z x1) in H8.
                                                                                     rewrite swap_involutive in H8.
                                                                                     apply aeq_fv_nom in H8.
                                                                                     rewrite <- H8 in H7.
                                                                                     apply fv_nom_swap_2 in H7.
                                                                                     assumption.
                                                                               ***** apply (aeq_swap _ _ z x1) in H8.
                                                                                     rewrite swap_involutive in H8.
                                                                                     apply (aeq_swap _ _ x y) in H8.
                                                                                     rewrite swap_involutive in H8.
                                                                                     apply aeq_fv_nom in H8.
                                                                                     apply notin_union_2 in n0.
                                                                                     apply notin_union_1 in n0.
                                                                                     apply (diff_remove_2 _ _ _ n11) in n0.
                                                                                     rewrite <- H8 in n0.
                                                                                     repeat (apply fv_nom_swap_remove in n0;default_simp).
                                                                          **** apply aeq_swap. assumption.
                                                                      *** rewrite shuffle_swap;default_simp.
                                                                          apply (aeq_trans _ (swap z x2 t0)).
                                                                          **** apply aeq_swap0.
                                                                              ***** apply (aeq_swap _ _ z x0) in H8.
                                                                                    rewrite swap_involutive in H8.
                                                                                    apply aeq_fv_nom in H8.
                                                                                    rewrite <- H8 in H7.
                                                                                    apply fv_nom_swap_2 in H7.
                                                                                    assumption.
                                                                              ***** apply (aeq_swap _ _ z x0) in H8.
                                                                                    rewrite swap_involutive in H8.
                                                                                    apply (aeq_swap _ _ x y) in H8.
                                                                                    rewrite swap_involutive in H8.
                                                                                    apply aeq_fv_nom in H8.
                                                                                    apply notin_union_2 in n0.
                                                                                    apply notin_union_1 in n0.
                                                                                    apply (diff_remove_2 _ _ _ n11) in n0.
                                                                                    rewrite <- H8 in n0.
                                                                                    repeat (apply fv_nom_swap_remove in n0;default_simp).
                                                                          **** apply aeq_swap. apply (aeq_trans _ (swap z x1 t0)).
                                                                               ***** apply aeq_swap0.
                                                                                     ****** apply (aeq_swap _ _ z x0) in H8.
                                                                                            rewrite swap_involutive in H8.
                                                                                            apply aeq_fv_nom in H8.
                                                                                            rewrite <- H8 in H7.
                                                                                            apply fv_nom_swap_2 in H7.
                                                                                            assumption.
                                                                                     ****** default_simp.
                                                                               ***** apply aeq_swap. assumption.
                    ------ apply (aeq_trans _ (subst_rec (size (swap x2 x1 (swap z x2 t1'))) (swap x2 x1 (swap z x2 t1'))
                           (swap x2 x1 t2) (swap_var x2 x1 y))).
                           ------- apply aeq_m_subst_1. apply aeq_swap0;default_simp.
                           ------- pose proof aeq_swap_m_subst. unfold m_subst in H3. apply aeq_sym.
                                   apply H3.
  - simpl in H1. inversion H1. unfold m_subst in *. simpl. assert (H': size t0 <= size t0 + size t3);try lia.
    assert (H'': size t3 <= size t0 + size t3);try lia. assert (H''': size t1'1 <= size t1'1 + size t1'2);try lia.
    assert (H'''': size t1'2 <= size t1'1 + size t1'2);try lia.
    rewrite (subst_size _ _ _ _ H'). rewrite (subst_size _ _ _ _ H''). rewrite (subst_size _ _ _ _ H''').
    rewrite (subst_size _ _ _ _ H''''). simpl in H0. apply aeq_app.
    -- apply IHt1'1;default_simp.
    -- apply IHt1'2;default_simp.
  - unfold m_subst in *. inversion H2.
    -- unfold swap_var in *. simpl. assert (H': size t3 <= size t0 + size t3); try lia.
       assert (H'': size t1'2 <= size t1'1 + size t1'2); try lia.
       rewrite (subst_size _ _ _ _ H'). rewrite (subst_size _ _ _ _ H''). default_simp.
       --- apply aeq_sub_diff.
           ---- apply IHt1'1;default_simp.
           ---- assumption.
           ---- default_simp.
           ---- rewrite swap_symmetric. assumption.
       --- assert (H''': size (swap y x0 t0) <= size t0 + size t3); try (rewrite swap_size_eq;lia).
           assert (H'''': size (swap x x1 t1'1) <= size t1'1 + size t1'2); try (rewrite swap_size_eq;lia).
           rewrite (subst_size _ _ _ _ H'''). rewrite (subst_size _ _ _ _ H''''). case(x0 == x1);intros.
           ---- rewrite e in *. apply aeq_sub_same.
                ----- apply H.
                      ------ reflexivity.
                      ------ assumption.
                      ------ apply fv_nom_swap. default_simp.
                      ------ rewrite (swap_symmetric _ x y). rewrite shuffle_swap;default_simp.
                             apply aeq_swap. rewrite swap_symmetric. assumption.
                ----- apply IHt1'1;default_simp.
           ---- apply aeq_sub_diff.
                ----- apply IHt1'1;default_simp.
                ----- assumption.
                ----- pose proof in_or_notin. specialize (H3 y (fv_nom (swap x x1 t1'1))).
                      destruct H3.
                      ------ apply (fv_nom_m_subst_in _ t2) in H3. unfold m_subst in H3.
                             rewrite H3. simpl. apply notin_union_3.
                             ------- case (x0 == y);intros.
                                     -------- rewrite e. default_simp.
                                     -------- apply diff_remove; try assumption. apply fv_nom_remove_swap;default_simp.
                                              apply (aeq_swap _ _ x y) in H6. rewrite swap_involutive in H6.
                                              apply aeq_fv_nom in H6. rewrite <- H6.
                                              apply fv_nom_remove_swap;default_simp.
                             ------- default_simp.
                      ------ apply (fv_nom_m_subst_notin _ t2) in H3. unfold m_subst in H3. rewrite H3.
                             case (x0 == y);intros.
                             ------- rewrite e. default_simp.
                             ------- apply diff_remove; try assumption. apply fv_nom_remove_swap;default_simp.
                                     apply (aeq_swap _ _ x y) in H6. rewrite swap_involutive in H6.
                                     apply aeq_fv_nom in H6. rewrite <- H6.
                                     apply fv_nom_remove_swap;default_simp.
                ----- apply (aeq_trans _ (subst_rec (size (swap x1 x0 (swap x x1 t1'1))) (swap x1 x0 (swap x x1 t1'1))
                      t2 (swap_var x1 x0 y))).
                      ------ unfold swap_var. pose proof n0. repeat apply notin_union_2 in H3.
                             apply notin_singleton_1 in H3. default_simp.
                             ------- rewrite swap_id. case (x == x1);intros.
                                     -------- rewrite e in *. apply aeq_m_subst_2. rewrite swap_id.
                                              assumption.
                                     -------- apply H.
                                              --------- rewrite swap_size_eq. reflexivity.
                                              --------- assumption.
                                              --------- apply fv_nom_remove_swap;default_simp.
                                                        apply fv_nom_swap;default_simp.
                                              --------- rewrite shuffle_swap;default_simp.
                                                        rewrite swap_involutive. assumption.
                             ------- apply H.
                                     -------- rewrite swap_size_eq. reflexivity.
                                     -------- assumption.
                                     --------  case (x == x1);intros.
                                               --------- rewrite e in *. apply fv_nom_swap. rewrite swap_id.
                                                         apply (aeq_swap _ _ x1 y) in H6.
                                                         rewrite swap_involutive in H6. apply aeq_fv_nom in H6.
                                                         rewrite <- H6. apply fv_nom_remove_swap;default_simp.
                                               --------- apply fv_nom_remove_swap;default_simp.
                                                         apply fv_nom_swap. default_simp.
                                     -------- apply (aeq_swap _ _ y x0). rewrite swap_involutive.
                                              rewrite swap_symmetric. rewrite (swap_symmetric _ x y).
                                              rewrite shuffle_swap;default_simp.
                                              rewrite swap_symmetric. rewrite shuffle_swap;default_simp.
                                              rewrite (swap_symmetric _ x1 x0).
                                              case (x == x1);intros.
                                              --------- rewrite e in *. rewrite swap_id.
                                                        rewrite (swap_symmetric _ x1 x0).
                                                        rewrite swap_involutive. assumption.
                                              --------- rewrite shuffle_swap;default_simp.
                                                        rewrite (swap_symmetric _ x x1).
                                                        rewrite shuffle_swap;default_simp.
                                                        rewrite (swap_symmetric _ x x1).
                                                        rewrite swap_involutive. apply (aeq_trans _ (swap x y t1'1)).
                                                        * assumption.
                                                        * apply aeq_swap. apply aeq_swap0.
                                                          ** default_simp.
                                                          ** pose proof n.
                                                             apply notin_union_2 in n. repeat apply notin_union_1 in n.
                                                             apply diff_remove_2 in n;try default_simp.
                                                             apply aeq_fv_nom in H6. rewrite H6 in n.
                                                             apply fv_nom_swap_remove in n;default_simp.
                      ------ apply (aeq_trans _ (subst_rec (size (swap x1 x0 (swap x x1 t1'1))) (swap x1 x0 (swap x x1 t1'1))
                             (swap x1 x0 t2) (swap_var x1 x0 y))).
                             ------- apply aeq_m_subst_1. apply aeq_swap0;default_simp.
                             ------- apply aeq_sym. apply aeq_swap_m_subst.
       --- assert (H''': size (swap z x0 t0) <= size t0 + size t3); try (rewrite swap_size_eq;lia).
           assert (H'''': size (swap z x1 t1'1) <= size t1'1 + size t1'2); try (rewrite swap_size_eq;lia).
           rewrite (subst_size _ _ _ _ H'''). rewrite (subst_size _ _ _ _ H''''). case(x0 == x1);intros.
           ---- rewrite e in *. apply aeq_sub_same.
                ----- apply H.
                      ------ reflexivity.
                      ------ assumption.
                      ------ apply fv_nom_remove_swap;default_simp.
                      ------ rewrite (swap_symmetric_2);default_simp. apply aeq_swap.
                             assumption.
                ----- apply IHt1'1;default_simp.
           ---- apply aeq_sub_diff.
                ----- apply IHt1'1;default_simp.
                ----- assumption.
                ----- pose proof in_or_notin. specialize (H3 y (fv_nom (swap z x1 t1'1))).
                      destruct H3.
                      ------ apply (fv_nom_m_subst_in _ t2) in H3. unfold m_subst in H3.
                             rewrite H3. simpl. apply notin_union_3.
                             ------- case (x0 == y);intros;try default_simp.
                                     apply diff_remove;try assumption. case (x0 == z);intros.
                                     -------- rewrite e in *. apply fv_nom_swap. default_simp.
                                     -------- apply fv_nom_remove_swap;default_simp.
                                              apply (aeq_swap _ _ x y) in H6. rewrite swap_involutive in H6.
                                              apply aeq_fv_nom in H6. rewrite <- H6.
                                              apply fv_nom_remove_swap;default_simp.
                             ------- default_simp.
                      ------ apply (fv_nom_m_subst_notin _ t2) in H3. unfold m_subst in H3.
                             rewrite H3. case (x0 == y);intros;try default_simp.
                             apply diff_remove;try assumption. case (x0 == z);intros.
                             ------- rewrite e in *. apply fv_nom_swap. default_simp.
                             ------- apply fv_nom_remove_swap;default_simp.
                                     apply (aeq_swap _ _ x y) in H6. rewrite swap_involutive in H6.
                                     apply aeq_fv_nom in H6. rewrite <- H6.
                                     apply fv_nom_remove_swap;default_simp.
                ----- apply (aeq_trans _ (subst_rec (size (swap x1 x0 (swap z x1 t1'1)))
                     (swap x1 x0 (swap z x1 t1'1)) t2 (swap_var x1 x0 y))).
                     ------ unfold swap_var in *. pose proof n0. repeat apply notin_union_2 in H3.
                            apply notin_singleton_1 in H3. default_simp.
                            ------- case (x == x1);intros.
                                    -------- rewrite e in *. apply aeq_m_subst_2. rewrite (swap_symmetric _ x1 x0).
                                             rewrite (swap_symmetric _ z x1). rewrite shuffle_swap;default_simp.
                                             rewrite swap_symmetric. apply aeq_swap. rewrite swap_symmetric.
                                             assumption.
                                    -------- apply H.
                                             --------- rewrite swap_size_eq. reflexivity.
                                             --------- assumption.
                                             --------- repeat apply fv_nom_remove_swap;default_simp.
                                             --------- rewrite (swap_symmetric _ x1 x0).
                                                       rewrite (swap_symmetric _ z x1).
                                                       case (x1 == z);intros.
                                                       ---------- rewrite e in *. rewrite swap_id.
                                                                  rewrite (swap_symmetric _ x0 z).
                                                                  rewrite shuffle_swap;default_simp.
                                                                  rewrite (swap_symmetric _ x x0). 
                                                                  rewrite shuffle_swap;default_simp.
                                                                  rewrite (swap_symmetric _ x0 z).
                                                                  apply aeq_swap. rewrite swap_symmetric. assumption.  
                                                       ---------- rewrite shuffle_swap;default_simp.
                                                                  rewrite (swap_symmetric _ x0 z).
                                                                  rewrite swap_symmetric_2;default_simp.
                                                                  apply aeq_swap. rewrite (swap_symmetric _ x0 x1).
                                                                  rewrite shuffle_swap;default_simp.
                                                                  apply (aeq_trans _ (swap x x0 t1'1)).
                                                                  * assumption.
                                                                  * apply aeq_swap. apply aeq_swap0;default_simp.
                            ------- apply H.
                                    -------- rewrite swap_size_eq. reflexivity.
                                    -------- assumption.
                                    -------- case (x == x1);intros.
                                             --------- rewrite e in *. apply fv_nom_swap. case (z == x0);intros.
                                                       ---------- rewrite e0 in *. apply fv_nom_swap. default_simp.
                                                       ---------- apply fv_nom_remove_swap;default_simp.
                                                                  apply (aeq_swap _ _ x1 y) in H6.
                                                                  rewrite swap_involutive in H6.
                                                                  apply aeq_fv_nom in H6. rewrite <- H6.
                                                                  apply fv_nom_remove_swap;default_simp.
                                             --------- repeat apply fv_nom_remove_swap;default_simp.
                                    -------- apply (aeq_swap _ _ z x0). rewrite swap_involutive.
                                             rewrite swap_symmetric_2;default_simp.
                                             rewrite (swap_symmetric _ x1 x0). case (z == x1);intros.
                                             --------- rewrite e in *. rewrite swap_id.
                                                       rewrite (swap_symmetric _ x1 x0).
                                                       rewrite swap_involutive. assumption.
                                             --------- rewrite shuffle_swap;default_simp.
                                                       rewrite (swap_symmetric _ z x1).
                                                       case (z == x0);intros.
                                                       ---------- rewrite e in *.
                                                                  rewrite swap_id.
                                                                  rewrite (swap_symmetric _ x1 x0).
                                                                  rewrite swap_involutive. assumption.
                                                       ---------- rewrite shuffle_swap;default_simp.
                                                                  rewrite (swap_symmetric _ x1 z). rewrite swap_involutive.
                                                                  apply (aeq_trans _ (swap x y t1'1)).
                                                                  * assumption.
                                                                  * apply aeq_swap. apply aeq_swap0.
                                                                    ** default_simp.
                                                                    ** apply (aeq_swap _ _ x y) in H6.
                                                                       rewrite swap_involutive in H6.
                                                                       apply aeq_fv_nom in H6. rewrite <- H6.
                                                                       apply fv_nom_remove_swap;default_simp.
                     ------ apply (aeq_trans _ (subst_rec (size (swap x1 x0 (swap z x1 t1'1))) (swap x1 x0 (swap z x1 t1'1))
                            (swap x1 x0 t2) (swap_var x1 x0 y))).
                            ------- apply aeq_m_subst_1. apply aeq_swap0;default_simp.
                            ------- apply aeq_sym. apply aeq_swap_m_subst.
    -- simpl. unfold swap_var in *. assert (H': size t3 <= size t0 + size t3); try lia.
       assert (H'': size t1'2 <= size t1'1 + size t1'2); try lia.
       rewrite (subst_size _ _ _ _ H'). rewrite (subst_size _ _ _ _ H''). default_simp.
       --- assert (H''': size (swap x0 x2 t1'1) <= size t1'1 + size t1'2); try (rewrite swap_size_eq;lia).
           rewrite (subst_size _ _ _ _ H'''). case (x0 == x2);intros.
           ---- rewrite e in *. apply aeq_sub_same.
                ----- rewrite swap_id. apply (aeq_trans _ t1'1).
                      ------ rewrite swap_symmetric in H10. rewrite swap_involutive in H10.
                             assumption.
                      ------ apply aeq_sym. pose proof subst_fresh_eq. unfold m_subst in H3.
                             apply H3. rewrite swap_symmetric in H9. apply fv_nom_swap_2 in H9.
                             assumption.
                ----- apply IHt1'1;default_simp.
           ---- apply aeq_sub_diff.
                ----- apply IHt1'1;default_simp.
                ----- assumption.
                ----- pose proof in_or_notin.
                      specialize (H3 y (fv_nom (swap x0 x2 t1'1))). destruct H3.
                      ------ rewrite swap_symmetric in H9. apply fv_nom_swap_2 in H9.
                             apply (fv_nom_remove_swap _ _ x2 x0) in H9;default_simp.
                      ------ apply (fv_nom_m_subst_notin _ t2) in H3. unfold m_subst in H3.
                             rewrite H3. apply diff_remove;default_simp. apply fv_nom_swap. default_simp.
                ----- apply (aeq_trans _ (swap x2 x0 (swap x0 x2 t1'1))).
                      ------ rewrite swap_symmetric. rewrite swap_symmetric in H10.
                             rewrite swap_involutive. rewrite swap_involutive in H10. assumption.
                      ------ apply aeq_swap. apply aeq_sym. pose proof subst_fresh_eq. unfold m_subst in H3.
                             apply H3. rewrite swap_symmetric in H9. apply fv_nom_swap_2 in H9.
                             apply fv_nom_remove_swap;default_simp.
       --- assert (H''': size (swap z x2 t1'1) <= size t1'1 + size t1'2); try (rewrite swap_size_eq;lia).
           rewrite (subst_size _ _ _ _ H'''). case (x0 == x2);intros.
           ---- rewrite e in *. apply aeq_sub_same.
                ----- apply (aeq_trans _ (swap z x2 t1'1)).
                      ------ apply (aeq_trans _ (swap z x2 (swap x2 y t1'1))).
                             ------- assumption.
                             ------- apply aeq_swap. apply aeq_sym. apply aeq_swap0.
                                     -------- default_simp.
                                     -------- rewrite swap_symmetric in H9. apply fv_nom_swap_2 in H9.
                                              assumption.
                      ------ apply aeq_sym. pose proof subst_fresh_eq. unfold m_subst in H3.
                             apply H3. rewrite swap_symmetric in H9. apply fv_nom_swap_2 in H9.
                             apply fv_nom_remove_swap;default_simp.
                ----- apply IHt1'1;default_simp.
           ---- apply aeq_sub_diff.
                ----- apply IHt1'1;default_simp.
                ----- assumption.
                ----- pose proof in_or_notin.
                      specialize (H3 y (fv_nom (swap z x2 t1'1))). destruct H3.
                      ------ rewrite swap_symmetric in H9. apply fv_nom_swap_2 in H9.
                            apply (fv_nom_remove_swap _ _ x2 z) in H9;default_simp.
                      ------ apply (fv_nom_m_subst_notin _ t2) in H3. unfold m_subst in H3.
                            rewrite H3. apply diff_remove;default_simp. apply fv_nom_remove_swap;default_simp.
                ----- apply (aeq_trans _ (swap x2 x0 (swap z x2 t1'1))).
                      ------ case (x2 == z);intros.
                             ------- rewrite e in *. rewrite swap_id.
                                     apply (aeq_trans _ (swap z x0 (swap x0 y t1'1))).
                                     -------- assumption.
                                     -------- apply aeq_swap. apply aeq_sym.
                                              apply aeq_swap0.
                                              * default_simp.
                                              * rewrite swap_symmetric in H9. apply fv_nom_swap_2 in H9.
                                                assumption.
                             ------- rewrite swap_symmetric. rewrite (swap_symmetric _ z x2).
                                     rewrite shuffle_swap;default_simp. rewrite swap_symmetric.
                                     apply (aeq_trans _ (swap z x0 t1'1)).
                                     -------- apply (aeq_trans _ (swap z x0 (swap x0 y t1'1))).
                                              ---------- assumption.
                                              ---------- apply aeq_swap. apply aeq_sym. apply aeq_swap0.
                                                         * default_simp.
                                                         * rewrite swap_symmetric in H9. apply fv_nom_swap_2 in H9.
                                                           assumption.
                                     -------- apply aeq_swap. apply aeq_swap0;default_simp.
                      ------ apply aeq_swap. apply aeq_sym. pose proof subst_fresh_eq.
                             unfold m_subst in H3. apply H3. rewrite swap_symmetric in H9.
                             apply fv_nom_swap_2 in H9. apply fv_nom_remove_swap;default_simp.
       --- assert (H''': size (swap x0 x1 t0) <= size t0 + size t3); try (rewrite swap_size_eq;lia).
           rewrite (subst_size _ _ _ _ H'''). case (x1 == z);intros.
           ---- rewrite e0 in *. apply aeq_sub_same.
                ----- apply (aeq_trans _ (swap x0 z t0)).
                      ------ pose proof subst_fresh_eq. unfold m_subst in H3.
                             apply H3. apply (aeq_swap _ _ x x0) in H10. rewrite swap_involutive in H10.
                             apply aeq_fv_nom in H10. rewrite <- H10 in H9.
                             apply fv_nom_swap_2 in H9. apply fv_nom_remove_swap;default_simp.
                      ------ rewrite swap_symmetric in H10. case (x0 == z);intros.
                             ------- rewrite e1 in *. rewrite swap_id. rewrite swap_symmetric in H10.
                                     rewrite swap_involutive in H10. assumption.
                             ------- rewrite shuffle_swap in H10;default_simp.
                                     apply (aeq_swap _ _ x0 z) in H10.
                                     rewrite swap_involutive in H10. apply (aeq_trans _ (swap x0 x t1'1)).
                                     -------- assumption.
                                     -------- apply aeq_sym. apply aeq_swap0.
                                              * apply fv_nom_swap_remove in H9;default_simp.
                                              * default_simp.
                ----- apply IHt1'1;default_simp.
           ---- apply aeq_sub_diff.
                ----- apply IHt1'1;default_simp.
                ----- assumption.
                ----- case (x1 == x0);intros.
                      ------ rewrite e0 in *. apply fv_nom_swap_remove in H9;default_simp.
                      ------ apply (aeq_swap _ _ x x0) in H10. apply (aeq_swap _ _ x z) in H10.
                             repeat rewrite swap_involutive in H10. apply aeq_fv_nom in H10.
                             rewrite <- H10. repeat apply fv_nom_remove_swap;default_simp.
                ----- apply (aeq_trans _ (swap x0 x1 t0)). 
                      ------ pose proof subst_fresh_eq. unfold m_subst in H3. apply H3.
                             apply (aeq_swap _ _ x x0) in H10. rewrite swap_involutive in H10.
                             apply aeq_fv_nom in H10. rewrite <- H10 in H9.
                             apply fv_nom_swap_2 in H9. apply fv_nom_remove_swap;default_simp.
                      ------ apply (aeq_swap _ _ x0 x1). rewrite swap_involutive.
                             rewrite (swap_symmetric _ z x1). case (x0 == z);intros.
                             -------- rewrite e0 in *. rewrite swap_symmetric.
                                      rewrite swap_involutive in H10. rewrite swap_involutive.
                                      assumption.
                             -------- rewrite shuffle_swap;default_simp. rewrite swap_symmetric in H10.
                                      pose proof H10. rewrite shuffle_swap in H10;default_simp.
                                      apply (aeq_trans _ (swap x0 z t1'1)).
                                      * apply (aeq_trans _ (swap x0 z (swap x0 x t1'1))).
                                        ** assumption.
                                        ** apply aeq_swap. apply aeq_sym. apply aeq_swap0.
                                           *** apply fv_nom_swap_remove in H9;default_simp.
                                           *** default_simp.
                                      * apply aeq_swap. case (x0 == x1);intros.
                                        ** rewrite e0. rewrite swap_id. apply aeq_refl.
                                        ** apply aeq_swap0.
                                           *** apply fv_nom_swap_remove in H9;default_simp.
                                           *** apply notin_union_2 in n. pose proof n.
                                               repeat apply notin_union_1 in n.
                                               assert (H'''': x1 <> x0). default_simp.
                                               apply (diff_remove_2 _ _ _ H'''') in n. apply aeq_fv_nom in H10.
                                               rewrite H10 in n. apply fv_nom_swap_remove in n;try assumption.
                                               apply fv_nom_swap_remove in n;default_simp.
       --- assert (H''': size (swap x0 x1 t0) <= size t0 + size t3); try (rewrite swap_size_eq;lia).
           rewrite (subst_size _ _ _ _ H''').
           assert (H'''': size (swap x x2 t1'1) <= size t1'1 + size t1'2); try (rewrite swap_size_eq;lia).
           rewrite (subst_size _ _ _ _ H''''). case (x1 == x2);intros.
           ---- rewrite e in *. apply aeq_sub_same.
                ----- apply H.
                      ------ reflexivity.
                      ------ assumption.
                      ------ apply fv_nom_swap. default_simp.
                      ------ rewrite (swap_symmetric _ x y). rewrite shuffle_swap;default_simp.
                             rewrite (swap_symmetric _ y x). apply (aeq_swap _ _ x0 x2).
                             rewrite swap_involutive. rewrite (swap_symmetric _ y x2).
                             rewrite shuffle_swap;default_simp. rewrite swap_symmetric.
                             case (x0 == x2);intros.
                             ------- rewrite e in *. rewrite swap_id. assumption.
                             ------- rewrite shuffle_swap;default_simp.
                                     apply (aeq_trans _ (swap y x2 t0)).
                                     -------- apply aeq_swap0.
                                              * apply (aeq_swap _ _ y x0) in H10.
                                                rewrite swap_involutive in H10.
                                                apply aeq_fv_nom in H10.
                                                rewrite <- H10 in H9. apply fv_nom_swap_2 in H9.
                                                assumption.
                                              * default_simp.
                                     -------- apply aeq_swap. assumption.
                ----- apply IHt1'1;default_simp.
           ---- apply aeq_sub_diff.
                ----- apply IHt1'1;default_simp.
                ----- assumption.
                ----- pose proof in_or_notin. specialize (H3 y (fv_nom (swap x x2 t1'1))).
                      destruct H3.
                      ------ apply (fv_nom_m_subst_in _ t2) in H3. unfold m_subst in H3. rewrite H3.
                             simpl. apply notin_union_3.
                             -------- case (x1 == y);intros.
                                      --------- rewrite e.  default_simp.
                                      --------- apply diff_remove;default_simp.
                                                apply fv_nom_remove_swap;default_simp.
                                                case (x1 == x0);intros.
                                                ---------- rewrite e in *.
                                                           apply fv_nom_swap_remove in H9;default_simp.
                                                ---------- apply (aeq_swap _ _ y x0) in H10.
                                                           apply (aeq_swap _ _ x y) in H10.
                                                           repeat rewrite swap_involutive in H10.
                                                           apply aeq_fv_nom in H10.
                                                           rewrite <- H10.
                                                           apply fv_nom_remove_swap;default_simp.
                                                           apply fv_nom_remove_swap;default_simp.
                             -------- default_simp.
                      ------ apply (fv_nom_m_subst_notin _ t2) in H3. unfold m_subst in H3.
                             rewrite H3. case (x1 == y);intros.
                             -------- rewrite e.  default_simp.
                             -------- apply diff_remove;default_simp.
                                      apply fv_nom_remove_swap;default_simp.
                                      case (x1 == x0);intros.
                                      --------- rewrite e in *.
                                                apply fv_nom_swap_remove in H9;default_simp.
                                      --------- apply (aeq_swap _ _ y x0) in H10.
                                                apply (aeq_swap _ _ x y) in H10.
                                                repeat rewrite swap_involutive in H10.
                                                apply aeq_fv_nom in H10.
                                                rewrite <- H10.
                                                apply fv_nom_remove_swap;default_simp.
                                                apply fv_nom_remove_swap;default_simp.
                ----- apply (aeq_trans _ (subst_rec (size (swap x2 x1 (swap x x2 t1'1))) (swap x2 x1 (swap x x2 t1'1))
                      t2 (swap_var x2 x1 y))).
                      ------ unfold swap_var in *. pose proof n0. repeat apply notin_union_2 in H3.
                             apply notin_singleton_1 in H3. default_simp.
                             ------- case (x == x2);intros.
                                     -------- rewrite e0 in *. apply aeq_m_subst_2. rewrite swap_id.
                                              rewrite swap_symmetric. apply (aeq_swap _ _ x1 x0).
                                              rewrite swap_involutive. assumption.
                                     -------- apply H.
                                              --------- rewrite swap_size_eq. reflexivity.
                                              --------- assumption.
                                              --------- apply fv_nom_remove_swap;default_simp.
                                                        apply fv_nom_swap. default_simp.
                                              --------- rewrite shuffle_swap;default_simp. rewrite swap_involutive.
                                                        rewrite swap_symmetric. apply (aeq_swap _ _ x1 x0).
                                                        rewrite swap_involutive. assumption.
                             ------- apply H.
                                     -------- rewrite swap_size_eq. reflexivity. 
                                     -------- assumption.
                                     -------- case (x == x2);intros.
                                              --------- rewrite e0 in *. apply fv_nom_swap. rewrite swap_id.
                                                        apply (aeq_swap _ _ y x0) in H10.
                                                        pose proof H10.
                                                        apply (aeq_swap _ _ x2 y) in H10.
                                                        repeat rewrite swap_involutive in H10.
                                                        apply aeq_fv_nom in H10.
                                                        rewrite <- H10.
                                                        apply fv_nom_remove_swap;default_simp.
                                                        case (x1 == x0);intros.
                                                        ---------- rewrite e0 in *. rewrite swap_symmetric.
                                                                   apply fv_nom_swap. rewrite swap_involutive in H4.
                                                                   apply aeq_fv_nom in H4.
                                                                   rewrite <- H4 in H9.
                                                                   apply fv_nom_swap_2 in H9.
                                                                   assumption. 
                                                        ---------- apply fv_nom_remove_swap;default_simp.
                                              --------- apply fv_nom_remove_swap;default_simp. apply fv_nom_swap.
                                                        default_simp.
                                     -------- case (x == x2);intros.
                                              --------- rewrite e0 in *. rewrite swap_id.
                                                        rewrite (swap_symmetric _ x2 y).
                                                        rewrite shuffle_swap;default_simp.
                                                        rewrite (swap_symmetric _ y x2).
                                                        case (x1 == x0);intros;try(rewrite e0;rewrite swap_id;assumption).
                                                        apply (aeq_swap _ _ x0 x1). rewrite swap_involutive.
                                                        rewrite (swap_symmetric _ y x1). rewrite shuffle_swap;default_simp.
                                                        rewrite swap_symmetric. rewrite shuffle_swap;default_simp.
                                                        apply (aeq_trans _ (swap y x1 t0)).
                                                        ---------- apply aeq_swap0.
                                                                   * apply (aeq_swap _ _ y x0) in H10.
                                                                     rewrite swap_involutive in H10.
                                                                     apply aeq_fv_nom in H10.
                                                                     rewrite <- H10 in H9.
                                                                     apply fv_nom_swap_2 in H9.
                                                                     assumption.
                                                                   * default_simp.
                                                        ---------- apply aeq_swap. assumption.
                                              --------- rewrite (swap_symmetric_2 x y);default_simp.
                                                        rewrite (swap_symmetric _ x y).
                                                        rewrite shuffle_swap;default_simp.
                                                        rewrite (swap_symmetric _ y x).
                                                        rewrite (swap_symmetric _ x2 x1).
                                                        apply (aeq_swap _ _ x0 x1). rewrite swap_involutive.
                                                        case (x0 == x2);intros.
                                                        ---------- rewrite e0 in *. rewrite swap_symmetric.
                                                                   rewrite swap_involutive. assumption.
                                                        ---------- rewrite shuffle_swap;default_simp.
                                                                   rewrite swap_symmetric.
                                                                   case (x0 == x1);intros.
                                                                   * rewrite e0 in *.
                                                                     rewrite swap_id.
                                                                     rewrite swap_symmetric.
                                                                     rewrite (swap_symmetric _ y x2).
                                                                     rewrite shuffle_swap;default_simp.
                                                                     rewrite swap_symmetric.
                                                                     rewrite shuffle_swap;default_simp.
                                                                     apply (aeq_trans _ (swap y x2 t0)).
                                                                     ** apply aeq_swap0.
                                                                        *** apply (aeq_swap _ _ y x1) in H10.
                                                                            rewrite swap_involutive in H10.
                                                                            apply aeq_fv_nom in H10.
                                                                            rewrite <- H10 in H9.
                                                                            apply fv_nom_swap_2 in H9.
                                                                            assumption.
                                                                        *** apply aeq_fv_nom in H10.
                                                                            rewrite H10.
                                                                            apply fv_nom_remove_swap;default_simp.
                                                                            apply fv_nom_remove_swap;default_simp.
                                                                     ** apply aeq_swap. assumption.
                                                                   * rewrite shuffle_swap;default_simp.
                                                                     rewrite (swap_symmetric _ x2 x0).
                                                                     rewrite (swap_symmetric _ y x2).
                                                                     rewrite shuffle_swap;default_simp.
                                                                     rewrite (swap_symmetric _ x0 y).
                                                                     rewrite shuffle_swap;default_simp.
                                                                     apply (aeq_trans _ (swap x2 x1 t0)).
                                                                     ** apply aeq_swap0.
                                                                        *** apply aeq_fv_nom in H10.
                                                                            rewrite H10.
                                                                            apply fv_nom_remove_swap;default_simp.
                                                                            apply fv_nom_remove_swap;default_simp.
                                                                        *** default_simp.
                                                                     ** apply aeq_swap.
                                                                        apply (aeq_trans _ (swap y x2 t0)).
                                                                        *** apply aeq_swap0.
                                                                            **** apply (aeq_swap _ _ y x0) in H10.
                                                                                 rewrite swap_involutive in H10.
                                                                                 apply aeq_fv_nom in H10.
                                                                                 rewrite <- H10 in H9.
                                                                                 apply fv_nom_swap_2 in H9.
                                                                                 assumption.
                                                                            **** apply aeq_fv_nom in H10.
                                                                                 rewrite H10.
                                                                                 apply fv_nom_remove_swap;default_simp.
                                                                                 apply fv_nom_remove_swap;default_simp.
                                                                        *** apply aeq_swap. assumption.
                      ------ apply (aeq_trans _ (subst_rec (size (swap x2 x1 (swap x x2 t1'1))) (swap x2 x1 (swap x x2 t1'1))
                             (swap x2 x1 t2) (swap_var x2 x1 y))).
                             ------- apply aeq_m_subst_1. apply aeq_swap0;default_simp.
                             ------- apply aeq_sym. apply aeq_swap_m_subst.
       --- assert (H''': size (swap x0 x1 t0) <= size t0 + size t3); try (rewrite swap_size_eq;lia).
           rewrite (subst_size _ _ _ _ H''').
           assert (H'''': size (swap z x2 t1'1) <= size t1'1 + size t1'2); try (rewrite swap_size_eq;lia).
           rewrite (subst_size _ _ _ _ H''''). case (x1 == x2);intros.
           ---- rewrite e in *. apply aeq_sub_same.
                ----- apply H.
                      ------ reflexivity.
                      ------ assumption.
                      ------ apply fv_nom_remove_swap;default_simp.
                      ------ rewrite swap_symmetric_2;default_simp. apply (aeq_swap _ _ x0 x2).
                             rewrite swap_involutive. rewrite (swap_symmetric _ z x2).
                             case (x2 == z);intros.
                             ------- rewrite e in *. rewrite swap_symmetric. rewrite swap_id. assumption.
                             ------- rewrite shuffle_swap;default_simp. rewrite swap_symmetric.
                                     case (x0 == x2);intros.
                                     -------- rewrite e in *. rewrite swap_id. assumption.
                                     -------- rewrite shuffle_swap;default_simp.
                                              apply (aeq_trans _ (swap z x2 t0)).
                                              --------- apply aeq_swap0.
                                                        * apply (aeq_swap _ _ z x0) in H10.
                                                          rewrite swap_involutive in H10.
                                                          apply aeq_fv_nom in H10.
                                                          rewrite <- H10 in H9.
                                                          apply fv_nom_swap_2 in H9. assumption.
                                                        * apply aeq_fv_nom in H10. rewrite H10.
                                                          apply fv_nom_remove_swap;default_simp.
                                                          apply fv_nom_remove_swap;default_simp.
                                              --------- apply aeq_swap. assumption.
                ----- apply IHt1'1;default_simp.
           ---- apply aeq_sub_diff.
                ----- apply IHt1'1;default_simp.
                ----- assumption.
                ----- pose proof in_or_notin. specialize (H3 y (fv_nom (swap z x2 t1'1))).
                      destruct H3.
                      ------ apply (fv_nom_m_subst_in _ t2) in H3. unfold m_subst in H3. rewrite H3.
                             simpl. apply notin_union_3.
                             ------- case (x1 == y);intros;try(rewrite e;default_simp).
                                     apply diff_remove;default_simp.
                                     case (x1 == z);intros;try(rewrite e;apply fv_nom_swap;default_simp).
                                     apply fv_nom_remove_swap;default_simp. case (x1 == x0);intros.
                                     -------- rewrite e in *. apply fv_nom_swap_remove in H9;default_simp.
                                     -------- pose proof n.
                                              apply notin_union_2 in n. repeat apply notin_union_1 in n.
                                              apply diff_remove_2 in n;default_simp. apply aeq_fv_nom in H10.
                                              rewrite H10 in n. apply fv_nom_swap_remove in n;default_simp.
                                              apply fv_nom_swap_remove in n;default_simp.
                             ------- default_simp.
                      ------ apply (fv_nom_m_subst_notin _ t2) in H3. unfold m_subst in H3.
                             rewrite H3. case (x1 == y);intros;try(rewrite e;default_simp).
                                         apply diff_remove;default_simp.
                                         case (x1 == z);intros;try(rewrite e;apply fv_nom_swap;default_simp).
                                         apply fv_nom_remove_swap;default_simp. case (x1 == x0);intros.
                                         ------- rewrite e in *. apply fv_nom_swap_remove in H9;default_simp.
                                         ------- pose proof n.
                                                 apply notin_union_2 in n. repeat apply notin_union_1 in n.
                                                 apply diff_remove_2 in n;default_simp. apply aeq_fv_nom in H10.
                                                 rewrite H10 in n. apply fv_nom_swap_remove in n;default_simp.
                                                 apply fv_nom_swap_remove in n;default_simp.
                ----- apply (aeq_trans _ (subst_rec (size (swap x2 x1 (swap z x2 t1'1))) (swap x2 x1 (swap z x2 t1'1))
                      t2 (swap_var x2 x1 y))).
                      ------ unfold swap_var in *. pose proof n0. repeat apply notin_union_2 in H3.
                             apply notin_singleton_1 in H3. default_simp.
                             ------- case (x == x2);intros.
                                     * rewrite e in *. apply aeq_m_subst_2. rewrite (swap_symmetric _ x2 x1).
                                       rewrite (swap_symmetric _ z x2). rewrite shuffle_swap;default_simp.
                                       rewrite (swap_symmetric _ x1 x2). apply (aeq_swap _ _ x0 x1).
                                       rewrite shuffle_swap;default_simp. rewrite swap_involutive.
                                       rewrite swap_symmetric. case (x0 == x1);intros.
                                       ** rewrite e in *. rewrite swap_id. assumption.
                                       ** rewrite shuffle_swap;default_simp.
                                          apply (aeq_trans _ (swap z x1 t0)).
                                          *** apply aeq_swap0.
                                              **** apply (aeq_swap _ _ z x0) in H10.
                                                   rewrite swap_involutive in H10.
                                                   apply aeq_fv_nom in H10.
                                                   rewrite <- H10 in H9. apply fv_nom_swap_2 in H9.
                                                   assumption.
                                              **** default_simp.
                                          *** apply aeq_swap. assumption.
                                     * apply H.
                                       ** rewrite swap_size_eq. reflexivity.
                                       ** assumption.
                                       ** apply fv_nom_remove_swap;default_simp.
                                          apply fv_nom_remove_swap;default_simp.
                                       ** rewrite shuffle_swap;default_simp.
                                          rewrite (swap_symmetric _ x x1).
                                          rewrite shuffle_swap;default_simp.
                                          rewrite (swap_symmetric _ x1 x).
                                          rewrite (swap_symmetric_2 x x1);default_simp.
                                          rewrite (swap_symmetric _ z x2).
                                          apply (aeq_swap _ _ x0 x1). rewrite swap_involutive.
                                          case (x2 == z);intros.
                                          *** rewrite e in *. rewrite swap_id.
                                              rewrite shuffle_swap;default_simp.
                                              rewrite swap_symmetric.
                                              case (x0 == x1);intros;try(rewrite e in *;rewrite swap_id;default_simp).
                                              rewrite shuffle_swap;default_simp.
                                              apply (aeq_trans _ (swap z x1 t0)).
                                              **** apply aeq_swap0.
                                                   ***** apply (aeq_swap _ _ z x0) in H10.
                                                         rewrite swap_involutive in H10.
                                                         apply aeq_fv_nom in H10.
                                                         rewrite <- H10 in H9. apply fv_nom_swap_2 in H9.
                                                         assumption.
                                                   ***** default_simp.
                                              **** apply aeq_swap. assumption.
                                          *** case (x0 == x2);intros.
                                              **** rewrite e in *. rewrite swap_symmetric. rewrite swap_involutive.
                                                   rewrite swap_symmetric. assumption.
                                              **** rewrite shuffle_swap;default_simp. rewrite swap_symmetric.
                                                   case (x0 == x1);intros.
                                                   ***** rewrite e in *. rewrite swap_id.
                                                         rewrite swap_symmetric. rewrite shuffle_swap;default_simp.
                                                         rewrite swap_symmetric. rewrite shuffle_swap;default_simp.
                                                         apply (aeq_trans _ (swap z x2 t0)).
                                                         ****** apply aeq_swap0.
                                                                ******* apply (aeq_swap _ _ z x1) in H10.
                                                                        rewrite swap_involutive in H10.
                                                                        apply aeq_fv_nom in H10.
                                                                        rewrite <- H10 in H9. apply fv_nom_swap_2 in H9.
                                                                        assumption.
                                                                ******* apply aeq_fv_nom in H10. rewrite H10.
                                                                        apply fv_nom_remove_swap;default_simp.
                                                                        apply fv_nom_remove_swap;default_simp.
                                                         ****** apply aeq_swap. assumption.
                                                   ***** rewrite shuffle_swap;default_simp.
                                                         rewrite (swap_symmetric _ x2 x0).
                                                         rewrite shuffle_swap;default_simp.
                                                         rewrite (swap_symmetric _ x0 z).
                                                         rewrite shuffle_swap;default_simp.
                                                         apply (aeq_trans _ (swap x2 x1 t0)).
                                                         ****** apply aeq_swap0.
                                                                ******* apply aeq_fv_nom in H10. rewrite H10.
                                                                        apply fv_nom_remove_swap;default_simp.
                                                                        apply fv_nom_remove_swap;default_simp.
                                                                ******* default_simp.
                                                         ****** apply aeq_swap. apply (aeq_trans _ (swap z x2 t0)).
                                                                ******* apply aeq_swap0.
                                                                        ******** apply (aeq_swap _ _ z x0) in H10.
                                                                                 rewrite swap_involutive in H10.
                                                                                 apply aeq_fv_nom in H10.
                                                                                 rewrite <- H10 in H9. apply fv_nom_swap_2 in H9.
                                                                                 assumption.
                                                                        ******** apply aeq_fv_nom in H10. rewrite H10.
                                                                                 apply fv_nom_remove_swap;default_simp.
                                                                                 apply fv_nom_remove_swap;default_simp.
                                                                ******* apply aeq_swap. assumption.
                             ------- apply H.
                                     * rewrite swap_size_eq. reflexivity.
                                     * assumption.
                                     * case (x == x2);intros.
                                       ** rewrite e in *. apply fv_nom_swap. case (x1 == z);intros.
                                          *** rewrite e0 in *. apply fv_nom_swap. default_simp.
                                          *** apply fv_nom_remove_swap;default_simp.
                                              apply notin_union_2 in n. repeat apply notin_union_1 in n.
                                              case (x1 == x0);intros.
                                              **** rewrite e in *. apply fv_nom_swap_remove in H9;default_simp.
                                              **** apply (diff_remove_2 _ _ _ n11) in n. apply aeq_fv_nom in H10. rewrite H10 in n.
                                                   apply fv_nom_swap_remove in n;default_simp.
                                                   apply fv_nom_swap_remove in n;default_simp.
                                       ** apply fv_nom_remove_swap;default_simp. apply fv_nom_remove_swap;default_simp.
                                     * case (x == x2);intros.
                                       ** rewrite e in *. rewrite (swap_symmetric _ x2 y).
                                          rewrite shuffle_swap;default_simp.
                                          rewrite (swap_symmetric _ z x2).
                                          rewrite shuffle_swap;default_simp.
                                          rewrite (swap_symmetric _ y x2).
                                          rewrite (swap_symmetric _ y x1).
                                          case (x1 == z);intros.
                                          *** rewrite e in *. rewrite (swap_symmetric _ z y).
                                              rewrite swap_involutive. apply (aeq_swap _ _ x0 z).
                                              rewrite swap_involutive. rewrite swap_symmetric.
                                              assumption.
                                          *** rewrite shuffle_swap;default_simp. apply (aeq_swap _ _ x0 x1).
                                              rewrite swap_involutive. rewrite shuffle_swap;default_simp.
                                              rewrite swap_symmetric. case (x0 == x1);intros.
                                              **** rewrite e in *. rewrite swap_id. rewrite shuffle_swap;default_simp.
                                                   apply (aeq_trans _ (swap z y t0)).
                                                   ***** apply aeq_swap0.
                                                         ****** apply (aeq_swap _ _ z x1) in H10.
                                                                rewrite swap_involutive in H10.
                                                                apply aeq_fv_nom in H10.
                                                                rewrite <- H10 in H9. apply fv_nom_swap_2 in H9.
                                                                assumption.
                                                         ****** apply aeq_fv_nom in H10. rewrite H10.
                                                                apply fv_nom_remove_swap;default_simp.
                                                                rewrite swap_symmetric. apply fv_nom_swap. default_simp.
                                                   ***** apply aeq_swap. assumption.
                                              **** rewrite shuffle_swap;default_simp. case (x0 == y);intros.
                                                   ***** rewrite e in *. rewrite (swap_symmetric _ x1 y).
                                                         rewrite shuffle_swap;default_simp. rewrite swap_involutive.
                                                         assumption.
                                                   ***** rewrite (swap_symmetric_2 z x0);default_simp.
                                                         apply (aeq_trans _ (swap z x1 t0)).
                                                         ****** apply aeq_swap0.
                                                                ******* apply (aeq_swap _ _ z x0) in H10.
                                                                        rewrite swap_involutive in H10.
                                                                        apply aeq_fv_nom in H10.
                                                                        rewrite <- H10 in H9. apply fv_nom_swap_2 in H9.
                                                                        assumption.
                                                                ******* default_simp.
                                                         ****** apply aeq_swap. apply (aeq_trans _ (swap x1 y t0)).
                                                                ******* apply aeq_swap0.
                                                                        ******** default_simp.
                                                                        ******** apply aeq_fv_nom in H10. rewrite H10.
                                                                                 apply fv_nom_remove_swap;default_simp.
                                                                                 rewrite swap_symmetric. apply fv_nom_swap. default_simp.
                                                                ******* apply aeq_swap. assumption.
                                       ** rewrite swap_symmetric_2;default_simp. rewrite (swap_symmetric_2 x y);default_simp.
                                          apply (aeq_swap _ _ x0 x1). rewrite swap_involutive.
                                          rewrite (swap_symmetric _ x2 x1). case (x0 == x2);intros.
                                          *** rewrite e in *. rewrite swap_symmetric. rewrite swap_involutive. assumption.
                                          *** rewrite shuffle_swap;default_simp. rewrite swap_symmetric. case (x0 == x1);intros.
                                              **** rewrite e in *. rewrite swap_id. rewrite swap_symmetric.
                                                   rewrite (swap_symmetric _ z x2). case (x2 == z);intros.
                                                   ***** rewrite e0 in *. rewrite swap_symmetric. rewrite swap_id. assumption.
                                                   ***** rewrite shuffle_swap;default_simp. rewrite swap_symmetric.
                                                         rewrite shuffle_swap;default_simp. apply (aeq_trans _ (swap z x2 t0)).
                                                         ****** apply aeq_swap0.
                                                                ******* apply (aeq_swap _ _ z x1) in H10.
                                                                        rewrite swap_involutive in H10.
                                                                        apply aeq_fv_nom in H10.
                                                                        rewrite <- H10 in H9. apply fv_nom_swap_2 in H9.
                                                                        assumption.
                                                                ******* apply aeq_fv_nom in H10. rewrite H10.
                                                                        apply fv_nom_remove_swap;default_simp.
                                                                        apply fv_nom_remove_swap;default_simp.
                                                         ****** apply aeq_swap. assumption.
                                              **** rewrite shuffle_swap;default_simp. rewrite (swap_symmetric _ x2 x0).
                                                   rewrite (swap_symmetric _ z x2). case (x2 == z);intros.
                                                   ***** rewrite e in *. rewrite swap_id. apply (aeq_trans _ (swap z x1 t0)).
                                                         ****** apply aeq_swap0.
                                                                ******* apply (aeq_swap _ _ z x0) in H10.
                                                                        rewrite swap_involutive in H10.
                                                                        apply aeq_fv_nom in H10.
                                                                        rewrite <- H10 in H9. apply fv_nom_swap_2 in H9.
                                                                        assumption.
                                                                ******* default_simp.
                                                         ****** apply aeq_swap. rewrite swap_symmetric. assumption.
                                                   ***** rewrite shuffle_swap;default_simp. rewrite (swap_symmetric _ x0 z).
                                                         rewrite shuffle_swap;default_simp. apply (aeq_trans _ (swap x2 x1 t0)).
                                                         ****** apply aeq_swap0.
                                                                ******* apply aeq_fv_nom in H10. rewrite H10.
                                                                        apply fv_nom_remove_swap;default_simp.
                                                                        apply fv_nom_remove_swap;default_simp.
                                                                ******* default_simp.
                                                         ****** apply aeq_swap. apply (aeq_trans _ (swap z x2 t0)).
                                                                ******* apply aeq_swap0.
                                                                        ******** apply (aeq_swap _ _ z x0) in H10.
                                                                                 rewrite swap_involutive in H10.
                                                                                 apply aeq_fv_nom in H10.
                                                                                 rewrite <- H10 in H9. apply fv_nom_swap_2 in H9.
                                                                                 assumption.
                                                                        ******** apply aeq_fv_nom in H10. rewrite H10.
                                                                                 apply fv_nom_remove_swap;default_simp.
                                                                                 apply fv_nom_remove_swap;default_simp.
                                                                ******* apply aeq_swap. assumption.
                      ------ apply (aeq_trans _ (subst_rec (size (swap x2 x1 (swap z x2 t1'1))) (swap x2 x1 (swap z x2 t1'1))
                             (swap x2 x1 t2) (swap_var x2 x1 y))).
                             * apply aeq_m_subst_1. apply aeq_swap0;default_simp.
                             * apply aeq_sym. apply aeq_swap_m_subst.
Qed.                                                                                                                                                                                      
Lemma aeq_P: forall t1 t2, aeq t1 t2 -> aeq (P t1) (P t2).
Proof.
  intros t1. induction t1 using n_sexp_induction;intros.
  - inversion H. apply aeq_refl.
  - inversion H0.
    -- simpl. apply aeq_abs_same. rewrite <- (swap_id t1 x).
       rewrite <- (swap_id t1 x) in H4. apply H. reflexivity.
       assumption.
    -- simpl. apply aeq_abs_diff.
       --- assumption.
       --- apply notin_P. assumption.
       --- assert (size t3 = size t1).
           ---- apply aeq_size in H6. rewrite swap_size_eq in H6.
                rewrite H6. reflexivity.
           ---- specialize (H t3 y z). apply (aeq_trans _ (P (swap y z t3))).
                ----- apply aeq_sym. apply aeq_sym in H6. apply H; assumption.
                ----- apply aeq_swap_P.
  - inversion H. simpl. apply aeq_app.
    -- apply IHt1_1. assumption.
    -- apply IHt1_2. assumption.
  - inversion H0;simpl.
    -- apply (aeq_trans _ (m_subst (P t1_2) z (P t1'))).
       --- apply aeq_m_subst_2. rewrite <- (swap_id t1_1 x). apply H.
           ---- reflexivity.
           ---- rewrite swap_id. assumption.
       --- apply aeq_m_subst_1. apply IHt1_1. assumption.
    -- apply (aeq_trans _ (m_subst (P t2') z (P t1_1))).
       --- apply aeq_m_subst_1. apply IHt1_1. assumption.
       --- apply aeq_m_subst_3.
           ---- assumption.
           ---- apply notin_P. assumption.
           ---- apply aeq_sym. apply (aeq_trans _ (P (swap z y t1'))).
                ----- apply aeq_sym. apply aeq_swap_P.
                ----- apply H.
                      ------ apply aeq_size in H8. rewrite H8. rewrite swap_size_eq. reflexivity.
                      ------ apply aeq_sym. rewrite swap_symmetric. assumption.
Qed.

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

(**)
(*Lemma 5.3(1) in Nakazawa*)    
Lemma pi_P: forall t1 t2, (ctx pix) t1 t2 -> aeq (P t1) (P t2).
Proof.
  intros t1 t2 H. induction H.
  - apply aeq_P.
    assumption.
  - inversion H0; subst.
    -- apply aeq_trans with (P e3).
       --- apply aeq_P in H.
           simpl in H.
           unfold m_subst in H.
           simpl in H.
           destruct (y == y).
           ---- assumption.
           ---- contradiction.
       --- apply aeq_P; assumption.
    -- apply aeq_P in H.
       simpl in H.
       unfold m_subst in H.
       simpl in H.
       destruct (y == x).
       --- symmetry in e0.
           contradiction.
       --- apply aeq_trans with (n_var x).
           ---- assumption.
           ---- apply aeq_P in H1.
                simpl in H1.
                assumption.
    -- apply aeq_P in H. simpl in H. unfold m_subst in H.
       simpl in H. destruct (y == y).
       --- apply aeq_P in H1. simpl in H1.
           apply (aeq_trans _ _ _ H H1).
       --- contradiction.
    -- apply aeq_P in H.
       simpl in H.
       unfold m_subst in H.
       simpl in H.
       destruct (y == x).
       --- symmetry in e; contradiction.
       --- destruct (atom_fresh (Metatheory.union (fv_nom (P e5)) (Metatheory.union (remove x (fv_nom (P e0))) (singleton y)))).
           apply aeq_trans with (n_abs x0 (subst_rec (size (P e0)) (swap x x0 (P e0)) (P e5) y)).
           ---- assumption.
           ---- apply aeq_P in H1.
                simpl in H1.
                unfold m_subst in H1.
                apply aeq_trans with (n_abs x (subst_rec (size (P e0)) (P e0) (P e5) y)).
                ----- case ( x == x0 ).
                      ------ intro Heq; subst.
                             rewrite swap_id.
                             apply aeq_refl.
                      ------ intro Hneq.
                             apply aeq_sym.
                             apply aeq_abs_diff.
                             ------- assumption.
                             ------- rewrite <- (swap_size_eq x x0).
                                     pose proof in_or_notin.
                                     specialize (H4 y (fv_nom (swap x x0 (P e0)))).
                                     destruct H4.
                                     -------- apply (fv_nom_m_subst_in _ (P e5)) in H4.
                                              unfold m_subst in H4. rewrite H4.
                                              simpl. apply notin_union_3.
                                              --------- apply (diff_remove _ _ _ H2).
                                                        apply fv_nom_swap.
                                                        apply notin_union_2 in n0.
                                                        apply notin_union_1 in n0.
                                                        assert (H5: x0 <> x). default_simp.
                                                        apply (diff_remove_2 _ _ _ H5 n0).
                                              --------- apply (notin_P _ _ H3). 
                                     -------- apply (fv_nom_m_subst_notin _ (P e5)) in H4.
                                              unfold m_subst in H4. rewrite H4.
                                              apply (diff_remove _ _ _ H2).
                                              apply fv_nom_swap.
                                              apply notin_union_2 in n0.
                                              apply notin_union_1 in n0.
                                              assert (H5: x0 <> x). default_simp.
                                              apply (diff_remove_2 _ _ _ H5 n0).
                             ------- rewrite <- (swap_size_eq x x0 (P e0)) at 2.
                                     rewrite swap_symmetric. apply (aeq_trans _ 
                                     (subst_rec (size (swap x x0 (swap x x0 (P e0))))
                                     (swap x x0 (swap x x0 (P e0))) (swap x x0 (P e5)) 
                                     (swap_var x x0 y))).
                                     -------- rewrite swap_involutive. unfold swap_var. pose proof n0.
                                              repeat apply notin_union_2 in H4. apply notin_singleton_1 in H4.
                                              default_simp. apply aeq_m_subst_1.
                                              apply aeq_swap0.
                                              --------- apply notin_P. assumption.
                                              --------- default_simp.
                                     -------- apply aeq_sym. apply aeq_swap_m_subst.
                ----- assumption.
    -- apply aeq_P in H. simpl in H. apply aeq_P in H1. simpl in H1.  apply (aeq_trans _
       (m_subst (P e5) y (n_abs x (P e0)))).
       --- assumption.
       --- apply (aeq_trans _ (n_abs z (m_subst (P e5) y (P (swap x z e0))))).
           ---- unfold m_subst. simpl. default_simp. rewrite <- (swap_size_eq x x0). case (x0 == z);intros.
                ----- rewrite e in *. apply aeq_abs_same.
                      apply aeq_m_subst_2. apply aeq_sym. apply aeq_swap_P.
                ----- apply aeq_abs_diff.
                      ------ assumption.
                      ------ pose proof in_or_notin. specialize (H7 y (fv_nom (P (swap x z e0)))).
                             destruct H7.
                             ------- apply (fv_nom_m_subst_in _ (P e5)) in H7. unfold m_subst in H7.
                                     rewrite H7. simpl. apply notin_union_3.
                                     * apply diff_remove;default_simp. apply notin_swap_P.
                                       case (x0 == x);intros.
                                       ** rewrite e in *. apply fv_nom_swap. apply notin_P.
                                          assumption.
                                       ** apply fv_nom_remove_swap;default_simp.
                                     * default_simp.
                             ------- apply (fv_nom_m_subst_notin _ (P e5)) in H7. unfold m_subst in H7.
                                     rewrite H7. apply diff_remove;default_simp. apply notin_swap_P.
                                     case (x0 == x);intros.
                                     * rewrite e in *. apply fv_nom_swap. apply notin_P.
                                       assumption.
                                     * apply fv_nom_remove_swap;default_simp.
                      ------ apply (aeq_trans _ (subst_rec (size (swap z x0 (P (swap x z e0))))
                             (swap z x0 (P (swap x z e0))) (P e5) (swap_var z x0 y))).
                             ------- unfold swap_var. pose proof n. repeat apply notin_union_2 in H7.
                                     apply notin_singleton_1 in H7. default_simp.
                                     apply aeq_m_subst_2. apply (aeq_swap _  _ z x0).
                                     rewrite swap_involutive.
                                     apply (aeq_trans _ (swap x z (P e0))).
                                     * rewrite (swap_symmetric _ x x0).
                                       case (z == x);intros.
                                       ** rewrite e in *. rewrite swap_symmetric.
                                          rewrite swap_id. rewrite swap_involutive.
                                          apply aeq_refl.
                                       ** case (x0 == x);intros.
                                          *** rewrite e in *. rewrite swap_id.
                                              rewrite swap_symmetric. apply aeq_refl.
                                          *** rewrite shuffle_swap;default_simp.
                                              rewrite swap_symmetric. apply aeq_swap.
                                              apply aeq_sym. apply aeq_swap0.
                                              **** apply notin_P. assumption.
                                              **** default_simp.
                                     * apply aeq_sym. apply aeq_swap_P.
                             ------- apply (aeq_trans _ (subst_rec (size (swap z x0 (P (swap x z e0))))
                                     (swap z x0 (P (swap x z e0))) (swap z x0 (P e5)) (swap_var z x0 y))).
                                     -------- apply aeq_m_subst_1. apply aeq_swap0.
                                              * apply notin_P. assumption.
                                              * default_simp.
                                     -------- apply aeq_sym. apply aeq_swap_m_subst.
           ---- assumption.
    -- apply aeq_P in H. apply aeq_P in H1. apply (aeq_trans _ (P (n_sub (n_app e0 e5) y e6))).
       --- assumption.
       --- simpl. simpl in H1. unfold m_subst in *. simpl in *.
           assert (H': size (P e0) <= size (P e0) + size (P e5));try lia.
           assert (H'': size (P e5) <= size (P e0) + size (P e5));try lia.
           rewrite (subst_size _ _ _ _ H'). rewrite (subst_size _ _ _ _ H'').
           assumption.
  - simpl. apply aeq_abs_same. assumption.
  - simpl. apply aeq_app. 
    -- assumption.
    -- apply aeq_refl.
  - simpl. apply aeq_app. 
    -- apply aeq_refl.
    -- assumption.
  - simpl. apply aeq_m_subst_2. assumption.
  - simpl. apply aeq_m_subst_1. assumption.
Qed.

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

Lemma ctx_betapi_iff_lx:  forall e1 e2,
  refltrans lx e1 e2 <-> refltrans (ctx betapi) e1 e2.
Proof.
  intros. split; default_simp.
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

Lemma refltrans_app3 (R: Rel n_sexp): forall e1 e2 e3 e4,
    refltrans (ctx R) e1 e2 -> refltrans (ctx R) e3 e4 -> refltrans (ctx R) (n_app e1 e3) (n_app e2 e4).
Proof.
  intros. induction H0.
  - induction H.
    -- apply refl.
    -- apply refltrans_app1.
       apply rtrans with b.
       --- assumption.
       --- assumption.
  - apply refltrans_composition with (n_app e1 b).
    -- apply refltrans_app2. apply rtrans with (ctx R) a b b in H0.
       --- assumption.
       --- apply refl.
    -- assumption.
Qed.

Lemma refltrans_sub1 (R: Rel n_sexp): forall e1 e2 e3 x,
    refltrans (ctx R) e2 e3 -> refltrans (ctx R) (n_sub e1 x e2) (n_sub e1 x e3).
  intros. induction H.
  - apply refl.
  - apply refltrans_composition with (n_sub e1 x b).
    -- apply rtrans with (n_sub e1 x b).
       --- apply step_sub_right. assumption.
       --- apply refl.
    -- assumption.
Qed.

Lemma refltrans_sub2 (R: Rel n_sexp): forall e1 e2 e3 x,
    refltrans (ctx R) e2 e3 -> refltrans (ctx R) (n_sub e2 x e1) (n_sub e3 x e1).
Proof.
  intros. induction H.
  - apply refl.
  - apply refltrans_composition with (n_sub b x e1).
    -- apply rtrans with (n_sub b x e1).
       --- apply step_sub_left. assumption.
       --- apply refl.
    -- assumption.
Qed.

Lemma refltrans_sub3 (R: Rel n_sexp): forall e1 e2 e3 e4 x,
  refltrans (ctx R) e1 e3 -> refltrans (ctx R) e2 e4 ->
  refltrans (ctx R) (n_sub e1 x e2) (n_sub e3 x e4).
Proof.
  intros. apply (refltrans_composition _ _ (n_sub e3 x e2)).
  - apply refltrans_sub2. assumption.
  - apply refltrans_sub1. assumption.
Qed.

(*Lemma 4 in Nakazawa*)
Lemma pure_pix: forall e1 x e2, pure e1 -> refltrans (ctx pix) (n_sub e1 x e2) (m_subst e2 x e1).
Proof.
  induction e1 using n_sexp_induction.
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
  - intros. inversion H0; subst.
    unfold m_subst in *. simpl.
    case (x == z).
    -- intros; subst. apply rtrans with (n_abs z e1).
       --- apply step_redex_R. apply step_abs1.
       --- simpl. apply refl.
    -- intros. default_simp. pose proof in_or_notin.
       specialize (H0 z (fv_nom e2)). destruct H0.
       --- apply (rtrans _ _ (n_abs x0 (n_sub (swap z x0 e1) x e2))).
           ---- apply (step_redex _ _ (n_sub (n_abs z e1) x e2)
                (n_abs x0 (n_sub (swap z x0 e1) x e2)) _ ).
                ----- apply aeq_refl.
                ----- apply step_abs3;default_simp. case (x0 == z);intros.
                      ------ rewrite e in *. apply notin_union_1 in n0. default_simp.
                      ------ default_simp.
                ----- apply aeq_refl.
           ---- apply refltrans_abs. rewrite <- (swap_size_eq z x0). apply H.
                ----- reflexivity.
                ----- apply pure_swap. assumption.
       --- apply (rtrans _ _ (n_abs z (n_sub e1 x e2))).
           ---- apply step_redex_R. apply step_abs2;default_simp.
           ---- apply (rtrans _ _ (n_abs x0 (swap z x0 (n_sub e1 x e2)))).
                ----- apply step_aeq. case (z == x0);intros.
                      ------ rewrite e in *. rewrite swap_id. apply aeq_refl.
                      ------ apply aeq_abs_diff.
                             ------- assumption.
                             ------- apply fv_nom_swap. simpl. apply notin_union_3;default_simp.
                             ------- rewrite swap_symmetric. rewrite swap_involutive. apply aeq_refl.
                ----- apply refltrans_abs. simpl. unfold swap_var. pose proof n0.
                      repeat apply notin_union_2 in H1. apply notin_singleton_1 in H1.
                      default_simp. apply (rtrans _ _ (n_sub (swap z x0 e1) x e2)).
                      ------ apply step_aeq. apply aeq_sub_same.
                             * apply aeq_refl.
                             * apply aeq_sym. apply aeq_swap0;default_simp.
                      ------ rewrite <- (swap_size_eq z x0). apply H.
                             * reflexivity.
                             * apply pure_swap. assumption.
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



Lemma pure_pix_2: forall e1 x e2, pure e1 -> refltrans (ctx betapi) (n_sub e1 x e2) (m_subst e2 x e1).
Proof.
  intros. apply (pure_pix _ x e2) in H. induction H.
  - apply refl.
  - apply (rtrans _ _ b).
    -- apply ctx_betax_beta_pix. apply union_or. left. assumption.
    -- assumption.
Qed.  

Lemma pure_B: forall e, pure e -> pure (B e).
Proof.
  intros. induction H.
  - simpl. apply pure_var.
  - simpl. destruct e1.
    -- simpl in *. apply pure_app;assumption.
    -- apply pure_m_subst.
       --- assumption.
       --- simpl in IHpure1. inversion IHpure1. assumption.
    -- apply pure_app;assumption.
    -- simpl in IHpure1. inversion IHpure1.
  - simpl. apply pure_abs. assumption.
Qed.

Lemma swap_B: forall x1 x2 t, aeq (swap x1 x2 (B t)) (B (swap x1 x2 t)).
Proof.
  intros.
  induction t.
  - simpl. apply aeq_refl.
  - simpl. apply aeq_abs_same. assumption.
  - simpl. destruct t1;default_simp. inversion IHt1.
    -- apply (aeq_trans _ (m_subst (swap x1 x2 (B t2)) (swap_var x1 x2 x) (swap x1 x2 (B t1)))).
       --- apply aeq_swap_m_subst.
       --- apply (aeq_trans _ (m_subst (swap x1 x2 (B t2)) (swap_var x1 x2 x) (B (swap x1 x2 t1)))).
           ---- apply aeq_m_subst_2. assumption.
           ---- apply aeq_m_subst_1. assumption.
    -- default_simp.
  - simpl. apply aeq_sub_same;assumption.
Qed.

Lemma pure_refltrans_B: forall e, pure e -> refltrans lx e (B e).
Proof.
  induction e using n_sexp_induction;intros.
  - simpl. apply refl.
  - simpl. apply refltrans_abs. rewrite <- (swap_id e z). apply H.
    -- reflexivity.
    -- rewrite swap_id. inversion H0. assumption.
  - simpl. destruct e1 eqn:H'.
    -- simpl. apply refltrans_app2. apply IHe2. inversion H. assumption.
    -- inversion H. apply (refltrans_composition _ _ (n_app (B (n_abs x n)) e2)).
       --- apply refltrans_app1. apply IHe1. assumption.
       --- simpl. apply (rtrans _ _ (n_sub (B n) x e2)).
           ---- apply step_redex_R. apply b_rule. apply step_betax.
           ---- apply (refltrans_composition _ _ (n_sub (B n) x (B e2))).
                ----- apply refltrans_sub1. apply IHe2. assumption.
                ----- apply pure_pix_2. apply pure_B. inversion H2. assumption.
    -- apply refltrans_app3.
       --- apply IHe1. inversion H. assumption.
       --- apply IHe2. inversion H. assumption.
    -- inversion H. inversion H2.
  - inversion H0.
Qed.

Lemma refltrans_P: forall a, refltrans (ctx pix) a (P a).
Proof.
  induction a.
  - simpl. apply refl.
  - simpl. apply refltrans_abs. assumption.
  - simpl. apply refltrans_app3;assumption.
  - simpl. apply (refltrans_composition3 _ (n_sub (P a1) x a2)).
    -- apply (refltrans_composition3 _ (n_sub (P a1) x (P a2))).
       --- apply pure_pix. apply pure_P.
       --- apply refltrans_sub1. assumption.
    -- apply refltrans_sub2. assumption.
Qed.

Lemma refltrans_lx_pix: forall a b, refltrans (ctx pix) a b -> refltrans lx a b.
Proof.
  intros. induction H.
  - apply refl.
  - apply (rtrans _ a b c).
    -- apply ctx_betax_beta_pix. apply union_or. left. assumption.
    -- assumption.
Qed.

Lemma refltrans_lx_betax: forall a b, refltrans (ctx betax) a b -> refltrans lx a b.
Proof.
  intros. induction H.
  - apply refl.
  - apply (rtrans _ a b c).
    -- apply ctx_betax_beta_pix. apply union_or. right. assumption.
    -- assumption.
Qed.

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

Lemma m_subst_lemma: forall e1 e2 e3 x y, x <> y -> x `notin` (fv_nom e3) ->
  aeq (m_subst e3 y (m_subst e2 x e1)) (m_subst (m_subst e3 y e2) x (m_subst e3 y e1)).
Proof.
Admitted.

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
  refltrans lx e1 e2 -> refltrans lx (m_subst e1 x e3) (m_subst e2 x e3).
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
  refltrans lx e1 (m_subst e2 x e1).
Proof.
  intros. apply (rtrans _ _ (m_subst e2 x e1)).
  - apply step_aeq. apply aeq_sym. apply subst_fresh_eq. assumption.
  - apply refl.
Qed.

Lemma refltrans_subst_fresh_2: forall e1 e2 x, x `notin` (fv_nom e1) -> 
  refltrans lx (m_subst e2 x e1) e1.
Proof.
  intros. apply (rtrans _ _ e1).
  - apply step_aeq. apply subst_fresh_eq. assumption.
  - apply refl.
Qed.

Lemma refltrans_m_subst1 (R: Rel n_sexp): forall e1 e2 e3 x, refltrans (ctx R) e1 e2 -> 
  refltrans (ctx R) (m_subst e1 x e3) (m_subst e2 x e3).
Admitted.

Lemma refltrans_m_subst2 (R: Rel n_sexp): forall e1 e2 e3 x, refltrans (ctx R) e1 e2 -> 
  refltrans (ctx R) (m_subst e3 x e1) (m_subst e3 x e2).
Admitted.

Lemma aeq_double_m_subst: forall e1 e2 e3 x, aeq (m_subst (e1) x (m_subst e2 x e3)) (m_subst (m_subst e1 x e2) x e3).
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
 
Lemma aeq_B: forall e1 e2, aeq e1 e2 -> aeq (B e1) (B e2).
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

Lemma refltrans_m_subst_B: forall e1 e2 x, pure e1 -> pure e2 -> refltrans lx (m_subst (B e2) x (B e1)) (B (m_subst e2 x e1)).
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
  refltrans (ctx R) e3 e4 -> refltrans (ctx R) (m_subst e3 x e1) (m_subst e4 x e2).
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

Lemma aeq_pure: forall e1 e2, aeq e1 e2 -> pure e1 -> pure e2.
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

Lemma Z_property_B_beta: forall e1 e2, pure e1 -> pure e2 -> (ctx beta) e1 e2 -> refltrans (ctx beta) e2 (B e1) /\
  refltrans (ctx beta) (B e1) (B e2).
Proof.
Admitted.

Lemma refltrans_beta_imply_B: forall e1 e2, pure e1 -> pure e2 -> refltrans (ctx beta) e1 e2 ->
  refltrans (ctx beta) (B e1) (B e2). 
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

Lemma refltrans_beta_to_lx: forall e1 e2, pure e1 -> pure e2 -> refltrans (ctx beta) e1 e2 ->
  refltrans lx e1 e2.
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
