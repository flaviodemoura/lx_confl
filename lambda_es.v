(* Infrastructure *)
(* begin hide *)
Require Export Arith Lia.  Print LoadPath.
Require Export Metalib.Metatheory.
Require Export Metalib.LibDefaultSimp.
Require Export Metalib.LibLNgen.

Lemma strong_induction :
 forall (P:nat->Prop),
   (forall n, (forall m, m < n -> P m) -> P n) ->
   (forall n, P n).
Proof.
  intros Q IH n.
  assert (H := nat_ind (fun n => (forall m : nat, m < n -> Q m))).
  apply IH. apply H.
  - intros m Hlt; inversion Hlt.
  - intros n' H' m Hlt. apply IH.
    intros m0 Hlt'. apply H'.
    apply lt_n_Sm_le in Hlt.
    apply lt_le_trans with m; assumption.
Qed.

(* não utilizado
Lemma in_or_notin: forall x s, x `in` s \/ x `notin` s.
Proof.
  intros. pose proof notin_diff_1. specialize (H x s s).
  rewrite AtomSetProperties.diff_subset_equal in H.
  - apply or_comm. apply H.
    apply notin_empty_1.
  - reflexivity.
Qed. 

Lemma remove_singleton_neq: forall x y,
    x <> y -> remove y (singleton x) [=] singleton x.
Proof.
  intros. 
  pose proof notin_singleton_2. specialize (H0 x y).
  apply H0 in H.
  apply AtomSetProperties.remove_equal in H. assumption.
Qed. *)

Lemma diff_remove_2: forall x y s,
  x <> y -> x `notin` remove y s -> x `notin` s.
Proof.
  intros. default_simp.
Qed. 

(* não utilizado
Lemma diff_equal: forall s s' t,
    s [=] s' -> AtomSetImpl.diff s t [=] AtomSetImpl.diff s' t.
Proof.
intros. rewrite H. reflexivity.
Qed. *)

Lemma aux_not_equal : forall (x:atom) (y:atom),
    x <> y -> y <> x.
Proof.
  intros. unfold not. intros. unfold not in H.
  assert (x = y). {
    rewrite H0. reflexivity.
  }
  contradiction.
Qed.

(* não utilizado 
Lemma Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof.
  intros n m H. inversion H.
  - apply le_n.
  - apply (le_trans n (S n) m).
    -- apply le_S. reflexivity.
    -- assumption.
Qed. *)

Lemma remove_singleton_empty: forall x,
    remove x (singleton x) [=] empty.
Proof.
  intros. rewrite AtomSetProperties.singleton_equal_add.
  rewrite AtomSetProperties.remove_add.
  - reflexivity.
  - apply notin_empty_1.
Qed.

Lemma remove_singleton: forall t1 t2,
    remove t1 (singleton t1) [=] remove t2 (singleton t2).
Proof.
  intros. repeat rewrite remove_singleton_empty. reflexivity.
Qed.

Lemma notin_singleton_is_false: forall x,
    x `notin` (singleton x) -> False.
Proof.
  intros. intros. apply notin_singleton_1 in H. contradiction.
Qed.

Lemma double_remove: forall x s,
           remove x (remove x s) [=] remove x s.
Proof.
  intros. pose proof AtomSetProperties.remove_equal.
  assert (x `notin` remove x s). {
    apply AtomSetImpl.remove_1. reflexivity.
  }
  specialize (H (remove x s) x). apply H in H0. assumption.
Qed.

Lemma remove_symmetric: forall x y s,
           remove x (remove y s) [=] remove y (remove x s).
Proof.
  intros. split.
  - intros. case (a == x); intros; case (a == y); intros; subst.
    apply AtomSetImpl.remove_3 in H.
    -- rewrite double_remove. assumption.
    -- apply remove_iff in H. inversion H. contradiction.
    -- apply remove_iff in H. inversion H.
       apply remove_iff in H0. inversion H0.
       contradiction.
    -- pose proof H. apply AtomSetImpl.remove_3 in H.
       apply AtomSetImpl.remove_2.
       --- apply aux_not_equal; assumption.
       --- apply AtomSetImpl.remove_2.
           + apply aux_not_equal; assumption.
           + apply AtomSetImpl.remove_3 in H. assumption.
  - intros. case (a == x); intros; case (a == y); intros; subst.
    apply AtomSetImpl.remove_3 in H.
    -- rewrite double_remove. assumption.
    -- apply remove_iff in H. inversion H.
       apply remove_iff in H0. inversion H0.
       contradiction.
    -- apply remove_iff in H. inversion H. contradiction.
    -- pose proof H. apply AtomSetImpl.remove_3 in H.
       apply AtomSetImpl.remove_2.
       --- apply aux_not_equal; assumption.
       --- apply AtomSetImpl.remove_2.
           + apply aux_not_equal; assumption.
           + apply AtomSetImpl.remove_3 in H. assumption.
Qed.

Lemma remove_empty: forall x,
    remove x empty [=] empty.
Proof.
  intros. pose proof notin_empty. specialize (H x).
  apply AtomSetProperties.remove_equal in H.
  assumption.
Qed.

Lemma diff_remove: forall x y s,
    x <> y -> x `notin` s -> x `notin` remove y s.
Proof.
  intros. apply notin_remove_2. assumption.
Qed.
(* end hide *)

(** * Introduction *)

(** In this work, we are insterested in formalizing an extension of the substitution lemma%\cite{barendregtLambdaCalculusIts1984}% in the Coq proof assistant. The substitution lemma is an important result concerning the composition of the substitution operation, and is usually presented as follows: if $x$ does not occur in the set of free variables of the term $v$ then $t\{x/u\}\{y/v\} =_\alpha t\{y/v\}\{x/u\{y/v\}\}$. This is a well known result already formalized several times in the context of the $\lambda$-calculus %\cite{berghoferHeadtoHeadComparisonBruijn2007}%.

In the context of the $\lambda$-calculus with explicit substitutions its formalization is not straightforward because, in addition to the metasubstitution operation, there is the explicit substitution operator. Our formalization is done in a nominal setting that uses the MetaLib package of Coq, but no particular explicit substitution calculi is taken into account because the expected behaviour between the metasubstitution operation with the explicit substitutition constructor is the same regardless the calculus.

*)

(** * A syntactic extension of the $\lambda$-calculus *)

(** We consider a generic signature with the following constructors: *)

Inductive n_sexp : Set :=
 | n_var (x:atom)
 | n_abs (x:atom) (t:n_sexp)
 | n_app (t1:n_sexp) (t2:n_sexp)
 | n_sub (t1:n_sexp) (x:atom) (t2:n_sexp).

(** %\noindent% where [n_var] is the constructor for variables, [n_abs] for abstractions, [n_app] for applications and [n_sub] for the explicit substitution operation. *)

(* begin hide *)
Fixpoint size (t : n_sexp) : nat :=
  match t with
  | n_var x => 1
  | n_abs x t => 1 + size t
  | n_app t1 t2 => 1 + size t1 + size t2
  | n_sub t1 x t2 => 1 + size t1 + size t2
  end.

Fixpoint fv_nom (n : n_sexp) : atoms :=
  match n with
  | n_var x => {{x}}
  | n_abs x n => remove x (fv_nom n)
  | n_app t1 t2 => fv_nom t1 `union` fv_nom t2
  | n_sub t1 x t2 => (remove x (fv_nom t1)) `union` fv_nom t2
  end.
(* end hide *)

(* não utilizado
Lemma fv_nom_dec: forall t x, x `in` fv_nom t \/ x `notin` fv_nom t.
Proof.
  induction t.
  - intros x'. pose proof eq_dec. specialize (H x x'). destruct H.
    + subst. left. simpl. auto.
    + right. simpl. auto.
  - intro x'. simpl. pose proof eq_dec. specialize (H x x'). destruct H.
    + subst. specialize (IHt x'). destruct IHt; default_simp.
    + specialize (IHt x'). destruct IHt.
      * left. default_simp.
      * right. default_simp.
  - intro x. simpl. specialize (IHt1 x). destruct IHt1.
    + left. default_simp.
    + specialize (IHt2 x). destruct IHt2.
      * left. default_simp.
      * right. default_simp.
  - intro x'. simpl. pose proof eq_dec. specialize (H x x'). destruct H.
    + subst. specialize (IHt1 x'). destruct IHt1.
      * specialize (IHt2 x'). destruct IHt2.
        ** left. default_simp.
        ** right. default_simp.
      * specialize (IHt2 x'). destruct IHt2.
        ** left. default_simp.
        ** right. default_simp.
    + specialize (IHt1 x'). destruct IHt1.
      * specialize (IHt2 x'). destruct IHt2.
        ** left. default_simp.
        ** left. default_simp.
      * specialize (IHt2 x'). destruct IHt2.
        ** left. default_simp.
        ** right. default_simp.
Qed. 

Lemma fv_nom_app: forall t1 t2 x, x `notin` fv_nom (n_app t1 t2) -> x `notin` fv_nom t1  /\ x `notin` fv_nom t2.
Proof.
  intros t1 t2 x H. simpl in H. split.
  - apply notin_union_1 in H. assumption.
  - apply notin_union_2 in H. assumption.
Qed. *) 

(* begin hide *)
Definition swap_var (x:atom) (y:atom) (z:atom) :=
  if (z == x) then y else if (z == y) then x else z.

Lemma swap_var_id: forall x y, (swap_var x x y = y).
Proof.
  intros. unfold swap_var. case (y == x); intros; subst; reflexivity.
Qed.

Fixpoint swap (x:atom) (y:atom) (t:n_sexp) : n_sexp :=
  match t with
  | n_var z     => n_var (swap_var x y z)
  | n_abs z t1  => n_abs (swap_var x y z) (swap x y t1)
  | n_app t1 t2 => n_app (swap x y t1) (swap x y t2)
  | n_sub t1 z t2 => n_sub (swap x y t1) (swap_var x y z) (swap x y t2)
  end.
(* end hide *)

(* begin hide *)
Lemma swap_id : forall t x,
    swap x x t = t.
Proof.
  induction t; simpl; unfold swap_var; default_simp.
Qed.

Lemma swap_size_eq : forall x y t,
    size (swap x y t) = size t.
Proof.
  induction t; simpl; auto.
Qed.

Hint Rewrite swap_size_eq.

Lemma n_sexp_induction :
 forall P : n_sexp -> Prop,
 (forall x, P (n_var x)) ->
 (forall t1 z,
    (forall t2 x y, size t2 = size t1 ->
    P (swap x y t2)) -> P (n_abs z t1)) ->
 (forall t1 t2, P t1 -> P t2 -> P (n_app t1 t2)) ->
 (forall t1 t3 z, P t3 -> 
    (forall t2 x y, size t2 = size t1 ->
    P (swap x y t2)) -> P (n_sub t1 z t3)) -> 
 (forall t, P t).
Proof.
  intros P Hvar Habs Happ Hsub t.
  remember (size t) as n.
  generalize dependent t.
  induction n using strong_induction.
  intro t; case t.
  - intros x Hsize.
    apply Hvar.
  - intros x t' Hsize.
    apply Habs.
    intros t'' x1 x2 Hsize'.
    apply H with (size t'').
    + rewrite Hsize'.
      rewrite Hsize.
      simpl.
      apply Nat.lt_succ_diag_r.
    + symmetry.
      apply swap_size_eq.
  - intros. apply Happ.
    + apply H with ((size t1)).
      ++ simpl in Heqn. rewrite Heqn.
         apply le_lt_n_Sm.
         apply le_plus_l.
      ++ reflexivity.
    + apply H with ((size t2)).
      ++ simpl in Heqn. rewrite Heqn.
          apply le_lt_n_Sm.
         apply le_plus_r.
      ++ reflexivity.
  - intros. apply Hsub.
    + apply H with ((size t2)).
      ++ simpl in Heqn. rewrite Heqn.
          apply le_lt_n_Sm.
         apply le_plus_r.
      ++ reflexivity.
    + intros. apply H with ((size (swap x0 y t0))).
      ++ rewrite swap_size_eq. rewrite H0.
         simpl in Heqn. rewrite Heqn.
         apply le_lt_n_Sm.
         apply le_plus_l.
      ++ reflexivity.
Qed. 

Lemma swap_symmetric : forall t x y,
    swap x y t = swap y x t.
Proof.
  induction t.
  - intros x' y. simpl. unfold swap_var. default_simp.
  - intros x' y; simpl. unfold swap_var. default_simp.
  - intros x y; simpl. rewrite IHt1. rewrite IHt2; reflexivity.
  - intros. simpl. unfold swap_var. default_simp.
Qed.

Lemma swap_symmetric_2: forall x y x' y' t,
    x <> x' -> y <> y' -> x <> y'-> y <> x' -> swap x y (swap x' y' t) = swap x' y' (swap x y t). 
Proof.
  intros. induction t; simpl in *; unfold swap_var in *; default_simp.
Qed.

Lemma swap_involutive : forall t x y,
    swap x y (swap x y t) = t.
Proof.
 induction t; intros; simpl; unfold swap_var; default_simp.
Qed.

Lemma shuffle_swap : forall w y n z,
    w <> z -> y <> z ->
    (swap w y (swap y z n)) = (swap w z (swap w y n)).
Proof.
  induction n; intros; simpl; unfold swap_var; default_simp.
Qed.
(* end hide *)

(* não utilizado
Lemma shuffle_swap' : forall w y n z,
    w <> z -> y <> z ->
    (swap w y (swap y z n)) = (swap z w (swap y w n)).
Proof.
  induction n; intros; simpl; unfold swap_var; default_simp.
Qed.

Lemma swap_var_equivariance : forall v x y z w,
    swap_var x y (swap_var z w v) =
    swap_var (swap_var x y z) (swap_var x y w) (swap_var x y v).
Proof.
  intros; unfold swap_var; case(v == z); case (w == x); default_simp.
Qed.*)

(* begin hide *)
Lemma swap_equivariance : forall t x y z w,
    swap x y (swap z w t) = swap (swap_var x y z) (swap_var x y w) (swap x y t).
Proof.
  induction t.
  - intros. unfold swap_var. case (z == x0).
    -- case (w == x0).
       --- intros. rewrite swap_id. rewrite e; rewrite e0.
           rewrite swap_id. reflexivity.
       --- intros. case (w == y).
           + intros. rewrite swap_symmetric. rewrite e; rewrite e0.
             reflexivity.
           + intros. unfold swap. unfold swap_var. default_simp.
    -- unfold swap. unfold swap_var. intros. default_simp.
  - intros. simpl. rewrite IHt. unfold swap_var.
    case (x == z).
    -- case (w == x0); default_simp.
    -- case (w == x0).
       --- default_simp.
       --- intros. case (x == w); intros; case (z == x0); default_simp.
  - intros. simpl. rewrite IHt1. rewrite IHt2. reflexivity.
  - intros. simpl. rewrite IHt1. rewrite IHt2. unfold swap_var.
    default_simp.    
Qed.

Lemma fv_nom_swap : forall z y t,
  z `notin` fv_nom t ->
  y `notin` fv_nom (swap y z t).
Proof.
  induction t; intros; simpl; unfold swap_var; default_simp.
Qed.

Lemma fv_nom_swap_2 : forall z y t,
  z `notin` fv_nom (swap y z t) -> y `notin` fv_nom t.
Proof.
  intros. induction t; simpl in *; unfold swap_var in H; default_simp.
Qed.

Lemma fv_nom_swap_remove: forall t x y y0, x <> y ->  x <> y0 -> x `notin` fv_nom (swap y0 y t) -> x `notin` fv_nom t.
Proof.
  intros. induction t; simpl in *; unfold swap_var in *; default_simp.
Qed.
    
Lemma fv_nom_remove_swap: forall t x y y0, x <> y ->  x <> y0 -> x `notin` fv_nom t -> x `notin` fv_nom (swap y0 y t).
  Proof.
    induction t; simpl in *; unfold swap_var; default_simp.
Qed.

Lemma notin_fv_nom_equivariance : forall x0 x y t ,
  x0 `notin` fv_nom t ->
  swap_var x y x0  `notin` fv_nom (swap x y t).
Proof.
  intros. unfold swap_var. case (x0 == x).
  - intros. simpl. rewrite swap_symmetric. apply fv_nom_swap.
    rewrite <- e. assumption.
  - intros. case (x0 == y).
    -- intros. apply fv_nom_swap. rewrite <- e. assumption.
    -- intros. apply aux_not_equal in n. apply aux_not_equal in n0.
       assert ((x <> x0) -> (y <> x0)). {
         intros. assumption.
       }
       eapply (shuffle_swap x y t) in H0.
       --- induction t.
           + simpl. unfold swap_var. default_simp.
           + simpl. unfold swap_var. default_simp.
           + simpl. default_simp.
           + simpl. unfold swap_var. default_simp.
       --- assumption.
       --- assumption.
Qed. 
(* end hide *)


(* não utilizado
Lemma in_fv_nom_equivariance : forall x y x0 t,
  x0 `in` fv_nom t ->
  swap_var x y x0 `in` fv_nom (swap x y t).
Proof.
  induction t.
  - simpl. intro H. pose proof singleton_iff.
    specialize (H0 x1 x0). apply H0 in H. rewrite H.
    apply singleton_iff. reflexivity.
  - simpl. intros. unfold swap_var. default_simp.
    -- pose proof AtomSetImpl.remove_1.
       assert (H1:x `notin` remove x (fv_nom t)). {
         apply H0. reflexivity.
       }contradiction.
    -- pose proof AtomSetImpl.remove_2. apply H0.
       --- unfold not. intro. symmetry in H1. contradiction.
       --- specialize (H0 (fv_nom t) y x). assert(y<>x). {
             apply n.
           }
           
           apply H0 in n.
           + apply AtomSetImpl.remove_3 in H. apply IHt in H.
             unfold swap_var in IHt. case (x == x) in IHt.
             ++ apply AtomSetImpl.remove_3 in n.
                apply IHt in n. assumption.
             ++ unfold not in n0. contradiction. 
           + apply AtomSetImpl.remove_3 in H. assumption.
    -- apply AtomSetImpl.remove_2.
       --- assumption.
       --- apply AtomSetImpl.remove_3 in H. apply IHt in H.
           unfold swap_var in H. case (x == x) in H.
           + assumption.
           + contradiction.
    -- apply AtomSetImpl.remove_2.
       --- assumption.
       --- apply AtomSetImpl.remove_3 in H. unfold swap_var in IHt.
           case (y == x) in IHt.
           + intros. contradiction.
           + intros. case (y == y) in IHt.
             ++ apply IHt in H. assumption.
             ++ contradiction.
    -- assert (y = y). {
         reflexivity.
       }
       pose proof AtomSetImpl.remove_1.
       specialize (H1 (fv_nom t) y y).
       apply H1 in H0. unfold not in H0. contradiction.
    -- unfold swap_var in IHt. case (y == x) in IHt.
       --- contradiction.
       --- case (y == y) in IHt.
           + apply AtomSetImpl.remove_3 in H. apply IHt in H.
             pose proof AtomSetImpl.remove_2.
             specialize (H0 (fv_nom (swap x y t)) x1 x).
             apply H0 in n0.
             ++ assumption.
             ++ assumption.
           + contradiction.
    -- apply AtomSetImpl.remove_3 in H. apply IHt in H.
       unfold swap_var in H. case(x0 == x) in H.
       --- contradiction.
       --- case(x0 == y) in H.
           + pose proof AtomSetImpl.remove_2.
             specialize (H0 (fv_nom (swap x y t)) y x0).
             apply aux_not_equal in n0. apply H0 in n0.
             ++ assumption.
             ++ symmetry in e. contradiction.
           + unfold swap_var in IHt. case (x0 == x) in IHt.
             ++ contradiction.
             ++ pose proof AtomSetImpl.remove_2.
                specialize (H0 (fv_nom (swap x y t)) y x0).
                apply aux_not_equal in n0. apply H0 in n0.
                +++ assumption.
                +++ assumption.
    -- unfold swap_var in IHt. default_simp.
       apply AtomSetImpl.remove_3 in H. apply IHt in H.
       pose proof AtomSetImpl.remove_2.
       specialize (H0 (fv_nom (swap x y t)) x x0).
       apply aux_not_equal in n. apply H0 in n.
       --- assumption.
       --- assumption.
    -- case (x == y). 
       --- intros. rewrite e. rewrite swap_id. assumption.
       --- intros. case (x0 == x1).
           + intros. rewrite e in H. pose proof notin_remove_3.
             specialize (H0 x1 x1 (fv_nom t)). assert (x1 = x1). {
               reflexivity.
             }
             apply H0 in H1. unfold not in H1. contradiction.
           + intros. apply AtomSetImpl.remove_3 in H.
             unfold swap_var in IHt. case (x0 == x) in IHt.
             ++ contradiction.
             ++ case (x0 == y) in IHt.
                +++ contradiction.
                +++ apply IHt in H. pose proof remove_neq_iff.
                    specialize (H0 (fv_nom (swap x y t)) x1 x0).
                    apply aux_not_equal in n4.
                    apply H0 in n4. apply n4 in H. assumption.      
  - unfold swap_var. unfold swap_var in IHt1.
    unfold swap_var in IHt2. default_simp.
    -- pose proof AtomSetImpl.union_1.
       specialize (H0 (fv_nom t1) (fv_nom t2) x). apply H0 in H.
       pose proof AtomSetImpl.union_2.
       inversion H. 
       --- specialize (H1 (fv_nom (swap x y t1)) (fv_nom (swap x y t2)) y). apply IHt1 in H2.  apply H1 in H2. assumption.
       --- specialize (H1 (fv_nom (swap x y t2)) (fv_nom (swap x y t1)) y).
           pose proof AtomSetProperties.union_sym. apply H3.
           apply IHt2 in H2.  apply H1 in H2. assumption.
    -- pose proof union_iff. apply union_iff in H. inversion H.
       --- apply IHt1 in H1. apply union_iff. left. assumption.
       --- apply IHt2 in H1. apply union_iff. right. assumption.
    -- apply union_iff in H. inversion H.
       --- apply union_iff. apply IHt1 in H0. left. assumption.
       --- apply union_iff. apply IHt2 in H0. right. assumption.
  - intros. simpl. unfold swap_var. case (x == y).
    -- intros. default_simp.
       --- repeat rewrite swap_id. assumption.
       --- repeat rewrite swap_id. assumption.
       --- repeat rewrite swap_id. assumption.
       --- repeat rewrite swap_id. assumption.
    -- intros. default_simp.
       --- pose proof AtomSetImpl.remove_1.
           specialize (H0 (fv_nom t1) x x).
           assert (x = x). {
             reflexivity.
           }
           apply H0 in H1. pose proof union_iff. apply H2.
           apply H2 in H. inversion H.
           + contradiction.
           + right. simpl. apply IHt2 in H3. unfold swap_var in H3.
             case (x == x) in H3.
             ++ assumption.
             ++ contradiction.
       --- apply union_iff in H. apply union_iff. inversion H.
           + unfold swap_var in IHt2. case (x == x) in IHt2.
             ++ apply remove_iff in H0. inversion H0.
                unfold swap_var in IHt1. case (x == x) in IHt1.
                +++ apply IHt1 in H1. pose proof remove_neq_iff.
                    left. apply H3.
                    * assumption.
                    * assumption.                
                +++ contradiction.
             ++ contradiction.
           + apply IHt2 in H0. unfold swap_var in H0.
             case (x == x) in H0.
             ++ right. assumption.
             ++ contradiction.
       --- apply union_iff. apply union_iff in H. inversion H.
           + apply remove_neq_iff in H0. apply IHt1 in H0.
             unfold swap_var in H0. case (x == x) in H0.
             ++ left. apply remove_iff. split.
                +++ assumption.
                +++ assumption.
             ++ contradiction.
             ++ assumption.
           + apply IHt2 in H0. unfold swap_var in H0.
             case (x == x) in H0.
             ++ right. assumption.
             ++ contradiction.
       --- apply union_iff. apply union_iff in H. inversion H.
           + apply remove_neq_iff in H0. apply IHt1 in H0.
             unfold swap_var in H0. case (y == x) in H0.
             ++ contradiction.
             ++ case (y == y) in H0.
                +++ left. apply remove_iff. split.
                    * assumption.
                    * assumption.
                +++ contradiction.
             ++ assumption.
           + apply IHt2 in H0. unfold swap_var in H0.
             case (y == x) in H0.
             ++ contradiction.
             ++ case (y == y) in H0.
                +++ right. assumption.
                +++ contradiction.
       --- pose proof AtomSetImpl.remove_1.
           specialize (H0 (fv_nom t1) x x).
           assert (x = x). {
             reflexivity.
           }
           apply H0 in H1. apply union_iff. right.
           unfold swap_var in IHt2. case (y == x) in IHt2.
           + contradiction.
           + case (y == y) in IHt2.
             ++ apply union_iff in H. inversion H.
                +++ pose proof AtomSetImpl.remove_1.
                    specialize (H3 (fv_nom t1) y y).
                    assert (y = y). {
                      reflexivity.
                    }
                    apply H3 in H4. contradiction.
                +++ apply IHt2 in H2. assumption.
             ++ contradiction.
       --- apply union_iff. apply union_iff in H. inversion H.
           + apply remove_neq_iff in H0. apply IHt1 in H0.
             unfold swap_var in H0. case (y == x) in H0.
             ++ contradiction.
             ++ case (y == y) in H0.
                +++ left. apply remove_neq_iff.
                    * assumption.
                    * assumption.
                +++ contradiction.
             ++ assumption.  
           + apply IHt2 in H0. unfold swap_var in H0.
             case (y == x) in H0.
             ++ contradiction.
             ++ case (y == y) in H0.
                +++ right. assumption.
                +++ contradiction.
       --- apply union_iff. apply union_iff in H. inversion H.
           + apply remove_neq_iff in H0. apply IHt1 in H0.
             unfold swap_var in H0. case (x0 == x) in H0.
             ++ contradiction.
             ++ case (x0 == y) in H0.
                +++ contradiction.
                +++ left. apply remove_neq_iff.
                    * apply aux_not_equal. assumption.
                    * assumption.
             ++ apply aux_not_equal. assumption.  
           + apply IHt2 in H0. unfold swap_var in H0.
             case (x0 == x) in H0.
             ++ contradiction.
             ++ case (x0 == y) in H0.
                +++ contradiction.
                +++ right. assumption. 
       --- apply union_iff. apply union_iff in H. inversion H.
           + apply remove_neq_iff in H0.
             ++ apply IHt1 in H0. unfold swap_var in H0.
                case (x0 == x) in H0.
                +++ contradiction.
                +++ case (x0 == y) in H0.
                    * contradiction.
                    * left. apply remove_neq_iff.
                      ** apply aux_not_equal. assumption.
                      ** assumption.
             ++ apply aux_not_equal. assumption.
           + apply IHt2 in H0. unfold swap_var in H0.
             case (x0 == x) in H0.
             ++ contradiction.
             ++ case (x0 == y) in H0.
                +++ contradiction.
                +++ right. assumption.
       --- apply union_iff. apply union_iff in H. case (x1 == x0).
           + intros. right. inversion H.
             ++ rewrite e in H0. apply remove_iff in H0.
                inversion H0. contradiction.
             ++ apply IHt2 in H0. unfold swap_var in H0.
                case (x0 == x) in H0.
                +++ contradiction.
                +++ case (x0 == y) in H0.
                    * contradiction.
                    * assumption.
           + inversion H.
             ++ intros. apply remove_neq_iff in H0.
                +++ apply IHt1 in H0. unfold swap_var in H0.
                case (x0 == x) in H0.
                    * contradiction.
                    * case (x0 == y) in H0.
                      ** contradiction.
                      ** left. apply remove_neq_iff.
                         *** assumption.
                         *** assumption.
                +++ assumption.
             ++ intros. apply IHt2 in H0. unfold swap_var in H0.
                case (x0 == x) in H0.
                +++ contradiction.
                +++ case (x0 == y) in H0.
                    * contradiction.
                    * right. assumption.
Qed.*)

(* begin hide *)
Lemma swap_remove_reduction: forall x y t,
    remove x (remove y (fv_nom (swap y x t))) [=] remove x (remove y (fv_nom t)).
Proof.
  induction t.
  - rewrite remove_symmetric. simpl. unfold swap_var. default_simp.
    -- repeat rewrite remove_singleton_empty.
       repeat rewrite remove_empty. reflexivity.
    -- rewrite remove_symmetric. rewrite remove_singleton_empty.
       rewrite remove_symmetric. rewrite remove_singleton_empty.
       repeat rewrite remove_empty. reflexivity.
    -- rewrite remove_symmetric. reflexivity.
  - simpl. unfold swap_var. default_simp.
    -- rewrite double_remove. rewrite remove_symmetric.
       rewrite double_remove. rewrite remove_symmetric.
       assumption.
    -- rewrite double_remove. symmetry.
       rewrite remove_symmetric. rewrite double_remove.
       rewrite remove_symmetric. symmetry.
       assumption.
    -- assert (remove y (remove x0 (fv_nom (swap y x t))) [=] remove x0 (remove y (fv_nom (swap y x t)))). {
         rewrite remove_symmetric. reflexivity.
       }
       assert (remove y (remove x0 (fv_nom  t)) [=] remove x0 (remove y (fv_nom t))). {
         rewrite remove_symmetric. reflexivity.
       }
       rewrite H; rewrite H0. rewrite remove_symmetric.
       symmetry. rewrite remove_symmetric. rewrite IHt.
       reflexivity.       
  - simpl. repeat rewrite remove_union_distrib.
    apply Equal_union_compat.
    -- assumption.
    -- assumption.
  - simpl. unfold swap_var. default_simp.
    -- repeat rewrite remove_union_distrib.
       apply Equal_union_compat.
       --- rewrite remove_symmetric. rewrite double_remove.
           rewrite double_remove. rewrite remove_symmetric.
           assumption.
       --- assumption.
    -- repeat rewrite remove_union_distrib.
       apply Equal_union_compat.
       --- rewrite double_remove. symmetry.
           rewrite remove_symmetric.
           rewrite double_remove. rewrite remove_symmetric.
           symmetry. assumption.
       --- assumption.
    -- repeat rewrite remove_union_distrib.
       apply Equal_union_compat.
       --- assert (remove y (remove x0 (fv_nom (swap y x t1))) [=] remove x0 (remove y (fv_nom (swap y x t1)))). {
         rewrite remove_symmetric. reflexivity.
           }
           assert (remove y (remove x0 (fv_nom  t1)) [=] remove x0 (remove y (fv_nom t1))). {
         rewrite remove_symmetric. reflexivity.
           }
           rewrite H; rewrite H0.
           rewrite remove_symmetric. symmetry.
           rewrite remove_symmetric. symmetry.
           rewrite IHt1. reflexivity.
       --- assumption.
Qed.

Lemma remove_fv_swap: forall x y t, x `notin` fv_nom t -> remove x (fv_nom (swap y x t)) [=] remove y (fv_nom t).
Proof.
  (** %\noindent {\bf Proof.}% The proof is by induction on the structure of [t].%\newline% *)
  intros x y t. induction t.
  (** %\noindent%$\bullet$ The first case is when [t] is a variable, say [x0]. By hypothesis [x0 <> x], and we need to show that [remove x (fv_nom (swap y x x0)) [=] remove y (fv_nom x0)]. There are two cases to consider: *)
  - intro Hfv. simpl in *. apply notin_singleton_1 in Hfv. unfold swap_var. case (x0 == y).
    (** If [x0 = y] then both sides of the equality are the empty set, and we are done. *)
    + intro Heq. subst. apply remove_singleton.
    (** If [x0 <> y] then we are also done because both sets are equal to the singleton containing [x0].%\newline% *)
    + intro Hneq. case (x0 == x).
      * intro Heq. contradiction.
      * intro Hneq'. rewrite AtomSetProperties.remove_equal.
        ** rewrite AtomSetProperties.remove_equal.
           *** reflexivity.
           *** apply notin_singleton_2; assumption.
        ** apply notin_singleton_2; assumption.
  (** %\noindent% $\bullet$ If [t] is an abstraction, say [n_abs x0 t] then *)
  - intros Hfv. simpl in *. apply notin_remove_1 in Hfv. destruct Hfv.
    + subst. assert (H: swap_var y x x = y).
      {
        unfold swap_var. destruct (x == y).
        - assumption.
        - rewrite eq_dec_refl. reflexivity.
      }
      rewrite H. rewrite remove_symmetric. rewrite swap_symmetric. apply swap_remove_reduction.
    + unfold swap_var. destruct (x0 == y).
      * subst. repeat rewrite double_remove. apply IHt. assumption.
      * destruct (x0 == x).
        ** subst. rewrite remove_symmetric. rewrite swap_symmetric. apply swap_remove_reduction.
        ** rewrite remove_symmetric. assert (Hr: remove y (remove x0 (fv_nom t)) [=] remove x0 (remove y (fv_nom t))).
           {
           rewrite remove_symmetric. reflexivity.
           }
           rewrite Hr. clear Hr. apply AtomSetProperties.Equal_remove. apply IHt. assumption.
  - intro Hfv. simpl in *. pose proof Hfv as Hfv'. apply notin_union_1 in Hfv'. apply notin_union_2 in Hfv.
    apply IHt1 in Hfv'. apply IHt2 in Hfv. pose proof remove_union_distrib as H1. pose proof H1 as H2.
    specialize (H1 (fv_nom (swap y x t1)) (fv_nom (swap y x t2)) x). specialize (H2 (fv_nom t1) (fv_nom t2) y). rewrite Hfv' in H1. rewrite Hfv in H1. rewrite H1. rewrite H2. reflexivity.
  - intro Hfv. simpl in *. pose proof Hfv as Hfv'. apply notin_union_1 in Hfv'. apply notin_union_2 in Hfv.
    pose proof remove_union_distrib as H1. pose proof H1 as H2.
    specialize (H1 (remove (swap_var y x x0) (fv_nom (swap y x t1))) (fv_nom (swap y x t2)) x). rewrite H1.
    specialize (H2 (remove x0 (fv_nom t1)) (fv_nom t2) y). rewrite H2. apply Equal_union_compat.
    + unfold swap_var. case (x0 == y); intros; subst.
      unfold swap_var in H1. rewrite eq_dec_refl in H1. rewrite double_remove in *. apply IHt2 in Hfv. case (x == y); intros; subst.
      * repeat rewrite swap_id in *. rewrite double_remove. reflexivity.
      * rewrite double_remove. apply IHt1. Search remove. apply diff_remove_2 in Hfv'.
        ** assumption.
        ** assumption.
      * destruct (x0 == x).
        ** subst. rewrite remove_symmetric. rewrite swap_symmetric. apply swap_remove_reduction.
        ** subst. rewrite remove_symmetric. assert (Hr: remove y (remove x0 (fv_nom t1)) [=] remove x0 (remove y (fv_nom t1))).
           {
           rewrite remove_symmetric. reflexivity.
           }
           rewrite Hr. clear Hr. apply AtomSetProperties.Equal_remove. apply IHt1. Search remove. apply diff_remove_2 in Hfv'.
            *** assumption.
            *** auto.
    + apply IHt2. apply Hfv.
Qed.
(* end hide *)

(*        subst. repeat rewrite double_remove. rewrite swap_id. reflexivity.
      * repeat rewrite double_remove. apply IHt. assumption.
    + intro Hneq. case (x0 == x).
      * intro Heq. subst. rewrite swap_remove_reduction. rewrite remove_symmetric. reflexivity.
      * intro Hneq'. rewrite remove_symmetric. symmetry. rewrite remove_symmetric. symmetry.
        apply AtomSetProperties.Equal_remove. apply IHt. simpl in Hfv. apply notin_remove_1 in Hfv. inversion Hfv.
        ** contradiction.
        ** assumption.           
  - intro Hfv. simpl in *. pose proof Hfv as Hfv'. apply notin_union_1 in Hfv'. apply notin_union_2 in Hfv.
    apply IHt1 in Hfv'. apply IHt2 in Hfv. pose proof remove_union_distrib as H1. pose proof H1 as H2.
    specialize (H1 (fv_nom (swap y x t1)) (fv_nom (swap y x t2)) x). specialize (H2 (fv_nom t1) (fv_nom t2) y). rewrite Hfv' in H1. rewrite Hfv in H1. rewrite H1. rewrite H2. reflexivity.
  - intro Hfv. simpl in *. pose proof Hfv as Hfv'. apply notin_union_1 in Hfv'. apply notin_union_2 in Hfv.
    pose proof remove_union_distrib as H1. pose proof H1 as H2.
    specialize (H1 (remove (swap_var y x x0) (fv_nom (swap y x t1))) (fv_nom (swap y x t2)) x). rewrite H1.
    specialize (H2 (remove x0 (fv_nom t1)) (fv_nom t2) y). rewrite H2. apply Equal_union_compat.
    + unfold swap_var. case (x0 == y); intros; subst.
      unfold swap_var in H1. rewrite eq_dec_refl in H1. rewrite double_remove in *. apply IHt2 in Hfv. case (x == y); intros; subst.
      * repeat rewrite swap_id in *. Admitted. *)

(*        
        reflexivity.
      * apply notin_remove_1 in Hfv'. inversion Hfv'; subst.
        ** contradiction.
        ** clear Hfv'. pose proof remove_union_distrib as H3. pose proof H3 as H4.
           specialize (H3 (remove y (fv_nom t1)) (fv_nom (swap y x t2)) x).
           specialize (H4 (remove y (fv_nom t1)) (fv_nom t2) y). rewrite H1. rewrite H2. rewrite double_remove in H4.
           apply diff_remove with x y (fv_nom t1) in n.
           *** apply AtomSetProperties.remove_equal in n.



               rewrite H2 in H4.
               rewrite n in H4; rewrite H4; rewrite H5.
                      reflexivity.
           *** assumption.
       --- contradiction.
  -- case (x0 == x); intros; subst.
     --- unfold swap_var in H0. case (x == y) in H0; intros.
         + contradiction.
         + case (x == x) in H0; intros.
           ++ simpl in H. pose proof H. apply notin_union_1 in H.
              apply notin_union_2 in H2. apply IHt2 in H2.
              rewrite H2 in H0. symmetry. Search "remove_union".
              rewrite remove_union_distrib. symmetry.
              rewrite remove_symmetric.
              rewrite swap_remove_reduction in H0. assumption.
           ++ contradiction.
     --- simpl in H. pose proof H. apply notin_union_1 in H.
         apply notin_remove_1 in H. inversion H; subst.
         + contradiction.
         + apply notin_union_2 in H2.
           apply IHt1 in H3; apply IHt2 in H2.
           unfold swap_var in H0. default_simp.
           rewrite H0. rewrite remove_symmetric.
           rewrite H1; rewrite H2; rewrite H3.
           rewrite remove_symmetric. reflexivity.        
Qed.*)

(* ver necessidade
Lemma fv_nom_swap_eq: forall x y t, x `notin` fv_nom t -> y `notin` fv_nom t -> fv_nom t [=] fv_nom (swap x y t).
Proof.
  induction t using n_sexp_induction.
  - intros H1 H2. simpl in *.
    unfold swap_var. default_simp.
    + apply notin_singleton_is_false in H1. contradiction.
    + apply notin_singleton_is_false in H2. contradiction.     
    + reflexivity.
  - intros H1 H2. simpl in *.
    Admitted. *)

(** The notion of $\alpha$-equivalence is defined as follows: *)

Inductive aeq : n_sexp -> n_sexp -> Prop :=
 | aeq_var : forall x,
     aeq (n_var x) (n_var x)
 | aeq_abs_same : forall x t1 t2,
     aeq t1 t2 -> aeq (n_abs x t1) (n_abs x t2)
 | aeq_abs_diff : forall x y t1 t2,
     x <> y -> x `notin` fv_nom t2 ->
     aeq t1 (swap y x t2) ->
     aeq (n_abs x t1) (n_abs y t2)
 | aeq_app : forall t1 t2 t1' t2',
     aeq t1 t1' -> aeq t2 t2' ->
     aeq (n_app t1 t2) (n_app t1' t2')
 | aeq_sub_same : forall t1 t2 t1' t2' x,
     aeq t1 t1' -> aeq t2 t2' ->
     aeq (n_sub t1 x t2) (n_sub t1' x t2')
 | aeq_sub_diff : forall t1 t2 t1' t2' x y,
     aeq t2 t2' -> x <> y -> x `notin` fv_nom t1' ->
     aeq t1 (swap y x t1') ->
     aeq (n_sub t1 x t2) (n_sub t1' y t2').

(** %\noindent% where ... *)

(* begin hide *)
Hint Constructors aeq.
Notation "t =a u" := (aeq t u) (at level 60).

Example aeq1 : forall x y, x <> y -> (n_abs x (n_var x)) =a (n_abs y (n_var y)).
Proof.
  intros.
  eapply aeq_abs_diff; auto.
  simpl; unfold swap_var; default_simp.
Qed.

Lemma aeq_var_2 : forall x y, (n_var x) =a (n_var y) -> x = y.
Proof.
  intros. inversion H; subst. reflexivity.
Qed.

Lemma aeq_size: forall t1 t2, t1 =a t2 -> size t1 = size t2.
Proof.
  induction 1.
  - reflexivity.
  - simpl. rewrite IHaeq; reflexivity.
  - simpl. rewrite IHaeq. rewrite swap_size_eq. reflexivity.
  - simpl. rewrite IHaeq1. rewrite IHaeq2. reflexivity.
  - simpl. rewrite IHaeq1. rewrite IHaeq2. reflexivity.
  - simpl. rewrite IHaeq1. rewrite IHaeq2. rewrite swap_size_eq. reflexivity.
Qed.

Lemma aeq_refl : forall n, n =a n.
Proof.
  induction n; auto.
Qed.
(* end hide *)

Lemma aeq_fv_nom : forall t1 t2, t1 =a t2 -> fv_nom t1 [=] fv_nom t2.
Proof.
  intros. induction H.
  - reflexivity.
  - simpl. rewrite IHaeq. reflexivity.
  - simpl. inversion H1; subst; rewrite IHaeq; apply remove_fv_swap; assumption.
  - simpl. rewrite IHaeq1; rewrite IHaeq2. reflexivity.
  - simpl. rewrite IHaeq1; rewrite IHaeq2. reflexivity.
  - simpl. pose proof remove_fv_swap.
    specialize (H3 x y t1'). apply H3 in H1.
    inversion H2; subst; rewrite IHaeq1; rewrite IHaeq2; rewrite H1; reflexivity.
Qed.  

Lemma aeq_swap1: forall t1 t2 x y, t1 =a t2 -> (swap x y t1) =a (swap x y t2).
Proof.
  intros. induction H.
  - apply aeq_refl.
  - simpl. unfold swap_var. case (x0 == x); intros; subst.
    -- apply aeq_abs_same. assumption.
    -- case (x0 == y); intros; subst.
       --- apply aeq_abs_same. assumption.
       --- apply aeq_abs_same. assumption.
  - simpl. unfold  swap_var. default_simp.
    -- apply aeq_abs_diff.
       + assumption.
       + apply fv_nom_swap with x y t2 in H0.
         rewrite swap_symmetric. assumption.
       + assert (swap x y t2 = swap y x t2).
         rewrite swap_symmetric; reflexivity.
         rewrite H2. assumption.
    -- apply aeq_abs_diff.
       + apply aux_not_equal. assumption.
       + apply fv_nom_swap with x y t2 in H0.
         rewrite swap_symmetric. assumption.
       + case (x == y); intros; subst.
         ++ repeat rewrite swap_id. repeat rewrite swap_id in IHaeq.
            assumption.
         ++ assert (swap x y t2 = swap y x t2).
            rewrite swap_symmetric; reflexivity.
            rewrite H2. pose proof shuffle_swap.
            pose proof H3.
            specialize (H3 y0 y t2 x).
            rewrite H3.
            +++ specialize (H4 x y0 t2 y).
                assert (swap y0 x (swap y0 y t2) = swap x y0 (swap y0 y t2)). rewrite swap_symmetric; reflexivity.
                rewrite H5.
                rewrite H4.
                * assert (swap y0 x t2 = swap x y0 t2).
                  apply swap_symmetric; reflexivity.
                  rewrite <- H6. assumption.
                * assumption.
                * assumption.
            +++ assumption.       
            +++ apply aux_not_equal. assumption.
    -- apply aeq_abs_diff.
       + apply aux_not_equal; assumption.
       + apply fv_nom_swap with y x t2 in H0. assumption.
       + assert (swap y x (swap x y t2) = swap x y (swap x y t2)).
         rewrite swap_symmetric; reflexivity.
         rewrite H2. assumption. 
    -- apply aeq_abs_diff.
       + apply aux_not_equal; assumption.
       + apply fv_nom_swap. assumption.
       + rewrite shuffle_swap.
         ++ assert (swap y0 y (swap y0 x t2) = swap y y0 (swap y0 x t2)). rewrite swap_symmetric; reflexivity.
            rewrite H2.
            rewrite shuffle_swap.
            +++ assert (swap y x (swap y y0 t2) = swap x y (swap y y0 t2)). rewrite swap_symmetric; reflexivity.
                assert ((swap y y0 t2) = (swap y0 y t2)). rewrite swap_symmetric; reflexivity.
                rewrite H3; rewrite H4.
                assumption.
            +++ assumption.
            +++ assumption.
         ++ assumption.
         ++ apply aux_not_equal; assumption.
    -- apply aeq_abs_diff.
       + assumption.
       + apply fv_nom_remove_swap; assumption.
       + case (x == y); intros; subst.
         ++ repeat rewrite swap_id; repeat rewrite swap_id in IHaeq.
            assumption.
         ++ assert (swap y x0 (swap x y t2) = swap x0 y (swap x y t2)).
            rewrite swap_symmetric; reflexivity.
            rewrite H2.
            assert (swap x y t2 = swap y x t2).
            rewrite swap_symmetric; reflexivity.
            rewrite H3. rewrite shuffle_swap.
            +++ assert (swap x0 x (swap x0 y t2) = swap x x0 (swap x0 y t2)). rewrite swap_symmetric; reflexivity.
            rewrite H4. rewrite shuffle_swap.
                * assumption.
                * assumption.
                * assumption.
            +++ assumption.
            +++ apply aux_not_equal; assumption.        
    -- apply aeq_abs_diff.
       + assumption.
       + apply fv_nom_remove_swap; assumption.
       + assert (swap x x0 (swap x y t2) = swap x0 x (swap x y t2)).
         rewrite swap_symmetric; reflexivity.
         rewrite H2. rewrite shuffle_swap.
         ++ assert (swap x0 y (swap x0 x t2) = swap y x0 (swap x0 x t2)).
            rewrite swap_symmetric; reflexivity.
            rewrite H3; rewrite shuffle_swap.
            +++ assert (swap y x (swap y x0 t2) = swap x y (swap y x0 t2)).
                rewrite swap_symmetric; reflexivity.
                rewrite H4.
                assumption.
            +++ assumption.
            +++ assumption.
         ++ assumption.
         ++ apply aux_not_equal; assumption.     
    -- apply aeq_abs_diff.
       + assumption.
       + apply fv_nom_remove_swap.
         ++ assumption.
         ++ assumption.
         ++ assumption.
       + assert (swap x0 y0 (swap x y t2) = swap x y (swap x0 y0 t2)). {
           rewrite swap_equivariance. unfold swap_var. default_simp.
         }
         assert (swap y0 x0 t2 = swap x0 y0 t2).
         rewrite swap_symmetric; reflexivity.
         assert ((swap y0 x0 (swap x y t2)) = swap x0 y0 (swap x y t2)).
         rewrite swap_symmetric; reflexivity.
         rewrite H3 in IHaeq. rewrite H4.
         rewrite H2. assumption.
  - simpl. apply aeq_app.
    -- assumption.
    -- assumption.
  - simpl. apply aeq_sub_same.
    -- assumption.
    -- assumption.
  - simpl. unfold swap_var. default_simp.
    -- apply aeq_sub_diff.
       --- assumption.
       --- assumption.
       --- apply fv_nom_swap with x y t1' in H1.
           rewrite swap_symmetric. assumption.
       --- assert (swap y x t1' = swap x y t1').
           rewrite swap_symmetric; reflexivity.
           rewrite <- H3. assumption.
    -- apply aeq_sub_diff.
       --- assumption.
       --- apply aux_not_equal; assumption.
       --- rewrite swap_symmetric. apply fv_nom_swap. assumption.
       --- case (x == y); intros; subst.
           + repeat rewrite swap_id.
             repeat rewrite swap_id in IHaeq2. assumption.
           + assert (swap y x t1' = swap x y t1').
             rewrite swap_symmetric; reflexivity.
             rewrite <- H3. rewrite shuffle_swap.
             ++ assert (swap y0 x (swap y0 y t1') = swap x y0 (swap y0 y t1')). rewrite swap_symmetric; reflexivity.
                rewrite H4. rewrite shuffle_swap.
                +++ assert (swap x y0 t1' = swap y0 x t1').
                    rewrite swap_symmetric; reflexivity.
                    rewrite H5. assumption.
                +++ assumption.
                +++ assumption.
             ++ assumption.
             ++ apply aux_not_equal; assumption.
    -- apply aeq_sub_diff.
       --- assumption.
       --- apply aux_not_equal; assumption.
       --- apply fv_nom_swap. assumption.
       --- assert (swap y x (swap x y t1') = swap x y (swap x y t1')).
           rewrite swap_symmetric; reflexivity.
           rewrite H3. rewrite swap_involutive.
           rewrite swap_involutive in IHaeq2. assumption.
    -- apply aeq_sub_diff.
       --- assumption.
       --- apply aux_not_equal; assumption.
       --- apply fv_nom_swap. assumption.
       --- rewrite shuffle_swap.
           + assert (swap y0 y (swap y0 x t1') = swap y y0 (swap y0 x t1')). rewrite swap_symmetric; reflexivity.
             rewrite H3. rewrite shuffle_swap.
             ++ assert (swap y x (swap y y0 t1') = swap x y(swap y y0 t1')).
                rewrite swap_symmetric; reflexivity.
                rewrite H4.
                assert (swap y0 y t1' = swap y y0 t1').
                rewrite swap_symmetric; reflexivity.
                rewrite <- H5. assumption.
             ++ assumption.
             ++ assumption.
           + assumption.
           + apply aux_not_equal; assumption.
    -- apply aeq_sub_diff.
       --- assumption.
       --- assumption.
       --- apply fv_nom_remove_swap.
           + assumption.
           + assumption.
           + assumption.
       --- case (x == y); intros; subst.
           + repeat rewrite swap_id.
             repeat rewrite swap_id in IHaeq2.
             assumption.
           + assert (swap y x0 (swap x y t1') = swap x0 y (swap x y t1')).
             rewrite swap_symmetric; reflexivity.
             rewrite H3.
             assert (swap x y t1' = swap y x t1').
             rewrite swap_symmetric; reflexivity.
             rewrite H4. rewrite shuffle_swap.
             ++ assert (swap x0 x (swap x0 y t1') = swap x x0 (swap x0 y t1')). rewrite swap_symmetric; reflexivity.
                rewrite H5. rewrite shuffle_swap.
                * assumption.
                * assumption.
                * assumption.
             ++ assumption.
             ++ apply aux_not_equal; assumption.
    -- apply aeq_sub_diff.
       --- assumption.
       --- assumption.
       --- apply fv_nom_remove_swap.
           + assumption.
           + assumption.
           + assumption.
       --- assert (swap x x0 (swap x y t1') = swap x0 x (swap x y t1')).
           rewrite swap_symmetric; reflexivity.
           rewrite H3. rewrite shuffle_swap.
           + assert (swap x0 y (swap x0 x t1') = swap y x0 (swap x0 x t1')).
             rewrite swap_symmetric; reflexivity.
             rewrite H4; rewrite shuffle_swap.
             ++ assert (swap y x (swap y x0 t1') = swap x y (swap y x0 t1')).
                rewrite swap_symmetric; reflexivity.
                rewrite H5. assumption.
             ++ assumption.
             ++ assumption.
           + assumption.
           + apply aux_not_equal; assumption.
    -- apply aeq_sub_diff.
       --- assumption.
       --- assumption.
       --- apply fv_nom_remove_swap.
           + assumption.
           + assumption.
           + assumption.
       --- case (x == y); intros; subst.
           + repeat rewrite swap_id.
             repeat rewrite swap_id in IHaeq2.
             assumption.
           + assert (swap x0 y0 (swap x y t1') = swap x y (swap x0 y0 t1')). {
           rewrite swap_equivariance. unfold swap_var. default_simp.
         }
         assert (swap y0 x0 t1' = swap x0 y0 t1').
         rewrite swap_symmetric; reflexivity.
         assert ((swap y0 x0 (swap x y t1')) = swap x0 y0 (swap x y t1')).
         rewrite swap_symmetric; reflexivity.
         rewrite H4 in IHaeq2. rewrite H5.
         rewrite H3. assumption.
Qed.

Lemma aeq_swap2: forall t1 t2 x y, (swap x y t1) =a (swap x y t2) -> t1 =a t2.
Proof.
  induction t1.
  - intros. induction t2.
    -- simpl in H. unfold swap_var in H. default_simp.
    -- simpl in H. inversion H.
    -- simpl in H. inversion H.
    -- simpl in H. inversion H.
  - intros. induction t2.
    -- simpl in H. inversion H.
    -- simpl in H. inversion H.
       --- unfold swap_var in *. default_simp.
           + specialize (IHt1 t2 x0 y). apply aeq_abs_same.
             apply IHt1. assumption.
           + specialize (IHt1 t2 x0 y). apply aeq_abs_same.
             apply IHt1. assumption.
           + specialize (IHt1 t2 x0 y). apply aeq_abs_same.
             apply IHt1. assumption.
       --- unfold swap_var in *. default_simp.
           + apply aeq_abs_diff.
             ++ assumption.
             ++ apply fv_nom_swap_2 with x0.
                rewrite swap_symmetric; assumption.
             ++ specialize (IHt1 (swap x0 y t2) x0 y).
                apply IHt1.
                assert (swap x0 y (swap x0 y t2) = swap y x0 (swap x0 y t2)).
                rewrite swap_symmetric; reflexivity.
                rewrite H0. assumption.
           + apply aeq_abs_diff.
             ++ assumption.
             ++ apply fv_nom_swap_remove with x0 y.
                +++ assumption.
                +++ assumption.
                +++ rewrite swap_symmetric; assumption.
             ++ specialize (IHt1 (swap x0 x t2) x0 y).
                apply IHt1.
                assert (swap x0 y (swap x0 x t2) = swap y x0 (swap x0 x t2)).
                rewrite swap_symmetric; reflexivity.
                rewrite H0. rewrite shuffle_swap.
                +++ assert (swap x0 y t2 = swap y x0 t2).
                    rewrite swap_symmetric; reflexivity.
                    rewrite <- H1. assumption.
                +++ apply aux_not_equal; assumption.
                +++ apply aux_not_equal; assumption.
           + apply aeq_abs_diff.
             ++ apply aux_not_equal; assumption.
             ++ apply fv_nom_swap_2 with y. assumption.
             ++ specialize (IHt1 (swap y x0 t2) x0 y).
                apply IHt1.
                assert (swap y x0 t2 = swap x0 y t2).
                rewrite swap_symmetric; reflexivity.
                rewrite H0. assumption.
           + apply aeq_abs_diff.
             ++ assumption.
             ++ apply fv_nom_swap_remove with x0 y.
                +++ assumption.
                +++ assumption.
                +++ rewrite swap_symmetric; assumption.
             ++ specialize (IHt1 (swap y x t2) x0 y).
                apply IHt1. rewrite shuffle_swap.
                +++ assumption.
                +++ apply aux_not_equal; assumption.
                +++ apply aux_not_equal; assumption.
           + apply aeq_abs_diff.
             ++ apply aux_not_equal. assumption.
             ++ apply fv_nom_swap_2 with y. assumption.
             ++ specialize (IHt1 (swap x1 x0 t2) x0 y).
                apply IHt1.
                assert (swap x0 y (swap x1 x0 t2) = swap y x0 (swap x1 x0 t2)).
                rewrite swap_symmetric; reflexivity.
                rewrite H0.
                assert (swap x1 x0 t2 = swap x0 x1 t2).
                rewrite swap_symmetric; reflexivity.
                rewrite H1. rewrite shuffle_swap.
                +++ assert (swap x1 y (swap y x0 t2) = swap y x1 (swap y x0 t2)).
                    rewrite swap_symmetric; reflexivity.
                    rewrite <- H2.
                    assert (swap y x0 t2 = swap x0 y t2).
                    rewrite swap_symmetric; reflexivity.
                    rewrite H3. assumption.
                +++ apply aux_not_equal; assumption.
                +++ apply aux_not_equal; assumption.
           + apply aeq_abs_diff.
             ++ apply aux_not_equal. assumption.
             ++ apply fv_nom_swap_2 with x0.
                rewrite swap_symmetric; assumption.
             ++ specialize (IHt1 (swap x1 y t2) x0 y).
                apply IHt1.
                assert (swap x1 y t2 = swap y x1 t2).
                rewrite swap_symmetric; reflexivity.
                rewrite H0. rewrite shuffle_swap.
                +++ assert (swap x0 x1 (swap x0 y t2) = swap x1 x0 (swap x0 y t2)).
                    rewrite swap_symmetric; reflexivity.
                    rewrite H1. assumption.
                +++ apply aux_not_equal; assumption.
                +++ apply aux_not_equal; assumption.
           + apply aeq_abs_diff.
             ++ assumption.
             ++ apply fv_nom_swap_remove with x0 y.
                +++ assumption.
                +++ assumption.
                +++ rewrite swap_symmetric; assumption.
             ++ specialize (IHt1 (swap x1 x t2) x0 y).
                apply IHt1. rewrite swap_symmetric_2.
                +++ assumption.
                +++ apply aux_not_equal; assumption.
                +++ apply aux_not_equal; assumption.
                +++ apply aux_not_equal; assumption.
                +++ apply aux_not_equal; assumption.
    -- simpl in H. inversion H.
    -- simpl in H. inversion H.
  - intros. induction t2.
    -- simpl in H. inversion H.
    -- simpl in H. inversion H.
    -- simpl in H. inversion H.
       apply aeq_app.
       --- apply IHt1_1 with x y. assumption.
       --- apply IHt1_2 with x y. assumption.
    -- simpl in H. inversion H.
  - intros. induction t2.
    -- simpl in H. inversion H.
    -- simpl in H. inversion H.
    -- simpl in H. inversion H.
    -- simpl in H. inversion H.
       --- simpl in *; unfold swap_var in *. default_simp.
           + apply aeq_sub_same.
             ++ apply IHt1_1 with x0 y. assumption.
             ++ apply IHt1_2 with x0 y. assumption.
           + apply aeq_sub_same.
             ++ apply IHt1_1 with x0 y. assumption.
             ++ apply IHt1_2 with x0 y. assumption.
           + apply aeq_sub_same.
             ++ apply IHt1_1 with x0 y. assumption.
             ++ apply IHt1_2 with x0 y. assumption.
       --- simpl in *; unfold swap_var in *. default_simp.
           + apply aeq_sub_diff.
             ++ apply IHt1_2 with x0 y. assumption.
             ++ assumption.
             ++ apply fv_nom_swap_2 with x0.
                rewrite swap_symmetric; assumption.
             ++ apply IHt1_1 with x0 y.
                assert (swap y x0 (swap x0 y t2_1) = swap x0 y (swap x0 y t2_1)).
                rewrite swap_symmetric; reflexivity.
                rewrite <- H0. assumption.
           + apply aeq_sub_diff.
             ++ apply IHt1_2 with x0 y. assumption.
             ++ assumption.
             ++ apply fv_nom_swap_remove with x0 y.
                +++ assumption.
                +++ assumption.
                +++ rewrite swap_symmetric; assumption.
             ++ apply IHt1_1 with x0 y.
                assert (swap x0 y (swap x0 x t2_1) = swap y x0 (swap x0 x t2_1)).
                rewrite swap_symmetric; reflexivity.
                rewrite H0. rewrite shuffle_swap.
                +++ assert (swap y x0 t2_1 = swap x0 y t2_1).
                    rewrite swap_symmetric; reflexivity.
                    rewrite H1. assumption.
                +++ apply aux_not_equal; assumption.
                +++ apply aux_not_equal; assumption.
           + apply aeq_sub_diff.
             ++ apply IHt1_2 with x0 y. assumption.
             ++ apply aux_not_equal; assumption.
             ++ apply fv_nom_swap_2 with y. assumption.
             ++ apply IHt1_1 with x0 y.
                assert (swap y x0 t2_1 = swap x0 y t2_1).
                rewrite swap_symmetric; reflexivity.
                rewrite H0. assumption.
           + apply aeq_sub_diff.
             ++ apply IHt1_2 with x0 y. assumption.
             ++ assumption.
             ++ apply fv_nom_swap_remove with x0 y.
                +++ assumption.
                +++ assumption.
                +++ rewrite swap_symmetric; assumption.
             ++ specialize (IHt1_1 (swap y x t2_1) x0 y).
                apply IHt1_1. rewrite shuffle_swap.
                +++ assumption.
                +++ apply aux_not_equal; assumption.
                +++ apply aux_not_equal; assumption.
           + apply aeq_sub_diff.
             ++ apply IHt1_2 with x0 y. assumption.
             ++ apply aux_not_equal. assumption.
             ++ apply fv_nom_swap_2 with y. assumption.
             ++ specialize (IHt1_1 (swap x1 x0 t2_1) x0 y).
                apply IHt1_1.
                assert (swap x0 y (swap x1 x0 t2_1) = swap y x0 (swap x1 x0 t2_1)).
                rewrite swap_symmetric; reflexivity.
                rewrite H0.
                assert (swap x1 x0 t2_1 = swap x0 x1 t2_1).
                rewrite swap_symmetric; reflexivity.
                rewrite H1. rewrite shuffle_swap.
                +++ assert (swap x1 y (swap y x0 t2_1) = swap y x1 (swap y x0 t2_1)).
                    rewrite swap_symmetric; reflexivity.
                    rewrite <- H2.
                    assert (swap y x0 t2_1 = swap x0 y t2_1).
                    rewrite swap_symmetric; reflexivity.
                    rewrite H3. assumption.
                +++ apply aux_not_equal; assumption.
                +++ apply aux_not_equal; assumption.
           + apply aeq_sub_diff.
             ++ apply IHt1_2 with x0 y. assumption.
             ++ apply aux_not_equal. assumption.
             ++ apply fv_nom_swap_2 with x0.
                rewrite swap_symmetric; assumption.
             ++ specialize (IHt1_1 (swap x1 y t2_1) x0 y).
                apply IHt1_1.
                assert (swap x1 y t2_1 = swap y x1 t2_1).
                rewrite swap_symmetric; reflexivity.
                rewrite H0. rewrite shuffle_swap.
                +++ assert (swap x0 x1 (swap x0 y t2_1) = swap x1 x0 (swap x0 y t2_1)).
                    rewrite swap_symmetric; reflexivity.
                    rewrite H1. assumption.
                +++ apply aux_not_equal; assumption.
                +++ apply aux_not_equal; assumption.
           + apply aeq_sub_diff.
             ++ apply IHt1_2 with x0 y. assumption.
             ++ assumption.
             ++ apply fv_nom_swap_remove with x0 y.
                +++ assumption.
                +++ assumption.
                +++ rewrite swap_symmetric; assumption.
             ++ specialize (IHt1_1 (swap x1 x t2_1) x0 y).
                apply IHt1_1. rewrite swap_symmetric_2.
                +++ assumption.
                +++ apply aux_not_equal; assumption.
                +++ apply aux_not_equal; assumption.
                +++ apply aux_not_equal; assumption.
                +++ apply aux_not_equal; assumption.
Qed.

Corollary aeq_swap: forall t1 t2 x y, t1 =a t2 <-> (swap x y t1) =a (swap x y t2).
Proof.
  intros. split.
  - apply aeq_swap1.
  - apply aeq_swap2.
Qed.

Lemma aeq_abs: forall t x y, y `notin` fv_nom t -> (n_abs y (swap x y t)) =a (n_abs x t).
Proof.
  intros. case (x == y); intros; subst.
  - rewrite swap_id. apply aeq_refl.
  - apply aeq_abs_diff.
    -- apply aux_not_equal. assumption.
    -- assumption.
    -- apply aeq_refl.
Qed.

Lemma swap_reduction: forall t x y,
    x `notin` fv_nom t -> y `notin` fv_nom t -> (swap x y t) =a  t.
Proof.
  induction t.
  - intros x' y H1 H2.
    simpl.
    unfold swap_var.
    destruct (x == x'); subst.
    + apply notin_singleton_is_false in H1.
      contradiction.
    + destruct (x == y); subst.
      * apply notin_singleton_is_false in H2.
        contradiction. 
      * apply aeq_refl.
  - intros x' y H1 H2.
    simpl in *.
    unfold swap_var.
    apply notin_remove_1 in H1.
    apply notin_remove_1 in H2.
    destruct H1.
    + destruct (x == x').
      * subst.
        destruct H2.
        ** subst.
           rewrite swap_id.
           apply aeq_refl.
        ** apply aeq_abs; assumption.
      * contradiction.
    + destruct (x == x').
      * subst.
        destruct H2.
        ** subst.
           rewrite swap_id.
           apply aeq_refl.
        ** apply aeq_abs; assumption.
      * destruct H2.
        ** subst. rewrite eq_dec_refl.
           rewrite swap_symmetric.
           apply aeq_abs; assumption.
        ** destruct (x == y).
           *** subst.
               rewrite swap_symmetric.
               apply aeq_abs; assumption.
           *** apply aeq_abs_same.
               apply IHt; assumption.
  - intros x y H1 H2.
    simpl in *.
    assert (H1' := H1).
    apply notin_union_1 in H1.
    apply notin_union_2 in H1'.
    assert (H2' := H2).
    apply notin_union_1 in H2.
    apply notin_union_2 in H2'.
    apply aeq_app.
    + apply IHt1; assumption.
    + apply IHt2; assumption.
  - intros x' y H1 H2.
    simpl in *.
    assert (H1' := H1).
    apply notin_union_1 in H1.
    apply notin_union_2 in H1'.
    assert (H2' := H2).
    apply notin_union_1 in H2.
    apply notin_union_2 in H2'.
    apply notin_remove_1 in H1.
    apply notin_remove_1 in H2.
    unfold swap_var.
    destruct H1.
    + subst. rewrite eq_dec_refl. destruct H2.
      * subst. repeat rewrite swap_id. apply aeq_refl.
      * case (x' == y); intros; subst.
        ** repeat rewrite swap_id. apply aeq_refl.
        ** apply aeq_sub_diff.
           *** apply IHt2; assumption.
           *** apply aux_not_equal; assumption.
           *** assumption.
           *** apply aeq_refl.
    + destruct (x == x').
      * subst.
        destruct H2.
        ** subst.
           repeat rewrite swap_id.
           apply aeq_refl.
        ** case (x' == y); intros; subst.
           *** repeat rewrite swap_id. apply aeq_refl.
           *** apply aeq_sub_diff.
           **** apply IHt2; assumption.
           **** apply aux_not_equal; assumption.
           **** assumption.
           **** apply aeq_refl.
      * destruct H2.
        ** subst. rewrite eq_dec_refl. rewrite swap_symmetric.
               replace (swap x' y t2) with (swap y x' t2).
               **** apply aeq_sub_diff.
               ***** apply IHt2; assumption.
               ***** apply aux_not_equal; assumption.
               ***** assumption.
               ***** apply aeq_refl.
               **** apply swap_symmetric.             
        ** destruct (x == y).
           *** subst.
               rewrite swap_symmetric.
               replace (swap x' y t2) with (swap y x' t2).
               **** apply aeq_sub_diff.
               ***** apply IHt2; assumption.
               ***** apply aux_not_equal; assumption.
               ***** assumption.
               ***** apply aeq_refl.
               **** apply swap_symmetric.
           *** rewrite swap_symmetric.
               replace (swap x' y t2) with (swap y x' t2).
               **** apply aeq_sub_same.
                    ***** apply IHt1; assumption.
                    ***** apply IHt2; assumption.
               **** apply swap_symmetric.
Qed.

Lemma aeq_swap_swap: forall t x y z, z `notin` fv_nom t -> x `notin` fv_nom t -> (swap z x (swap x y t)) =a (swap z y t).
Proof.
  intros. case (x == z); intros; subst.
  - rewrite swap_id; apply aeq_refl.
  - case (y == z); intros; subst.
    -- replace (swap x z t) with (swap z x t).
       --- rewrite swap_involutive; rewrite swap_id. apply aeq_refl.
       --- rewrite swap_symmetric; reflexivity.
    -- case (x == y); intros; subst.
       --- rewrite swap_id; apply aeq_refl.
       --- rewrite shuffle_swap.
           + apply aeq_swap. apply swap_reduction; assumption.
           + apply aux_not_equal; assumption.
           + assumption.
Qed.

Lemma aeq_sym: forall t1 t2, t1 =a t2 -> t2 =a t1.
Proof.
  induction 1.
  - apply aeq_refl.
  - apply aeq_abs_same; assumption.
  - apply aeq_abs_diff.
    -- apply aux_not_equal; assumption.
    -- apply fv_nom_swap with x y t2 in H0.
       apply aeq_fv_nom in H1.
       rewrite H1; assumption.
    -- apply aeq_swap2 with x y.
       rewrite swap_involutive.
       rewrite swap_symmetric.
       assumption.
  - apply aeq_app; assumption.
  - apply aeq_sub_same; assumption.
  - apply aeq_sub_diff.
    -- assumption.
    -- apply aux_not_equal. assumption.
    -- apply aeq_fv_nom in H2. rewrite H2.
       apply fv_nom_swap. assumption.
    -- rewrite swap_symmetric. apply aeq_swap2 with y x.
       rewrite swap_involutive. assumption.
Qed.

Lemma aeq_trans: forall t1 t2 t3, t1 =a t2 -> t2 =a t3 -> t1 =a t3.
Proof.
  induction t1 using n_sexp_induction.
  - intros t2 t3 H1 H2. inversion H1; subst. assumption.
  - intros t2 t3 H1 H2. inversion H1; subst.
    + inversion H2; subst.
      * apply aeq_abs_same. replace t1 with (swap z z t1).
        ** apply H with t4.
           *** reflexivity.
           *** rewrite swap_id; assumption.
           *** assumption.
        ** apply swap_id.
      * apply aeq_abs_diff.
        ** assumption.
       ** assumption.
        ** apply aeq_sym.
           apply H with t4.
           *** apply eq_trans with (size t4).
               **** apply aeq_size in H8.
                    rewrite swap_size_eq in H8.
                    symmetry; assumption.
               **** apply aeq_size in H5.
                    symmetry; assumption.
           *** apply aeq_sym; assumption.
           *** apply aeq_sym; assumption.
    + inversion H2; subst.
      * apply aeq_abs_diff.
        ** assumption.
        ** apply aeq_fv_nom in H8.
           rewrite <- H8; assumption.
        ** apply aeq_sym.
           apply H with (swap y z t4).
           *** apply eq_trans with (size t4).
               **** apply aeq_size in H8.
                    symmetry; assumption.
               **** apply aeq_size in H7.
                    rewrite H7.
                    rewrite swap_size_eq.
                    reflexivity.
           *** apply aeq_sym.
               apply aeq_swap1; assumption.
           *** apply aeq_sym; assumption.
      * case (z == y0).
        ** intro Heq; subst.
           apply aeq_abs_same.
           apply aeq_swap1 with t4 (swap y0 y t2) y0 y in H10.
           rewrite swap_involutive in H10.
           apply aeq_sym.
           replace t2 with (swap y y t2).
           *** apply H with (swap y0 y t4).
               **** apply aeq_size in H7.
                    rewrite  H7.
                    apply aeq_size in H10.
                    rewrite <- H10.
                    rewrite swap_symmetric.
                    reflexivity.
               **** apply aeq_sym.
                    rewrite swap_id; assumption.
               **** apply aeq_sym.
                    rewrite swap_symmetric; assumption.
           *** apply swap_id.             
        ** intro Hneq.
           apply aeq_fv_nom in H10.
           assert (H5' := H5).
           rewrite H10 in H5'.
           apply fv_nom_swap_remove in H5'.           
           *** apply aeq_abs_diff.
               **** assumption.
               **** assumption.
               **** apply aeq_sym.
                    apply H with (swap z y t4).
                    ***** inversion H2; inversion H1; subst.
                    ****** apply aeq_size in H3.
                           apply aeq_size in H14.
                           rewrite <- H3; rewrite H14.
                           reflexivity.
                    ****** apply aeq_size in H3.
                           apply aeq_size in H19.
                           rewrite swap_size_eq in H19.
                           rewrite <- H3; rewrite H19.
                           reflexivity.
                    ****** apply aeq_size in H14.
                           apply aeq_size in H16.
                           rewrite swap_size_eq in H14.
                           rewrite <- H14; rewrite H16.
                           reflexivity.
                    ****** apply aeq_size in H14.
                           apply aeq_size in H21.
                           rewrite swap_size_eq in H14.
                           rewrite swap_size_eq in H21.
                           rewrite <- H14; rewrite H21.
                           reflexivity. 
                    ***** replace (swap z y t4) with (swap y z t4).
                          ****** inversion H2; subst.
                                 ******* apply aeq_sym.
                                         apply aeq_swap1; assumption.
                                 ******* apply aeq_sym.
                                         apply aeq_swap2 with y z.
                                         rewrite swap_involutive.
                                         apply aeq_sym.
                                         apply H with (swap y0 y t2).
                                         ******** rewrite swap_size_eq.
                                         apply aeq_size in H7.
                                         rewrite swap_size_eq in H7.
                                         inversion H2; subst.
                                         ********* apply aeq_size in H3.
                                                   rewrite H7; rewrite <- H3.
                                                   reflexivity.
                                         ********* apply aeq_size in H17. rewrite swap_size_eq in H17.
                                                   rewrite H7; rewrite <- H17. reflexivity.
                                         ******** replace (swap y0 z t2) with (swap z y0 t2).
                                                  ********* replace (swap y0 y t2) with (swap y y0 t2). 
                                                            ********** apply aeq_swap_swap; assumption.
                                                            ********** apply swap_symmetric.
                                                  ********* apply swap_symmetric.

                                         ******** apply aeq_sym; assumption.
                        ****** apply swap_symmetric.
                  ***** rewrite swap_symmetric.
                        apply aeq_sym; assumption.
           *** assumption.
           *** assumption.
  - intros. inversion H; subst. inversion H0; subst.
    apply aeq_app.
    -- specialize (IHt1_1 t1' t1'0). apply IHt1_1 in H3.
       --- assumption.
       --- assumption.
    -- specialize (IHt1_2 t2' t2'0). apply IHt1_2 in H5.
       --- assumption.
       --- assumption.
  - intros. inversion H0; subst.
    -- inversion H1; subst.
       --- apply aeq_sub_same.
           + specialize (H t1_1 z z).
             assert (size t1_1 = size t1_1). reflexivity.
             apply H with t1' t1'0 in H2; clear H.
             ++ rewrite swap_id in H2. assumption.
             ++ rewrite swap_id. assumption.
             ++ assumption.
           + specialize (IHt1_1 t2' t2'0). apply IHt1_1.
             ++ assumption.
             ++ assumption.
       --- apply aeq_sub_diff.
           + specialize (H t1'0 y z).
             assert (size t1_1 = size t1'0). {
               apply aeq_size in H6; apply aeq_size in H11.
               rewrite swap_size_eq in H11. rewrite <- H11.
               assumption.
             }
             symmetry in H2.
             apply H with t1' (swap y z t1'0) in H2.
             ++ specialize (IHt1_1 t2' t2'0). apply IHt1_1.
                +++ assumption.
                +++ assumption.
             ++ apply H with (swap y z t1'0) t1' in H2.
                +++ assumption.
                +++ apply aeq_refl.
                +++ apply aeq_sym. assumption.
             ++ assumption.
           + assumption.
           + assumption.
           + specialize (H (swap y z t1_1) y z).
             rewrite swap_size_eq in H.
             assert (size t1_1 = size t1_1). reflexivity.
             apply H with t1' (swap y z t1'0) in H2; clear H.
             ++ rewrite swap_involutive in H2. assumption.
             ++ rewrite swap_involutive. assumption.
             ++ assumption.
    -- inversion H1; subst.            
       --- apply aeq_sub_diff.
           + specialize (IHt1_1 t2' t2'0). apply IHt1_1.
             ++ assumption.
             ++ assumption.
           + assumption.
           + apply aeq_fv_nom in H10. rewrite H10 in H8.
             assumption.
           + specialize (H (swap y z t1_1) y z).
             assert (size (swap y z t1_1) = size t1_1).
             rewrite swap_size_eq; reflexivity.
             apply H with (swap y z t1') (swap y z t1'0) in H2.
             ++ rewrite swap_involutive in H2. assumption.
             ++ rewrite swap_involutive. assumption.
             ++ apply aeq_swap. assumption.     
       --- case (z == y0); intros; subst.
           + apply aeq_sub_same.
             specialize (H t1_1 y0 y).
             assert (size t1_1 = size t1_1). reflexivity.
             apply aeq_swap2 with y0 y.
             apply H with (swap y y0 (swap y y0 t1')) (swap y y0 t1'0) in H2.
             ++ apply aeq_sym; rewrite swap_symmetric; apply aeq_sym.
                assumption.
             ++ rewrite swap_involutive. apply aeq_swap2 with y y0.
                rewrite swap_symmetric. rewrite swap_involutive.
                assumption.
             ++ rewrite swap_involutive. rewrite swap_symmetric.
                assumption.
             ++ specialize (IHt1_1 t2' t2'0). apply IHt1_1.
                +++ assumption.
                +++ assumption.
           + apply aeq_sub_diff.
             ++ specialize (IHt1_1 t2' t2'0). apply IHt1_1.
                +++ assumption.
                +++ assumption.
             ++ assumption.
             ++ apply aeq_fv_nom in H13.
                rewrite H13 in H8.
                apply fv_nom_swap_remove in H8.
                +++ assumption.
                +++ assumption.
                +++ assumption.
             ++ pose proof H as H'. specialize (H t1_1 y0 z).
                assert (size t1_1 = size t1_1). reflexivity.
                apply H with (swap y0 z (swap y z t1')) t1'0 in H2.
                +++ apply aeq_swap2 with y0 z.
                    rewrite swap_involutive. assumption.
                +++ apply aeq_swap1. assumption.
                +++ pose proof H13.
                    apply aeq_swap1 with t1' (swap y0 y t1'0) y0 y in H3.
                    rewrite swap_involutive in H3.
                    apply aeq_fv_nom in H3.
                    rewrite <- H3 in H12.
                    apply fv_nom_swap_2 in H12.
                    pose proof swap_reduction.
                    specialize (H4 t1' y0 z).
                    apply aeq_sym in H4.
                    * specialize (H' (swap y z t1') y0 z).
                      assert (size (swap y z t1') = size t1_1).
                      apply aeq_size in H9; rewrite H9; reflexivity.
                      apply H' with (swap y y0 t1') t1'0 in H11.
                      ** assumption.
                      ** assert (swap y z t1' = swap z y t1').
                         rewrite swap_symmetric; reflexivity.
                         rewrite H14.
                         rewrite shuffle_swap.
                         *** rewrite swap_symmetric.
                             apply aeq_swap.
                             apply aeq_sym.
                             assumption.
                         *** apply aux_not_equal; assumption.
                         *** assumption.
                      ** apply aeq_swap2 with y y0.
                         rewrite swap_involutive.
                         rewrite swap_symmetric.
                         assumption.
                    * assumption.
                    * assumption.
Qed.                 


(*
Lemma swap_comp : forall x y z t, x `notin` fv_nom t -> y `notin` fv_nom t ->
    (swap x y (swap y z t)) =a (swap x z t).
Proof.
  induction t.
  - intros H1 H2. simpl. destruct (x0 == z). 
    + subst. destruct (x == z). 
      * subst. destruct (y == z).
        ** subst. unfold swap_var. rewrite eq_dec_refl. rewrite eq_dec_refl. apply aeq_refl.
        ** unfold swap_var. rewrite eq_dec_refl. destruct (z == y).
            *** rewrite eq_dec_refl. subst. apply aeq_refl.
            *** destruct (y == z). 
                **** contradiction.
                **** rewrite eq_dec_refl. apply aeq_refl.
      * unfold swap_var. destruct (z == y).
        ** destruct (z == x). 
            *** subst. contradiction.
            *** subst. rewrite eq_dec_refl. apply aeq_refl.
        ** rewrite eq_dec_refl. 
            *** destruct (y == x).
                **** subst. destruct (z == x).
                      ***** contradiction.
                      ***** apply aeq_refl.
                **** rewrite eq_dec_refl. destruct (z == x).
                      ***** subst. apply aeq_refl.
                      ***** apply aeq_refl.
    + unfold swap_var. destruct (x0 == y).
      * subst. destruct (z == x). 
        ** subst. destruct (y == x). 
            *** subst. contradiction.
            *** apply aeq_refl.
        ** destruct (z == y).
            *** subst. destruct (y == x). 
                **** contradiction.
                **** rewrite eq_dec_refl. apply aeq_refl.
            *** destruct (y == x). 
                **** apply aeq_refl.
                **** destruct (y == z).
                      ***** subst. contradiction.
                      ***** simpl in H2. apply notin_singleton_is_false in H2. exfalso. assumption.
      * destruct (x0 == z). 
        ** subst. destruct (y == x). 
            *** subst. contradiction.
            *** rewrite eq_dec_refl. destruct (z == x).
                **** subst. contradiction.
                **** contradiction.
        ** destruct (x0 == x).
            *** subst. apply notin_singleton_is_false in H1. exfalso. assumption.
            *** subst. destruct (x0 == y). 
                **** subst. contradiction.
                **** apply aeq_refl.
  - intros H1 H2. simpl in *. apply notin_remove_1 in H1.  apply notin_remove_1 in H2. destruct H1.
    + subst.
    + Admitted.

    unfold swap_var. destruct (x0 == z). 
    + destruct (x0 == y). 
      * subst. destruct (y == x). 
        ** subst. repeat rewrite swap_id. apply aeq_refl.
        ** rewrite eq_dec_refl. apply aeq_abs_same. apply IHt.
          *** admit.
          *** admit.
      * subst. destruct (y == x). 
        ** destruct (z == x).
          *** subst. repeat rewrite swap_id. apply aeq_refl.
          *** subst. repeat rewrite swap_id. apply aeq_refl.
        ** rewrite eq_dec_refl. destruct (z == x).
          *** subst. apply aeq_abs_same. apply IHt.
              **** admit.
              **** admit.
          *** apply aeq_abs_same. apply IHt.
              **** admit.
              **** admit.
    + destruct (x0 == y). 
      * subst. destruct (y == x). 
        ** subst. destruct (z == x).
          *** subst. contradiction.
          *** rewrite swap_id. apply aeq_refl.
        ** destruct (z == x). 
          *** subst. apply aeq_abs_same. apply IHt.
              **** admit.
              **** admit.
          *** destruct (z == y). 
              **** subst. contradiction.
              **** admit.
      * destruct (x0 == x).
        ** subst. admit.
        ** destruct (x0 == y).
          *** subst. contradiction.
          *** apply aeq_abs_same. apply IHt.
              **** admit.
              **** admit.
   - intros H1 H2. simpl. apply aeq_app.
    + apply IHt1. 
      * simpl in H1. apply notin_union_1 in H1. assumption.
      * simpl in H2. apply notin_union_1 in H2. assumption.
    + apply IHt2. 
      * simpl in H1. apply notin_union_2 in H1. assumption.
      * simpl in H2. apply notin_union_2 in H2. assumption.
  - intros H1 H2. simpl. admit.

Admitted. *)

Require Import Setoid Morphisms.

Instance Equivalence_aeq: Equivalence aeq.
Proof.
  split.
  - unfold Reflexive. apply aeq_refl.
  - unfold Symmetric. apply aeq_sym.
  - unfold Transitive. apply aeq_trans.
Qed.

(*
Lemma aeq_same_abs: forall x t1 t2,
    aeq (n_abs x t1) (n_abs x t2) -> aeq t1 t2.
Proof.
  intros. inversion H.
  - assumption.
  - rewrite swap_id in H6; assumption.
Qed.

Lemma aeq_diff_abs: forall x y t1 t2,
    aeq (n_abs x t1) (n_abs y t2) -> aeq t1 (swap x y t2).
Proof.
  intros. inversion H; subst.
  - rewrite swap_id; assumption.
  - rewrite swap_symmetric; assumption.
Qed.

Lemma aeq_same_sub: forall x t1 t1' t2 t2',
    aeq (n_sub t1 x t2) (n_sub t1' x t2') -> aeq t1 t1' /\ aeq t2 t2'.
Proof.
  intros. inversion H; subst.
  - split; assumption.
  - split.
    + rewrite swap_id in H9; assumption.
    + assumption.
Qed.

Lemma aeq_diff_sub: forall x y t1 t1' t2 t2',
    aeq (n_sub t1 x t2) (n_sub t1' y t2') -> aeq t1 (swap x y t1') /\ aeq t2 t2'.
Proof.
  intros. inversion H; subst.
  - split.
    + rewrite swap_id; assumption.
    + assumption.
  - split.
    + rewrite swap_symmetric; assumption.
    + assumption.
Qed. *)

Lemma aeq_sub: forall t1 t2 x y, y `notin` fv_nom t1 -> (n_sub (swap x y t1) y t2) =a (n_sub t1 x t2).
Proof.
  intros. case (x == y); intros; subst.
  - rewrite swap_id; apply aeq_refl.
  - apply aeq_sub_diff.
    -- apply aeq_refl.
    -- apply aux_not_equal; assumption.
    -- assumption.
    -- apply aeq_refl.
Qed.
               
(*
Lemma swap_comp: forall t x y z,
    x <> z -> y <> z -> x `notin` fv_nom t -> y `notin` fv_nom t -> aeq (swap y x (swap y z t)) (swap x z t).
Proof.
Admitted.

false: take t = y or t = x
Lemma swap_trans: forall t x y z, (swap x y (swap y z t)) = swap x z t.
Proof.
  induction t.
  - intros. simpl. unfold swap_var. default_simp.
    + apply notin_singleton_is_false in H.
      contradiction.
    + apply notin_singleton_is_false in H0.
      contradiction.
  - intros. simpl. unfold swap_var.
    case (x == y).
    + intro H'; subst.
      case (z == x0).
      * intro H'; subst.
        case (y == x0).
        ** intro H'; subst.
           rewrite swap_involutive.
           rewrite swap_id.
           reflexivity.
        ** intro H'.
           rewrite IHt.
           *** reflexivity.
           *** simpl in H.
               apply notin_remove_1 in H.
               destruct H.
               **** contradiction.
               **** assumption.
           *** simpl in H0.
               apply notin_remove_1 in H0.
               destruct H0.
               **** contradiction.
               **** assumption.
      * intro H; case (z == y).
        ** intro H'; subst.
           case (y == x0).
           *** intro H'; contradiction.
           *** intro H'; case (y == y).
               **** intro H''; reflexivity.
               **** intro H''; contradiction.
        ** intro H'; case (y == x0).
           *** intro H''; subst.
               reflexivity.
           *** intro H''; case (y == z).
               **** intro H'''; subst.
                    contradiction.
               **** Admitted.

  - intros. simpl. unfold swap_var. default_simp.
  - intros. simpl. unfold swap_var. default_simp.

Lemma aeq_diff_abs': forall x y t1 t2, x `notin` fv_nom t2 -> aeq t1 (swap x y t2) -> aeq (n_abs x t1) (n_abs y t2).
Proof.
  intros x y t1 t2 Hnotin H.
  inversion H; subst.
  - rewrite H2.
    rewrite swap_symmetric.
    apply aeq_abs; assumption.
  - rewrite swap_symmetric; assumption.
Qed.

Lemma aeq_abs_diff_swap: forall t1 t2 x y z, x <> y -> z `notin` fv_nom t1 -> z `notin` fv_nom t2 -> aeq (n_abs x t1) (n_abs y t2) -> aeq (swap x z t1) (swap y z t2).
Proof.
  intros t1 t2 x y z Hneq Hnotin1 Hnotin2 Haeq.
  induction Haeq.
  -
  Admitted.
 *)
    

(** ** Capture-avoiding substitution *)

(** We need to use size to define capture avoiding
    substitution. Because we sometimes swap the name of the
    bound variable, this function is _not_ structurally
    recursive. So, we add an extra argument to the function
    that decreases with each recursive call. 

Fixpoint subst_rec (n:nat) (t:n_sexp) (u :n_sexp) (x:atom)  : n_sexp :=
  match n with
  | 0 => t
  | S m => match t with
          | n_var y =>
            if (x == y) then u else t
          | n_abs y t1 =>
            if (x == y) then t
            else
              (* rename to avoid capture *)
              let (z,_) :=
                  atom_fresh (fv_nom u `union` fv_nom t `union` {{x}}) in
                 n_abs z (subst_rec m (swap y z t1) u x)
          | n_app t1 t2 =>
            n_app (subst_rec m t1 u x) (subst_rec m t2 u x)
          | n_sub t1 y t2 =>
            if (x == y) then n_sub t1 y (subst_rec m t2 u x)
            else
              (* rename to avoid capture *)
              let (z,_) :=
                  atom_fresh (fv_nom u `union` fv_nom t `union` {{x}}) in
                 n_sub  (subst_rec m (swap y z t1) u x) z (subst_rec m t2 u x) 
           end
  end. *)

Require Import Recdef.

Function subst_rec_fun (t:n_sexp) (u :n_sexp) (x:atom) {measure size t} : n_sexp :=
  match t with
  | n_var y =>
      if (x == y) then u else t
  | n_abs y t1 =>
      if (x == y) then t
      else let (z,_) :=
                  atom_fresh (fv_nom u `union` fv_nom t1 `union` {{x}} `union` {{y}}) in
                n_abs z (subst_rec_fun (swap y z t1) u x)
  | n_app t1 t2 =>
      n_app (subst_rec_fun t1 u x) (subst_rec_fun t2 u x)
  | n_sub t1 y t2 =>
      if (x == y) then n_sub t1 y (subst_rec_fun t2 u x)
      else let (z,_) :=
                  atom_fresh (fv_nom u `union` fv_nom t1 `union` {{x}} `union` {{y}}) in
              n_sub  (subst_rec_fun (swap y z t1) u x) z (subst_rec_fun t2 u x) 
           end.
Proof.
 - intros. simpl. rewrite swap_size_eq. auto.
 - intros. simpl. lia.
 - intros. simpl. lia.
 - intros. simpl. lia.
 - intros. simpl. lia.
 - intros. simpl. rewrite swap_size_eq. lia.
Defined.

(*
Inductive meta_subst: n_sexp -> atom -> n_sexp -> n_sexp -> Prop :=
| meta_var_eq: forall x u, meta_subst (n_var x) x u u
| meta_var_neq: forall x y u, x <> y -> meta_subst (n_var y) x u (n_var y)
| meta_app: forall t1 t1' t2 t2' x u, meta_subst t1 x u t1' -> meta_subst t2 x u t2' -> meta_subst (n_app t1 t2) x u (n_app t1' t2')
| meta_abs_eq: forall t x u, meta_subst (n_abs x t) x u (n_abs x t) 
| meta_abs_neq1: forall t x y u v, y `notin` fv_nom u -> meta_subst t x u v -> meta_subst (n_abs y t) x u v 
| meta_abs_neq2: forall t x y z u v, y `in` fv_nom u -> z `notin` (fv_nom t `union` fv_nom u `union` {{x}} `union` {{y}}) -> meta_subst (swap y z t) x u v -> meta_subst (n_abs y t) x u v
| meta_sub_eq: forall t1 t2 t2' x u, meta_subst t2 x u t2' -> meta_subst (n_sub t1 x t2) x u (n_sub t1 x t2') 
| meta_sub_neq1: forall t1 t1' t2 t2' x y u, x <> y ->  y `notin` fv_nom u ->  meta_subst t1 x u t1' -> meta_subst t2 x u t2' -> meta_subst (n_sub t1 y t2) x u (n_sub t1' x t2')
| meta_sub_neq2: forall t1 t1' t2 t2' x y z u, x <> y ->  y `in` fv_nom u -> z `notin` (fv_nom t1 `union` fv_nom u `union` {{x}} `union` {{y}}) ->  meta_subst (swap y z t1) x u t1' -> meta_subst t2 x u t2' -> meta_subst (n_sub t1 y t2) x u (n_sub t1' x t2'). 

Lemma fv_nom_remove: forall t u v x y, y `notin` fv_nom u -> y `notin` remove x (fv_nom t) -> meta_subst t x u v ->  y `notin` fv_nom v.
Proof. 
  intros t u v x y H1 H2 H3. induction H3.
  - assumption.
  - apply notin_remove_1 in H2. destruct H2.
    + subst. apply notin_singleton. apply aux_not_equal; assumption.
    + assumption.
  - simpl in *. rewrite remove_union_distrib in H2. assert (H3 := H2). apply notin_union_1 in H2. apply notin_union_2 in H3. apply notin_union.
    + apply IHmeta_subst1; assumption.
    + apply IHmeta_subst2; assumption.
  - simpl in *. rewrite double_remove in H2. assumption.
  - apply IHmeta_subst.
    + assumption.
    + simpl in H2.

      rewrite remove_symmetric in H2. apply notin_remove_1 in H2. destruct H2.
      * subst. assumption.
      *)
        
(** The definitions subst_rec and subst_rec_fun are alpha-equivalent. 
Theorem subst_rec_fun_equiv: forall t u x, (subst_rec (size t) t u x) =a (subst_rec_fun t u x).
Proof.
  intros t u x. functional induction (subst_rec_fun t u x).
  - simpl. rewrite e0. apply aeq_refl.
  - simpl. rewrite e0. apply aeq_refl.
  - simpl. rewrite e0. apply aeq_refl.
  - simpl. rewrite e0. destruct (atom_fresh (Metatheory.union (fv_nom u) (Metatheory.union (remove y (fv_nom t1)) (singleton x)))).  admit.
  - simpl. admit.
  - simpl. rewrite e0. admit.
  - simpl. rewrite e0.
Admitted.

Require Import EquivDec.
Generalizable Variable A.

Definition equiv_decb `{EqDec A} (x y : A) : bool :=
  if x == y then true else false.

Definition nequiv_decb `{EqDec A} (x y : A) : bool :=
  negb (equiv_decb x y).

Infix "==b" := equiv_decb (no associativity, at level 70).
Infix "<>b" := nequiv_decb (no associativity, at level 70).

Parameter Inb : atom -> atoms -> bool.
Definition equalb s s' := forall a, Inb

Function subst_rec_b (t:n_sexp) (u :n_sexp) (x:atom) {measure size t} : n_sexp :=
  match t with
  | n_var y =>
      if (x == y) then u else t
  | n_abs y t1 =>
      if (x == y) then t
      else if (Inb y (fv_nom u)) then let (z,_) :=
                  atom_fresh (fv_nom u `union` fv_nom t `union` {{x}}) in
                                      n_abs z (subst_rec_b (swap y z t1) u x)
                                            else n_abs y (subst_rec_b t1 u x)
  | n_app t1 t2 =>
      n_app (subst_rec_b t1 u x) (subst_rec_b t2 u x)
  | n_sub t1 y t2 =>
      if (x == y) then n_sub t1 y (subst_rec_b t2 u x)
      else if (Inb y (fv_nom u)) then let (z,_) :=
                  atom_fresh (fv_nom u `union` fv_nom t `union` {{x}}) in
                                      n_sub  (subst_rec_b (swap y z t1) u x) z (subst_rec_b t2 u x)
                                             else n_sub (subst_rec_b t1 u x) y (subst_rec_b t2 u x)
           end.
Proof.
 - intros. simpl. rewrite swap_size_eq. auto.
 - intros. simpl. lia.
 - intros. simpl. lia.
 - intros. simpl. lia.
 - intros. simpl. lia.
 - intros. simpl. rewrite swap_size_eq. lia.
Defined. *)

(** Our real substitution function uses the size of the size of the term
    as that extra argument. *)

Definition m_subst (u : n_sexp) (x:atom) (t:n_sexp) :=
  subst_rec_fun t u x.
Notation "[ x := u ] t" := (m_subst u x t) (at level 60).

Lemma m_subst_var_eq : forall u x,
    [x := u](n_var x) = u.
Proof.
  intros u x. unfold m_subst. rewrite subst_rec_fun_equation. rewrite eq_dec_refl. reflexivity.
Qed.

Lemma m_subst_var_neq : forall u x y, x <> y ->
    [y := u](n_var x) = n_var x.
Proof.
  intros u x y H. unfold m_subst. rewrite subst_rec_fun_equation. destruct (y == x) eqn:Hxy.
  - subst. contradiction.
  - reflexivity.
Qed.

Lemma fv_nom_remove: forall t u x y, y `notin` fv_nom u -> y `notin` remove x (fv_nom t) ->  y `notin` fv_nom ([x := u] t).
Proof. 
  intros t u x y H0 H1. unfold m_subst. functional induction (subst_rec_fun t u x).
  - assumption.
  - apply notin_remove_1 in H1. destruct H1.
    + subst. simpl. apply notin_singleton. apply aux_not_equal; assumption.
    + assumption.
  - simpl in *. rewrite double_remove in H1. assumption.
  - simpl in *. case (y == z).
    + intro Heq. subst. apply notin_remove_3; reflexivity.
    + intro Hneq. apply notin_remove_2. apply IHn.
      * assumption.
      * apply notin_remove_1 in H1. destruct H1.
        ** subst. apply notin_remove_3; reflexivity.
        ** clear IHn e1 e0. case (y == x).
           *** intro Heq. subst. apply notin_remove_3; reflexivity.
           *** intro Hneq'. apply notin_remove_2. apply notin_remove_1 in H. destruct H.
               **** subst. apply fv_nom_swap. apply notin_union_2 in _x0. apply notin_union_1 in _x0. assumption.
               **** case (y == y0).
                    ***** intro Heq. subst. apply fv_nom_swap. apply notin_union_2 in _x0. apply notin_union_1 in _x0. assumption.
                    ***** intro Hneq''. apply fv_nom_remove_swap; assumption.
  - simpl in *. apply notin_union_3. 
    + apply IHn.
      * assumption.
      * apply notin_remove_1 in H1. destruct H1. 
        ** subst. apply notin_remove_3'. reflexivity.
        ** apply notin_union_1 in H. apply notin_remove_2. assumption.
    + apply IHn0.
      * assumption.
      * apply notin_remove_1 in H1. destruct H1. 
        ** subst. apply notin_remove_3'. reflexivity.
        ** apply notin_union_2 in H. apply notin_remove_2. assumption.
  - simpl in *. apply notin_union_3. 
    + apply notin_remove_1 in H1. destruct H1.
      * subst. Search remove. apply notin_remove_3'. reflexivity.
      * simpl. apply notin_union_1 in H. assumption.
    + apply IHn. 
      * assumption. 
      * apply notin_remove_1 in H1. destruct H1.
        ** subst. Search remove. apply notin_remove_3'. reflexivity.
        ** simpl. apply notin_union_2 in H. apply notin_remove_2. assumption.
  - simpl in *. apply notin_remove_1 in H1. destruct H1.
    + subst. apply notin_union_3.
      * case (y == z).
        ** intros Heq. subst. apply notin_remove_3'. reflexivity.
        ** intros Hneq. apply notin_remove_2. clear e1. apply notin_union_2 in _x0. apply notin_union_1 in _x0. 
           apply IHn.
          *** assumption.
          *** apply notin_remove_3. reflexivity.
      * simpl. apply IHn0. 
        ** assumption.
        ** apply notin_remove_3. reflexivity.
    + simpl. apply notin_union_3.
      * case (y == z). 
        ** intro Heq. subst. apply notin_remove_3. reflexivity.
        ** intro Hneq. apply notin_remove_2. apply notin_union_1 in H. apply IHn.
            *** assumption.
            *** apply notin_remove_1 in H. destruct H.
                **** simpl. subst. apply notin_remove_2. apply fv_nom_swap.
                     clear e1. apply notin_union_2 in _x0. apply notin_union_1 in _x0.
                     assumption.
                **** apply notin_remove_2. case (y == y0). 
                      ***** intro Heq. subst. apply fv_nom_swap.
                            clear e1. apply notin_union_2 in _x0. apply notin_union_1 in _x0.
                            assumption.
                      ***** intro Hneq'. apply fv_nom_remove_swap.
                            ****** assumption.
                            ****** assumption.
                            ****** assumption.
      * apply IHn0.
        ** assumption.
        ** apply notin_union_2 in H. apply notin_remove_2. assumption.
Qed.

(* não utilizado
Lemma fv_nom_m_subst: forall t u x, x `in` fv_nom t -> fv_nom ([x := u] t) [=] (union (remove x (fv_nom t)) (fv_nom u)).
Proof.
  intros t u x. unfold m_subst. functional induction (subst_rec_fun t u x).
  - intros H. simpl in H. rewrite remove_singleton_empty. rewrite AtomSetProperties.empty_union_1.
    + reflexivity.
    + unfold AtomSetImpl.Empty. auto.
  - intro H. simpl in H. apply singleton_iff in H. symmetry in H. contradiction.
  - intro H. simpl in H. pose proof notin_remove_3'. specialize (H0 x x (fv_nom t1)). assert (H': x = x). { reflexivity. } apply H0 in H'. contradiction.
  - simpl. intro H. rewrite IHn. Admitted. *)

(*    + rewrite remove_union_distrib.
      swap_remove_reduction
        remove_fv_swap
    +
    rewrite remove_symmetric.

    
  induction t.
  - intros u x' H. simpl in *. apply singleton_iff in H. subst. unfold m_subst. rewrite subst_rec_fun_equation. rewrite eq_dec_refl. rewrite remove_singleton_empty. rewrite AtomSetProperties.empty_union_1.
    + reflexivity.
    + unfold AtomSetImpl.Empty. intro a. auto.
  - intros u x' H. *)
   
(* Lemma subst_size : forall (n:nat) (u : n_sexp) (x:atom) (t:n_sexp),
    size t <= n -> subst_rec n t u x = subst_rec (size t) t u x.
Proof.
  intro n. eapply (lt_wf_ind n). clear n.
  intros n IH u x t SZ.
  destruct t; simpl in *; destruct n; try lia.
  - default_simp.
  - default_simp.
    rewrite <- (swap_size_eq x0 x1).
    rewrite <- (swap_size_eq x0 x1) in SZ.
    apply IH; lia. 
  - simpl.
    rewrite (IH n); try lia.
    rewrite (IH n); try lia.
    rewrite (IH (size t1 + size t2)); try lia.
    rewrite (IH (size t1 + size t2)); try lia.
    auto.
  - default_simp.
    -- rewrite (IH n); try lia.
       symmetry.
       apply IH.
       --- apply Nat.lt_le_trans with (S (size t1 + size t2)).
           ---- lia.
           ---- assumption.
       --- lia.
    -- rewrite (IH n); try lia.
       --- rewrite (swap_size_eq x0 x1).
           symmetry.
           rewrite <- (swap_size_eq x0 x1) at 2.    
           apply IH.
           ---- apply Nat.lt_le_trans with (S (size t1 + size t2)).
                ----- lia.
                ----- assumption.
           ---- rewrite (swap_size_eq x0 x1).
                lia.
       --- rewrite (swap_size_eq x0 x1).
           apply le_trans with (size t1 + size t2).
           ---- lia.
           ---- lia.
    -- rewrite (IH n); try lia.
       symmetry.
       apply IH.
       --- apply Nat.lt_le_trans with (S (size t1 + size t2)).
           ---- lia.
           ---- assumption.
       --- lia.
Qed. *)

Lemma m_subst_app: forall t1 t2 u x, [x := u](n_app t1 t2) = n_app ([x := u]t1) ([x := u]t2).
Proof.
  intros t1 t2 u x. unfold m_subst. rewrite subst_rec_fun_equation. reflexivity.
Qed.

(*
Lemma test : 
*)

(* realocar *)
Lemma aeq_m_subst: forall t t' u u' x, t =a t' -> u =a u' -> ([x := u] t) =a ([x := u'] t').
Proof.
  intros t t' u u' x Ht Hu. unfold m_subst. Search eq_dec.
  Admitted.
  
(* realocar *)
Lemma swap_subst_rec_fun: forall x y z t u, swap x y (subst_rec_fun t u z) =a subst_rec_fun (swap x y t) (swap x y u) (swap_var x y z).
Proof.
  intros x y z t u. destruct (x == y).
  - subst. repeat rewrite swap_id. rewrite swap_var_id. apply aeq_refl.
  - generalize dependent u. generalize dependent z. generalize dependent y. generalize dependent x.
    induction t using n_sexp_induction.
    + intros x' y H z u. simpl. admit.
    + intros x y Hneq z' u. rewrite subst_rec_fun_equation. case (z' == z).
      * intro Heq. subst. simpl. admit. (* ok *)
        
      * intro Hneq'. destruct (atom_fresh (union (fv_nom u) (union (fv_nom t) (union (singleton z') (singleton z))))). simpl. remember (subst_rec_fun (swap z x0 t) u z') as ee. rewrite subst_rec_fun_equation.
       assert (Hdiff: ((swap_var x y z') <> (swap_var x y z))).
     {
       unfold swap_var at 1. destruct (z' == x).
       * subst. unfold swap_var. destruct (z == x).
         ** subst. contradiction.
         ** destruct (z == y). 
             *** subst. auto.
             *** auto.
       * destruct (z' == y).
         ** unfold swap_var.  destruct (z == x).
            *** subst. assumption.
            *** apply eq_sym in e. subst. destruct (z == z').
                **** subst. contradiction.
                **** auto.
         ** unfold swap_var.  destruct (z == x).
            *** subst. assumption.
            *** destruct (z == y).
                **** auto.
                **** auto.
     }
     assert (Hdiff': ((swap_var x y z') == (swap_var x y z)) = right Hdiff).
     {
       admit. (* ? *)
     }
       rewrite Hdiff'.
     destruct (atom_fresh (union (fv_nom (swap x y u)) (union (fv_nom (swap x y t)) (union (singleton (swap_var x y z')) (singleton (swap_var x y z)))))). subst. case ((swap_var x y x0) == x1).
       ** intro Heq. subst. apply aeq_abs_same. rewrite H.
          *** pose proof aeq_m_subst as Haeq. unfold m_subst in Haeq. apply Haeq.
              **** rewrite swap_equivariance. apply aeq_refl.
              **** apply aeq_refl.
          *** reflexivity.
          *** assumption.          
       ** intro Hneq''. apply aeq_abs_diff.
          *** assumption.
          *** apply fv_nom_remove.
              **** apply notin_fv_nom_equivariance. apply notin_union_1 in n. assumption.
              **** apply diff_remove.
                   ***** apply notin_union_2 in n. apply notin_union_2 in n. apply notin_union_1 in n. apply notin_singleton_1 in n. apply aux_not_equal. admit. (* ok *)
                   ***** admit. (* ok *)
          *** rewrite H.
              **** admit. (* começar por aqui *)
              **** reflexivity.
              **** assumption.
   + Admitted.

(*
        
      * intro Hneq'. destruct (atom_fresh (union (fv_nom u) (union (fv_nom t) (union (singleton z') (singleton z))))). simpl.
    + intros x' y H z u. simpl. rewrite subst_rec_fun_equation. rewrite eq_dec_refl. apply aeq_refl.
    + intros x' y' H. clear e1. simpl.
      assert (Hdiff: ((swap_var x' y' x) <> (swap_var x' y' y))).
      {
        unfold swap_var at 1. destruct (x == x').
        * subst. unfold swap_var. destruct (y == x').
          ** subst. contradiction.
          ** destruct (y == y'). 
              *** subst. auto.
              *** auto.
        * destruct (x == y').
          ** unfold swap_var.  destruct (y == x').
             *** subst. assumption.
             *** apply eq_sym in e. subst. destruct (y == x).
                 **** subst. contradiction.
                 **** auto.
          ** unfold swap_var.  destruct (y == x').
             *** subst. assumption.
             *** destruct (y == y').
                 **** auto.
                 **** auto.
      }
      assert (Hdiff': ((swap_var x' y' x) == (swap_var x' y' y)) = right Hdiff).
      {
        admit. (* ? *)
      }
      remember (subst_rec_fun (swap y z t1) u x) as ee. rewrite subst_rec_fun_equation. rewrite Hdiff'.
      destruct (atom_fresh (union (fv_nom (swap x' y' u)) (union (fv_nom (swap x' y' t1)) (union (singleton (swap_var x' y' x)) (singleton (swap_var x' y' y)))))). subst. case (x0 == (swap_var x' y' z)).
      * intro Heq. subst. apply aeq_abs_same. rewrite IHn.
        ** pose proof aeq_m_subst as H'. unfold m_subst in H'. apply H'.
           *** rewrite swap_equivariance. apply aeq_refl.
           *** apply aeq_refl.
        ** assumption.
      * intro Hdiff''. apply aeq_abs_diff.
        ** apply aux_not_equal. assumption.
        ** apply fv_nom_remove.
           *** apply notin_fv_nom_equivariance. apply notin_union_1 in _x0. assumption.
           *** apply diff_remove.
               **** apply notin_union_2 in _x0. apply notin_union_2 in _x0. apply notin_union_1 in _x0. apply notin_singleton_1 in _x0. apply aux_not_equal. admit. (* ok *)
               **** admit. (* ? *)
        ** rewrite IHn.
           *** 
           *** assumption
      
      
      
      unfold swap_var at 2. destruct (y == x').
      * subst. unfold swap_var at 1. destruct (z == x').
        ** subst. destruct (x0 == y').
           *** subst. apply aeq_abs_same. rewrite IHn. 


           rewrite swap_equivariance in IHn. replace x0 with (swap_var x' x0 x') at 3. apply IHn.
           *** assumption.
           *** unfold swap_var. rewrite eq_dec_refl. reflexivity.
        




        unfold swap_var at 1. destruct (z == x').
        ** subst. apply aeq_abs_same. specialize (IHn x' x0).
           rewrite swap_equivariance in IHn. replace x0 with (swap_var x' x0 x') at 3. apply IHn.
           *** assumption.
           *** unfold swap_var. rewrite eq_dec_refl. reflexivity.
        ** apply aeq_abs_diff.
           *** assumption.
           *** admit.
           *** Admitted. *)

(* indução funcional utilizando a definição de subst_rec_fun

  intros x y z t u. destruct (x == y).
  - subst. repeat rewrite swap_id. rewrite swap_var_id. apply aeq_refl.
  - generalize dependent y. generalize dependent x. functional induction (subst_rec_fun t u z).
    + intros x' y H. simpl. remember (swap_var x' y x) as z. rewrite subst_rec_fun_equation. rewrite eq_dec_refl. apply aeq_refl.
    + intros x' y' H. pose proof m_subst_var_neq as H'. unfold m_subst in H'. simpl (swap x' y' (n_var y)). specialize (H' (swap x' y' u) (swap_var x' y' y) (swap_var x' y' x)). rewrite H'.
      * apply aeq_refl.
      * unfold swap_var. default_simp.
    + intros x' y H. simpl. remember (swap_var x' y x) as z. rewrite subst_rec_fun_equation. rewrite eq_dec_refl. apply aeq_refl.
    + intros x' y' H. clear e1. simpl.
      assert (Hdiff: ((swap_var x' y' x) <> (swap_var x' y' y))).
      {
        unfold swap_var at 1. destruct (x == x').
        * subst. unfold swap_var. destruct (y == x').
          ** subst. contradiction.
          ** destruct (y == y'). 
              *** subst. auto.
              *** auto.
        * destruct (x == y').
          ** unfold swap_var.  destruct (y == x').
             *** subst. assumption.
             *** apply eq_sym in e. subst. destruct (y == x).
                 **** subst. contradiction.
                 **** auto.
          ** unfold swap_var.  destruct (y == x').
             *** subst. assumption.
             *** destruct (y == y').
                 **** auto.
                 **** auto.
      }
      assert (Hdiff': ((swap_var x' y' x) == (swap_var x' y' y)) = right Hdiff).
      {
        admit. (* ? *)
      }
      remember (subst_rec_fun (swap y z t1) u x) as ee. rewrite subst_rec_fun_equation. rewrite Hdiff'.
      destruct (atom_fresh (union (fv_nom (swap x' y' u)) (union (fv_nom (swap x' y' t1)) (union (singleton (swap_var x' y' x)) (singleton (swap_var x' y' y)))))). subst. case (x0 == (swap_var x' y' z)).
      * intro Heq. subst. apply aeq_abs_same. rewrite IHn.
        ** pose proof aeq_m_subst as H'. unfold m_subst in H'. apply H'.
           *** rewrite swap_equivariance. apply aeq_refl.
           *** apply aeq_refl.
        ** assumption.
      * intro Hdiff''. apply aeq_abs_diff.
        ** apply aux_not_equal. assumption.
        ** apply fv_nom_remove.
           *** apply notin_fv_nom_equivariance. apply notin_union_1 in _x0. assumption.
           *** apply diff_remove.
               **** apply notin_union_2 in _x0. apply notin_union_2 in _x0. apply notin_union_1 in _x0. apply notin_singleton_1 in _x0. apply aux_not_equal. admit. (* ok *)
               **** admit. (* ? *)
        ** rewrite IHn.
           *** 
           *** assumption
      
      
      
      unfold swap_var at 2. destruct (y == x').
      * subst. unfold swap_var at 1. destruct (z == x').
        ** subst. destruct (x0 == y').
           *** subst. apply aeq_abs_same. rewrite IHn. 


           rewrite swap_equivariance in IHn. replace x0 with (swap_var x' x0 x') at 3. apply IHn.
           *** assumption.
           *** unfold swap_var. rewrite eq_dec_refl. reflexivity.
        




        unfold swap_var at 1. destruct (z == x').
        ** subst. apply aeq_abs_same. specialize (IHn x' x0).
           rewrite swap_equivariance in IHn. replace x0 with (swap_var x' x0 x') at 3. apply IHn.
           *** assumption.
           *** unfold swap_var. rewrite eq_dec_refl. reflexivity.
        ** apply aeq_abs_diff.
           *** assumption.
           *** admit.
           *** Admitted.


 *)

(*      *



      apply aeq_trans with (n_abs (swap_var x' y' z) ((subst_rec_fun (swap x' y' (swap y z t1)) (swap x' y' u) (swap_var x' y' x)))).
      * apply aeq_abs_same. apply IHn. apply H.
      * unfold swap_var at 1. destruct (z == x').
        ** subst. destruct (y' == x0).
           *** subst. apply aeq_abs_same. rewrite swap_equivariance. replace (swap_var x' x0 x') with x0.
               **** apply aeq_refl.
               **** unfold swap_var. rewrite eq_dec_refl. reflexivity.
           *** apply aeq_abs_diff.
               **** assumption.
               **** admit.
               **** apply aeq_sym. apply IHn.
        **
           
      change (swap x' y' (n_abs z (subst_rec_fun (swap y z t1) u x))) with (n_abs (swap_var x' y' z) (swap x' y' (subst_rec_fun (swap y z t1) u x))).  simpl. unfold swap_var. destruct (y == x').
      * subst. destruct (x == x').
        ** subst. destruct (z == x').
           *** subst. rewrite swap_id. 
           ***

        **
      *


      


      change (subst_rec_fun (n_abs (swap_var x' y' y) (swap x' y' t1)) (swap x' y' u) (swap_var x' y' x)) with 


      
      apply aeq_trans with (n_abs (swap_var x' y' z) (subst_rec_fun (swap x'  y' (swap y z t1)) (swap x' y' u) (swap_var x' y' x))).
      * apply aeq_abs_same. apply IHn. assumption.
      * change (swap x' y' (n_abs y t1)) with (n_abs (swap_var x' y' y) (swap x' y' t1)). case (x == y).
        ** intro Heq. subst. contradiction.
        ** intro Hneq. Admitted. 

 rewrite swap_symmetric. pose proof swap_symmetric as H2. specialize (H2 t y z). rewrite H2. pose proof swap_symmetric as H3. specialize (H3 t y x0). rewrite H3. apply aeq_swap_swap.
                    ******* apply notin_union_2 in n1. apply notin_union_1 in n1. assumption.
                    ******* apply notin_union_2 in H. apply notin_union_1 in H. simpl in H. apply notin_remove_1 in H. destruct H.
                    ******** subst.
             
           ***

          
          destruct (atom_fresh (union (fv_nom u) (union (fv_nom (n_abs y t)) (singleton x)))). case (x1 == x0).
      * intro H. subst. destruct (atom_fresh (union (fv_nom u) (union (fv_nom t) (union (singleton x) (singleton y))))).
        case (x0 == x1). 
        ** intro Heq. subst. apply aeq_refl.
        ** intro Hneq. Search n_abs. admit.
      * intro H. destruct (atom_fresh (union (fv_nom u) (union (fv_nom t) (union (singleton x) (singleton y))))).
        case (x0 == x2). 
        ** intro Heq. subst. apply aeq_refl.
        ** intro Hneq. Search n_abs. admit.
Admitted. *)

(*    -- unfold not. intros. assert (y = y). {
         reflexivity.
       }
       contradiction.
  - intros. unfold m_subst. simpl. case (x == y).
    -- intros. contradiction.
    -- intros. pose proof AtomSetImpl.union_1.
       assert (forall z, size t  = size (swap y z t )). {
         intros. case (y == z).
         - intros. rewrite e. rewrite swap_id. reflexivity.
         - intros. rewrite swap_size_eq. reflexivity.         
       }
       destruct (atom_fresh
       (Metatheory.union (fv_nom u)
          (Metatheory.union (remove y (fv_nom t )) (singleton x)))). 
       specialize (H0 x0). rewrite H0. reflexivity.
Qed. *)

Lemma m_subst_abs : forall u x y t , m_subst u x (n_abs y t)  =a
       if (x == y) then (n_abs y t )
       else let (z,_) := atom_fresh (fv_nom u `union` fv_nom (n_abs y t ) `union` {{x}}) in
       n_abs z (m_subst u x (swap y z t )).
Proof.
  intros u x y t. destruct (atom_fresh (union (fv_nom u) (union (fv_nom (n_abs y t)) (singleton x)))) as [z H]. destruct (x == y).
  - subst. unfold m_subst. rewrite subst_rec_fun_equation. rewrite eq_dec_refl. apply aeq_refl.
  - unfold m_subst. rewrite subst_rec_fun_equation. destruct (x == y).
    + contradiction.
    + destruct (atom_fresh (union (fv_nom u) (union (fv_nom t) (union (singleton x) (singleton y))))). case (x0 == z).
      * intro Heq. subst. apply aeq_refl.
      * intro Hneq. apply aeq_abs_diff.
        ** assumption.
        ** apply fv_nom_remove.
           *** apply notin_union_1 in n1. assumption.
           *** apply notin_union_2 in H. apply notin_union_1 in H. simpl in H. apply notin_remove_1 in H. destruct H.
               **** subst. rewrite swap_id. apply notin_remove_2. apply notin_union_2 in n1. apply notin_union_1 in n1. assumption.
               **** apply notin_remove_2. apply fv_nom_remove_swap.
                    ***** assumption.
                    ***** repeat apply notin_union_2 in n1. apply notin_singleton_1 in n1. apply aux_not_equal. assumption.
                    ***** apply notin_union_2 in n1. apply notin_union_1 in n1. assumption.
        ** case (y == z).
           *** intro Heq. subst. rewrite swap_id. apply aeq_trans with (subst_rec_fun (swap z x0 t) (swap z x0 u) (swap_var z x0 x)).
           **** pose proof aeq_m_subst as H1. unfold m_subst in H1. unfold swap_var. destruct (x == z).
                ***** repeat apply notin_union_2 in H. apply notin_singleton_1 in H. contradiction.
                ***** destruct (x == x0).
                ****** apply notin_union_2 in n1. apply notin_union_2 in n1. apply notin_union_1 in n1. apply notin_singleton_1 in n1. contradiction.
                ****** apply H1.
                ******* apply aeq_sym. apply aeq_refl.
                ******* Search swap. apply aeq_sym. apply swap_reduction.
                ******** apply notin_union_1 in H. assumption.
                ******** apply notin_union_1 in n1. assumption.
           **** apply aeq_sym. apply swap_subst_rec_fun.
           *** intro Heq. Search aeq_swap_swap. Search swap. rewrite swap_subst_rec_fun.
               pose proof aeq_m_subst as H1. unfold m_subst in H1. unfold swap_var. destruct (x == z).
                **** repeat apply notin_union_2 in H. apply notin_singleton_1 in H. contradiction.
                **** destruct (x == x0).
                ***** apply notin_union_2 in n1. apply notin_union_2 in n1. apply notin_union_1 in n1. apply notin_singleton_1 in n1. contradiction.
                ***** apply H1.
                ****** apply aeq_sym. Search aeq. rewrite swap_symmetric. pose proof swap_symmetric as H2. specialize (H2 t y z). rewrite H2.
                       pose proof swap_symmetric as H3. specialize (H3 t y x0). rewrite H3. apply aeq_swap_swap.
                ******* apply notin_union_2 in n1. apply notin_union_1 in n1. assumption.
                ******* apply notin_union_2 in H. apply notin_union_1 in H. Search n_abs. simpl in H. Search remove.
                        apply diff_remove_2 in H.
                ******** assumption.
                ******** auto.
                ****** Search swap. rewrite swap_reduction.
                ******* apply aeq_refl.
                ******* apply notin_union_1 in H. assumption. 
                ******* apply notin_union_1 in n1. assumption. 
Qed.

Lemma m_subst_abs_eq : forall u x t, [x := u](n_abs x t) = n_abs x t.
Proof.
  intros u x t. unfold m_subst. rewrite subst_rec_fun_equation. rewrite eq_dec_refl. reflexivity.
Qed.

(*
Corollary test1 : forall u x y w t, n_abs w ([x := u] swap y w t) = n_abs w (swap y w ([x := u] t)). 
Proof.
Admitted.

Corollary test2 : forall u x y w z t, swap y w ([x := u] t) =a swap z w (swap y z ([x := u] t)).
Proof.
Admitted.
*)

Lemma m_subst_abs_neq : forall u x y z t, x <> y -> z `notin` (fv_nom u `union` fv_nom (n_abs y t ) `union` {{x}}) -> [x := u](n_abs y t) =a n_abs z ([x := u](swap y z t)).
Proof.
  intros u x y z t H H1. pose proof m_subst_abs as H2. specialize (H2 u x y t). destruct (x == y) eqn:Hx.
  - subst. contradiction.
  - destruct (atom_fresh (Metatheory.union (fv_nom u) (Metatheory.union (fv_nom (n_abs y t)) (singleton x)))).
    apply aeq_trans with (n_abs x0 ([x := u] swap y x0 t)).
    + assumption.
    + case (x0 == z).
      * intro H3. rewrite H3. apply aeq_refl.
      * intro H3. simpl in *. Search n_abs. admit. (*rewrite test1. rewrite test1. Search n_abs. apply aeq_abs_diff.
        ** auto.
        ** admit.
        ** apply test2.*)
Admitted.


(*
Corollary m_subst_abs_neq : forall u x y t, x <> y -> let (z,_) := atom_fresh (fv_nom u `union` fv_nom (n_abs y t ) `union` {{x}}) in [x := u](n_abs y t) =a n_abs z ([x := u](swap y z t)).
Proof.
  intros u x y t H. pose proof m_subst_abs. specialize (H0 u x y t). destruct (x == y) eqn:Hx.
  - subst. contradiction.
  - destruct (atom_fresh (Metatheory.union (fv_nom u) (Metatheory.union (fv_nom (n_abs y t)) (singleton x)))). assumption.    
Qed.  
*)
  
Lemma m_subst_abs_diff : forall t u x y, x <> y -> x `notin` (remove y (fv_nom t)) -> [x := u](n_abs y t) = n_abs y t.
Proof. 
  intros t u x y H0 H1. Search n_abs. admit.
Admitted.
  
Lemma m_subst_notin : forall t u x, x `notin` fv_nom t -> [x := u]t =a t.
Proof.
  unfold m_subst. intros t u x. functional induction (subst_rec_fun t u x).
  - intro. apply aeq_sym. rewrite <- m_subst_var_eq with (x:=x). rewrite m_subst_var_neq. apply aeq_refl. destruct H. simpl. auto.
  - intro. reflexivity.
  - intro. reflexivity. 
  - intro. pose proof m_subst_abs_diff. specialize (H0 t1 u x y).
    unfold m_subst in H0. rewrite <- H0.
    + pose proof m_subst_abs_neq as H1. apply aeq_sym. unfold m_subst in H1. apply H1. 
      * assumption.
      * simpl. apply notin_union_3.
        ** clear e1. apply notin_union_1 in _x0. assumption.
        ** apply notin_union_3. apply notin_remove_2.
            *** clear e1. apply notin_union_2 in _x0. apply notin_union_1 in _x0. assumption.
            ***clear e1. apply notin_union_2 in _x0. apply notin_union_2 in _x0. apply notin_union_1 in _x0. assumption.
    + assumption. 
    + simpl in H. assumption.
  - intro. simpl in *. pose proof H as H1. apply notin_union_1 in H. apply notin_union_2 in H1.
    apply IHn in H. clear IHn. apply IHn0 in H1. clear IHn0. apply aeq_app; assumption.
  - intro. Search n_sub. pose proof aeq_sub_same. specialize (H0 t1 (subst_rec_fun t2 u x) t1 t2 x).
    rewrite H0. 
    + apply aeq_refl.
    + apply aeq_refl.
    + apply IHn. admit.
  - intro. Search n_sub. rewrite aeq_sub_same with (t1:=(subst_rec_fun (swap y z t1) u x)) (t2:=(subst_rec_fun t2 u x)) (t1':=(swap y z t1)) (t2':=t2). 
    + Search n_sub. apply aeq_sub. clear e1. apply notin_union_2 in _x0. apply notin_union_1 in _x0. assumption.
    + rewrite IHn. 
      * apply aeq_refl.
      * admit.
Admitted.
 
(** * The substitution lemma for the metasubstitution *)

(**
   In the pure $\lambda$-calculus, the substitution lemma is probably the first non trivial property. In our framework, we have defined two different substitution operation, namely, the metasubstitution denoted by [[x:=u]t] and the explicit substitution that has [n_sub] as a constructor. In what follows, we present the main steps of our proof of the substitution lemma for the metasubstitution operation: 
 *)

Lemma m_subst_notin_m_subst: forall t u v x y, y `notin` fv_nom t -> [y := v]([x := u] t) = [x := [y := v]u] t.
Proof.
  intros t u v x y H.
  functional induction (subst_rec_fun t u x).
  - subst. admit.
  - subst. admit.
  - subst. admit.
  - subst. admit.
  - subst. admit.
  - subst. admit.
  - subst. admit.
  Admitted.
  
Lemma m_subst_lemma: forall e1 e2 x e3 y, x <> y -> x `notin` (fv_nom e3) ->
 ([y := e3]([x := e2]e1)) =a ([x := ([y := e3]e2)]([y := e3]e1)).
Proof.

(* Due to permutation propagation, a stronger induction hypothesis is needed.
  (** We proceed by functional induction on the structure of function [subst_rec_fun], i.e. the definition of the meta-substitution. The induction splits the proof in seven cases: two cases concern variables, the next two concern abstractions, the next case concerns the application and the last two concern the explicit substitution.  *) 
  intros e1 e2 x. functional induction (subst_rec_fun e1 e2 x).
  (** *)
  (**The first case is about the variable. It considers that there are two variables, $x$ and $y$ and they differ from one another. *)
  - intros e3 y XY H. rewrite m_subst_var_eq. rewrite m_subst_var_neq.
  (** *)
  (**When we rewrite the lemmas concerning equality and negation on variables substitution, we have two cases.*)
  (** *)
  (**If we only have these two variables, we can use the equality lemma to find that both sides of the proof are equal and finish it using reflexivity and in the second case assumptions are used to finish the proof.*)
    + rewrite m_subst_var_eq. apply aeq_refl.
    + assumption.
  (** *)
  (**The second case is also about variables. In it, we consider a third variable, $z$, meaning that each variable is different from the other. In the former case, we had that $x = y$.*)
  - intros e3 z XY H. rewrite m_subst_var_neq.
  (** *)
  (**To unfold the cases in this proof, we need to destruct one variable as another. We chose to do $x == z$.*)
    + destruct (y == z) eqn:Hyz.
  (** *)
  (**This splits the proof in two cases.*)
  (** *)
  (**In the first case, we have that $x = z$. To expand this case, we use the lemma $m_subst_notin$ as an auxiliary lemma. It is added as an hypothesis, using the specialization tactics to match the last case in that hypothesis to the proof we want.*)
  (** *)
(*   (**The rest of the caases are finished  using the varible substitution's negation of equality, the varible substitution's equality or the standard library lemmas.*)  *)
    * subst. rewrite m_subst_var_eq. pose proof m_subst_notin as H'. specialize (H' e3 ([z := e3] u) x). apply aeq_sym. apply H'; assumption.
      * rewrite m_subst_var_neq.
        ** rewrite m_subst_var_neq.
           *** apply aeq_refl.
           *** auto.
        ** auto.
    + auto. 
  - intros e3 z XY H. rewrite m_subst_abs_eq.
    pose proof m_subst_notin as H'. specialize (H' ([z := e3] n_abs x t1) ([z := e3] u) x). 
    apply aeq_sym. apply H'. apply fv_nom_remove.
    + assumption.
    + apply diff_remove.
      * assumption.
      * simpl. apply notin_remove_3. reflexivity.
  - intros e3 y' XY H. destruct (y == y').
    + subst. rewrite m_subst_abs_eq. rewrite m_subst_notin_m_subst.
      * apply aeq_refl.
      * simpl. apply notin_remove_3. reflexivity.
    + unfold m_subst. specialize (IHn e3 y'). admit. 
(*
      pose proof m_subst_abs_neq. specialize (H u x y t1). destruct (atom_fresh (union (fv_nom u) (union (fv_nom (n_abs y t1)) (singleton x)))). clear e0. assert (Hxy := _x). apply H in _x. rewrite _x. clear H.
      * destruct (x0 == y').
        ** pose proof m_subst_abs_neq. specialize (H e3 y' y t1). destruct (atom_fresh (union (fv_nom e3) (union (fv_nom (n_abs y t1)) (singleton y')))). rewrite H.
           ***
           ***
          subst. rewrite m_subst_abs_eq.
        **
      * *)
  (** *)
  (**The case of application is solved by using the auxiliary lemmas on application. First, it is rewritten so that the substitution is made inside the aplication, instead of on it. The same lemma is applied multiple times to make sure nothing can be replaced anymore. This leads to a case that can be solved using the standard library lemmas.*)
  - intros e3 z XY IH. rewrite m_subst_app. rewrite m_subst_app. rewrite m_subst_app.  rewrite m_subst_app. auto.
  - intros e3 z XY IH.  admit.
  - admit.  *)


(*  induction e1 using n_sexp_size_induction. *) 

  (** We procced by case analisys on the structure of [e1]. The cases in between square brackets below mean that in the first case, [e1] is a variable named [z], in the second case [e1] is an abstraction of the form $\lambda$[z.e11], in the third case [e1] is an application of the form ([e11] [e12]), and finally in the fourth case [e1] is an explicit substitution of the form [e11] $\langle$ [z] := [e12] $\rangle$. *)
  
  induction e1 using n_sexp_induction. 
  - (* variable case: *) intros e2 x' e3 y Hneq Hfv. admit. (* to be completed as in the previous attempt. *)
  - (* abstraction case: *) intros e2 x e3 y Hneq Hfv. Admitted.

    
    (*
    (** The first case: [e1] is a variable, say [z], and there are several subcases to analyse. *)
    intros IH e2 e3 x y Hneq. destruct (x == z) eqn:Hxz.
    + (** In the first subcase [z] is equal to [x]. *)
      subst. rewrite (m_subst_var_neq e3 z y).
      * repeat rewrite m_subst_var_eq. apply aeq_refl.
      * assumption.
    + rewrite m_subst_var_neq.
      * (** If [z] is equal to [y] then both lhs and rhs reduces to [e3], since [x] does not occur in the set [fv_nom e3] by hypothesis. *)
        subst. apply aeq_sym. Admitted.
(*        pose proof subst_fresh_eq. change (subst_rec (size e3) e3 (subst_rec (size e2) e2 e3 z) x) with (m_subst (m_subst e3 z e2) x e3). apply H. assumption.
      * (** In the last subcase [x] is not equal to [y] and not equal to [z], therefore both lhs and rhs reduces to [z]. *) 
        apply aeq_sym. change (subst_rec (size (n_var z)) (n_var z) (subst_rec (size e2) e2 e3 y) x) with (m_subst (m_subst e3 y e2) x (n_var z)). apply subst_fresh_eq. simpl. apply notin_singleton_2. intro H. subst. contradiction.
  - (** Suppose [e1] is an abstraction, say [n_abs z e11]. There are several subcases. *)
    intros IH e2 e3 x y Hneq Hfv. unfold m_subst at 2 3. simpl. destruct (x == z) eqn:Hxz.
    + (** In the first subcase, [x] is equal to [z] and both lhs and rhs reduces straightfoward to the same term. *)
      subst. change (subst_rec (size (m_subst e3 y (n_abs z e11))) (m_subst e3 y (n_abs z e11)) (m_subst e3 y e2) z) with (m_subst (m_subst e3 y e2) z (m_subst e3 y (n_abs z e11))). rewrite subst_abs_eq.
    +
*)
Admitted. *)

   





