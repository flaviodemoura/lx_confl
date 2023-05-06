(* begin hide *)
(** * A nominal representation of the lambda_x calculus. *)


Print LoadPath.

Require Export Arith Lia.
Require Export Metalib.Metatheory.
Require Export Metalib.LibDefaultSimp.
Require Export Metalib.LibLNgen.

Require Import ZtoConfl_nom.

Inductive pure : n_sexp -> Prop :=
 | pure_var : forall x, pure (n_var x)
 | pure_app : forall e1 e2, pure e1 -> pure e2 -> pure (n_app e1 e2) 
 | pure_abs : forall x e1, pure e1 -> pure (n_abs x e1).


(* The n_sub constructor is part of the grammar of the terms, therefore the definition size' (n_sub t1 x t2) is computing the size of the normal form of the term (n_sub t1 x t2), and not the size of the term itself.
Fixpoint size' (t : n_sexp) : nat :=
  match t with
  | n_var x => 1
  | n_abs x t => 1 + size' t
  | n_app t1 t2 => 1 + size' t1 + size' t2
  | n_sub t1 x t2 => size' t1 + ((num_occ x t1) * ((size' t2) - 1))
  end.  
 *)

Lemma in_or_notin: forall x s, x `in` s \/ x `notin` s.
Proof.
  intros. pose proof notin_diff_1. specialize (H x s s).
  rewrite AtomSetProperties.diff_subset_equal in H.
  - apply or_comm. apply H.
    apply notin_empty_1.
  - reflexivity.
Qed.
   


Lemma pure_swap : forall x y t, pure t -> pure (swap x y t).
Proof.
  intros. induction t.
  - simpl. apply pure_var.
  - simpl. apply pure_abs. inversion H. apply IHt in H1.
    assumption.
  - simpl. apply pure_app.
    -- inversion H. apply IHt1 in H2. assumption.
    -- inversion H. apply IHt2 in H3. assumption.
  - inversion H.
Qed.
  
Lemma remove_singleton_neq: forall x y,
    x <> y -> remove y (singleton x) [=] singleton x.
Proof.
  intros. 
  pose proof notin_singleton_2. specialize (H0 x y).
  apply H0 in H.
  apply AtomSetProperties.remove_equal in H. assumption.
Qed.

Lemma diff_remove_2: forall x y s,
  x <> y -> x `notin` remove y s -> x `notin` s.
Proof.
  intros. default_simp.
Qed.

Lemma diff_equal: forall s s' t,
    s [=] s' -> AtomSetImpl.diff s t [=] AtomSetImpl.diff s' t.
Proof.
intros. rewrite H. reflexivity.
Qed.
  
Lemma shuffle_swap' : forall w y n z,
    w <> z -> y <> z ->
    (swap w y (swap y z n)) = (swap z w (swap y w n)).
Proof.
  induction n; intros; simpl; unfold swap_var; default_simp.
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
Qed.

Fixpoint num_occ x t : nat :=
  match t with
  | n_var y => if (x == y) then 1 else 0
  | n_abs y t1 => if (x == y) then 0 else num_occ x t1
  | n_app t1 t2 => (num_occ x t1) + (num_occ x t2)
  | n_sub t1 y t2 => if (x == y) then num_occ x t2 else (num_occ x t1) + (num_occ x t2)
  end.

Lemma swap_same_occ: forall x y t,
    num_occ y (swap x y t) = num_occ x t.
Proof.
  induction t; simpl; unfold swap_var; default_simp.
Qed.

Lemma swap_diff_occ: forall x y z t,
    x <> y -> x <> z -> num_occ x (swap y z t) = num_occ x t.
Proof.
  induction t; simpl; unfold swap_var; default_simp.
Qed.


Lemma fv_nom_swap_eq: forall x y t, x `notin` fv_nom t -> y `notin` fv_nom t -> fv_nom t [=] fv_nom (swap x y t).
Proof.
  induction t using n_sexp_induction.
  - intros H1 H2. simpl in *.
    unfold swap_var. default_simp.
    + apply notin_singleton_is_false in H1. contradiction.
    + apply notin_singleton_is_false in H2. contradiction.     
    + reflexivity.
  - intros H1 H2. simpl in *.
    Admitted.
      
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
Qed.

Lemma aeq_sub: forall t1 t2 x y, y `notin` fv_nom t1 -> aeq (n_sub (swap x y t1) y t2) (n_sub t1 x t2).
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
                  atom_fresh (fv_nom u `union` fv_nom t `union` {{x}}) in
                n_abs z (subst_rec_fun (swap y z t1) u x)
  | n_app t1 t2 =>
      n_app (subst_rec_fun t1 u x) (subst_rec_fun t2 u x)
  | n_sub t1 y t2 =>
      if (x == y) then n_sub t1 y (subst_rec_fun t2 u x)
      else let (z,_) :=
                  atom_fresh (fv_nom u `union` fv_nom t `union` {{x}}) in
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
  - apply notin_remove_1 in H1. simpl in *. destruct H1.
    + subst. apply notin_remove_2. apply IHn.
      * assumption.
      * apply notin_remove_3. reflexivity.
    + Admitted.
  
Lemma fv_nom_m_subst: forall t u x, x `in` fv_nom t -> fv_nom ([x := u] t) [=] (union (remove x (fv_nom t)) (fv_nom u)).
Proof.
  intros t u x. unfold m_subst. functional induction (subst_rec_fun t u x).
  - intros H. simpl in H. rewrite remove_singleton_empty. rewrite AtomSetProperties.empty_union_1.
    + reflexivity.
    + unfold AtomSetImpl.Empty. auto.
  - intro H. simpl in H. apply singleton_iff in H. symmetry in H. contradiction.
  - intro H. simpl in H. pose proof notin_remove_3'. specialize (H0 x x (fv_nom t1)). assert (H': x = x). { reflexivity. } apply H0 in H'. contradiction.
  - simpl. intro H. rewrite IHn. Admitted.
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

Lemma m_subst_abs : forall u x y t , m_subst u x (n_abs y t)  =a
       if (x == y) then (n_abs y t )
       else let (z,_) := atom_fresh (fv_nom u `union` fv_nom (n_abs y t ) `union` {{x}}) in
       n_abs z (m_subst u x (swap y z t )).
Proof.
  intros u x y t. destruct (atom_fresh (union (fv_nom u) (union (fv_nom (n_abs y t)) (singleton x)))). destruct (x == y).
  - subst. unfold m_subst. rewrite subst_rec_fun_equation. rewrite eq_dec_refl. apply aeq_refl.
  - unfold m_subst. rewrite subst_rec_fun_equation. destruct (x == y).
    + contradiction.
    + destruct (atom_fresh (union (fv_nom u) (union (fv_nom (n_abs y t)) (singleton x)))). case (x1 == x0).
      * intro H. subst. apply aeq_abs_same. apply aeq_refl.
      * intro H. apply aeq_abs_diff.
        ** assumption.
        ** simpl.
      
    -- trivial. Admitted.
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

Corollary m_subst_abs_neq : forall u x y z t, x <> y -> z `notin` (fv_nom u `union` fv_nom (n_abs y t ) `union` {{x}}) -> [x := u](n_abs y t) =a n_abs z ([x := u](swap y z t)).
Proof.
  intros u x y z t H H1. pose proof m_subst_abs as H2. specialize (H2 u x y t). destruct (x == y) eqn:Hx.
  - subst. contradiction.
  - destruct (atom_fresh (Metatheory.union (fv_nom u) (Metatheory.union (fv_nom (n_abs y t)) (singleton x)))).
    apply aeq_trans with (n_abs x0 ([x := u] swap y x0 t)).
    + assumption.
    + case (x0 == z).
      * intro H3. rewrite H3. apply aeq_refl.
      * intro H3. admit. (*rewrite test1. rewrite test1. Search n_abs. apply aeq_abs_diff.
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
    + pose proof m_subst_abs_neq as H1. apply aeq_sym. unfold m_subst in H1. apply H1; assumption.
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
    + Search n_sub. apply aeq_sub. admit.
    + rewrite IHn. 
      * apply aeq_refl.
      * Search swap. apply fv_nom_remove_swap. 
        ** auto. admit.
        ** auto.
        ** admit.
    + apply IHn0. Search n_sub. admit.
Admitted.
 

(* end hide *)

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
  (** *)
  (** We proceed by functional induction on the structure of subst_rec_fun, the definition of the substitution. The induction splits the proof in seven cases: two cases concern variables, the next two concern abstractions, the next case concerns the application and the last two concern the explicit substitution. *) 
  intros e1 e2 x. functional induction (subst_rec_fun e1 e2 x).
  (** *)
  (**The first case is about the variable. It considers that there are two variables, $x$ and $y$ and they differ from one another. *)
  - intros e3 y XY IH. rewrite m_subst_var_eq. rewrite m_subst_var_neq.
  (** *)
  (**When we rewrite the lemmas concerning equality and negation on variables substitution, we have two cases.*)
  (** *)
  (**If we only have these two variables, we can use the equality lemma to find that both sides of the proof are equal and finish it using reflexivity and in the second case assumptions are used to finish the proof.*)
    + rewrite m_subst_var_eq. apply aeq_refl.
    + assumption.
  (** *)
  (**The second case is also about variables. In it, we consider a third variable, $z$, meaning that each variable is different from the other. In the former case, we had that $x = y$.*)
  - intros e3 z XY IH. rewrite m_subst_var_neq.
  (** *)
  (**To unfold the cases in this proof, we need to destruct one variable as another. We chose to do $x == z$.*)
    + destruct (y == z) eqn:Hyz.
  (** *)
  (**This splits the proof in two cases.*)
  (** *)
  (**In the first case, we have that $x = z$. To expand this case, we use the lemma $m_subst_notin$ as an auxiliary lemma. It is added as an hypothesis, using the specialization tactics to match the last case in that hypothesis to the proof we want.*)
  (** *)
  (**The rest of the cases are finished  using the varible substitution's negation of equality, the varible substitution's equality or the standard library lemmas.*) 
    * subst. rewrite m_subst_var_eq. pose proof m_subst_notin. specialize (H e3 ([z := e3] u) x). apply aeq_sym. apply H; assumption.
      * rewrite m_subst_var_neq.
        ** rewrite m_subst_var_neq.
           *** apply aeq_refl.
           *** auto.
        ** auto.
    + auto. 
  - intros e3 z XY IH. rewrite m_subst_abs_eq.
    pose proof m_subst_notin. specialize (H ([z := e3] n_abs x t1) ([z := e3] u) x). 
    apply aeq_sym. apply H. apply fv_nom_remove.
    + assumption.
    + apply diff_remove.
      * assumption.
      * simpl. apply notin_remove_3. reflexivity.
  - intros e3 y' XY IH. destruct (y == y').
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
  - intros e3 z XY IH. admit.
  - admit. 

(*

(*  induction e1 using n_sexp_size_induction. *) 

  (** We procced by case analisys on the structure of [e1]. The cases in between square brackets below mean that in the first case, [e1] is a variable named [z], in the second case [e1] is an abstraction of the form $\lambda$[z.e11], in the third case [e1] is an application of the form ([e11] [e12]), and finally in the fourth case [e1] is an explicit substitution of the form [e11] $\langle$ [z] := [e12] $\rangle$. *)
  
  intro e1.
  generalize dependent e1. intro e1; case e1 as [z | z e11 | e11 e12 | e11 z e12].

  - (** The first case: [e1] is a variable, say [z], and there are several subcases to analyse. *)
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
*)
Admitted.

Lemma m_subst_lemma: forall e1 e2 e3 x y, x <> y -> x `notin` (fv_nom e3) ->
  aeq (m_subst e3 y (m_subst e2 x e1)) (m_subst (m_subst e3 y e2) x (m_subst e3 y e1)).
Proof.
Admitted.


 *)


Inductive betax : n_sexp -> n_sexp -> Prop :=
 | step_betax : forall (e1 e2: n_sexp) (x: atom),
     betax (n_app  (n_abs x e1) e2)  (n_sub e1 x e2).

(* evitar renomeamento no caso step_abs2: 

Inductive pix : n_sexp -> n_sexp -> Prop :=
| step_var : forall (e: n_sexp) (y: atom),
    pix (n_sub (n_var y) y e) e
| step_gc : forall (e: n_sexp) (x y: atom),
    x <> y -> pix (n_sub (n_var x) y e) (n_var x)
| step_abs1 : forall (e1 e2: n_sexp) (y : atom),
    pix (n_sub (n_abs y e1) y e2)  (n_abs y e1)
| step_abs2 : forall (e1 e2: n_sexp) (x y: atom),
    x <> y -> x `notin` fv_nom e2 ->
    pix (n_sub (n_abs x e1) y e2)  (n_abs x (n_sub e1 y e2))
| step_app : forall (e1 e2 e3: n_sexp) (y: atom),
    pix (n_sub (n_app e1 e2) y e3) (n_app (n_sub e1 y e3) (n_sub e2 y e3)).

Inductive pix : n_sexp -> n_sexp -> Prop :=
| step_var : forall (e: n_sexp) (y: atom),
    pix (n_sub (n_var y) y e) e
| step_gc : forall (e: n_sexp) (x y: atom),
    x <> y -> pix (n_sub (n_var x) y e) (n_var x)
| step_abs : forall (e1 e2: n_sexp) (x y z: atom),
    z <> x /\ z <> y /\ z `notin` fv_nom e1 /\ z `notin` fv_nom e2 ->
    pix (n_sub (n_abs x e1) y e2)  (n_abs z (n_sub (swap x z e1) y e2))
| step_app : forall (e1 e2 e3: n_sexp) (y: atom),
    pix (n_sub (n_app e1 e2) y e3) (n_app (n_sub e1 y e3) (n_sub e2 y e3)).  *)

Fixpoint f_pix (t: n_sexp): n_sexp :=
  match t with
  | (n_sub (n_var x) y e) => if x == y then e else (n_var x)
  | (n_sub (n_abs x e1) y e2) =>
      let (z,_) :=
        atom_fresh (fv_nom (n_abs x e1) `union` fv_nom e2 `union` {{y}}) in
      (n_abs z (n_sub (swap x z e1) y e2))
  | (n_sub (n_app e1 e2) y e3) => (n_app (n_sub e1 y e3) (n_sub e2 y e3))
  | _ => t
  end.

Inductive pix : n_sexp -> n_sexp -> Prop :=
| one_step : forall t, pix t (f_pix t).

(* Pegar uma variável que não esteja livre tanto em e1 quanto em e2 e
  fazer um swap dessa variável com o x em e1. Estou considerando que é  possível uma
  abstração conter dentro dela uma outra abstração com a mesma variável.
  ex: \x -> x (\x -> x z) *)

Inductive betapi: n_sexp -> n_sexp -> Prop :=
| b_rule : forall t u, betax t u -> betapi t u
| x_rule : forall t u, pix t u -> betapi t u.

Inductive ctx  (R : n_sexp -> n_sexp -> Prop): n_sexp -> n_sexp -> Prop :=
 | step_aeq: forall e1 e2, aeq e1 e2 -> ctx R e1 e2
 | step_redex: forall (e1 e2 e3 e4: n_sexp), aeq e1 e2 -> R e2 e3 -> aeq e3 e4 -> ctx R e1 e4
 | step_abs_in: forall (e e': n_sexp) (x: atom), ctx R e e' -> ctx R (n_abs x e) (n_abs x e')
 | step_app_left: forall (e1 e1' e2: n_sexp) , ctx R e1 e1' -> ctx R (n_app e1 e2) (n_app e1' e2)
 | step_app_right: forall (e1 e2 e2': n_sexp) , ctx R e2 e2' -> ctx R (n_app e1 e2) (n_app e1 e2')
 | step_sub_left: forall (e1 e1' e2: n_sexp) (x : atom) , ctx R e1 e1' -> ctx R (n_sub e1 x e2) (n_sub e1' x e2)
 | step_sub_right: forall (e1 e2 e2': n_sexp) (x:atom), ctx R e2 e2' -> ctx R (n_sub e1 x e2) (n_sub e1 x e2').

Definition lx t u := ctx betapi t u.

Lemma step_abs_eq: forall (e1 e2: n_sexp) (y: atom), exists (z: atom) (e: n_sexp), refltrans_aeq (ctx pix) (n_sub (n_abs y e1) y e2) (n_abs z e) /\ (n_abs z e =a n_abs y e1).
Proof.
  induction e1 using n_sexp_size_induction. generalize dependent H. case e1.
  - intros x IH e2 y. pose proof eq_dec. specialize (H x y). destruct H.
    + subst. 
Admitted.

(* Reflexive transitive closure modulo alpha equivalence 
Inductive refltrans (R: n_sexp -> n_sexp -> Prop) : n_sexp -> n_sexp -> Prop :=
| refl: forall a b, aeq a b -> (refltrans R) a b
| step: forall a b c, aeq a b -> R b c -> refltrans R a c
| rtrans: forall a b c, refltrans R a b -> refltrans R b c -> refltrans R a c.
Lemma red_rel: forall a b c d, aeq a b -> pix b c -> aeq c d -> refltrans pix a d.
Proof.
  intros a b c d H1 H2 H3.
  apply rtrans with c.
  + apply step with b; assumption.
  + apply refl.
    assumption.
Qed. 
Não resolve porque precisamos da alpha-equiv em um passo de redução
 
Definition f_is_weak_Z' (R R': Rel n_sexp) (f: n_sexp -> n_sexp) := forall a b, R a b -> ((refltrans' R') b (f a) /\ (refltrans' R') (f a) (f b)). 

Definition Z_comp_eq_aeq (R: Rel n_sexp) := exists (R1 R2: Rel n_sexp) (f1 f2: n_sexp -> n_sexp), (forall a b, R a b <-> (R1 !_! R2) a b) /\ (forall a b, R1 a b -> (f1 a) =a (f1 b)) /\ (forall a, (refltrans R1) a (f1 a)) /\ (forall b a, a = f1 b -> (refltrans R) a (f2 a)) /\ (f_is_weak_Z R2 R (f2 # f1)). *)


(*    
Definition Z_prop' (R: Rel n_sexp) := exists f: n_sexp -> n_sexp, forall a b, R a b -> ((refltrans' R) b (f a) /\ (refltrans' R) (f a) (f b)).

Lemma Z_comp_eq_implies_Z_prop: forall (R: Rel n_sexp), Z_comp_eq' R -> Z_prop' R.
Proof.
  intros R H. unfold Z_comp_eq' in H. 
  destruct H as [R1 [R2 [f1 [f2 [Hunion [H1 [H2 [H3 H4]]]]]]]]. 
  unfold Z_prop'.  exists (f2 # f1). intros a b Hab. split.
  - unfold comp. apply Hunion in Hab. inversion Hab; subst.
    + clear Hab H4. apply refltrans_composition with (f1 a).
      * apply refl_aeq. apply H1 in H.


        
        apply refltrans_composition with (f1 b).
        ** specialize (H2 b). pose proof refltrans_union_equiv R. specialize (H0 R1 R2 a b).
           apply H0.
           *** apply Hunion.
           *** admit.
        **
      *
    apply Hunion. inversion Hunion; subst; clear H.  inversion Hab; subst; clear Hab. (**
  %\comm{Since $a$ $R$-reduces in one step to $b$ and $R$ is the union of the
  relations $R1$ and $R2$ then we consider two cases:}% *)
  
  - unfold comp; split. (** %\comm{The first case is when $a \to_{R1}
    b$. This is equivalent to say that $f_2 \circ f_1$ is weak Z for
    $R1$ by $R1 \cup R2$.}% *)
    
    + apply refltrans_composition with (f1 b). (** %\comm{Therefore, we first
    prove that $b \tto_{(R1\cup R2)} (f_2 (f_1\ a))$, which can be
    reduced to $b \tto_{(R1\cup R2)} (f_1\ b)$ and $(f_1\ b)
    \tto_{(R1\cup R2)} (f_2 (f_1\ a))$ by the transitivity of
    $refltrans$.}% *)
      
      * apply refltrans_union.  apply H2. (** %\comm{From hypothesis $H2$, we
        know that $a \tto_{R1} (f_1\ a)$ for all $a$, and hence
        $a\tto_{(R1\cup R2)} (f_1\ a)$ and we conclude.}% *)
        
      * apply H1 in H.  rewrite H.  apply H3 with b; reflexivity. (**
        %\comm{The proof that $(f_1\ b)\tto_{(R1\cup R2)} (f_2 (f_1\ a))$ is
        exactly the hypothesis $H3$.}% *)

    + apply H1 in H.  rewrite H.  apply refl. (** %\comm{The proof that $(f_2
    (f_1\ a)) \tto_{(R1\cup R2)} (f_2 (f_1\ b))$ is done using the
    reflexivity of $refltrans$ because $(f_2 (f_1\ a)) = (f_2 (f_1\
    b))$ by hypothesis $H1$.}% *)
      
  - apply H4; assumption. (** %\comm{When $a \to_{R2} b$ then we are done by
    hypothesis $H4$.}% *)
Qed.
 *)

Lemma step_redex_R : forall (R : n_sexp -> n_sexp -> Prop) e1 e2,
    R e1 e2 -> ctx R e1 e2.
Proof.
  intros. pose proof step_redex. specialize (H0 R e1 e1 e2 e2).
  apply H0.
  - apply aeq_refl.
  - assumption.
  - apply aeq_refl.
Qed.

(*
(*************************************************************)
(** * An abstract machine for cbn evaluation                 *)
(*************************************************************)
(** The advantage of named terms is an efficient operational
    semantics! Compared to LN or de Bruijn representation, we
    don't need always need to modify terms (such as via open or
    shifting) as we traverse binders. Instead, as long as the
    binder is "sufficiently fresh" we can use the name as is,
    and only rename (via swapping) when absolutely
    necessary. *)
(** Below, we define an operational semantics based on an
    abstract machine. As before, it will model execution as a
    sequence of small-step transitions. However, transition
    will be between _machine configurations_, not just
    expressions.
    Our abstract machine configurations have three components
    - the current expression being evaluated the heap (aka
    - environment): a mapping between variables and expressions
    - the stack: the evaluation context of the current
    - expression
    Because we have a heap, we don't need to use substitution
    to define our semantics. To implement [x ~> e] we add a
    definition that [x] maps to [e] in the heap and then look
    up the definition when we get to [x] during evaluation.  *)
Definition heap := list (atom * n_sexp).
Inductive frame : Set := | n_app2 : n_sexp -> frame.
Notation  stack := (list frame).
Definition configuration := (heap * n_sexp * stack)%type.
(** The (small-step) semantics is a _function_ from
    configurations to configurations, until completion or
    error. *)
Inductive Step a := Error    : Step a
                  | Done     : Step a
                  | TakeStep : a -> Step a.
Definition isVal (t : n_sexp) :=
  match t with
  | n_abs _ _ => true
  | _         => false
  end.
Definition machine_step (avoid : atoms) (c : configuration) : Step configuration :=
  match c with
    (h, t, s) =>
    if isVal t then
      match s with
      | nil => Done _
      | n_app2 t2 :: s' =>
        match t with
        | n_abs x t1 =>
          (* if the bound name [x] is not fresh, we need to rename it *)
          if AtomSetProperties.In_dec x avoid  then
            let (y,_) := atom_fresh avoid in
             TakeStep _ ((y,t2)::h, swap x y t1, s')
          else
            TakeStep _ ((x,t2)::h, t1, s')
        | _ => Error _ (* non-function applied to argument *)
        end
      end
    else match t with
         | n_var x => match get x h with
                     | Some t1 => TakeStep _ (h, t1, s)
                     | None    => Error _ (* Unbound variable *)
                     end
         | n_app t1 t2 => TakeStep _ (h, t1, n_app2 t2 :: s)
         | _ => Error _ (* unreachable (value in nonValueStep) *)
         end
  end.
Definition initconf (t : n_sexp) : configuration := (nil,t,nil).
(** Example: evaluation of  "(\y. (\x. x) y) 3"
<<
     machine                                       corresponding term
      {}, (\y. (\x. x) y) 3, nil                   (\y. (\x. x) y) 3
  ==> {}, (\y. (\x. x) y), n_app2 3 :: nil         (\y. (\x. x) y) 3
  ==> {y -> 3}, (\x.x) y, nil                      (\x. x) 3
  ==> {y -> 3}, (\x.x), n_app2 y :: nil            (\x. x) 3
  ==> {x -> y, y -> 3}, x, nil                     3
  ==> {x -> y, y -> 3}, y, nil                     3
  ==> {x -> y, y -> 3}, 3, nil                     3
  ==> Done
>>
(Note that the machine takes extra steps compared to the
substitution semantics.)
We will prove that this machine implements the substitution
semantics in the next section.
*)
(** ** Recommended Exercise [values_are_done]
    Show that values don't step using this abstract machine.
    (This is a simple proof.)
*)
Lemma values_are_done : forall D t,
    isVal t = true -> machine_step D (initconf t) = Done _.
Proof.
  intros. unfold machine_step. simpl. case (isVal t) eqn:E.
  - reflexivity.
  - discriminate.
Qed.*)


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

(** Our real substitution function uses the size of the size of the term
    as that extra argument. 

Definition m_subst (u : n_sexp) (x:atom) (t:n_sexp) :=
  subst_rec (size t) t u x.
Notation "[ x := u ] t" := (m_subst u x t) (at level 60). 

Lemma m_subst_var_eq : forall u x,
    [x := u](n_var x) = u.
Proof.
  intros. unfold m_subst. simpl. rewrite eq_dec_refl. reflexivity.
Qed. 

Lemma m_subst_var_neq : forall u x y, x <> y ->
    [y := u](n_var x) = n_var x.
Proof.
  intros. unfold m_subst. simpl. destruct (y == x) eqn:Hxy.
  - subst. contradiction.
  - reflexivity.
Qed. 

Lemma m_subst_abs : forall u x y t , m_subst u x (n_abs y t)  =
       if (x == y) then (n_abs y t )
       else let (z,_) := atom_fresh (fv_nom u `union` fv_nom (n_abs y t ) `union` {{x}}) in
       n_abs z (m_subst u x (swap y z t )).
Proof.
  intros. case (x == y).
  - intros. unfold m_subst.  rewrite e. simpl. case (y == y).
    -- trivial.
    -- unfold not. intros. assert (y = y). {
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
Qed.

Corollary m_subst_abs_eq : forall u x t, [x := u](n_abs x t) = n_abs x t.
Proof.
  intros u x t.
  pose proof m_subst_abs. specialize (H u x x t). rewrite eq_dec_refl in H. assumption.
Qed.  

Corollary m_subst_abs_neq : forall u x y t, x <> y -> let (z,_) := atom_fresh (fv_nom u `union` fv_nom (n_abs y t ) `union` {{x}}) in [x := u](n_abs y t) = n_abs z ([x := u](swap y z t)).
Proof.
  intros u x y t H. pose proof m_subst_abs. specialize (H0 u x y t). destruct (x == y) eqn:Hx.
  - subst. contradiction.
  - destruct (atom_fresh (Metatheory.union (fv_nom u) (Metatheory.union (fv_nom (n_abs y t)) (singleton x)))). assumption.    
Qed.  

Lemma m_subst_notin : forall t u x, x `notin` fv_nom t -> [x := u]t = t.
Proof.
  induction t.
  - intros u x' H. unfold m_subst. simpl in *. apply notin_singleton_1' in H. destruct (x' == x) eqn:Hx.
    + subst. contradiction.
    + reflexivity.
  - intros u x' H. simpl in *.
  -
  -
  
  intros. unfold m_subst. simpl. destruct (y == x) eqn:Hxy.
  - subst. contradiction.
  - reflexivity.
Qed.

(* end hide *)

(** * The substitution lemma for the metasubstitution *)

(**
   In the pure $\lambda$-calculus, the substitution lemma is probably the first non trivial property. In our framework, we have defined two different substitution operation, namely, the metasubstitution denoted by [[x:=u]t] and the explicit substitution that has [n_sub] as a constructor. In what follows, we present the main steps of our proof of the substitution lemma for the metasubstitution operation: 
 *)

Lemma m_subst_lemma: forall e1 e2 e3 x y, x <> y -> x `notin` (fv_nom e3) ->
 ([y := e3]([x := e2]e1)) =a ([x := ([y := e3]e2)]([y := e3]e1)).
Proof.
  (** The proof is by induction on the size of [e1] using the size induction principle, named [n_sexp_size_induction] presented above. *)

  induction e1 using n_sexp_size_induction.

  (** We procced by case analisys on the structure of [e1]. The cases in between square brackets below mean that in the first case, [e1] is a variable named [z], in the second case [e1] is an abstraction of the form $\lambda$[z.e11], in the third case [e1] is an application of the form ([e11] [e12]), and finally in the fourth case [e1] is an explicit substitution of the form [e11] $\langle$ [z] := [e12] $\rangle$. *)
  
  generalize dependent e1. intro e1; case e1 as [z | z e11 | e11 e12 | e11 z e12].

  - (** The first case: [e1] is a variable, say [z], and there are several subcases to analyse. *)
    intros IH e2 e3 x y Hneq Hfv. destruct (x == z) eqn:Hxz.
    + (** In the first subcase [z] is equal to [x]. *)
      subst. rewrite (m_subst_var_neq e3 z y).
      * repeat rewrite m_subst_var_eq. apply aeq_refl.
      * assumption.
    + rewrite m_subst_var_neq.
      * (** If [z] is equal to [y] then both lhs and rhs reduces to [e3], since [x] does not occur in the set [fv_nom e3] by hypothesis. *)
        subst. apply aeq_sym. pose proof subst_fresh_eq. change (subst_rec (size e3) e3 (subst_rec (size e2) e2 e3 z) x) with (m_subst (m_subst e3 z e2) x e3). apply H. assumption.
      * (** In the last subcase [x] is not equal to [y] and not equal to [z], therefore both lhs and rhs reduces to [z]. *) 
        apply aeq_sym. change (subst_rec (size (n_var z)) (n_var z) (subst_rec (size e2) e2 e3 y) x) with (m_subst (m_subst e3 y e2) x (n_var z)). apply subst_fresh_eq. simpl. apply notin_singleton_2. intro H. subst. contradiction.
  - (** Suppose [e1] is an abstraction, say [n_abs z e11]. There are several subcases. *)
    intros IH e2 e3 x y Hneq Hfv. unfold m_subst at 2 3. simpl. destruct (x == z) eqn:Hxz.
    + (** In the first subcase, [x] is equal to [z] and both lhs and rhs reduces straightfoward to the same term. *)
      subst. change (subst_rec (size (m_subst e3 y (n_abs z e11))) (m_subst e3 y (n_abs z e11)) (m_subst e3 y e2) z) with (m_subst (m_subst e3 y e2) z (m_subst e3 y (n_abs z e11))). rewrite subst_abs_eq.
    +
Admitted.
>>>>>>> 52cf4c422428638712e894346e04a71a1e69b53f *)

(* begin hide *)
(** This next lemma uses course of values induction [lt_wf_ind] to prove that
    the size of the term [t] is enough "fuel" to completely calculate a
    substitution. Providing larger numbers produces the same result. *)

Inductive beta : n_sexp -> n_sexp -> Prop :=
| step_beta : forall (e1 e2: n_sexp) (x: atom),
    beta (n_app  (n_abs x e1) e2)  (m_subst e2 x e1).


Lemma subst_sub : forall u x y t1 t2,
    m_subst u x (n_sub t1 y t2) =
       if (x == y) then (n_sub t1 y (m_subst u x t2))
       else let (z,_) := atom_fresh (fv_nom u `union` fv_nom (n_sub t1 y t2) `union` {{x}}) in
            n_sub (m_subst u x (swap y z t1)) z (m_subst u x t2).
Proof.
  intros. case (x == y).
  - intro H; subst.
    unfold m_subst.
    simpl.
    case (y == y).
    -- intro H. Admitted.
(*       rewrite subst_size.
       --- reflexivity.
       ---  lia.
    -- intro H.
      contradiction.      
  - intro Hneq.
    unfold m_subst.
    simpl.
    case (x == y).
    -- intro H; contradiction.
    -- intro Hneq'.
       destruct (atom_fresh (Metatheory.union (fv_nom u)
        (Metatheory.union (Metatheory.union (remove y (fv_nom t1)) (fv_nom t2)) (singleton x)))).
       pose proof subst_size. 
       rewrite swap_size_eq.
       specialize (H (size t1 + size t2) u x (swap y x0 t1)).
       rewrite H.
       --- rewrite swap_size_eq.
           pose proof subst_size. 
           specialize (H0 (size t1 + size t2) u x t2).
           rewrite H0.
           ---- reflexivity.
           ---- lia.
       --- rewrite swap_size_eq.
           lia.
Qed. *)
  
Lemma pure_m_subst : forall t u x, pure u -> pure t -> pure (m_subst u x t).
Proof.
  induction t using n_sexp_induction.
  - intros. unfold m_subst. simpl. case (x0 == x).
    -- intros. Admitted.
(*       assumption.
    -- intros. assumption.
  - intros. unfold m_subst. simpl. case (x==z).
    -- intros; subst. assumption.
    -- intros. destruct (atom_fresh
         (Metatheory.union (fv_nom u)
                (Metatheory.union (remove z (fv_nom t)) (singleton x)))).
       apply pure_abs. inversion H1. unfold m_subst in H.
       pose proof pure_swap. specialize (H5 z x0 t).
       pose proof H3. apply H5 in H6; clear H5.
       specialize (H t z x0). assert (size t = size t). {
         reflexivity.
       }
       specialize (H H5 u x); clear H5. rewrite swap_size_eq in H.
       apply H.
    --- assumption.
    --- assumption.
  - unfold m_subst; unfold m_subst in IHt1; unfold m_subst in IHt2.
    intros. simpl. inversion H0.
    clear H1; clear H2; clear e1; clear e2. apply pure_app.
    -- specialize (IHt1 u x).
       assert (size t1 <= size t1 + size t2). {
         apply le_plus_l.
       }
       pose proof subst_size.
       specialize (H2 (size t1 + size t2) u x t1).
       apply H2 in H1; clear H2. rewrite H1. apply IHt1.
    --- assumption.
    --- assumption.
    -- specialize (IHt2 u x).
       assert (size t2 <= size t1 + size t2). {
         apply le_plus_r.
       }
       pose proof subst_size.
       specialize (H2 (size t1 + size t2) u x t2).
       apply H2 in H1; clear H2. rewrite H1. apply IHt2.
    --- assumption.
    --- assumption.
  - intros. inversion H1.
Qed. *)

(* Não é possível provar esse lema porque ele não é correto,
   pois se não existirem y em t não ocorrera a substituição
   por u e as variáveis livres de u não estarão no conjunto
   de variáveis livres

   Lemma fv_nom_abs_subst_aux: forall t u y,
    fv_nom (subst_rec (size t) t u y) [=] 
    (remove y (fv_nom t)) `union` (fv_nom u).

  mas podemos provar o seguinte: *)

Lemma fv_nom_subst_subset: forall t u x, fv_nom (m_subst u x t) [<=] (remove x (fv_nom t)) `union` (fv_nom u). 
Proof.
  induction t using n_sexp_induction.
  - intros u x'. unfold m_subst.
    simpl. destruct (x' == x).
    +  Admitted.

(** ** Challenge Exercise [m_subst properties]
    Now show the following property by induction on the size of terms. *)

Lemma subst_same_aux : forall n, forall t y, size t <= n -> aeq (m_subst (n_var y) y t)  t.
Proof.
  intro n. induction n.
  - intros t y SZ. destruct t; simpl in SZ; lia.
  - intros t y SZ. destruct t; simpl in SZ.
    -- unfold m_subst. simpl. case (y == x).
       --- intros. rewrite e. rewrite subst_rec_fun_equation. default_simp.
       --- intros. rewrite subst_rec_fun_equation. default_simp.
    -- Admitted.
(* rewrite subst_abs.
       case (y == x).
       --- intros. apply aeq_refl.
       --- intros. simpl.
           destruct (atom_fresh
           (Metatheory.union (singleton y)
                  (Metatheory.union (remove x (fv_nom t)) (singleton y)))).
           case (x == x0).
           ---- intro Heq; subst.
                rewrite swap_id.
                apply aeq_abs_same.
                apply IHn.
                apply Sn_le_Sm__n_le_m in SZ.
                assumption.
           ---- intro Hneq.
                apply aeq_abs_diff.
                ----- apply aux_not_equal. assumption.
                ----- apply notin_union_2 in n1.
                      apply notin_union_1 in n1.
                      apply notin_remove_1 in n1.
                      destruct n1.
                      ------ contradiction.
                      ------ assumption.
                      ----- apply IHn.
                            rewrite swap_size_eq.
                            apply Sn_le_Sm__n_le_m in SZ.
                            assumption.
    -- rewrite subst_app.
       apply aeq_app.
       --- apply IHn. apply Sn_le_Sm__n_le_m in SZ.
           transitivity (size t1 + size t2).
       ---- apply le_plus_l.
       ---- assumption.
       --- apply IHn. apply Sn_le_Sm__n_le_m in SZ.
           transitivity (size t1 + size t2).
       ---- apply le_plus_r.
       ---- assumption.
    -- rewrite subst_sub. case (y == x).
       --- intro Heq; subst. apply aeq_sub_same.
           ---- apply aeq_refl.
           ---- apply IHn. apply le_S_n in SZ.
                apply (Nat.le_trans (size t2) (size t1 + size t2) n).
                ----- lia.
                ----- assumption.
       --- intro Hneq.
           simpl.
           destruct (atom_fresh
           (Metatheory.union (singleton y)
                  (Metatheory.union (Metatheory.union (remove x (fv_nom t1)) (fv_nom t2)) (singleton y)))).
           case (x == x0).
             ---- intros; subst. rewrite swap_id.
                  apply aeq_sub_same.
                  ----- specialize (IHn t1 y); apply IHn.
                        apply Sn_le_Sm__n_le_m in SZ.
                        transitivity (size t1 + size t2).
                  ------ apply le_plus_l.
                  ------ assumption.
                  ----- specialize (IHn t2 y); apply IHn.
                        apply Sn_le_Sm__n_le_m in SZ.
                        transitivity (size t1 + size t2).
                  ------ apply le_plus_r.
                  ------ assumption.
             ---- intro Hneq'.
                  apply aeq_sub_diff.
                  ----- specialize (IHn t2 y); apply IHn.
                        apply Sn_le_Sm__n_le_m in SZ.
                        transitivity (size t1 + size t2).
                  ------ apply le_plus_r.
                  ------ assumption.
                  ----- apply aux_not_equal in Hneq'; assumption.
                  ----- apply notin_union_2 in n0.
                        repeat apply notin_union_1 in n0.
                        apply notin_remove_1 in n0. inversion n0.
                   ------ contradiction.
                   ------ assumption.
                   ----- specialize (IHn (swap x x0 t1) y).
                         apply IHn. rewrite swap_size_eq.
                         apply Sn_le_Sm__n_le_m in SZ.
                         transitivity (size t1 + size t2).
                   ------ apply le_plus_l.
                   ------ assumption.
Qed. *)

Lemma subst_same : forall t y, aeq (m_subst (n_var y) y t)  t.
Proof.
  intros.
  apply subst_same_aux with (n := size t). auto.
Qed.

Lemma size_gt_0: forall t, size t > 0.
Proof.
  induction t.
  - simpl. unfold gt. unfold lt. reflexivity.
  - simpl. unfold gt; unfold gt in IHt. unfold lt; unfold lt in IHt.
    default_simp.
  - simpl. unfold gt; unfold gt in IHt1; unfold gt in IHt2.
    unfold lt; unfold lt in IHt1; unfold lt in IHt2.
    inversion IHt1.
    -- inversion IHt2.
       --- simpl. default_simp.
       --- simpl. default_simp.
    -- inversion IHt2.
       --- assert (S m + 1 = 1 + S m). {
             apply plus_comm.
           }
           subst. simpl. default_simp. rewrite H3. default_simp.
       --- simpl. assert (m + S m0 = S m0 + m). {
             apply plus_comm.
           }
           rewrite H3. simpl. default_simp. repeat apply le_S.
           default_simp. assert (m0 <= m0 + m). {
             apply le_plus_l.
           }
           transitivity (m0).
           + assumption.
           + assumption.
 - simpl. unfold gt; unfold gt in IHt1; unfold gt in IHt2.
   unfold lt; unfold lt in IHt1; unfold lt in IHt2.
   inversion IHt1.
    -- inversion IHt2.
       --- simpl. default_simp.
       --- simpl. default_simp.
    -- inversion IHt2.
       --- assert (S m + 1 = 1 + S m). {
             apply plus_comm.
           }
           subst. simpl. default_simp. rewrite H3. default_simp.
       --- simpl. assert (m + S m0 = S m0 + m). {
             apply plus_comm.
           }
           rewrite H3. simpl. default_simp. repeat apply le_S.
           default_simp. assert (m0 <= m0 + m). {
             apply le_plus_l.
           }
           transitivity (m0).
           + assumption.
           + assumption.
Qed.


Lemma subst_fresh_eq_aux : forall n, forall (x : atom) t u, size t <= n ->
  x `notin` fv_nom t -> aeq (m_subst u x t) t.
Proof.
  intro n; induction n.
  - intros x t u H.
    assert (H': size t > 0).
    {
      apply size_gt_0.
    }
    unfold gt in H'.
    assert (H'': size t < size t).
    {
      apply Nat.le_lt_trans with 0; assumption.
    }
    assert (H''': ~(size t < size t)).
              {
                apply Nat.lt_irrefl.
              }
    contradiction.
  - destruct t.
    + intros. unfold m_subst. simpl. case (x == x0).
    -- intros. simpl in H0. pose proof singleton_iff.
       specialize (H1 x0 x). symmetry in e; apply H1 in e. 
       contradiction.
    -- intros. unfold m_subst; simpl. case (x == x0).
       --- intros; contradiction.
       --- Admitted.  (* intros; apply aeq_var.
    + intros. rewrite subst_abs.
      case (x == x0).
    -- intros. apply aeq_refl.
    -- intros.
       simpl.
       destruct (atom_fresh
                   (Metatheory.union (fv_nom u)
                          (Metatheory.union (remove x0 (fv_nom t)) (singleton x)))).
       pose proof notin_remove_1.
       specialize (H1 x0 x (fv_nom t)).
       simpl in H0.
       apply H1 in H0.
       clear H1.
       inversion H0; clear H0.
       --- symmetry in H1. contradiction.
       --- case (x1 == x0).
           ---- intro; subst.
                rewrite swap_id.
                apply aeq_abs_same.
                apply IHn.
                ----- simpl in H.
                      apply Sn_le_Sm__n_le_m in H; assumption.
                ----- assumption.
           ---- intro.
                apply aeq_abs_diff.
                ----- assumption.
                ----- apply notin_union_2 in n1.
                      apply notin_union_1 in n1.
                      apply notin_remove_1 in n1.
                      inversion n1.
                      ------ symmetry in H0; contradiction.
                      ------ assumption.
                ----- apply IHn.
                ------ rewrite swap_size_eq.
                       simpl in H.
                       apply Sn_le_Sm__n_le_m in H; assumption.
                ------ apply notin_union_2 in n1.
                      apply notin_union_2 in n1.
                      apply notin_singleton_1 in n1.
                      pose proof notin_fv_nom_equivariance.
                      specialize (H0 x x0 x1 t). 
                      apply H0 in H1.
                      assert (H2: swap_var x0 x1 x = x).
                      {
                        unfold swap_var.
                        default_simp.
                      }
                      rewrite H2 in H1.
                      assumption.
    + intros. simpl. simpl in H. pose proof le_plus_l.
      specialize (H1 (size t1) (size t2)).
      apply Sn_le_Sm__n_le_m in H as HH.
      apply Sn_le_Sm__n_le_m in H. pose proof le_trans.
      specialize (H2 (size t1) (size t1 + size t2) n).
      apply H2 in H1.
      -- pose proof le_plus_l. specialize (H3 (size t2) (size t1)).
         rewrite plus_comm in H. pose proof le_trans.
         specialize (H4 (size t2) (size t1 + size t2) n).
         rewrite plus_comm in H2. rewrite plus_comm in H4.
         apply H4 in H3.
         --- pose proof H0 as H'. simpl in H0.
             apply notin_union_2 in H0.
             simpl in H'. apply notin_union_1 in H'.
             rewrite subst_app. pose proof IHn as IHn'.
             specialize (IHn x t1 u); specialize (IHn' x t2 u).
             apply IHn in H1.
             ---- apply IHn' in H3.
             ----- apply aeq_app.
             ------ assumption.
             ------ assumption.
             ----- assumption.
             ---- assumption.
         --- assumption.
      -- assumption.
    + intros. unfold m_subst; simpl. default_simp.
      -- apply aeq_sub_same.
         --- apply aeq_refl.
         --- rewrite subst_size.
             ---- apply IHn.
                  ----- apply le_S_n in H.
                        apply (le_trans (size t2) (size t1 + size t2) n).
                        ------ lia.
                        ------ assumption.
                  ----- apply (notin_union_2 _ _ _ H0).
             ---- lia.
      -- case (x1 == x0); intros; subst.
         --- apply aeq_sub_same.
             ---- rewrite swap_id.
                  assert (size t1 <= size t1 + size t2).
                  apply le_plus_l.
                  apply subst_size with (size t1 + size t2) u x t1 in H1.
                  rewrite H1.
                  apply notin_union_1 in H0.
                  apply notin_remove_1 in H0.
                  inversion H0.
             ----- symmetry in H2; contradiction.
             ----- apply IHn.
             ------ apply le_S_n in H.
                    apply Nat.le_trans with (size t1 + size t2).
             ------- apply le_plus_l.
             ------- assumption.
             ------ assumption.
             ---- assert (size t2 <= size t1 + size t2).
                  apply le_plus_r.
                  apply subst_size with (size t1 + size t2) u x t2 in H1.
                  rewrite H1.
                  pose proof H0.
                  apply notin_union_1 in H0.
                  apply notin_remove_1 in H0.
                  inversion H0.
             ----- symmetry in H3; contradiction.
             ----- apply IHn.
             ------ apply le_S_n in H.
                    apply Nat.le_trans with (size t1 + size t2).
             ------- apply le_plus_r.
             ------- assumption.
             ------ repeat apply notin_union_2 in H2. assumption.
         --- assert (size (swap x0 x1 t1) <= size t1 + size t2). {
               rewrite swap_size_eq.
               apply le_plus_l.
             }
             assert (size t2 <= size t1 + size t2). apply le_plus_r.
             apply subst_size with (size t1 + size t2) u x (swap x0 x1 t1) in H1.
             apply subst_size with (size t1 + size t2) u x t2 in H2.
             rewrite H1; rewrite H2.
             apply aeq_sub_diff.
             ---- apply IHn.
             ----- apply le_S_n in H.
                   apply Nat.le_trans with (size t1 + size t2).
             ------ apply le_plus_r.
             ------ assumption.
             ----- repeat apply notin_union_2 in H0. assumption.
             ---- assumption.
             ---- apply notin_union_2 in n0.
                  repeat apply notin_union_1 in n0.
                  apply notin_remove_1 in n0.
             ----- inversion n0.
             ------ symmetry in H3; contradiction.
             ------ assumption.
             ---- apply IHn.
             ----- rewrite swap_size_eq. apply le_S_n in H.
                   apply Nat.le_trans with (size t1 + size t2).
             ------- apply le_plus_l.
             ------- assumption.
             ----- apply notin_union_1 in H0.
                   pose proof n0.
                   apply notin_union_2 in n0.
                   repeat apply notin_union_1 in n0.
                   apply notin_remove_1 in H0.
                   apply notin_remove_1 in n0.
                   inversion H0; inversion n0; subst.
             ------ contradiction.
             ------ contradiction.
             ------ contradiction.
             ------ apply notin_union_2 in H3.
                    apply notin_union_2 in H3.
                    apply notin_singleton_1 in H3.
                    apply fv_nom_remove_swap.
             ------- assumption.
             ------- assumption.
             ------- assumption.
Qed. *)

Lemma subst_fresh_eq : forall (x : atom) t u,  x `notin` fv_nom t -> aeq (m_subst u x t) t.
Proof.
  intros. apply subst_fresh_eq_aux with (n := size t). lia. auto.
Qed.

Lemma aeq_n_sub_compat: forall t1 t1' t2 x, aeq t1 t1' -> aeq (n_sub t1 x t2) (n_sub t1' x t2).
Proof.
  Admitted.

Lemma aeq_n_sub_in_compat: forall t1 t2 t2' x, aeq t2 t2' -> aeq (n_sub t1 x t2) (n_sub t1 x t2').
Proof.
  induction 1.
  - apply aeq_sub_same; apply aeq_refl.
  - apply aeq_sub_same.
   + apply aeq_refl.
   + apply aeq_abs_same.
     assumption.
  - apply aeq_sub_same.
    + apply aeq_refl.
    + apply aeq_abs_diff; assumption.
  - apply aeq_sub_same.
    + apply aeq_refl.
    + apply aeq_app; assumption.
  - apply aeq_sub_same.
    + apply aeq_refl.
    + apply aeq_sub_same; assumption.
  - apply aeq_sub_same.
    + apply aeq_refl.
    + apply aeq_sub_diff; assumption.
Qed.

Lemma aeq_swap0: forall x y t, x `notin` fv_nom t -> y `notin` fv_nom t -> 
  aeq t (swap x y t).
Proof.
  induction t;intros.
  - simpl. unfold swap_var. apply notin_singleton_1 in H. apply notin_singleton_1 in H0.
    default_simp.
  - simpl in *. unfold swap_var. case (x0 == x);intros.
    -- rewrite e. case (x == y);intros.
       --- rewrite e0. rewrite swap_id. apply aeq_refl.
       --- apply aeq_abs_diff. assumption.
           ---- apply fv_nom_swap.
                apply (diff_remove_2 y x0).
                * rewrite e. default_simp.
                * assumption.
           ---- rewrite swap_symmetric. rewrite swap_involutive. apply aeq_refl.
    -- case (x0 == y);intros.
       --- rewrite e. apply aeq_abs_diff.
           ---- rewrite e in n. assumption.
           ---- rewrite swap_symmetric.
                apply fv_nom_swap. apply (diff_remove_2 x x0).
                * default_simp.
                * assumption.
           ---- rewrite swap_involutive. apply aeq_refl.
       --- apply aeq_abs_same. apply diff_remove_2 in H.
           ---- apply diff_remove_2 in H0.
                ----- apply (IHt H H0).
                ----- default_simp.
           ---- default_simp.
  - simpl in *. apply aeq_app.
    -- apply notin_union_1 in H. apply notin_union_1 in H0.
       apply (IHt1 H H0).
    -- apply notin_union_2 in H. apply notin_union_2 in H0.
       apply (IHt2 H H0).
  - simpl in *. unfold swap_var. case (x0 == x);intros.
    -- rewrite e. case (x == y);intros.
       --- rewrite e0. rewrite swap_id. rewrite swap_id.
           apply aeq_refl.
       --- apply aeq_sub_diff.
           ---- apply notin_union_2 in H. apply notin_union_2 in H0.
                apply (IHt2 H H0).
           ---- assumption.
           ---- apply fv_nom_swap. apply (diff_remove_2 y x0).
                * rewrite e. default_simp.
                * apply notin_union_1 in H0. assumption.
           ---- rewrite swap_symmetric. rewrite swap_involutive.
                apply aeq_refl.
    -- case (x0 == y);intros.
       --- apply aeq_sub_diff.
           ---- apply notin_union_2 in H. apply notin_union_2 in H0.
                apply (IHt2 H H0).
           ---- assumption.
           ---- rewrite e. rewrite swap_symmetric. apply fv_nom_swap. apply (diff_remove_2 x x0).
                * default_simp.
                * apply notin_union_1 in H. assumption.
           ---- rewrite e. rewrite swap_involutive. apply aeq_refl.
       --- apply aeq_sub_same.
           ---- apply notin_union_1 in H. apply notin_union_1 in H0.
                apply (diff_remove_2 _ x0) in H.
                ----- apply (diff_remove_2 _ x0) in H0.
                      * apply (IHt1 H H0).
                      * default_simp.
                ----- default_simp.
           ---- apply notin_union_2 in H. apply notin_union_2 in H0.
                apply (IHt2 H H0).
Qed.
(* end hide *)
