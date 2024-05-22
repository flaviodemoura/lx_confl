(** * A nominal representation of the lambda_x calculus. *)

Require Export Arith Lia.
Require Export Metalib.Metatheory.
Require Export Metalib.LibDefaultSimp.
Require Export Metalib.LibLNgen.

Require Import ZtoConfl_nom.
Require Import lambda_es.

Inductive pure : n_sexp -> Prop :=
 | pure_var : forall x, pure (n_var x)
 | pure_app : forall e1 e2, pure e1 -> pure e2 -> pure (n_app e1 e2) 
 | pure_abs : forall x e1, pure e1 -> pure (n_abs x e1).

(** move to lambda_es.v *)
Lemma notin_singleton_is_false: forall x, x `notin` (singleton x) -> False.
Proof.
  intros. intros. apply notin_singleton_1 in H. contradiction.
Qed.

Lemma in_or_notin: forall x s, x `in` s \/ x `notin` s.
Proof.
  intros. pose proof notin_diff_1. specialize (H x s s).
  rewrite AtomSetProperties.diff_subset_equal in H.
  - apply or_comm. apply H. apply notin_empty_1.
  - reflexivity.
Qed.

Example swap1 : forall x y z, x <> z -> y <> z ->
    swap x y (n_abs z (n_app (n_var x)(n_var y))) = n_abs z (n_app (n_var y) (n_var x)).
Proof.
  intros. simpl; unfold vswap; default_simp.
Qed.

Example swap2 : forall x y, x <> y ->
    swap x y (n_abs x (n_var x)) = n_abs y (n_var y).
Proof.
  intros. simpl; unfold vswap; default_simp.
Qed.

Example swap3 : forall x y, x <> y ->
     swap x y (n_abs y (n_var x)) = n_abs x (n_var y).
Proof.
  intros. simpl; unfold vswap; default_simp.
Qed.

Lemma diff_equal: forall s s' t,
    s [=] s' -> AtomSetImpl.diff s t [=] AtomSetImpl.diff s' t.
Proof.
intros. rewrite H. reflexivity.
Qed.

Lemma swap_symmetric_2: forall x y x' y' t,
    x <> x' -> y <> y' -> x <> y'-> y <> x' -> swap x y (swap x' y' t) = swap x' y' (swap x y t). 
Proof.
  intros. induction t; simpl in *; unfold vswap in *; default_simp.
Qed.

Lemma in_fv_nom_equivariance : forall x y x0 t, x0 `in` fv_nom t -> vswap x y x0 `in` fv_nom (swap x y t).
Proof.
  induction t.
  - simpl. intro H. pose proof singleton_iff.
    specialize (H0 x1 x0). apply H0 in H. rewrite H.
    apply singleton_iff. reflexivity.
  - simpl. intros. unfold vswap. default_simp.
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
             unfold vswap in IHt. case (x == x) in IHt.
             ++ apply AtomSetImpl.remove_3 in n.
                apply IHt in n. assumption.
             ++ unfold not in n0. contradiction. 
           + apply AtomSetImpl.remove_3 in H. assumption.
    -- apply AtomSetImpl.remove_2.
       --- assumption.
       --- apply AtomSetImpl.remove_3 in H. apply IHt in H.
           unfold vswap in H. case (x == x) in H.
           + assumption.
           + contradiction.
    -- apply AtomSetImpl.remove_2.
       --- assumption.
       --- apply AtomSetImpl.remove_3 in H. unfold vswap in IHt.
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
    -- unfold vswap in IHt. case (y == x) in IHt.
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
       unfold vswap in H. case(x0 == x) in H.
       --- contradiction.
       --- case(x0 == y) in H.
           + pose proof AtomSetImpl.remove_2.
             specialize (H0 (fv_nom (swap x y t)) y x0).
             apply aux_not_equal in n0. apply H0 in n0.
             ++ assumption.
             ++ symmetry in e. contradiction.
           + unfold vswap in IHt. case (x0 == x) in IHt.
             ++ contradiction.
             ++ pose proof AtomSetImpl.remove_2.
                specialize (H0 (fv_nom (swap x y t)) y x0).
                apply aux_not_equal in n0. apply H0 in n0.
                +++ assumption.
                +++ assumption.
    -- unfold vswap in IHt. default_simp.
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
             unfold vswap in IHt. case (x0 == x) in IHt.
             ++ contradiction.
             ++ case (x0 == y) in IHt.
                +++ contradiction.
                +++ apply IHt in H. pose proof remove_neq_iff.
                    specialize (H0 (fv_nom (swap x y t)) x1 x0).
                    apply aux_not_equal in n4.
                    apply H0 in n4. apply n4 in H. assumption.      
  - unfold vswap. unfold vswap in IHt1.
    unfold vswap in IHt2. default_simp.
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
  - intros. simpl. unfold vswap. case (x == y).
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
           + right. simpl. apply IHt2 in H3. unfold vswap in H3.
             case (x == x) in H3.
             ++ assumption.
             ++ contradiction.
       --- apply union_iff in H. apply union_iff. inversion H.
           + unfold vswap in IHt2. case (x == x) in IHt2.
             ++ apply remove_iff in H0. inversion H0.
                unfold vswap in IHt1. case (x == x) in IHt1.
                +++ apply IHt1 in H1. pose proof remove_neq_iff.
                    left. apply H3.
                    * assumption.
                    * assumption.                
                +++ contradiction.
             ++ contradiction.
           + apply IHt2 in H0. unfold vswap in H0.
             case (x == x) in H0.
             ++ right. assumption.
             ++ contradiction.
       --- apply union_iff. apply union_iff in H. inversion H.
           + apply remove_neq_iff in H0. apply IHt1 in H0.
             unfold vswap in H0. case (x == x) in H0.
             ++ left. apply remove_iff. split.
                +++ assumption.
                +++ assumption.
             ++ contradiction.
             ++ assumption.
           + apply IHt2 in H0. unfold vswap in H0.
             case (x == x) in H0.
             ++ right. assumption.
             ++ contradiction.
       --- apply union_iff. apply union_iff in H. inversion H.
           + apply remove_neq_iff in H0. apply IHt1 in H0.
             unfold vswap in H0. case (y == x) in H0.
             ++ contradiction.
             ++ case (y == y) in H0.
                +++ left. apply remove_iff. split.
                    * assumption.
                    * assumption.
                +++ contradiction.
             ++ assumption.
           + apply IHt2 in H0. unfold vswap in H0.
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
           unfold vswap in IHt2. case (y == x) in IHt2.
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
             unfold vswap in H0. case (y == x) in H0.
             ++ contradiction.
             ++ case (y == y) in H0.
                +++ left. apply remove_neq_iff.
                    * assumption.
                    * assumption.
                +++ contradiction.
             ++ assumption.  
           + apply IHt2 in H0. unfold vswap in H0.
             case (y == x) in H0.
             ++ contradiction.
             ++ case (y == y) in H0.
                +++ right. assumption.
                +++ contradiction.
       --- apply union_iff. apply union_iff in H. inversion H.
           + apply remove_neq_iff in H0. apply IHt1 in H0.
             unfold vswap in H0. case (x0 == x) in H0.
             ++ contradiction.
             ++ case (x0 == y) in H0.
                +++ contradiction.
                +++ left. apply remove_neq_iff.
                    * apply aux_not_equal. assumption.
                    * assumption.
             ++ apply aux_not_equal. assumption.  
           + apply IHt2 in H0. unfold vswap in H0.
             case (x0 == x) in H0.
             ++ contradiction.
             ++ case (x0 == y) in H0.
                +++ contradiction.
                +++ right. assumption. 
       --- apply union_iff. apply union_iff in H. inversion H.
           + apply remove_neq_iff in H0.
             ++ apply IHt1 in H0. unfold vswap in H0.
                case (x0 == x) in H0.
                +++ contradiction.
                +++ case (x0 == y) in H0.
                    * contradiction.
                    * left. apply remove_neq_iff.
                      ** apply aux_not_equal. assumption.
                      ** assumption.
             ++ apply aux_not_equal. assumption.
           + apply IHt2 in H0. unfold vswap in H0.
             case (x0 == x) in H0.
             ++ contradiction.
             ++ case (x0 == y) in H0.
                +++ contradiction.
                +++ right. assumption.
       --- apply union_iff. apply union_iff in H. case (x1 == x0).
           + intros. right. inversion H.
             ++ rewrite e in H0. apply remove_iff in H0.
                inversion H0. contradiction.
             ++ apply IHt2 in H0. unfold vswap in H0.
                case (x0 == x) in H0.
                +++ contradiction.
                +++ case (x0 == y) in H0.
                    * contradiction.
                    * assumption.
           + inversion H.
             ++ intros. apply remove_neq_iff in H0.
                +++ apply IHt1 in H0. unfold vswap in H0.
                case (x0 == x) in H0.
                    * contradiction.
                    * case (x0 == y) in H0.
                      ** contradiction.
                      ** left. apply remove_neq_iff.
                         *** assumption.
                         *** assumption.
                +++ assumption.
             ++ intros. apply IHt2 in H0. unfold vswap in H0.
                case (x0 == x) in H0.
                +++ contradiction.
                +++ case (x0 == y) in H0.
                    * contradiction.
                    * right. assumption.
Qed.

Lemma Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof.
  intros n m H. inversion H.
  - apply le_n.
  - apply (le_trans n (S n) m).
    + apply le_S. reflexivity.
    + assumption.
Qed.
(** fim - mover para lambda_es.v *)

Lemma pure_swap : forall x y t, pure t -> pure (swap x y t).
Proof.
  intros x y t H. induction H.
  - simpl. unfold vswap. case (x0 == x); case (x0 == y); intros; subst; apply pure_var.
  - simpl. apply pure_app; assumption.
  - simpl. unfold vswap. case (x0 == x); case (x0 == y); intros; subst; apply pure_abs; assumption.
Qed.

Lemma pure_m_subst : forall t u x, pure t -> pure u -> pure ({x := u}t).
Proof.
  induction t as [y | t1 y IHt1 | t1 t2 IHt1 IHt2 | t1 t2 y IHt1 IHt2] using n_sexp_induction.
  - intros u x H1 H2. unfold m_subst. rewrite subst_rec_fun_equation. destruct (x == y).
    + assumption.
    + assumption.
  - intros u x H1 H2. unfold m_subst in *. rewrite subst_rec_fun_equation. destruct (x == y).
    + assumption.
    + destruct (atom_fresh (union (fv_nom u) (union (fv_nom (n_abs y t1)) (singleton x)))) as [z Hnotin]. apply pure_abs. inversion H1; subst. pose proof pure_swap as H'. specialize (H' y z t1). pose proof H0 as H''. apply H' in H''. clear H'. apply IHt1.
      * rewrite swap_size_eq. reflexivity.
      * assumption.
      * assumption.
  - intros u x Happ Hpure. inversion Happ; subst. unfold m_subst in *. rewrite subst_rec_fun_equation. apply pure_app.
    + apply IHt1; assumption.
    + apply IHt2; assumption.
  - intros u x Hsubst Hpure. inversion Hsubst. 
Qed. 
  
Fixpoint num_occ x t : nat :=
  match t with
  | n_var y => if (x == y) then 1 else 0
  | n_abs y t1 => if (x == y) then 0 else num_occ x t1
  | n_app t1 t2 => (num_occ x t1) + (num_occ x t2)
  | n_sub t1 y t2 => if (x == y) then num_occ x t2 else (num_occ x t1) + (num_occ x t2)
  end.

Lemma swap_same_occ: forall x y t, num_occ y (swap x y t) = num_occ x t.
Proof.
  induction t; simpl; unfold vswap; default_simp.
Qed.

Lemma swap_diff_occ: forall x y z t, x <> y -> x <> z -> num_occ x (swap y z t) = num_occ x t.
Proof.
  induction t; simpl; unfold vswap; default_simp.
Qed.

(* The n_sub constructor is part of the grammar of the terms, therefore the definition size' (n_sub t1 x t2) is computing the size of the normal form of the term (n_sub t1 x t2), and not the size of the term itself.
Fixpoint size' (t : n_sexp) : nat :=
  match t with
  | n_var x => 1
  | n_abs x t => 1 + size' t
  | n_app t1 t2 => 1 + size' t1 + size' t2
  | n_sub t1 x t2 => size' t1 + ((num_occ x t1) * ((size' t2) - 1))
  end.  

Lemma swap_comp: forall t x y z,
    x <> z -> y <> z -> x `notin` fv_nom t -> y `notin` fv_nom t -> aeq (swap y x (swap y z t)) (swap x z t).
Proof.
Admitted.

false: take t = y or t = x
Lemma swap_trans: forall t x y z, (swap x y (swap y z t)) = swap x z t. *)
    
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
    pix (n_sub (n_app e1 e2) y e3) (n_app (n_sub e1 y e3) (n_sub e2 y e3)). *)

(* sempre renomeia, como m_subst. *)
Inductive pix : n_sexp -> n_sexp -> Prop :=
| step_var : forall (e: n_sexp) (y: atom),
    pix (n_sub (n_var y) y e) e
| step_gc : forall (e: n_sexp) (x y: atom),
    x <> y -> pix (n_sub (n_var x) y e) (n_var x)
| step_abs1 : forall (e1 e2: n_sexp) (y : atom),
    pix (n_sub (n_abs y e1) y e2)  (n_abs y e1)
| step_abs2 : forall (e1 e2: n_sexp) (x y z: atom),
    x <> y -> z <> x -> z <> y -> z `notin` fv_nom e1 -> z `notin` fv_nom e2 -> 
                   pix (n_sub (n_abs x e1) y e2)  (n_abs z (n_sub (swap x z e1) y e2))
| step_app : forall (e1 e2 e3: n_sexp) (y: atom),
    pix (n_sub (n_app e1 e2) y e3) (n_app (n_sub e1 y e3) (n_sub e2 y e3)).

(* Pegar uma variável que não esteja livre tanto em e1 quanto em e2 e
  fazer um swap dessa variável com o x em e1. Estou considerando que é  possível uma
  abstração conter dentro dela uma outra abstração com a mesma variável.
  ex: \x -> x (\x -> x z) *)


Inductive betapi: Rel n_sexp :=
| b_rule : forall t u, betax t u -> betapi t u
| x_rule : forall t u, pix t u -> betapi t u.

(* Inductive ctx  (R : Rel n_sexp): Rel n_sexp :=
 | step_aeq: forall e1 e2, e1 =a e2 -> ctx R e1 e2
 | step_redex: forall (e1 e2 e3 e4: n_sexp), aeq e1 e2 -> R e2 e3 -> aeq e3 e4 -> ctx R e1 e4
 | step_abs_in: forall (e e': n_sexp) (x: atom), ctx R e e' -> ctx R (n_abs x e) (n_abs x e')
 | step_app_left: forall (e1 e1' e2: n_sexp) , ctx R e1 e1' -> ctx R (n_app e1 e2) (n_app e1' e2)
 | step_app_right: forall (e1 e2 e2': n_sexp) , ctx R e2 e2' -> ctx R (n_app e1 e2) (n_app e1 e2')
 | step_sub_left: forall (e1 e1' e2: n_sexp) (x : atom) , ctx R e1 e1' -> ctx R (n_sub e1 x e2) (n_sub e1' x e2)
 | step_sub_right: forall (e1 e2 e2': n_sexp) (x:atom), ctx R e2 e2' -> ctx R (n_sub e1 x e2) (n_sub e1 x e2'). *)

Inductive ctx  (R : Rel n_sexp): Rel n_sexp :=
 | step_aeq: forall e1 e2, e1 =a e2 -> ctx R e1 e2
 | step_redex: forall (e1 e2 e3 e4: n_sexp), aeq e1 e2 -> R e2 e3 -> aeq e3 e4 -> ctx R e1 e4
 | step_abs_in: forall (e e': n_sexp) (x: atom), ctx R e e' -> ctx R (n_abs x e) (n_abs x e')
 | step_app_left: forall (e1 e1' e2: n_sexp) , ctx R e1 e1' -> ctx R (n_app e1 e2) (n_app e1' e2)
 | step_app_right: forall (e1 e2 e2': n_sexp) , ctx R e2 e2' -> ctx R (n_app e1 e2) (n_app e1 e2')
 | step_sub_left: forall (e1 e1' e2: n_sexp) (x : atom) , ctx R e1 e1' -> ctx R (n_sub e1 x e2) (n_sub e1' x e2)
 | step_sub_right: forall (e1 e2 e2': n_sexp) (x:atom), ctx R e2 e2' -> ctx R (n_sub e1 x e2) (n_sub e1 x e2').
Definition lx t u := ctx betapi t u.

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
 
Definition f_is_weak_Z' (R R': Rel n_sexp) (f: n_sexp -> n_sexp) := forall a b, R a b -> ((refltrans' R') b (f a) /\ (refltrans' R') (f a) (f b)). *)


Lemma step_redex_R : forall (R : n_sexp -> n_sexp -> Prop) e1 e2, R e1 e2 -> ctx R e1 e2.
Proof.
  intros. pose proof step_redex. specialize (H0 R e1 e1 e2 e2). apply H0.
  - apply aeq_refl.
  - assumption.
  - apply aeq_refl.
Qed.

Inductive beta : n_sexp -> n_sexp -> Prop :=
| step_beta : forall (e1 e2: n_sexp) (x: atom),
    beta (n_app  (n_abs x e1) e2)  ({x := e2}e1).
