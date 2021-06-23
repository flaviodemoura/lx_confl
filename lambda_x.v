(** A nominal representation of the lambda_x calculus.

    This version looks a lot like we expect a representation of
    the lambda calculus to look like. Unlike the LN version,
    the syntax does not distinguish between bound and free
    variables and abstractions include the name of binding
    variables.  *)

(*************************************************************)
(** * Imports                                                *)
(*************************************************************)

(** Some of our proofs are by induction on the *size* of
    terms. We'll use Coq's [omega] tactic to easily dispatch
    reasoning about natural numbers. *)
Require Export Omega.

(** We will use the [atom] type from the metatheory library to
    represent variable names. *)
Require Export Metalib.Metatheory.

(** Although we are not using LNgen, some of the tactics from
    its library are useful for automating reasoning about
    names (i.e. atoms).  *)
Require Export Metalib.LibLNgen.
Require Import Nominal.


(** Some fresh atoms *)
Notation X := (fresh nil).
Notation Y := (fresh (X :: nil)).
Notation Z := (fresh (X :: Y :: nil)).

Lemma YneX : Y <> X.
Proof.
  pose proof Atom.fresh_not_in (X :: nil) as H.
  apply elim_not_In_cons in H.
  auto.
Qed.


(*************************************************************)
(** * A nominal representation of lambda_x terms             *)
(*************************************************************)

Inductive n_sexp : Set :=
 | n_var (x:atom)
 | n_abs (x:atom) (t:n_sexp)
 | n_app (t1:n_sexp) (t2:n_sexp)
 | n_sub (t1:n_sexp) (x:atom) (t2:n_sexp).

Inductive pure : n_sexp -> Prop :=
 | pure_var : forall x, pure (n_var x)
 | pure_app : forall e1 e2, pure e1 -> pure e2 -> pure (n_app e1 e2) | pure_abs : forall x e1, pure e1 -> pure (n_abs x e1).

Inductive betax : n_sexp -> n_sexp -> Prop :=
 | step_betax : forall (e1 e2: n_sexp) (x: atom),
     betax (n_app  (n_abs x e1) e2)  (n_sub e1 x e2).

Inductive pix : n_sexp -> n_sexp -> Prop :=
 | step_var : forall (e: n_sexp) (y: atom),
     pix (n_sub (n_var y) y e) e
 | step_gc : forall (e: n_sexp) (x y: atom),
     x <> y -> pix (n_sub (n_var x) y e) (n_var x)
 | step_abs1 : forall (e1 e2: n_sexp) (y : atom),
     pix (n_sub (n_abs y e1) y e2)  (n_abs y e1)
 | step_abs2 : forall (e1 e2: n_sexp) (x y: atom),
     x <> y ->
     pix (n_sub (n_abs x e1) y e2)  (n_abs x (n_sub e1 y e2))
 | step_app : forall (e1 e2 e3: n_sexp) (y: atom),
     pix (n_sub (n_app e1 e2) y e3) (n_app (n_sub e1 y e3) (n_sub e2 y e3)).

Inductive step  (R : n_sexp -> n_sexp -> Prop): n_sexp -> n_sexp -> Prop :=
 | step_redex: forall (e1 e2 : n_sexp), R e1 e2 -> step R e1 e2
 | step_abs_in: forall (e e': n_sexp) (x: atom), step R e e' -> step R (n_abs x e) (n_abs x e')
 | step_app_left: forall (e1 e1' e2: n_sexp) , step R e1 e1' -> step R (n_app e1 e2) (n_app e1' e2)
 | step_app_right: forall (e1 e2 e2': n_sexp) , step R e2 e2' -> step R (n_app e1 e2) (n_app e1 e2')
 | step_sub_left: forall (e1 e1' e2: n_sexp) (x : atom) , step R e1 e1' -> step R (n_sub e1 x e2) (n_sub e1' x e2)
 | step_sub_right: forall (e1 e2 e2': n_sexp) (x:atom), step R e2 e2' -> step R (n_sub e1 x e2) (n_sub e1 x e2').

(** For example, we can encode the expression [(\X.Y X)] as below.  *)

Definition demo_rep1 := n_abs X (n_app (n_var Y) (n_var X)).

(** For example, we can encode the expression [(\Z.Y Z)] as below.  *)

Definition demo_rep2 := n_abs Z (n_app (n_var Y) (n_var Z)).


(** As usual, the free variable function needs to remove the
    bound variable in the [n_abs] case. *)
Fixpoint fv_nom (n : n_sexp) : atoms :=
  match n with
  | n_var x => {{x}}
  | n_abs x n => remove x (fv_nom n)
  | n_app t1 t2 => fv_nom t1 `union` fv_nom t2
  | n_sub t1 x t2 => (remove x (fv_nom t1)) `union` fv_nom t2
  end.

(** The tactics for reasoning about lists and sets of atoms are useful here
    too. *)

Example fv_nom_rep1 : fv_nom demo_rep1 [=] {{ Y }}.
Proof.
  pose proof YneX.
  simpl.
  fsetdec.
Qed.

(** What makes this a *nominal* representation is that our
    operations are based on the following swapping function for
    names.  Note that this operation is symmetric: [x] becomes
    [y] and [y] becomes [x]. *)

Definition swap_var (x:atom) (y:atom) (z:atom) :=
  if (z == x) then y else if (z == y) then x else z.

(** The main insight of nominal representations is that we can
    rename variables, without capture, using a simple
    structural induction. Note how in the [n_abs] case we swap
    all variables, both bound and free.

    For example:

      (swap x y) (\z. (x y)) = \z. (y x))

      (swap x y) (\x. x) = \y.y

      (swap x y) (\y. x) = \x.y

*)
Fixpoint swap (x:atom) (y:atom) (t:n_sexp) : n_sexp :=
  match t with
  | n_var z     => n_var (swap_var x y z)
  | n_abs z t1  => n_abs (swap_var x y z) (swap x y t1)
  | n_app t1 t2 => n_app (swap x y t1) (swap x y t2)
  | n_sub t1 z t2 => n_sub (swap x y t1) (swap_var x y z) (swap x y t2)
  end.

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


(** Because swapping is a simple, structurally recursive
    function, it is highly automatable using the [default_simp]
    tactic from LNgen library.

    This tactic "simplifies" goals using a combination of
    common proof steps, including case analysis of all disjoint
    sums in the goal. Because atom equality returns a sumbool,
    this makes this tactic useful for reasoning by cases about
    atoms.

    For more information about the [default_simp] tactic, see
    [metalib/LibDefaultSimp.v].

    WARNING: this tactic is not always safe. It's a power tool
    and can put your proof in an irrecoverable state. *)

Example swap1 : forall x y z, x <> z -> y <> z ->
    swap x y (n_abs z (n_app (n_var x)(n_var y))) = n_abs z (n_app (n_var y) (n_var x)).
Proof.
  intros. simpl; unfold swap_var; default_simp.
Qed.

Example swap2 : forall x y, x <> y ->
    swap x y (n_abs x (n_var x)) = n_abs y (n_var y).
Proof.
  intros. simpl; unfold swap_var; default_simp.
Qed.

Example swap3 : forall x y, x <> y ->
     swap x y (n_abs y (n_var x)) = n_abs x (n_var y).
Proof.
  intros. simpl; unfold swap_var; default_simp.
Qed.


(** We define the "alpha-equivalence" relation that declares
    when two nominal terms are equivalent (up to renaming of
    bound variables).

    Note the two different rules for [n_abs]: either the
    binders are the same and we can directly compare the
    bodies, or the binders differ, but we can swap one side to
    make it look like the other.  *)

Inductive aeq : n_sexp -> n_sexp -> Prop :=
 | aeq_var : forall x,
     aeq (n_var x) (n_var x)
 | aeq_abs_same : forall x t1 t2,
     aeq t1 t2 -> aeq (n_abs x t1) (n_abs x t2)
 | aeq_abs_diff : forall x y t1 t2,
     x <> y ->
     x `notin` fv_nom t2 ->
     aeq t1 (swap y x t2) ->
     aeq (n_abs x t1) (n_abs y t2)
 | aeq_app : forall t1 t2 t1' t2',
     aeq t1 t1' -> aeq t2 t2' ->
     aeq (n_app t1 t2) (n_app t1' t2')
 | aeq_sub_same : forall t1 t2 t1' t2' x,
     aeq t1 t1' -> aeq t2 t2' ->
     aeq (n_sub t1 x t2) (n_sub t1' x t2')
 | aeq_sub_diff : forall t1 t2 t1' t2' x y,
     aeq t2 t2' -> x <> y ->
     x `notin` fv_nom t1' -> aeq t1 (swap y x t1') ->
     aeq (n_sub t1 x t2) (n_sub t1' y t2').

Hint Constructors aeq.


Example aeq1 : forall x y, x <> y -> aeq (n_abs x (n_var x)) (n_abs y (n_var y)).
Proof.
  intros.
  eapply aeq_abs_diff; auto.
  simpl; unfold swap_var; default_simp.
Qed.

Lemma aeq_refl : forall n, aeq n n.
Proof.
  induction n; auto.
Qed.

(*************************************************************)
(** ** Properties about swapping                             *)
(*************************************************************)


(** Now let's look at some simple properties of swapping. *)

Lemma swap_id : forall n x,
    swap x x n = n.
Proof.
  induction n; simpl; unfold swap_var;  default_simp.
Qed.

(** Demo: We will need the next two properties later in the tutorial,
    so we show that even though there are many cases to consider,
    [default_simp] can find these proofs. *)

Lemma fv_nom_swap : forall z y n,
  z `notin` fv_nom n ->
  y `notin` fv_nom (swap y z n).
Proof.
  induction n; intros; simpl; unfold swap_var; default_simp.
Qed. 

Lemma shuffle_swap : forall w y n z,
    w <> z -> y <> z ->
    (swap w y (swap y z n)) = (swap w z (swap w y n)).
Proof.
  induction n; intros; simpl; unfold swap_var; default_simp.
Qed. 

(*************************************************************)
(** ** Exercises                                             *)
(*************************************************************)

(** *** Recommended Exercise: [swap] properties

    Prove the following properties about swapping, either
    explicitly (by destructing [x == y]) or automatically
    (using [default_simp]).  *)

Lemma swap_symmetric : forall t x y,
    swap x y t = swap y x t.
Proof.
  induction t.
  - intros x' y.
    simpl.
    unfold swap_var.
    default_simp.
  - intros x' y; simpl.
    unfold swap_var.
    default_simp.
  - intros x y; simpl.
    rewrite IHt1.
    rewrite IHt2; reflexivity.
  - intros. simpl. unfold swap_var. default_simp.
Qed.
    
Lemma swap_involutive : forall t x y,
    swap x y (swap x y t) = t.
Proof.
 induction t.
  - intros. simpl. unfold swap_var. default_simp.
  - intros. simpl. unfold swap_var. default_simp.
  - intros. simpl. unfold swap_var. default_simp.
  - intros. simpl. unfold swap_var. default_simp.    
Qed.

(** *** Challenge exercises: equivariance

    Equivariance is the property that all functions and
    relations are preserved under swapping.  Show that this
    holds for the various functions and relations below.

    (Hint: [default_simp] will be slow and sometimes
    ineffective on *some* of these properties. If it puts
    you in an dead-end state, you'll need to prove the
    lemm another way. *)

Lemma swap_var_equivariance : forall v x y z w,
    swap_var x y (swap_var z w v) =
    swap_var (swap_var x y z) (swap_var x y w) (swap_var x y v).
Proof.
  intros. unfold swap_var.
  case(v == z).
  - case (w == x).
    -- default_simp.
    -- default_simp.
  - case (w == x).
    -- default_simp.
    -- default_simp.
Qed.

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
    -- case (w == x0).
       --- default_simp.
       --- default_simp.
    -- case (w == x0).
       --- default_simp.
       --- intros. case (x == w).
           + intros. case (z == x0).
             ++ default_simp.
             ++ default_simp.
           + intros. case (z == x0).
             ++ default_simp.
             ++ default_simp.
  - intros. simpl. rewrite IHt1. rewrite IHt2. reflexivity.
  - intros. simpl. rewrite IHt1. rewrite IHt2. unfold swap_var.
    default_simp.    
Qed.

Lemma aux_not_equal : forall (x:atom) (y:atom),
    x <> y -> y <> x.
Proof.
  intros. unfold not. intros. unfold not in H.
  assert (x = y). {
    rewrite H0. reflexivity.
  }
  contradiction.
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

(* HINT: For a helpful fact about sets of atoms, check AtomSetImpl.union_1 *)

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
       --- Search "remove". pose proof AtomSetImpl.remove_1.
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
       --- Search "remove". pose proof AtomSetImpl.remove_1.
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


(*************************************************************)
(** * Size based reasoning                                   *)
(*************************************************************)


(** Some properties about nominal terms require calling the
    induction hypothesis not on a direct subterm, but on one
    that has first had a swapping applied to it.

    However, swapping names does not change the size of terms,
    so that means we can prove such properties by induction on
    that size.  *)

Fixpoint size (t : n_sexp) : nat :=
  match t with
  | n_var x => 1
  | n_abs x t => 1 + size t
  | n_app t1 t2 => 1 + size t1 + size t2
  | n_sub t1 x t2 => 1 + size t1 + size t2
  end.

Lemma swap_size_eq : forall x y t,
    size (swap x y t) = size t.
Proof.
  induction t; simpl; auto.
Qed.

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
 Admitted.
  
Hint Rewrite swap_size_eq.

(** ** Capture-avoiding substitution *)

(** We need to use size to define capture avoiding
    substitution. Because we sometimes swap the name of the
    bound variable, this function is _not_ structurally
    recursive. So, we add an extra argument to the function
    that decreases with each recursive call. *)

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
            if (x == y) then t
            else
              (* rename to avoid capture *)
              let (z,_) :=
                  atom_fresh (fv_nom u `union` fv_nom t `union` {{x}}) in
                 n_sub  (subst_rec m (swap y z t1) u x) z (subst_rec m t2 u x) 
          end
  end.

(** Our real substitution function uses the size of the size of the term
    as that extra argument. *)
Definition m_subst (u : n_sexp) (x:atom) (t:n_sexp) :=
  subst_rec (size t) t u x.

(** This next lemma uses course of values induction [lt_wf_ind] to prove that
    the size of the term [t] is enough "fuel" to completely calculate a
    substitution. Providing larger numbers produces the same result. *)
Lemma subst_size : forall n (u : n_sexp) (x:atom) (t:n_sexp),
    size t <= n -> subst_rec n t u x = subst_rec (size t) t u x.
Proof.
  intro n. eapply (lt_wf_ind n). clear n.
  intros n IH u x t SZ.
  destruct t; simpl in *; destruct n; try omega.
  - default_simp.
  - default_simp.
    rewrite <- (swap_size_eq x0 x1).
    rewrite <- (swap_size_eq x0 x1) in SZ.
    apply IH. omega. omega.
  - simpl.
    rewrite (IH n); try omega.
    rewrite (IH n); try omega.
    rewrite (IH (size t1 + size t2)); try omega.
    rewrite (IH (size t1 + size t2)); try omega.
    auto.
  - default_simp.
    -- rewrite (IH n); try omega.
       --- rewrite swap_size_eq.
           assert (size t1 <= size t1 + size t2). {
             apply le_plus_l.
           }
           Search "lt". apply Sn_le_Sm__n_le_m in SZ.
           apply le_lt_n_Sm in SZ.
           specialize (IH (size t1 + size t2) SZ u x (swap x0 x1 t1)).
           rewrite swap_size_eq in IH. apply IH in H.
           symmetry in H. assumption.
       --- rewrite swap_size_eq. apply Sn_le_Sm__n_le_m in SZ.
           assert (size t1 <= size t1 + size t2). {
             apply le_plus_l.
           }
           transitivity (size t1 + size t2).
           + assumption.
           + assumption.
   -- rewrite (IH n); try omega.
       --- rewrite plus_comm. rewrite plus_comm in SZ.
           assert (size t2 <= size t2 + size t1). {
             apply le_plus_l.
           }
           Search "lt". apply Sn_le_Sm__n_le_m in SZ.
           apply le_lt_n_Sm in SZ.
           specialize (IH (size t2 + size t1) SZ u x t2).
           apply IH in H.
           symmetry in H. assumption.       
Qed.

(** ** Challenge Exercise [m_subst]

    Use the definitions above to prove the following results about the
    nominal substitution function.  *)

Lemma subst_eq_var : forall u x,
    m_subst u x (n_var x) = u.
Proof.
  intros. unfold size. unfold subst_rec.
  unfold m_subst. simpl.
  case (x == x).
  - trivial.
  - intros. contradiction.
Qed.

Lemma subst_neq_var : forall u x y,
    x <> y ->
    m_subst u x (n_var y) = n_var y.
Proof.
  intros. unfold m_subst. unfold size. unfold subst_rec.
  case (x == y).
  - intros. contradiction.
  - reflexivity.
Qed.

Lemma subst_app : forall u x t1 t2,
    m_subst u x (n_app t1 t2) = n_app (m_subst u x t1) (m_subst u x t2).
Proof.
  intros. unfold m_subst. simpl.
  assert (size t1 <= (size t1 + size t2)). {
    apply le_plus_l.         
  }
  assert (size t2 <= (size t1 + size t2)). {
    rewrite plus_comm. apply le_plus_l.         
  }
  rewrite subst_size.
  - assert ((subst_rec (size t1 + size t2) t2 u x) = subst_rec (size t2) t2 u x). {
      apply subst_size. assumption.
    }
    rewrite H1. reflexivity.
  - assumption.
Qed.

Lemma subst_abs : forall u x y t1,
    m_subst u x (n_abs y t1) =
       if (x == y) then (n_abs y t1)
       else let (z,_) := atom_fresh (fv_nom u `union` fv_nom (n_abs y t1) `union` {{x}}) in
       n_abs z (m_subst u x (swap y z t1)).
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
       assert (forall z, size t1 = size (swap y z t1)). {
         intros. case (y == z).
         - intros. rewrite e. rewrite swap_id. reflexivity.
         - intros. rewrite swap_size_eq. reflexivity.         
       }
       destruct (atom_fresh
       (union (fv_nom u)
          (union (remove y (fv_nom t1)) (singleton x)))). 
       specialize (H0 x0). rewrite H0. reflexivity.
Qed.

Lemma subst_sub : forall u x y t1 t2,
    m_subst u x (n_sub t1 y t2) =
       if (x == y) then (n_sub t1 y t2)
       else let (z,_) := atom_fresh (fv_nom u `union` fv_nom (n_sub t1 y t2) `union` {{x}}) in
            n_sub (m_subst u x (swap y z t1)) z (m_subst u x t2).
Proof.
  intros. case (x == y).
  - intro H; subst.
    unfold m_subst.
    simpl.
    case (y == y).
    + intro H; reflexivity.
    + intro H.
      contradiction.      
  - intro Hneq.
    unfold m_subst.
    simpl.
    case (x == y).
    + intro H; contradiction.
    + intro Hneq'.
      destruct (atom_fresh (union (fv_nom u) (union (union (remove y (fv_nom t1)) (fv_nom t2)) (singleton x)))).
      rewrite swap_size_eq.
      pose proof subst_size.
      specialize (H (size t1 + size t2) u x (swap y x0 t1)).
      rewrite H.
Admitted.

Lemma pure_m_subst : forall t u x, pure u -> pure t -> pure (m_subst u x t).
Proof.
  induction t using n_sexp_induction.
  - admit.
  - 
  intros u x t H1 H2.
  unfold m_subst.
  remember (size t) as n.
  generalize dependent x.
  generalize dependent u.
  generalize dependent t.
  induction n.
  - intros t Ht Hsize u Hu x.
    simpl.
    assumption.
  - 

  
  - intros. unfold m_subst. simpl. case (x == x0).
    -- intros; assumption.
    -- intros; assumption.   
  - unfold m_subst. simpl. case (x == x0).
    -- intros; assumption.
    -- intros; destruct (atom_fresh
         (union (fv_nom u)
                (union (remove x0 (fv_nom t)) (singleton x)))).
       apply pure_abs.
       unfold m_subst in IHt.
       inversion H0. apply IHt in H2.
       --- clear H1; clear H3; clear e1. inversion H0.
           clear H1; clear H4; clear e1. pose proof pure_swap.
           specialize (H1 x0 x1 t). unfold m_subst in H2.
           admit.
       --- assumption.
  - intros. unfold m_subst; simpl. apply pure_app.
    -- inversion H0. clear H1; clear H2.
       pose proof subst_size. apply IHt1 in H.
       --- unfold m_subst in H.
           specialize (H1 (size t1 + size t2) u x t1).
           pose proof le_plus_l. specialize (H2 (size t1) (size t2)). apply H1 in H2. rewrite H2. assumption.
       --- assumption.
    -- inversion H0. clear H1; clear H2.
       pose proof subst_size. apply IHt2 in H.
       --- unfold m_subst in H.
           specialize (H1 (size t1 + size t2) u x t2).
           pose proof le_plus_r. specialize (H2 (size t1) (size t2)). apply H1 in H2. rewrite H2. assumption.
       --- assumption.
Admitted.

(** ** Challenge Exercise [m_subst properties]

    Now show the following property by induction on the size of terms. *)

Lemma subst_same_aux : forall n, forall t y, size t <= n -> aeq (m_subst (n_var y) y t)  t.
Proof.
  intro n. induction n.
  - intros t y SZ. destruct t; simpl in SZ; omega.
  - intros t y SZ. destruct t; simpl in SZ.
    -- unfold m_subst. simpl. case (y == x).
       --- intros. rewrite e. apply aeq_var.
       --- intros. apply aeq_var.
    -- rewrite subst_abs.
       case (y == x).
       --- intros. apply aeq_refl.
       --- intros. simpl.
           destruct (atom_fresh
           (union (singleton y)
                  (union (remove x (fv_nom t)) (singleton y)))).
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
       --- intro Heq; subst.
           apply aeq_refl.
       --- intro Hneq.
           simpl.
           destruct (atom_fresh
           (union (singleton y)
                  (union (union (remove x (fv_nom t1)) (fv_nom t2)) (singleton y)))).
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
Qed.

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
    + intros. unfold subst. simpl. case (x == x0).
    -- intros. simpl in H0. pose proof singleton_iff.
       specialize (H1 x0 x). symmetry in e; apply H1 in e. 
       contradiction.
    -- intros. unfold m_subst; simpl. case (x == x0).
       --- intros; contradiction.
       --- intros; apply aeq_var.
    + intros. rewrite subst_abs.
      case (x == x0).
    -- intros. apply aeq_refl.
    -- intros.
       simpl.
       destruct (atom_fresh
                   (union (fv_nom u)
                          (union (remove x0 (fv_nom t)) (singleton x)))).
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
    + intros. unfold m_subst; simpl. case (x == x0).
      -- intros; apply aeq_refl.
      -- intros; destruct (atom_fresh
         (union (fv_nom u)
            (union (union (remove x0 (fv_nom t1)) (fv_nom t2))
                   (singleton x)))). case (x1 == x0).
         --- intros; subst. apply aeq_sub_same.
             ---- rewrite swap_id.  pose proof le_plus_l.
                  specialize (H1 (size t1) (size t2)).
                  pose proof subst_size.
                  specialize (H2 (size t1 + size t2) u x t1).
                  rewrite H2.
             ----- unfold m_subst in IHn. apply IHn.
             ------ simpl in H. apply Sn_le_Sm__n_le_m in H.
                    transitivity (size t1 + size t2).
             ------- apply le_plus_l.
             ------- assumption.
             ------ simpl in H0. apply notin_union_1 in H0.
                    apply notin_remove_1 in H0. inversion H0.
             ------- symmetry in H3; contradiction.
             ------- assumption.
             ----- assumption.
             ---- pose proof le_plus_r.
                  specialize (H1 (size t1) (size t2)).
                  pose proof subst_size.
                  specialize (H2 (size t1 + size t2) u x t2).
                  rewrite H2.
             ----- unfold m_subst in IHn. apply IHn.
             ------ simpl in H. apply Sn_le_Sm__n_le_m in H.
                    transitivity (size t1 + size t2).
             ------- apply le_plus_r.
             ------- assumption.
             ------ simpl in H0. apply notin_union_2 in H0.
             assumption.
             ----- assumption.
         --- intros. apply aeq_sub_diff.
             ---- pose proof subst_size.
                  specialize (H1 (size t1 + size t2) u x t2).
                  pose proof le_plus_r.
                  specialize (H2 (size t1) (size t2)).
                  apply H1 in H2. rewrite H2.
                  unfold m_subst in IHn. specialize (IHn x t2 u).
                  apply IHn.
             ----- simpl in H. apply Sn_le_Sm__n_le_m in H.
                   transitivity (size t1 + size t2).
             ------ apply le_plus_r.
             ------ assumption.
             ----- simpl in H0. apply notin_union_2 in H0.
                   assumption.
             ---- assumption.
             ---- apply notin_union_2 in n1.
                  apply notin_union_1 in n1.
                  apply notin_union_1 in n1.
                  apply notin_remove_1 in n1.
                  inversion n1.
             ----- symmetry in H1; contradiction.
             ----- assumption.
             ---- pose proof subst_size.
                  specialize (H1 (size t1 + size t2) u x (swap x0 x1 t1) ).
                  pose proof le_plus_l.
                  specialize (H2 (size t1) (size t2)).
                  rewrite swap_size_eq in H1; apply H1 in H2.
                  rewrite H2.
                  specialize (IHn x (swap x0 x1 t1) u).
                  unfold m_subst in IHn.
                  rewrite swap_size_eq in IHn.
                  apply IHn.
             ----- simpl in H. apply Sn_le_Sm__n_le_m in H.
                   transitivity (size t1 + size t2).
             ------ apply le_plus_l.
             ------ assumption.
             ----- simpl in H0.
                   apply notin_union_1 in H0.
                   apply notin_remove_1 in H0.
                   inversion H0.
             ------ symmetry in H3; contradiction.
             ------ pose proof n1.
                    apply notin_union_2 in n1.
                    apply notin_union_1 in n1.
                    apply notin_union_1 in n1.
                    apply notin_remove_1 in n1. inversion n1.
             ------- symmetry in H5; contradiction.
             ------- clear H1; clear H2. apply notin_union_2 in H4.
                     apply notin_union_2 in H4.
                     apply notin_singleton_1 in H4.
                     pose proof notin_fv_nom_equivariance.
                     specialize (H1 x x0 x1 t1).
                     apply H1 in H3; clear H1.
                     unfold swap_var in H3. case (x == x0) in H3.
             -------- contradiction.
             -------- case (x == x1) in H3.
             --------- contradiction.
             --------- assumption.
Qed.                     

Lemma subst_fresh_eq : forall (x : atom) t u,  x `notin` fv_nom t -> aeq (m_subst u x t) t.
Proof.
  intros. apply subst_fresh_eq_aux with (n := size t). omega. auto.
Qed.



