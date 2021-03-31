(** A nominal representation of STLC terms.

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
(** * A nominal representation of terms                      *)
(*************************************************************)

Inductive n_exp : Set :=
 | n_var (x:atom)
 | n_abs (x:atom) (t:n_exp)
 | n_app (t1:n_exp) (t2:n_exp).

(** For example, we can encode the expression [(\X.Y X)] as below.  *)

Definition demo_rep1 := n_abs X (n_app (n_var Y) (n_var X)).

(** For example, we can encode the expression [(\Z.Y Z)] as below.  *)

Definition demo_rep2 := n_abs Z (n_app (n_var Y) (n_var Z)).


(** As usual, the free variable function needs to remove the
    bound variable in the [n_abs] case. *)
Fixpoint fv_nom (n : n_exp) : atoms :=
  match n with
  | n_var x => {{x}}
  | n_abs x n => remove x (fv_nom n)
  | n_app t1 t2 => fv_nom t1 `union` fv_nom t2
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
Fixpoint swap (x:atom) (y:atom) (t:n_exp) : n_exp :=
  match t with
  | n_var z     => n_var (swap_var x y z)
  | n_abs z t1  => n_abs (swap_var x y z) (swap x y t1)
  | n_app t1 t2 => n_app (swap x y t1) (swap x y t2)
  end.


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

Inductive aeq : n_exp -> n_exp -> Prop :=
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
     aeq (n_app t1 t2) (n_app t1' t2').

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
  (* WORKED IN CLASS *)
  induction n; intros; simpl; unfold swap_var; default_simp.
Qed.
Lemma shuffle_swap : forall w y n z,
    w <> z -> y <> z ->
    (swap w y (swap y z n)) = (swap w z (swap w y n)).
Proof.
  (* WORKED IN CLASS *)
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
  - intros. simpl. unfold swap_var. case (x == x0).
    -- intros. default_simp. 
    -- intros. reflexivity.
  - intros. simpl. rewrite IHt. unfold swap_var. default_simp.
  - intros. simpl. rewrite IHt1. rewrite IHt2. reflexivity.
Qed.
         
Lemma swap_involutive : forall t x y,
    swap x y (swap x y t) = t.
Proof.
  induction t.
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
       --- assumption.
       --- assumption.
Qed.
      
      

      
(* HINT: For a helpful fact about sets of atoms, check AtomSetImpl.union_1 *)

Check AtomSetImpl.union_1.
Check fv_nom_swap.

Search "remove".

(*Theorem notin_swap : forall x y t,
     x<>y -> y `notin` fv_nom((swap x y t)).
Proof.
  induction t.
  - intros. simpl. unfold swap_var. default_simp. Admitted.
    

Theorem in_swap : forall x y t,
    x `in` fv_nom(t) -> x<>y -> y `in` fv_nom(swap x y t).
Proof.
  induction t.
  - intros. simpl. unfold swap_var. default_simp.
    -- admit. (*n e H sao contraditorias*)
    -- admit. (*n e H sao contraditorias*)
  - intros. simpl in H. apply AtomSetImpl.remove_3 in H. simpl.
    unfold swap_var. default_simp. apply IHt in H. Admitted.*)
      
Search "not".
Print "_ == _".
Search "union".
Search "remove".
Search "singleton".

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
Qed.           


               
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


Definition heap := list (atom * n_exp).

Inductive frame : Set := | n_app2 : n_exp -> frame.
Notation  stack := (list frame).

Definition configuration := (heap * n_exp * stack)%type.

(** The (small-step) semantics is a _function_ from
    configurations to configurations, until completion or
    error. *)

Inductive Step a := Error    : Step a
                  | Done     : Step a
                  | TakeStep : a -> Step a.

Definition isVal (t : n_exp) :=
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

Definition initconf (t : n_exp) : configuration := (nil,t,nil).


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
Qed.      
(*************************************************************)
(** * Size based reasoning                                   *)
(*************************************************************)


(** Some properties about nominal terms require calling the
    induction hypothesis not on a direct subterm, but on one
    that has first had a swapping applied to it.

    However, swapping names does not change the size of terms,
    so that means we can prove such properties by induction on
    that size.  *)

Fixpoint size (t : n_exp) : nat :=
  match t with
  | n_var x => 1
  | n_abs x t => 1 + size t
  | n_app t1 t2 => 1 + size t1 + size t2
  end.

Lemma swap_size_eq : forall x y t,
    size (swap x y t) = size t.
Proof.
  induction t; simpl; auto.
Qed.

Hint Rewrite swap_size_eq.

(** ** Capture-avoiding substitution *)

(** We need to use size to define capture avoiding
    substitution. Because we sometimes swap the name of the
    bound variable, this function is _not_ structurally
    recursive. So, we add an extra argument to the function
    that decreases with each recursive call. *)

Fixpoint subst_rec (n:nat) (t:n_exp) (u :n_exp) (x:atom)  : n_exp :=
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
          end
  end.

(** Our real substitution function uses the size of the size of the term
    as that extra argument. *)
Definition subst (u : n_exp) (x:atom) (t:n_exp) :=
  subst_rec (size t) t u x.

(** This next lemma uses course of values induction [lt_wf_ind] to prove that
    the size of the term [t] is enough "fuel" to completely calculate a
    substitution. Providing larger numbers produces the same result. *)
Lemma subst_size : forall n (u : n_exp) (x:atom) (t:n_exp),
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
Qed.

(** ** Challenge Exercise [subst]

    Use the definitions above to prove the following results about the
    nominal substitution function.  *)

Lemma subst_eq_var : forall u x,
    subst u x (n_var x) = u.
Proof.
  intros. unfold subst. unfold size. unfold subst_rec.
  case (x == x).
  - trivial.
  - intros. elim n. reflexivity.
Qed.
    
Lemma subst_neq_var : forall u x y,
    x <> y ->
    subst u x (n_var y) = n_var y.
Proof.
  intros. unfold subst. unfold size. unfold subst_rec.
  case (x == y).
  - intros. contradiction.
  - reflexivity.
Qed.

Lemma plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n m. induction n as [|n' IHn'].
    - rewrite <- plus_n_O. reflexivity.
    - simpl. rewrite <- plus_n_Sm. rewrite <- IHn'. reflexivity.
Qed.

Lemma subst_app : forall u x t1 t2,
    subst u x (n_app t1 t2) = n_app (subst u x t1) (subst u x t2).
Proof.
  intros. unfold subst. simpl.
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
    subst u x (n_abs y t1) =
       if (x == y) then (n_abs y t1)
       else let (z,_) := atom_fresh (fv_nom u `union` fv_nom (n_abs y t1) `union` {{x}}) in
       n_abs z (subst u x (swap y z t1)).
Proof.
  intros. case (x == y).
  - intros. unfold subst.  rewrite e. simpl. case (y == y).
    -- trivial.
    -- unfold not. intros. assert (y = y). {reflexivity.}
       contradiction.
  - intros. unfold subst. simpl. case (x == y).
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
       

(** ** Challenge Exercise [subst properties]

    Now show the following property by induction on the size of terms. *)

Lemma Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof.
  intros n m H. inversion H.
  - apply le_n.
  - apply (le_trans n (S n) m).
    -- apply le_S. reflexivity.
    -- assumption.
Qed.

Lemma O_le_n : forall n,
  0 <= n.
Proof.
  intros n. induction n as [| n' IHn'].
  - reflexivity.
  - inversion IHn'.
    -- apply le_S. reflexivity.
    -- apply le_S. apply le_S. assumption.
Qed.

Lemma lala : forall n m,
  S n <= m -> n <= m.
Proof.
  intros. induction n.
  - induction m.
    -- apply le_n.
    -- apply O_le_n.
  - apply le_S in H. apply Sn_le_Sm__n_le_m. assumption.
Qed.

Theorem n_le_m__Sn_le_Sm : forall n m,
  n <= m -> S n <= S m.
Proof.
  intros n m H. induction H.
  - apply le_n.
  - apply le_S. assumption.
Qed.

Theorem le_plus_l : forall a b,
  a <= a + b.
Proof.
  intros a b. induction a.
  - apply O_le_n.
  - simpl. apply n_le_m__Sn_le_Sm. assumption.
Qed.

Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
Proof.
  intros m n o H1 H2. transitivity n.
  - assumption.
  - assumption.
Qed.
  
Lemma subst_same_aux : forall n, forall t y, size t <= n -> aeq (subst (n_var y) y t)  t.
Proof.
  intro n. induction n.
  - intros t y SZ. destruct t; simpl in SZ; omega.
  - intros t y SZ. destruct t; simpl in SZ.
    -- unfold subst. simpl. case (y == x).
       --- intros. rewrite e. apply aeq_var.
       --- intros. apply aeq_var.
    -- unfold subst. simpl. case (y == x).
       --- intros. apply aeq_abs_same. induction t.
           + apply aeq_var.
           + apply aeq_abs_same. apply IHt.
             apply Sn_le_Sm__n_le_m in SZ. simpl in SZ.
             apply le_S in SZ. assumption.
           + apply aeq_app.
             ++ apply IHt1. simpl in SZ.
                rewrite <- plus_Sn_m in SZ.
                rewrite plus_comm in SZ.
                rewrite <- plus_Sn_m in SZ.
                rewrite plus_comm in SZ.
                apply le_trans with (S (size t1) + S (size t2)).
                +++ apply le_plus_l.
                +++ assumption.
             ++ apply aeq_refl.
       --- intros. unfold not in n0. pose proof subst_abs.
           specialize (H (n_var y) y x t). case (y == x) in H.
           + contradiction.
           + simpl in H. unfold subst in H. unfold subst in IHn.
             apply Sn_le_Sm__n_le_m in SZ.
             destruct (atom_fresh
           (union (singleton y)
                  (union (remove x (fv_nom t)) (singleton y)))).
             case (x == x0).
             ++ intros. subst. apply aeq_abs_same. rewrite swap_id.
                specialize (IHn t y); apply IHn in SZ. assumption.
             ++ intros. apply aeq_abs_diff.
                +++ apply aux_not_equal. assumption.
                +++ pose proof notin_union_2.
                    pose proof notin_union_1.  
                    apply H0 in n2.
                    apply H1 in n2.
                    unfold not; intros. pose proof remove_neq_iff.
                    specialize (H3 (fv_nom t) x x0).
                    apply H3 in n3. apply n3 in H2.
                    unfold not in n2. contradiction.                
                +++ pose proof swap_size_eq.
                    specialize (H0 x x0 t).
                    rewrite <- H0.
                    specialize (IHn (swap x x0 t) y).
                    rewrite <- H0 in SZ. apply IHn in SZ.
                    assumption.
    -- rewrite subst_app. apply aeq_app.
       --- specialize (IHn t1 y). apply Sn_le_Sm__n_le_m in SZ.
           assert (size t1 <= size t1 + size t2). {
             apply le_plus_l.
           }
           pose proof le_trans.
           specialize (H0 (size t1) (size t1 + size t2) n).
           apply H0 in H.
           + apply IHn in H. assumption.
           + assumption.
       --- specialize (IHn t2 y). apply Sn_le_Sm__n_le_m in SZ.
           assert (size t2 <= size t1 + size t2). {
             rewrite plus_comm. apply le_plus_l.
           }
           pose proof le_trans.
           specialize (H0 (size t2) (size t1 + size t2) n).
           apply H0 in H.
           + apply IHn in H. assumption.
           + assumption.
Qed.
           
Lemma subst_same : forall t y, aeq (subst (n_var y) y t)  t.
Proof.
  intros.
  apply subst_same_aux with (n := size t). auto.
Qed.


Lemma subst_fresh_eq_aux : forall n, forall (x:atom) t u, size t <= n ->
  x `notin` fv_nom t -> aeq (subst u x t) t.
Proof.
  induction t.  
  - intros. unfold subst. simpl. case (x == x0).
    -- intros. simpl in H0. pose proof singleton_iff.
       specialize (H1 x0 x). symmetry in e; apply H1 in e. 
       contradiction.
    -- intros. apply aeq_var.
  - intros. unfold subst. simpl. case (x == x0).
    -- intros. simpl in H0. rewrite e in H0. apply aeq_abs_same.
       apply aeq_refl.
    -- intros. pose proof subst_abs. unfold subst in H1.
       specialize (H1 u x x0 t). case (x == x0) in H1.
       --- contradiction.
       --- destruct (atom_fresh
         (union (fv_nom u)
                (union (remove x0 (fv_nom t)) (singleton x)))).
           unfold subst in IHt. simpl in H. apply le_S in H.
           apply Sn_le_Sm__n_le_m in H. specialize (IHt u).
           apply IHt in H.
           + case (x1 == x0).
             ++ intros. rewrite e. rewrite swap_id.
                apply aeq_abs_same. assumption.
             ++ intros. apply notin_union_2 in n2.
                apply notin_union_1 in n2.
                apply notin_remove_1 in n2.
                inversion n2.
                +++ symmetry in H2. contradiction.
                +++ apply aeq_abs_diff.
                    * assumption.
                    * assumption.
                    * admit.



           + simpl in H0. pose proof notin_remove_1.
             apply H2 in H0. inversion H0.
             ++ symmetry in H3. contradiction.
             ++ assumption.
  - intros. unfold subst. simpl. simpl in H. pose proof le_plus_l.
    specialize (H1 (size t1) (size t2)). apply le_S in H.
    apply Sn_le_Sm__n_le_m in H. pose proof le_trans.
    specialize (H2 (size t1) (size t1 + size t2) n). apply H2 in H1.
    -- pose proof le_plus_l. specialize (H3 (size t2) (size t1)).
       rewrite plus_comm in H. pose proof le_trans.
       specialize (H4 (size t2) (size t1 + size t2) n).
       rewrite plus_comm in H2. rewrite plus_comm in H4.
       apply H4 in H3.
       --- specialize (IHt1 u). specialize (IHt2 u).
           apply IHt1 in H1.
           + simpl in H0. Search "union". pose proof notin_union_1.
             specialize (H5 x (fv_nom t1) (fv_nom t2)).
             pose proof notin_union_1.
             specialize (H6 x (fv_nom t2) (fv_nom t1)).
             apply IHt1 in H5.
             ++ apply IHt2 in H6.
                +++ pose proof subst_size. apply aeq_app.
                    * unfold subst in H5.
                      specialize (H7 (size t1 + size t2) u x t1).
                      rewrite H7.
                      ** assumption.
                      ** apply le_plus_l.
                    * unfold subst in H6.
                      specialize (H7 (size t1 + size t2) u x t2).
                      rewrite H7.
                      ** assumption.
                      ** rewrite plus_comm. apply le_plus_l.
                +++ assumption.
                +++ pose proof notin_union_1.
                    pose proof notin_union_2. pose proof H0.
                    apply H7 in H0. apply H8 in H9.
                    pose proof notin_union_3.
                    specialize (H10 x (fv_nom t2) (fv_nom t1)).
                    apply H10.
                    * assumption.
                    * assumption.
             ++ pose proof le_plus_l.
                apply H2.
                +++ rewrite plus_comm. apply le_plus_l.
                +++ assumption.
             ++ assumption.
           + simpl in H0. pose proof notin_union_1.
             apply H5 in H0. assumption.
       --- assumption.
    -- assumption.    
Admitted.
       
Lemma subst_fresh_eq : forall (x : atom) t u,  x `notin` fv_nom t -> aeq (subst u x t) t.
Proof.
  intros. apply subst_fresh_eq_aux with (n := size t). omega. auto.
Qed.



