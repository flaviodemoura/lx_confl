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

(** TBD  In this work, we present a formalization of an extension of the substitution lemma%\cite{barendregtLambdaCalculusIts1984}% with an explicit substitution operator in the Coq proof assistant%\cite{teamCoqProofAssistant2021}%. The substitution lemma is an important result concerning the composition of the substitution operation, and is usually presented as follows: if $x$ does not occur in the set of free variables of the term $v$ then $t\msub{x}{u}\msub{y}{v} =_\alpha t\msub{y}{v}\msub{x}{u\msub{y}{v}}$. This is a well known result already formalized several times in the context of the $\lambda$-calculus %\cite{berghoferHeadtoHeadComparisonBruijn2007}%.

In the context of the $\lambda$-calculus with explicit substitutions its formalization is not straightforward because, in addition to the metasubstitution operation, there is the explicit substitution operator. Our formalization is done in a nominal setting that uses the MetaLib package of Coq, but no particular explicit substitution calculi is taken into account because the expected behaviour between the metasubstitution operation with the explicit substitutition constructor is the same regardless the calculus.

- This paper is written from a Coq script file.
- include %\cite{berghoferHeadtoHeadComparisonBruijn2007}%
- repository
- constructive logic
- contributions
- challenges
*)

(** * A syntactic extension of the $\lambda$-calculus *)

(** In this section, we present the framework of the formalization, which is based on a nominal approach%\cite{gabbayNewApproachAbstract1999}% where variables use names. This approach contrasts with the use of  De Bruijn indexes detailed in De Bruijn's landmark paper on $\lambda$-calculus notation%\cite{bruijnLambdaCalculusNotation1972}%. In the nominal setting, variables are represented by atoms that are structureless entities with a decidable equality: 

<<
Parameter eq_dec : forall x y : atom, {x = y} + {x <> y}.
>>

Variable renaming is done via name-swapping defined as follows:

$\vswap{x}{y}{z} := \left\{ \begin{array}{ll}
y, & \mbox{ if } z = x; \\
x, & \mbox{ if } z = y; \\
z, & \mbox{ otherwise. } \\
\end{array}\right.$

\noindent and the corresponding Coq definition:

 *)

Definition swap_var (x:atom) (y:atom) (z:atom) :=
  if (z == x) then y else if (z == y) then x else z.


(* begin hide *)
Lemma swap_var_id: forall x y, (swap_var x x y = y).
Proof.
  intros. unfold swap_var. case (y == x); intros; subst; reflexivity.
Qed.
(* end hide *)

(** The next step is to extend the variable renaming operation to terms, which in our case corresponds to $\lambda$-terms augmented with an explicit substitution operation. We use [n_sexp] to denote the set of nominal expressions equipped with an explicit substitution operator, which, for simplicity, we will refer to as just "terms", and the corresponding grammar is outlined below: *)

Inductive n_sexp : Set :=
 | n_var (x:atom)
 | n_abs (x:atom) (t:n_sexp)
 | n_app (t1:n_sexp) (t2:n_sexp)
 | n_sub (t1:n_sexp) (x:atom) (t2:n_sexp).

(** %\noindent% where [n_var] is the constructor for variables, [n_abs] for abstractions, [n_app] for applications and [n_sub] for the explicit substitution. Explicit substitution calculi are formalisms that deconstruct the metasubstitution operation into more granular steps, thereby functioning as an intermediary between the $\lambda$-calculus and its practical implementations. In other words, these calculi shed light on the execution models of higher-order languages%\cite{kesnerTheoryExplicitSubstitutions2009}%. The [size] of terms and the set [fv_nom] of the free variables of a term are defined as usual: *)

Fixpoint size (t : n_sexp) : nat :=
  match t with
  | n_var x => 1
  | n_abs x t => 1 + size t
  | n_app t1 t2 => 1 + size t1 + size t2
  | n_sub t1 x t2 => 1 + size t1 + size t2
  end.

Fixpoint fv_nom (t : n_sexp) : atoms :=
  match t with
  | n_var x => {{x}}
  | n_abs x t1 => remove x (fv_nom t1)
  | n_app t1 t2 => fv_nom t1 `union` fv_nom t2
  | n_sub t1 x t2 => (remove x (fv_nom t1)) `union` fv_nom t2
  end.

(** The action of a permutation on a term, written $\swap{x}{y}{t}$, is inductively defined as follows:%\vspace{.5cm}%

$\swap{x}{y}{t} := \left\{ \begin{array}{ll}
\vswap{x}{y}{v}, & \mbox{ if } t \mbox{ is the variable } v; \\
\lambda_{\vswap{x}{y}{z}}. \swap{x}{y}{t_1}, & \mbox{ if } t = \lambda_z.t_1; \\
\swap{x}{y}{t_1}\ \swap{x}{y}{t_2}, & \mbox{ if } t = t_1\ t_2;\\
\esub{\swap{x}{y}{t_1}}{\vswap{x}{y}{z}}{\swap{x}{y}{t_2}}, & \mbox{ if } t = \esub{t_1}{z}{t_2}.
\end{array}\right.$%\vspace{.5cm}%

The corresponding Coq definition is given by the following recursive function: *)

Fixpoint swap (x:atom) (y:atom) (t:n_sexp) : n_sexp :=
  match t with
  | n_var z     => n_var (swap_var x y z)
  | n_abs z t1  => n_abs (swap_var x y z) (swap x y t1)
  | n_app t1 t2 => n_app (swap x y t1) (swap x y t2)
  | n_sub t1 z t2 => n_sub (swap x y t1) (swap_var x y z) (swap x y t2)
  end.

(* begin hide *)
Lemma swap_id : forall t x,
    swap x x t = t.
Proof.
  induction t; simpl; unfold swap_var; default_simp.
Qed.

Lemma swap_eq: forall x y z w, swap_var x y z = swap_var x y w -> z = w.
Proof.
  intros x y z w H. unfold swap_var in H. destruct (z == x).
  - subst. destruct (w == x).
    + rewrite e. reflexivity.
    + destruct (w == y).
      * subst. contradiction.
      * subst. contradiction.
  - destruct (z == y).
    + subst. destruct (w == x).
      * subst. contradiction.
      * destruct (w == y).
        ** subst. reflexivity.
        ** subst. contradiction.
    + destruct (w == x).
      * subst. contradiction.
      * destruct (w == y).
        ** subst. contradiction.
        ** assumption.
Qed.  

Lemma swap_neq: forall x y z w, z <> w -> swap_var x y z <> swap_var x y w.
Proof.
  intros x y z w H1 H2. unfold swap_var. destruct (z == x).
  - subst. apply swap_eq in H2. contradiction.
  - apply swap_eq in H2. contradiction.
Qed.
(* end hide *)

(** The [swap] function preserves the size of terms, as stated by the following lemma: *)
Lemma swap_size_eq : forall x y t, size (swap x y t) = size t.
Proof.
  induction t; simpl; auto.
Qed.

(* begin hide *)
Hint Rewrite swap_size_eq.

Lemma swap_symmetric : forall t x y, swap x y t = swap y x t.
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
      * rewrite double_remove. apply IHt1. apply diff_remove_2 in Hfv'.
        ** assumption.
        ** assumption.
      * destruct (x0 == x).
        ** subst. rewrite remove_symmetric. rewrite swap_symmetric. apply swap_remove_reduction.
        ** subst. rewrite remove_symmetric. assert (Hr: remove y (remove x0 (fv_nom t1)) [=] remove x0 (remove y (fv_nom t1))).
           {
           rewrite remove_symmetric. reflexivity.
           }
           rewrite Hr. clear Hr. apply AtomSetProperties.Equal_remove. apply IHt1. apply diff_remove_2 in Hfv'.
            *** assumption.
            *** auto.
    + apply IHt2. apply Hfv.
Qed.
(* end hide *)

(** The notion of $\alpha$-equivalence is defined in the usual way by the following rules:

%\begin{mathpar}
 \inferrule*[Right={({\rm\it aeq\_var})}]{~}{x =_\alpha x} \and  \inferrule*[Right={({\rm\it aeq\_abs\_same})}]{t_1 =_\alpha t_2}{\lambda_x.t_1 =_\alpha \lambda_x.t_2} 
\end{mathpar}%

%\begin{mathpar}
\inferrule*[Right={({\rm\it aeq\_abs\_diff})}]{x \neq y \and x \notin fv(t_2) \and t_1 =_\alpha \swap{y}{x}{t_2}}{\lambda_x.t_1 =_\alpha \lambda_y.t_2} 
\end{mathpar}%

%\begin{mathpar}
 \inferrule*[Right={({\rm\it aeq\_app})}]{t_1 =_\alpha t_1' \and t_2 =_\alpha t_2'}{t_1\ t_2 =_\alpha t_1'\ t_2'} \and  \inferrule*[Right={({\rm\it aeq\_sub\_same})}]{t_1 =_\alpha t_1' \and t_2 =_\alpha t_2'}{\esub{t_1}{x}{t_2} =_\alpha \esub{t_1'}{x}{t_2'}} 
\end{mathpar}%

%\begin{mathpar}
\inferrule*[Right={({\rm\it aeq\_sub\_diff})}]{t_2 =_\alpha t_2' \and x \neq y \and x \notin fv(t_1') \and t_1 =_\alpha \swap{y}{x}{t_1'}}{\esub{t_1}{x}{t_2} =_\alpha \esub{t_1'}{y}{t_2'}} 
\end{mathpar}%

Each of these rules correspond to a constructor in the [aeq] inductive definition below:

 *)

Inductive aeq : n_sexp -> n_sexp -> Prop :=
| aeq_var : forall x, aeq (n_var x) (n_var x)
| aeq_abs_same : forall x t1 t2, aeq t1 t2 -> aeq (n_abs x t1)(n_abs x t2)
| aeq_abs_diff : forall x y t1 t2, x <> y -> x `notin` fv_nom t2 -> aeq t1 (swap y x t2) -> aeq (n_abs x t1) (n_abs y t2)
| aeq_app : forall t1 t2 t1' t2', aeq t1 t1' -> aeq t2 t2' -> aeq (n_app t1 t2) (n_app t1' t2')
| aeq_sub_same : forall t1 t2 t1' t2' x, aeq t1 t1' -> aeq t2 t2' -> aeq (n_sub t1 x t2) (n_sub t1' x t2')
| aeq_sub_diff : forall t1 t2 t1' t2' x y, aeq t2 t2' -> x <> y -> x `notin` fv_nom t1' -> aeq t1 (swap y x t1') -> aeq (n_sub t1 x t2) (n_sub t1' y t2').
(* begin hide *)
Hint Constructors aeq.
(* end hide *)

(** In what follows, we use a infix notation for $\alpha$-equivalence in the Coq code: we write [t =a u] instead of [aeq t u].
 *)
(* begin hide *)
Notation "t =a u" := (aeq t u) (at level 60).
(* end hide *)
(** The above notion defines an equivalence relation over the set [n_sexp] of nominal expressions with explicit substitutions, %{\it i.e.}% the [aeq] relation is reflexive, symmetric and transitive. *)
(* begin hide *)
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
(* end hide *)
(** Informally, two terms are $\alpha$-equivalent if they differ only by the names of the bound variables. Therefore, $\alpha$-equivalent terms have the same size, and the same set of free variables: *)

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
(* begin hide *)
Lemma aeq_refl : forall n, n =a n.
Proof.
  induction n; auto.
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
(* end hide *)
(** The key point of the nominal approach is that the swap operation is stable under $\alpha$-equivalence in the sense that, $t_1 =_\alpha t_2$ if, and only if $\swap{x}{y}{t_1} =_\alpha \swap{x}{y}{t_2}$. Note that this is not true for renaming substitutions: in fact, $\lambda_x.z =_\alpha \lambda_y.z$, but $(\lambda_x.z)\msub{z}{x} = \lambda_x.x \neq_\alpha \lambda_y.x (\lambda_y.z)\msub{z}{x}$, assuming that $x \neq y$. This stability result is formalized as follows: *)

Corollary aeq_swap: forall t1 t2 x y, t1 =a t2 <-> (swap x y t1) =a (swap x y t2).
Proof.
  intros. split.
  - apply aeq_swap1.
  - apply aeq_swap2.
Qed.

(* begin hide *)
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

Lemma aeq_same_abs: forall x t1 t2, n_abs x t1 =a n_abs x t2 -> t1 =a t2.
Proof.
  intros. inversion H.
  - assumption.
  - rewrite swap_id in H6; assumption.
Qed.

Lemma aeq_diff_abs: forall x y t1 t2, (n_abs x t1) =a (n_abs y t2) -> t1 =a (swap x y t2).
Proof.
  intros. inversion H; subst.
  - rewrite swap_id; assumption.
  - rewrite swap_symmetric; assumption.
Qed.

Lemma aeq_same_sub: forall x t1 t1' t2 t2', (n_sub t1 x t2) =a (n_sub t1' x t2') -> t1 =a t1' /\ t2 =a t2'.
Proof.
  intros. inversion H; subst.
  - split; assumption.
  - split.
    + rewrite swap_id in H9; assumption.
    + assumption.
Qed.

Lemma aeq_diff_sub: forall x y t1 t1' t2 t2', (n_sub t1 x t2) =a (n_sub t1' y t2') -> t1 =a (swap x y t1') /\ t2 =a t2'.
Proof.
  intros. inversion H; subst.
  - split.
    + rewrite swap_id; assumption.
    + assumption.
  - split.
    + rewrite swap_symmetric; assumption.
    + assumption.
Qed.

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
(* end hide *)

(** There are several interesting auxiliary properties that need to be proved before achieving the substitution lemma. In what follows, we refer only to the tricky or challenging ones, but the interested reader can have a detailed look in the source files. Note that, swaps are introduced in proofs by the rules $({\rm\it aeq\_abs\_diff})$ and $({\rm\it aeq\_sub\_diff})$. As we will see, the proof steps involving these rules are trick because a naïve strategy can easily result in a proofless branch. so that one can establish the $\alpha$-equivalence between two abstractions or two explicit substitutions with different binders. The following proposition states when two swaps with a common name collapse, and it is used in the transitivity proof of [aeq]:
 *)

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

(** ** The metasubstitution operation of the $\lambda$-calculus *)

(** The main operation of the $\lambda$-calculus is the $\beta$-reduction that express how to evaluate a function applied to a given argument:

$(\lambda_x.t)\ u \to_\beta t\msub{x}{u}$

In a less formal context, the concept of $\beta$-reduction means that the result of evaluating the function $(\lambda_x.t)$ with argument $u$ is obtained by substituting $u$ for the free ocurrences of the variable $x$ in $t$. Moreover, it is a capture free substitution in the sense that no free variable becomes bound after the substitution. This operation is in the meta level because it is outside the grammar of the $\lambda$-calculus, and that's why it is called metasubstitution. As a metaoperation, its definition usually comes with a degree of informality. For instance, Barendregt%\cite{barendregtLambdaCalculusIts1984}% defines it as follows:

$t\msub{x}{u} = \left\{
 \begin{array}{ll}
  u, & \mbox{ if } t = x; \\
  y, & \mbox{ if } t = y \mbox{ and } x \neq y; \\
  t_1\msub{x}{u}\ t_2\msub{x}{u}, & \mbox{ if } t = (t_1\ t_2)\msub{x}{u}; \\
  \lambda_y.(t_1\msub{x}{u}), & \mbox{ if } t = \lambda_y.t_1.
 \end{array}\right.$%\vspace{.5cm}%

%\noindent% where it is assumed the so called "Barendregt's variable convention": if $t_1, t_2, \ldots, t_n$ occur in a certain mathematical context (e.g. definition, proof), then in these terms all bound variables are chosen to be different from the free variables.

This means that we are assumming that both $x \neq y$ and $y\notin fv(u)$ in the case $t = \lambda_y.t_1$. This approach is very convenient in informal proofs because it avoids having to rename bound variables. In order to formalize the capture free substitution of the $\lambda$-calculus, %{\it i.e.}% the metasubstitution, a renaming is performed whenever it is propagated inside a binder. In our case, there are two binders: the abstraction and the explicit substitution. 

%\begin{definition}

Let $t$ and $u$ be terms, and $x$ a variable. The result of substituting $u$ for the free ocurrences of $x$ in $t$, written $t\msub{x}{u}$ is defined as follows:

$t\msub{x}{u} = \left\{
 \begin{array}{ll}
  u, & \mbox{ if } t = x; \\
  y, & \mbox{ if } t = y \mbox{ and } x \neq y; \\
  t_1\msub{x}{u}\ t_2\msub{x}{u}, & \mbox{ if } t = (t_1\ t_2)\msub{x}{u}; \\
  \lambda_x.t_1, & \mbox{ if } t = \lambda_x.t_1; \\
  \lambda_z.((\swap{y}{z}{t_1})\msub{x}{u}), & \mbox{ if } t = \lambda_y.t_1, x \neq y \mbox{ and } z\notin fv(\lambda_y.t_1)\cup fv(u) \cup \{x\}; \\
  \esub{t_1}{x}{t_2\msub{x}{u}}, & \mbox{ if } t = \esub{t_1}{x}{t_2}; \\
  \esub{(\swap{y}{z}{t_1})\msub{x}{u}}{z}{t_2\msub{x}{u}}, & \mbox{ if } t = \esub{t_1}{y}{t_2}, x \neq y \mbox{ and } z\notin fv(\esub{t_1}{y}{t_2})\cup fv(u) \cup \{x\}; \\
 \end{array}\right.$

\end{definition}%

Note that this function is not structurally recursive due to the swaps in the recursive calls. A structurally recursive version of the function [subst_rec_fun] can be found in the file [nominal.v] of the [Metalib] library%\footnote{\url{https://github.com/plclub/metalib}}%, but it uses the size of the term in which the substitution will be performed as an extra argument that decreases with each recursive call. We write [[x:=u]t] instead of [subst_rec_fun t u x] in the Coq code to represent $t\msub{x}{u}$. The corresponding Coq code is as follows: *)

(* begin hide *)
Require Import Recdef.
(* end hide *)
Function subst_rec_fun (t:n_sexp) (u :n_sexp) (x:atom) {measure size t} : n_sexp :=
  match t with
  | n_var y => if (x == y) then u else t
  | n_abs y t1 => if (x == y) then t else let (z,_) :=
    atom_fresh (fv_nom u `union` fv_nom t `union` {{x}}) in n_abs z (subst_rec_fun (swap y z t1) u x)
  | n_app t1 t2 => n_app (subst_rec_fun t1 u x) (subst_rec_fun t2 u x)
  | n_sub t1 y t2 => if (x == y) then n_sub t1 y (subst_rec_fun t2 u x) else let (z,_) :=
    atom_fresh (fv_nom u `union` fv_nom t `union` {{x}}) in
    n_sub (subst_rec_fun (swap y z t1) u x) z (subst_rec_fun t2 u x) 
end.
Proof.
 - intros. simpl. rewrite swap_size_eq. auto.
 - intros. simpl. lia.
 - intros. simpl. lia.
 - intros. simpl. lia.
 - intros. simpl. lia.
 - intros. simpl. rewrite swap_size_eq. lia.
Defined.
(* begin hide *)
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

Lemma m_subst_app: forall t1 t2 u x, [x := u](n_app t1 t2) = n_app ([x := u]t1) ([x := u]t2).
Proof.
  intros t1 t2 u x. unfold m_subst. rewrite subst_rec_fun_equation. reflexivity.
Qed.
(* end hide *)

(** The standard proof strategy for the non trivial properties is induction on the structure of the terms. Nevertheless, the builtin induction principle automatically generated for the inductive definition [n_sexp] is not strong enough due to swappings. In fact, in general, the induction hypothesis in the abstraction case, for instance, refer to the body of the abstraction, while the goal involves a swap acting on the body of the abstraction. In order to circunvet this problem, we use an induction principle based on the size of terms: *)

Lemma n_sexp_induction:
 forall P : n_sexp -> Prop,
 (forall x, P (n_var x)) ->
 (forall t1 z, (forall t2 x y, size t2 = size t1 -> P (swap x y t2)) -> P (n_abs z t1)) ->
 (forall t1 t2, P t1 -> P t2 -> P (n_app t1 t2)) ->
 (forall t1 t3 z, P t3 -> (forall t2 x y, size t2 = size t1 -> P (swap x y t2)) -> P (n_sub t1 z t3)) -> 
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

(* begin hide *)
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

Require Import Setoid Morphisms.

Instance Equivalence_aeq: Equivalence aeq.
Proof.
  split.
  - unfold Reflexive. apply aeq_refl.
  - unfold Symmetric. apply aeq_sym.
  - unfold Transitive. apply aeq_trans.
Qed.
(* end hide *)

(** The following lemma states that if $x \notin fv(t)$ then $t\msub{x}{u} =_\alpha t$. In informal proofs the conclusion of this lemma is usually stated as a syntactic equality, %{\i.e.}% $t\msub{x}{u} = t$ instead of the $\alpha$-equivalence, but due to the changes of the names of the bound variables when the metasubstitution is propagated inside an abstraction or inside an explicit substitution, syntactic equality does not hold here. *)

Lemma m_subst_notin: forall t u x, x `notin` fv_nom t -> [x := u]t =a t.
Proof.
  induction t using n_sexp_induction.
  - intros u x' Hfv. simpl in *. apply notin_singleton_1 in Hfv. rewrite m_subst_var_neq.
    + apply aeq_refl.
    + assumption.
  - intros u x Hfv. simpl in *. unfold m_subst in *. rewrite subst_rec_fun_equation. destruct (x == z).
    + subst. apply aeq_refl.
    + destruct (atom_fresh (union (fv_nom u) (union (fv_nom (n_abs z t)) (singleton x)))). case (z == x0).
      * intro Heq. subst. apply aeq_abs_same. apply aeq_trans with (swap x0 x0 t).
        ** apply H.
           *** reflexivity.
           *** rewrite swap_id. apply notin_remove_1 in Hfv. destruct Hfv.
               **** symmetry in H0. contradiction.
               **** assumption.
        ** rewrite swap_id. apply aeq_refl.
      * intro Hneq. apply aeq_abs_diff.
        ** apply aux_not_equal. assumption.
        ** apply notin_union_2 in n0. apply notin_union_1 in n0. simpl in n0. apply notin_remove_1 in n0. destruct n0.
           *** contradiction.
           *** assumption.
        ** apply H.
           *** reflexivity.
           *** apply notin_remove_1 in Hfv. destruct Hfv.
               **** symmetry in H0. contradiction.
               **** repeat apply notin_union_2 in n0. apply notin_singleton_1 in n0. apply fv_nom_remove_swap; assumption.
  - intros u x Hfv. unfold m_subst in *. simpl in *. rewrite subst_rec_fun_equation. apply aeq_app.
    + apply IHt1. apply notin_union_1 in Hfv. assumption.
    + apply IHt2. apply notin_union_2 in Hfv. assumption.
  - intros u x Hfv. simpl in *. unfold m_subst in *. rewrite subst_rec_fun_equation. destruct (atom_fresh (union (fv_nom u) (union (fv_nom (n_sub t1 z t2)) (singleton x)))). destruct (x == z).
    + subst. apply aeq_sub_same.
      * apply aeq_refl.
      * apply notin_union_2 in Hfv. apply IHt1. assumption.
    + case (x0 == z).
      * intro Heq. subst. apply aeq_sub_same.
        ** apply aeq_trans with (swap z z t1). apply H.
           *** reflexivity.
           *** rewrite swap_id. apply notin_union_1 in Hfv. apply notin_remove_1 in Hfv. destruct Hfv.
               **** symmetry in H0. contradiction.
               **** assumption.
           *** rewrite swap_id. apply aeq_refl.
        ** apply IHt1. apply notin_union_2 in Hfv. assumption.
      * intro Hneq. apply aeq_sub_diff.
        ** apply IHt1. apply notin_union_2 in Hfv. assumption.
        ** assumption.
        ** apply notin_union_2 in n. apply notin_union_1 in n. simpl in n. apply notin_union_1 in n. apply notin_remove_1 in n. destruct n.
           *** symmetry in H0. contradiction.
           *** assumption.
        ** apply H.
           *** reflexivity.
           *** apply notin_union_1 in Hfv. apply notin_remove_1 in Hfv. destruct Hfv. 
               **** symmetry in H0. contradiction. 
               **** repeat apply notin_union_2 in n. apply notin_singleton_1 in n. apply fv_nom_remove_swap; assumption.
Qed.
(** %\noindent{\bf Proof.}% The proof is done by induction on the size of the term [t] using the [n_sexp_induction] principle. One interesting case is when $t = \lambda_y.t_1$ and $x \neq y$. In this case, we have to prove that $(\lambda_y.t_1)\msub{x}{u} =_\alpha \lambda_y.t_1$. The induction hypothesis express the fact that every term with the same size as the body of the abstraction $t_1$ satisfies the property to be proven:

$\forall t'\ x\ y, |t'| = |t_1| \to \forall u\ x', x' \notin fv(\swap{x}{y}{t'}) \to (\swap{x}{y}{t'})\msub{x'}{u} =_\alpha \swap{x}{y}{t'}$.

Therefore, according to the function [subst_rec_fun], the variable $y$ will be renamed to a new name, say $z$, such that $z \notin fv(\lambda_y.t_1) \cup fv(u) \cup \{x\}$, and we have to prove that $\lambda_z.(\swap{z}{y}{t_1})\msub{x}{u} =_\alpha \lambda_y.t_1$. Since $z \notin fv(\lambda_y.t_1) = fv(t_1)\backslash \{y\}$, there are two cases:
 %\begin{enumerate}
   \item $z = y$: In this case, we have to prove that $\lambda_z.(\swap{z}{z}{t_1})\msub{x}{u} =_\alpha \lambda_z.t_1$. By the rule $\mbox{\it aeq}\_\mbox{\it abs}\_\mbox{\it same}$ we get $(\swap{z}{z}{t_1})\msub{x}{u} =_\alpha t_1$, but in order to apply the induction hypothesis the body of the metasubstitution and the term in the right hand side need to be the same and both need to be a swap. For this reason, we use the transitivity of $\alpha$-equivalence with $\swap{z}{z}{t_1}$ as intermediate term. The first subcase is proved by the induction hypothesis, and the second one is proved by the reflexivity of $\alpha$-equivalence.
\item $z \neq y$: In this case, $x \notin fv(t)$ and we can apply the rule $\mbox{\it aeq}\_\mbox{\it abs}\_\mbox{\it diff}$. The new goal is $(\swap{z}{y}{t_1})\msub{x}{u} =_\alpha \swap{z}{y}{t_1}$ which holds by the induction hypothesis, since $|\swap{z}{y}{t_1}| = |t_1|$ and $x \notin fv(\swap{z}{y}{t_1})$ because $x \neq z$, $x \neq y$ and $x \notin fv(t)$.
  \end{enumerate}%
 The explicit substitution case is also interesting, but it follows a similar strategy used in the abstraction case for $t_1$. For $t_2$ the result follows from the induction hypothesis. $\hfill\Box$ *)
(* begin hide *)
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
               **** subst. apply fv_nom_swap. apply notin_union_2 in _x0. apply notin_union_1 in _x0. apply notin_remove_1 in _x0. destruct _x0.
                    ***** contradiction.
                    ***** assumption.
               **** case (y == y0).
                    ***** intro Heq. subst. apply fv_nom_swap. apply notin_union_2 in _x0. apply notin_union_1 in _x0. apply notin_remove_1 in _x0. destruct _x0.
                    ****** contradiction.
                    ****** assumption.
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
                     clear e1. apply notin_union_2 in _x0. apply notin_union_1 in _x0. apply notin_union_1 in _x0. apply notin_remove_1 in _x0. destruct _x0.
                     ***** contradiction.
                     ***** assumption.
                **** apply notin_remove_2. case (y == y0). 
                      ***** intro Heq. subst. apply fv_nom_swap.
                            clear e1. apply notin_union_2 in _x0. apply notin_union_1 in _x0. apply notin_union_1 in _x0. apply notin_remove_1 in _x0. destruct _x0.
                            ****** contradiction.
                            ****** assumption.
                      ***** intro Hneq'. apply fv_nom_remove_swap.
                            ****** assumption.
                            ****** assumption.
                            ****** assumption.
      * apply IHn0.
        ** assumption.
        ** apply notin_union_2 in H. apply notin_remove_2. assumption.
Qed.
(* end hide *)

(** We will now prove some stability results for the metasubstitution w.r.t. $\alpha$-equivalence. More precisely, we will prove that if $t =_\alpha t'$ and $u =_\alpha u'$ then $\metasub{t}{x}{u} =_\alpha \metasub{t'}{x}{u'}$, where $x$ is any variable and $t, t', u$ and $u'$ are any [n_sexp] terms. This proof is split in two steps: firstly, we prove that if $u =_\alpha u'$ then $\metasub{t}{x}{u} =_\alpha \metasub{t}{x}{u'}, \forall x, t, u, u'$; secondly, we prove that if $t =_\alpha t'$ then $\metasub{t}{x}{u} =_\alpha \metasub{t'}{x}{u}, \forall x, t, t', u$. These two steps are then combined through the transitivity of the $\alpha$-equivalence relation. Nevertheless, this task were not straighforward. Let's follow the steps of our first trial. *)

Lemma aeq_m_subst_in_trial: forall t u u' x, u =a u' -> ([x := u] t) =a ([x := u'] t).
Proof.
  induction t using n_sexp_induction.
  (** %\noindent{\bf Proof.}% The proof is done by induction on the size of the term [t].*)
  - intros u u' x' Haeq. unfold m_subst. repeat rewrite subst_rec_fun_equation. destruct (x' == x).
    + assumption.
    + apply aeq_refl.
  - intros u u' x Haeq. unfold m_subst in *. repeat rewrite subst_rec_fun_equation. destruct (x == z). (** The interesting case is when [t] is an abstraction, %{\it i.e.}% $t = \lambda_y.t_1$. We need to prove that $\metasub{(\lambda_y.t_1)}{x}{u} =_\alpha \metasub{(\lambda_y.t_1)}{x}{u'}$.*)      
    + apply aeq_refl. (** If $x = y$ then the result is trivial.*)
    + destruct (atom_fresh (union (fv_nom u) (union (fv_nom (n_abs z t)) (singleton x)))). destruct (atom_fresh (union (fv_nom u') (union (fv_nom (n_abs z t)) (singleton x)))). case (x0 == x1). (** Suppose $x \neq y$. The metasubstitution will be propagated inside the abstraction on each side of the $\alpha$-equation, after generating a new name for each side. The new goal is then $\lambda_{x_0}.\metasub{(\swap{y}{x_0}{t_1})}{x}{u} =_\alpha \lambda_{x_1}.\metasub{(\swap{y}{x_1}{t_1})}{x}{u'}$, where $x_0 \notin fv(\lambda_y.t_1) \cup fv(u) \cup \{x\}$ and $x_1 \notin fv(\lambda_y.t_1) \cup fv(u') \cup \{x\}$. The variables $x_0$ and $x_1$ are either the same or different.*)
      * intro Heq. subst. apply aeq_abs_same. (* aqui *) (** In the former case the result is trivial because $u =_\alpha u'$. *)
      *

      
Axiom Eq_implies_equality: forall s s': atoms, s [=] s' -> s = s'.

Lemma aeq_m_subst_in: forall t u u' x, u =a u' -> ([x := u] t) =a ([x := u'] t).
Proof.
  induction t using n_sexp_induction.
  - intros u u' x' Haeq. pose proof Haeq as Hfv. apply aeq_fv_nom in Hfv. apply Eq_implies_equality in Hfv. unfold m_subst in *. repeat rewrite subst_rec_fun_equation. destruct (x' == x).
    + assumption.
    + reflexivity.
  - intros u u' x Haeq. pose proof Haeq as Hfv. apply aeq_fv_nom in Hfv. apply Eq_implies_equality in Hfv. unfold m_subst in *. repeat rewrite subst_rec_fun_equation. rewrite Hfv. destruct (atom_fresh (union (fv_nom u') (union (fv_nom (n_abs z t)) (singleton x)))). destruct (x == z).
      * apply aeq_refl.
      * apply aeq_abs_same. apply H.
        ** reflexivity.
        ** assumption.
  - intros u u' x Haeq. unfold m_subst in *. rewrite subst_rec_fun_equation. apply aeq_sym. rewrite subst_rec_fun_equation. apply aeq_app.
    + apply IHt1. apply aeq_sym. assumption.
    + apply IHt2. apply aeq_sym. assumption.
  - intros u u' x Haeq. unfold m_subst in *. rewrite subst_rec_fun_equation. apply aeq_sym. rewrite subst_rec_fun_equation. pose proof Haeq as Hfv. apply aeq_fv_nom in Hfv. apply Eq_implies_equality in Hfv. rewrite Hfv. destruct (atom_fresh (union (fv_nom u') (union (fv_nom (n_sub t1 z t2)) (singleton x)))). destruct (x == z).
    + apply aeq_sub_same.
      * apply aeq_refl.
      * apply IHt1. apply aeq_sym. assumption.
    + apply aeq_sub_same.
      * apply H.
        ** reflexivity.
        ** apply aeq_sym. assumption.
      * apply IHt1. apply aeq_sym. assumption.
Qed.

Lemma aeq_abs_notin: forall t1 t2 x y, x <> y ->  n_abs x t1 =a n_abs y t2 -> x `notin` fv_nom t2.
Proof.
  intros t1 t2 x y Hneq Haeq. inversion Haeq; subst.
  - contradiction.
  - assumption.
Qed.

Lemma aeq_sub_notin: forall t1 t1' t2 t2' x y, x <> y ->  n_sub t1 x t2 =a n_sub t1' y t2' -> x `notin` fv_nom t1'.
Proof.
  intros t1 t1' t2 t2' x y Hneq Haeq. inversion Haeq; subst.
  - contradiction.
  - assumption.
Qed.

Lemma aeq_m_subst_out: forall t t' u x, t =a t' -> ([x := u] t) =a ([x := u] t').
Proof.
  induction t using n_sexp_induction.
  - intros t' u x' Haeq. inversion Haeq; subst. apply aeq_refl.
  - intros t' u x Haeq. inversion Haeq; subst.
    + pose proof Haeq as Hfv. apply aeq_fv_nom in Hfv. simpl in *. apply Eq_implies_equality in Hfv. unfold m_subst in *. repeat rewrite subst_rec_fun_equation. simpl. rewrite Hfv. destruct (atom_fresh (union (fv_nom u) (union (remove z (fv_nom t2)) (singleton x)))). destruct (x == z).
      * assumption.
      * apply aeq_abs_same. apply H.
        ** reflexivity.
        ** apply aeq_swap. assumption.
    + pose proof Haeq as Hfv. apply aeq_fv_nom in Hfv. simpl in *. apply Eq_implies_equality in Hfv. unfold m_subst in *. rewrite subst_rec_fun_equation. simpl. apply aeq_sym. rewrite subst_rec_fun_equation. simpl. rewrite Hfv. destruct (atom_fresh (union (fv_nom u) (union (remove y (fv_nom t2)) (singleton x)))). destruct (x == y).
      * subst. destruct (y == z).
        ** symmetry in e. contradiction.
        ** rewrite <- Haeq. pose proof n as Hnotin. repeat apply notin_union_2 in n. apply notin_singleton_1 in n. case (z == x0).
           *** intro Heq. subst.  apply aeq_abs_same. rewrite swap_id. apply aeq_sym in Haeq. apply aeq_abs_notin in Haeq.
               **** apply aeq_sym. apply m_subst_notin. assumption.
               ****assumption.
           *** intro Hneq. apply aeq_abs_diff.
               **** assumption.
               **** apply aeq_sym in Haeq. apply aeq_abs_notin in Haeq. assert (Hsub: subst_rec_fun (swap z x0 t) u y =a swap z x0 t).
                    ***** apply m_subst_notin. apply fv_nom_remove_swap; assumption.
                    ***** apply aeq_fv_nom in Hsub. rewrite Hsub. apply fv_nom_swap. rewrite <- Hfv in Hnotin. apply notin_union_2 in  Hnotin. apply notin_union_1 in Hnotin. apply notin_remove_1 in Hnotin. destruct Hnotin.
                    ****** contradiction.
                    ****** assumption.
                    ***** assumption.
               **** apply aeq_sym in Haeq. apply aeq_abs_notin in Haeq. rewrite (swap_symmetric _ z x0). apply aeq_trans with (swap x0 z (swap x0 z t)).
                    ***** rewrite swap_involutive. apply aeq_refl.
                    ***** apply aeq_swap. apply aeq_sym. apply m_subst_notin. apply fv_nom_remove_swap; assumption.
                    ***** assumption.
      * destruct (x == z).
        ** rewrite Haeq. subst. case (x0 == y). 
           *** intro Heq. subst. apply aeq_abs_same. rewrite swap_id. apply m_subst_notin. assumption.
           *** intro Hneq. apply aeq_abs_diff. 
               **** assumption.
               **** apply notin_union_2 in n. apply notin_union_1 in n. apply notin_remove_1 in n. destruct n.
                    ***** symmetry in H0. contradiction.
                    ***** assumption.
               **** apply m_subst_notin. apply fv_nom_remove_swap. 
                    ****** repeat apply notin_union_2 in n. apply notin_singleton_1 in n. assumption.
                    ****** assumption.
                    ****** assumption.
        ** apply aeq_abs_same. apply H.
           *** apply aeq_size in H5. rewrite swap_size_eq in H5. auto.
           *** case (x0 == y).
               **** intro Heq. subst. rewrite swap_id. apply (aeq_swap _ _ y z) in H5. rewrite swap_involutive in H5. apply aeq_sym. rewrite (swap_symmetric _ z y). assumption.
               **** intro Hneq. apply aeq_sym. apply (aeq_swap _ _ z x0) in H5. rewrite H5. rewrite (swap_symmetric _ z x0). rewrite (swap_symmetric _ y z). rewrite (swap_symmetric _ y x0). apply aeq_swap_swap.
                    ***** apply notin_union_2 in n. apply notin_union_1 in n. apply notin_remove_1 in n. destruct n.
                    ****** symmetry in H0. contradiction.
                    ****** assumption.
                    ***** assumption.
  - intros t u x Haeq. inversion Haeq; subst. clear Haeq. unfold m_subst in *. rewrite subst_rec_fun_equation. apply aeq_sym. rewrite subst_rec_fun_equation. apply aeq_app.
    + apply aeq_sym. apply IHt1. assumption.
    + apply aeq_sym. apply IHt2. assumption.
  - intros t u x Haeq. inversion Haeq; subst.
    + unfold m_subst in *. rewrite subst_rec_fun_equation. apply aeq_sym. rewrite subst_rec_fun_equation. apply aeq_fv_nom in Haeq. apply Eq_implies_equality in Haeq. rewrite Haeq. destruct (atom_fresh (union (fv_nom u) (union (fv_nom (n_sub t1' z t2')) (singleton x)))). simpl in *. destruct (x == z).
      * apply aeq_sub_same.
        ** apply aeq_sym. assumption.
        ** apply aeq_sym. apply IHt1. assumption.
      * apply aeq_sub_same.
        ** apply aeq_sym. apply H.
           *** reflexivity.
           *** apply aeq_swap. assumption.
        ** apply aeq_sym. apply IHt1. assumption.
    + unfold m_subst in *. rewrite subst_rec_fun_equation. apply aeq_sym. rewrite subst_rec_fun_equation. pose proof Haeq as Hfv. apply aeq_fv_nom in Hfv. apply Eq_implies_equality in Hfv. rewrite Hfv. destruct (atom_fresh (union (fv_nom u) (union (fv_nom (n_sub t1' y t2')) (singleton x)))). destruct (x == y).
      * subst. destruct (y == z).
        ** subst. contradiction.
        ** pose proof n as Hx0. repeat apply notin_union_2 in n. apply notin_singleton_1 in n. apply aeq_sym. apply aeq_sub_diff.
           *** apply IHt1. assumption.
           *** apply aux_not_equal. assumption.
           *** apply notin_union_2 in Hx0. apply notin_union_1 in Hx0. simpl in Hx0. apply notin_union_1 in Hx0. apply notin_remove_1 in Hx0. destruct Hx0.
               **** contradiction.
               ****assumption.
           *** apply aeq_trans with (swap z x0 t1).
               **** apply m_subst_notin. apply aeq_sym in Haeq. apply aeq_sub_notin in Haeq.
                    ***** apply fv_nom_remove_swap.
                    ****** assumption.
                    ****** apply aux_not_equal. assumption.
                    ****** assumption.
                    ***** assumption.
               **** apply aeq_trans with (swap z x0 (swap y z t1')).
                    ***** apply aeq_swap. assumption.
                    ***** rewrite (swap_symmetric _ z x0). rewrite (swap_symmetric _ y z). rewrite (swap_symmetric _ y x0). apply aeq_swap_swap.
                    ****** apply notin_union_2 in Hx0. apply notin_union_1 in Hx0. simpl in Hx0. apply notin_union_1 in Hx0. apply notin_remove_1 in Hx0. destruct Hx0.
                    ******* contradiction.
                    ******* assumption.
                    ****** assumption.
      * destruct (x == z).
        ** subst. pose proof n as Hx0. repeat apply notin_union_2 in n. apply notin_singleton_1 in n. apply aeq_sub_diff.
           *** apply aeq_sym. apply IHt1. assumption.
           *** apply aux_not_equal. assumption.
           *** rewrite <- Hfv in Hx0. apply notin_union_2 in Hx0. apply notin_union_1 in Hx0. simpl in Hx0. apply notin_union_1 in Hx0. apply notin_remove_1 in Hx0. destruct Hx0.
               **** contradiction.
               **** assumption.
           *** apply aeq_trans with (swap y x0 t1').
               **** apply m_subst_notin. apply fv_nom_remove_swap; assumption.
               **** rewrite <- Hfv in Hx0. apply (aeq_swap1  _ _ y z) in H7. rewrite swap_involutive in H7. apply aeq_sym in H7. apply (aeq_swap1 _ _ y x0) in H7. rewrite H7. rewrite (swap_symmetric _ y x0). rewrite (swap_symmetric _ z x0). apply aeq_swap_swap.
                    ****** apply notin_union_2 in Hx0. apply notin_union_1 in Hx0. simpl in Hx0. apply notin_union_1 in Hx0. apply notin_remove_1 in Hx0. destruct Hx0.
                    ******* contradiction.
                    ******* assumption.
                    ****** apply aeq_sym in Haeq. apply aeq_sub_notin in Haeq.
                    ******* assumption.
                    ******* apply aux_not_equal. assumption.
        ** apply aeq_sub_same.
           *** apply H.
               **** apply aeq_size in H7. symmetry. rewrite swap_size_eq in H7. assumption.
               **** case (x0 == y). 
                    ***** intro Heq. subst. rewrite swap_id. rewrite (swap_symmetric _ z y). apply (aeq_swap1 _ _ y z) in H7.
                    rewrite H7. rewrite swap_involutive. apply aeq_refl.
                    ***** intro Hneq. apply (aeq_swap1 _ _ z x0) in H7. rewrite H7. apply aeq_sym. rewrite (swap_symmetric _ z x0). rewrite (swap_symmetric _ y z). rewrite (swap_symmetric _ y x0). apply aeq_swap_swap.
                    ****** apply notin_union_2 in n. apply notin_union_1 in n. simpl in n. apply notin_union_1 in n. apply notin_remove_1 in n. destruct n.
                    ******* symmetry in H0. contradiction.
                    ******* assumption.
                    ****** assumption.
           *** apply aeq_sym. apply IHt1. assumption.
Qed.
          
Corollary aeq_m_subst_eq: forall t t' u u' x, t =a t' -> u =a u' -> ([x := u] t) =a ([x := u'] t').
Proof.
  intros t t' u u' x H1 H2. apply aeq_trans with ([x:=u]t').
  - apply aeq_m_subst_out. assumption.
  - apply aeq_m_subst_in. assumption.
Qed.

(** The following lemma states that a swap can be propagated inside the metasubstitution resulting in an $\alpha$-equivalent term. *)

Lemma swap_subst_rec_fun: forall x y z t u, swap x y (subst_rec_fun t u z) =a subst_rec_fun (swap x y t) (swap x y u) (swap_var x y z).
Proof.

  (** Firstly, we compare [x] and [y] which gives a trivial case when they are the same. *)
  intros x y z t u. destruct (x == y). 
  - subst. repeat rewrite swap_id. rewrite swap_var_id. apply aeq_refl.
    (** In this way, we can assume in the rest of the proof that [x] and [y] are different from each other. The proof proceeds by induction on the size of the term [t]. The tricky case is the abstraction and substitution cases. *)
  - generalize dependent u. generalize dependent z. generalize dependent y. generalize dependent x.
    induction t using n_sexp_induction.
    
    + intros x' y Hneq z u. rewrite subst_rec_fun_equation. destruct (z == x).
      * subst. simpl swap at 2. rewrite subst_rec_fun_equation. rewrite eq_dec_refl. apply aeq_refl.
      * pose proof swap_neq as Hswap. specialize (Hswap x' y z x). apply Hswap in n; clear Hswap.
        simpl swap at 2. rewrite subst_rec_fun_equation. destruct (swap_var x' y z == swap_var x' y x).
        ** contradiction.
        ** simpl swap. apply aeq_refl.
    + intros x y Hneq z' u. rewrite subst_rec_fun_equation. case (z' == z).
      * intro Heq. subst. simpl. rewrite subst_rec_fun_equation. rewrite eq_dec_refl. apply aeq_refl.
      * intro Hneq'. simpl in *. rewrite subst_rec_fun_equation. destruct (swap_var x y z' == swap_var x y z).
        ** apply (swap_neq x y) in Hneq'. contradiction.
        ** simpl. destruct (atom_fresh (union (fv_nom u) (union (remove z (fv_nom t)) (singleton z')))). destruct (atom_fresh (union (fv_nom (swap x y u)) (union (remove (swap_var x y z) (fv_nom (swap x y t))) (singleton (swap_var x y z'))))). simpl. apply aeq_trans with (n_abs (swap_var x y x0) (subst_rec_fun (swap x y (swap z x0 t)) (swap x y u) (swap_var x y z'))).
           *** apply aeq_abs_same. apply H. 
               **** reflexivity.
               **** assumption.
           *** case (x1 == swap_var x y x0). 
               **** intro Heq. subst. apply aeq_abs_same. apply aeq_m_subst_out. rewrite swap_equivariance. apply aeq_refl.
               **** intro Hneq''. rewrite (swap_equivariance _ x y z x0). apply aeq_abs_diff. 
                    ***** apply aux_not_equal. assumption.
                    ***** apply fv_nom_remove.
                    ****** apply notin_union_1 in n0. apply notin_fv_nom_equivariance. assumption.
                    ****** apply notin_remove_2. pose proof n0 as Hx0. apply notin_union_2 in n0. apply notin_union_1 in n0. apply notin_remove_1 in n0. case (z == x0).
                    ******** intro Heq. subst. apply fv_nom_swap. apply notin_union_2 in n1. apply notin_union_1 in n1. apply notin_remove_1 in n1. destruct n1.
                    ********* symmetry in H0. contradiction.
                    ********* assumption.
                    ******** intros Hneq'''. apply fv_nom_remove_swap.
                    ********* apply aux_not_equal. assumption.
                    ********* apply aux_not_equal. apply swap_neq. assumption.
                    ********* destruct n0.
                    ********** contradiction.
                    ********** apply notin_fv_nom_equivariance. assumption.
                    ***** rewrite H.
                    ****** replace (swap_var x1 (swap_var x y x0) (swap_var x y z')) with (swap_var x y z').
                    ******* apply aeq_m_subst_eq.
                    ******** apply notin_union_2 in n0. apply notin_union_1 in n0. apply notin_remove_1 in n0. destruct n0. 
                    *********** subst. repeat rewrite swap_id. rewrite (swap_symmetric _ x1 (swap_var x y x0)). rewrite swap_involutive. apply aeq_refl.
                    *********** apply notin_union_2 in n1. apply notin_union_1 in n1. apply notin_remove_1 in n1. destruct n1.
                    ************ subst. rewrite swap_id. apply aeq_refl.
                    ************ apply aeq_sym. rewrite (swap_symmetric _ x1 (swap_var x y x0)). rewrite (swap_symmetric _ (swap_var x y z) x1). pose proof aeq_swap_swap as Hswap. specialize (Hswap (swap x y t) x1 (swap_var x y z) (swap_var x y x0)). rewrite (swap_symmetric _ (swap_var x y z) (swap_var x y x0)). apply Hswap.
                    ************* apply notin_fv_nom_equivariance. assumption.
                    ************* assumption.
                    ******** apply aeq_sym. apply swap_reduction.
                    ********* apply notin_union_1 in n1. assumption.
                    ********* apply notin_union_1 in n0. apply notin_fv_nom_equivariance. assumption.
                    ******* symmetry. unfold swap_var at 1. destruct (swap_var x y z' ==  x1).
                    ******** repeat apply notin_union_2 in n1. apply notin_singleton_1 in n1. contradiction.
                    ******** destruct (swap_var x y z' == swap_var x y x0).
                    ********* repeat apply notin_union_2 in n0. apply notin_singleton_1 in n0. apply (swap_neq x y) in n0. contradiction.
                    ********* reflexivity.
                    ****** apply swap_size_eq.
                    ****** assumption.
    + intros x y H z u. rewrite subst_rec_fun_equation. simpl. apply aeq_sym. rewrite subst_rec_fun_equation. apply aeq_sym. apply aeq_app.
      * apply IHt1. assumption.
      * apply IHt2. assumption.
    + intros x y Hneq z' u. simpl. rewrite subst_rec_fun_equation. destruct (z' == z).
      * subst. simpl. apply aeq_sym. rewrite subst_rec_fun_equation. rewrite eq_dec_refl. apply aeq_sub_same.
        ** apply aeq_refl.
        ** apply aeq_sym. apply IHt1. assumption.
      * destruct (atom_fresh (union (fv_nom u) (union (fv_nom (n_sub t1 z t2)) (singleton z')))). simpl in *. apply aeq_sym. rewrite subst_rec_fun_equation. destruct (swap_var x y z' == swap_var x y z).
        ** apply (swap_neq x y) in n. contradiction.
        ** destruct (atom_fresh (union (fv_nom (swap x y u)) (union (fv_nom (n_sub (swap x y t1) (swap_var x y z) (swap x y t2))) (singleton (swap_var x y z'))))). case (x1 == (swap_var x y x0)).
           *** intro Heq. subst. apply aeq_sub_same.
               **** apply aeq_sym. rewrite <- swap_equivariance. apply H.
                    ***** reflexivity.
                    ***** assumption.
               **** apply aeq_sym. apply IHt1. assumption.
           *** intro Hneq'. simpl in *. apply aeq_trans with (n_sub (subst_rec_fun (swap x y (swap z x0 t1)) (swap x y u) (swap_var x y z')) (swap_var x y x0) (subst_rec_fun (swap x y t2) (swap x y u) (swap_var x y z'))). 
               **** apply aeq_sub_diff.
               ***** apply aeq_refl.
               ***** assumption.
               ***** pose proof n2 as Hx1. apply notin_union_2 in n2. apply notin_union_1 in n2. apply notin_union_1 in n2. apply notin_remove_1 in n2. destruct n2.
               ****** apply fv_nom_remove.
               ******* apply notin_union_1 in Hx1. assumption.
               ******* apply notin_remove_2. rewrite swap_equivariance. subst. pose proof n0 as Hx0. apply notin_union_2 in n0. apply notin_union_1 in n0. apply notin_union_1 in n0. apply notin_remove_1 in n0. destruct n0.
               ******** subst. contradiction.
               ******** apply fv_nom_swap. apply notin_fv_nom_equivariance. assumption.
               ****** apply fv_nom_remove.
               ******* apply notin_union_1 in Hx1. assumption.
               ******* apply notin_remove_2. rewrite swap_equivariance. apply notin_union_2 in Hx1. apply notin_union_1 in Hx1. apply notin_union_1 in Hx1. apply notin_remove_1 in Hx1. case (swap_var x y z == x1).
               ******** intro Heq. subst. apply fv_nom_swap. apply notin_union_2 in n0. apply notin_union_1 in n0. apply notin_union_1 in n0. apply notin_remove_1 in n0. destruct n0.
               ********* subst. contradiction.
               ********* apply notin_fv_nom_equivariance. assumption.
               ******** intro Hneq''. destruct Hx1.
               ********* contradiction.
               ********* apply fv_nom_remove_swap.
               ********** assumption.
               ********** apply aux_not_equal. assumption.
               ********** assumption.
               ***** rewrite H.
               ****** replace (swap_var (swap_var x y x0) x1 (swap_var x y z')) with (swap_var x y z').
               ******* apply aeq_m_subst_eq.
               ******** rewrite (swap_equivariance _ x y z x0). apply aeq_sym. rewrite swap_symmetric. rewrite (swap_symmetric _ (swap_var x y z) (swap_var x y x0)). rewrite (swap_symmetric _ (swap_var x y z) x1). pose proof n0 as Hx0. pose proof n2 as Hx1. apply notin_union_2 in n2. apply notin_union_1 in n2. apply notin_union_1 in n2. apply notin_remove_1 in n2. destruct n2.
               ********* subst. rewrite swap_id. apply notin_union_2 in n0. apply notin_union_1 in n0. apply notin_union_1 in n0. apply notin_remove_1 in n0. case (z == x0).
               ********** intro Heq. subst. repeat rewrite swap_id. apply aeq_refl.
               ********** intro Hneq''. rewrite (swap_symmetric _ (swap_var x y z) (swap_var x y x0)). rewrite swap_involutive. apply aeq_refl.
               ********* apply notin_union_2 in n0. apply notin_union_1 in n0. apply notin_union_1 in n0. apply notin_remove_1 in n0. case (z == x0).
               ********** intro Heq. subst. rewrite swap_id. apply aeq_refl.
               ********** intro Hneq''. destruct n0.
               *********** contradiction.
               *********** apply aeq_swap_swap.
               ************ assumption.
               ************ apply notin_union_2 in Hx0. apply notin_union_1 in Hx0. apply notin_union_1 in Hx0. apply notin_remove_1 in Hx0. destruct Hx0.
               ************* contradiction.
               ************* apply notin_fv_nom_equivariance. assumption.
               ******** symmetry. apply swap_reduction.
               ********* apply notin_fv_nom_equivariance. apply notin_union_1 in n0. assumption.
               ********* apply notin_union_1 in n2. assumption.
               ******* symmetry. unfold swap_var at 1. destruct (swap_var x y z' == swap_var x y x0).
               ******** repeat apply notin_union_2 in n0. apply notin_singleton_1 in n0. apply (swap_neq x y) in n0. contradiction.
               ******** destruct (swap_var x y z' == x1).
               ********* repeat apply notin_union_2 in n2. apply notin_singleton_1 in n2. contradiction.
               ********* reflexivity.
               ****** apply swap_size_eq.
               ****** apply aux_not_equal. assumption.
               **** apply aeq_sub_same.
                    ***** apply aeq_sym. apply H.
                    ****** reflexivity.
                    ****** assumption.
                    ***** apply aeq_sym. apply IHt1. assumption.
Qed.

(* begin hide *)

Lemma m_subst_abs: forall t1 u x y, [x := u](n_abs y t1)  =a
       if (x == y) then (n_abs y t1)
       else let (z,_) := atom_fresh (fv_nom u `union` fv_nom (n_abs y t1) `union` {{x}}) in n_abs z (subst_rec_fun (swap y z t1) u x).
Proof.
  intros. destruct (x == y).
  - subst. unfold m_subst. rewrite subst_rec_fun_equation. rewrite eq_dec_refl. apply aeq_refl.
  - unfold m_subst. rewrite subst_rec_fun_equation. destruct (x == y).
    + simpl. contradiction.
    + destruct (atom_fresh (union (fv_nom u) (union (fv_nom (n_abs y t1)) (singleton x)))). apply aeq_refl.
Qed.
(* end hide *)

(** The following lemmas state, respectively, what hapens when the variable in the meta-substitution is equal or different from the one in the abstraction. When it is equal, the meta-substitution is irrelevant. When they are different, we take a new variable that does not occur freely in the substituted term in the meta-substitution nor in the abstraction and is not the variable in the meta-substitution, and the abstraction of this new variable using the meta-substitution of the swap of the former variable in the meta-substitution is alpha-equivalent to the original meta-substitution of the abstraction. **)
(** The proofs were made using the definition of the meta-substitution, each case being respectively each one in the definition.**)
Lemma m_subst_abs_eq : forall u x t, [x := u](n_abs x t) = n_abs x t.
Proof.
  intros u x t. unfold m_subst. rewrite subst_rec_fun_equation. rewrite eq_dec_refl. reflexivity.
Qed.

Lemma m_subst_abs_neq : forall t u x y z, x <> y -> z `notin` fv_nom u `union` fv_nom (n_abs y t) `union` {{x}} -> [x := u](n_abs y t) =a n_abs z ([x := u](swap y z t)).
Proof.
  intros t u x y z H1 H2. unfold m_subst. pose proof m_subst_abs as Habs. specialize (Habs t u x y).
  destruct (x == y) in Habs. 
  - contradiction.
  - destruct (atom_fresh (union (fv_nom u) (union (fv_nom (n_abs y t)) (singleton x)))) in Habs.
    rewrite Habs. destruct (x0 == z).
    + subst. apply aeq_refl.
    + apply aeq_abs_diff.
      * assumption.
      * pose proof fv_nom_remove as H. unfold m_subst in *. apply H.
        ** apply notin_union_1 in n0. assumption.
        ** apply notin_remove_2. pose proof n0 as Hx0. apply notin_union_2 in n0. apply notin_union_1 in n0. simpl in *. apply notin_remove_1 in n0. destruct (x0 == y).
           *** subst. apply fv_nom_swap. apply notin_union_2 in H2. apply notin_union_1 in H2. simpl in H2.
               apply not_eq_sym in n1. apply diff_remove_2 in H2; assumption.
           *** destruct n0.
               **** symmetry in H0. contradiction. 
               **** apply fv_nom_remove_swap.
                    ***** assumption.
                    ***** assumption.
                    ***** assumption.
      * rewrite swap_subst_rec_fun. replace (swap_var z x0 x) with x.
        ** apply aeq_m_subst_eq.
           *** apply aeq_sym. rewrite (swap_symmetric _ z x0). rewrite (swap_symmetric _ y z). rewrite (swap_symmetric _ y x0). case (x0 == y).
               **** intro Heq. subst. rewrite swap_id. rewrite (swap_symmetric _ y z). rewrite swap_involutive. apply aeq_refl.
               **** intro Hneq. case (z == y).
                    ***** intro Heq. subst. rewrite swap_id. apply aeq_refl.
                    ***** intro Hneq'. apply aeq_swap_swap.
                    ****** apply notin_union_2 in n0. apply notin_union_1 in n0. simpl in n0. apply notin_remove_1 in n0. destruct n0.
                    ******* symmetry in H. contradiction.
                    *******  assumption.
                    ****** apply notin_union_2 in H2. apply notin_union_1 in H2. simpl in H2. apply notin_remove_1 in H2. destruct H2.
                    ******* symmetry in H. contradiction.
                    ******* assumption.
           *** apply aeq_sym. apply swap_reduction.
               **** apply notin_union_1 in H2. assumption.
               **** apply notin_union_1 in n0. assumption.
        ** apply eq_sym. unfold swap_var. destruct (x == z).
           *** subst. repeat apply notin_union_2 in H2. apply notin_singleton_1 in H2. contradiction.
           *** destruct (x == x0). 
               **** subst. repeat apply notin_union_2 in n0. apply notin_singleton_1 in n0. contradiction.
               **** reflexivity.
Qed.

(* begin hide *)

Lemma m_subst_sub: forall t1 t2 u x y, [x := u](n_sub t1 y t2)  =a
       if (x == y) then (n_sub t1 y ([x := u]t2))
       else let (z,_) := atom_fresh (fv_nom u `union` fv_nom (n_sub t1 y t2) `union` {{x}}) in
       n_sub ([x := u](swap y z t1)) z ([x := u]t2).
Proof.
  intros. destruct (x == y).
  - subst. unfold m_subst. rewrite subst_rec_fun_equation. rewrite eq_dec_refl. apply aeq_refl.
  - unfold m_subst. rewrite subst_rec_fun_equation. destruct (x == y).
    + simpl. contradiction.
    + simpl. destruct (atom_fresh (union (fv_nom u) (union (fv_nom (n_sub t1 y t2)) (singleton x)))). apply aeq_refl.
Qed.

(* end hide *)

(** The following lemmas state, respectively, what hapens when the variable in the meta-substitution is equal or different from the one in the explicit substitution. When it is equal, the meta-substitution is irrelevant on [t1], but it is applied to [e2]. When they are different, we take a new variable that does not occur freely in the substituted term in the meta-substitution nor in the substitution and is not the variable in the meta-substitution, and the explicit substitution of this new variable using the meta-substitution of the swap of the former variable in the meta-substitution in [e11] and the application of the original meta_substitution in [e12] is alpha-equivalent to the original meta-substitution of the explicit substitution. **)
(** The proofs were made using the definition of the meta-substitution, each case being respectively each one in the definition.**)

Lemma m_subst_sub_eq : forall u x t1 t2, [x := u](n_sub t1 x t2) = n_sub t1 x ([x := u] t2).
Proof.
  intros u x t1 t2. unfold m_subst. rewrite subst_rec_fun_equation. rewrite eq_dec_refl. reflexivity.
Qed.

Lemma m_subst_sub_neq : forall t1 t2 u x y z, x <> y -> z `notin` fv_nom u `union` fv_nom (n_sub t1 y t2) `union` {{x}} -> [x := u](n_sub t1 y t2) =a n_sub ([x := u](swap y z t1)) z ([x := u]t2).
Proof.
  intros t1 t2 u x y z H1 H2. unfold m_subst. pose proof m_subst_sub as Hsub. specialize (Hsub t1 t2 u x y).
  destruct (x == y) in Hsub. 
  - contradiction.
  - destruct (atom_fresh (union (fv_nom u) (union (fv_nom (n_sub t1 y t2)) (singleton x)))) in Hsub.
    rewrite Hsub. destruct (x0 == z).
    + subst. unfold m_subst. apply aeq_refl.
    + apply aeq_sub_diff.
      * unfold m_subst. apply aeq_refl.
      * assumption.
      * pose proof fv_nom_remove as H. unfold m_subst in *. apply H.
        ** apply notin_union_1 in n0. assumption.
        ** apply notin_remove_2. destruct (x0 == y).
           *** subst. apply fv_nom_swap. apply notin_union_2 in H2. apply notin_union_1 in H2. simpl in H2.
               apply not_eq_sym in n1. apply notin_union_1 in H2. apply diff_remove_2 in H2; assumption.
           *** apply fv_nom_remove_swap. 
               **** assumption.
               **** assumption.
               **** apply notin_union_2 in n0. apply notin_union_1 in n0. simpl in *. apply notin_union_1 in n0. apply diff_remove_2 in n0; assumption.
      * rewrite swap_subst_rec_fun. replace (swap_var z x0 x) with x.
        ** apply aeq_m_subst_eq.
           *** apply aeq_sym. rewrite (swap_symmetric _ z x0). rewrite (swap_symmetric _ y z). rewrite (swap_symmetric _ y x0). case (x0 == y).
               **** intro Heq. subst. rewrite swap_id. rewrite (swap_symmetric _ y z). rewrite swap_involutive. apply aeq_refl.
               **** intro Hneq. case (z == y).
                    ***** intro Heq. subst. rewrite swap_id. apply aeq_refl.
                    ***** intro Hneq'. apply aeq_swap_swap.
                    ****** apply notin_union_2 in n0. apply notin_union_1 in n0. simpl in n0. apply notin_union_1 in n0. apply notin_remove_1 in n0. destruct n0.
                    ******* symmetry in H. contradiction.
                    *******  assumption.
                    ****** apply notin_union_2 in H2. apply notin_union_1 in H2. simpl in H2. apply notin_union_1 in H2. apply notin_remove_1 in H2. destruct H2.
                    ******* symmetry in H. contradiction.
                    ******* assumption.
           *** apply aeq_sym. apply swap_reduction.
               **** apply notin_union_1 in H2. assumption.
               **** apply notin_union_1 in n0. assumption.
        ** apply eq_sym. unfold swap_var. destruct (x == z).
           *** subst. repeat apply notin_union_2 in H2. apply notin_singleton_1 in H2. contradiction.
           *** destruct (x == x0). 
               **** subst. repeat apply notin_union_2 in n0. apply notin_singleton_1 in n0. contradiction.
               **** reflexivity.
Qed.
 
(** * The substitution lemma for the metasubstitution *)

(**
   In the pure $\lambda$-calculus, the substitution lemma is probably the first non trivial property. In our framework, we have defined two different substitution operation, namely, the metasubstitution denoted by [[x:=u]t] and the explicit substitution that has [n_sub] as a constructor. In what follows, we present the main steps of our proof of the substitution lemma for the metasubstitution operation: 
 *)


Lemma m_subst_lemma: forall e1 e2 x e3 y, x <> y -> x `notin` (fv_nom e3) -> ([y := e3]([x := e2]e1)) =a ([x := ([y := e3]e2)]([y := e3]e1)).
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
    + rewrite m_subst_abs_neq.
      unfold m_subst in *. specialize (IHn e3 y'). admit. 
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

  (** The variable case was proved using the auxiliary lemmas on the equality and inequality of the meta-substitution applied to variables. It was also necessary to compare the variable in the meta-substitution and the variable one in each case of this proof.**)

  - (* variable case: *) intros e2 x' e3 y Hneq Hfv. case (x == x').
    + intro Heq. subst. rewrite m_subst_var_eq. case (x' == y).
      * intro Heq. subst. contradiction.
      * intro Hneq'. rewrite m_subst_var_neq.
        ** rewrite m_subst_var_eq. apply aeq_refl.
        ** assumption.
    + intro Hneq'. case (x == y).
      * intro Heq. subst. case (x' == y).
        ** intro Heq. subst. contradiction.
        ** intro Hneq''. rewrite m_subst_var_neq.
           *** rewrite m_subst_var_eq. rewrite m_subst_notin.
               **** apply aeq_refl.
               **** assumption.
           *** assumption.
      * intro Hneq''. rewrite m_subst_var_neq.
        ** rewrite m_subst_var_neq.
           *** rewrite m_subst_var_neq.
               **** apply aeq_refl.
               **** assumption.
           *** assumption.
        ** assumption.

      (** In the abstraction case, we used a similar approach, comparing the variable in the meta substitution and the one in the abstraction. When usion the using the auxiliary lemmas on the equality and inequality of the meta-substitution applied to abstractions, it was necessary to create new variables in each use of the inequality. This is due to the atempt of removing the abstraction from inside the meta-substitution.**)

  - intros e2 x e3 y Hxy Hfv. case (z == x).
    + intro Heq. subst. rewrite m_subst_abs_eq. assert (Haeq : ([x := [y := e3] e2] ([y := e3] n_abs x e1)) =a ([y := e3] n_abs x e1)).
      * apply m_subst_notin. apply fv_nom_remove.
        ** assumption.
        ** apply notin_remove_2. simpl. apply notin_remove_3. reflexivity.
      * apply aeq_sym. auto.
    + intro Hneq. destruct (y == z).
      * subst. rewrite m_subst_abs_eq. pose proof m_subst_abs_neq as Habs. pick fresh w for (union (fv_nom e3) (union (fv_nom e2) (union (fv_nom (n_abs z e1)) (singleton x)))). specialize (Habs e1 e2 x z w).
        apply aeq_trans with ([z := e3] n_abs w ([x := e2] swap z w e1)). apply aeq_m_subst_out.
        ** apply Habs.
           *** assumption.
           *** apply notin_union_2 in Fr. assumption.
        ** destruct (z == w).
           *** subst. rewrite m_subst_abs_eq. rewrite swap_id. pose proof m_subst_abs_neq as Habs'. specialize (Habs' e1 ([w := e3] e2) x w w).
               rewrite Habs'. apply aeq_abs_same. rewrite swap_id. apply aeq_sym. apply aeq_m_subst_in. apply m_subst_notin. apply notin_union_2 in Fr. apply notin_union_1 in Fr. assumption.
               assumption. apply notin_union. apply fv_nom_remove. apply notin_union_1 in Fr. assumption. apply notin_remove_3. reflexivity. apply notin_union_2 in Fr. 
               apply notin_union_2 in Fr. assumption.
           *** pose proof m_subst_abs_neq as Habs'. specialize (Habs' e1 ([z := e3] e2) x z w). pick fresh w' for (union (fv_nom e3) (union (fv_nom e2) (union (fv_nom (n_abs z e1)) (singleton x)))).
               destruct (w == w'). 
               **** subst. rewrite Habs'. pose proof m_subst_abs_neq as Habs''. specialize (Habs'' ([x := e2] swap z w' e1) e3 z w' w'). rewrite Habs''.
                    apply aeq_abs_same. rewrite swap_id. rewrite H. apply aeq_m_subst_out. apply m_subst_notin. apply fv_nom_swap. apply notin_union_2 in Fr. apply notin_union_2 in Fr.
                    apply notin_union_1 in Fr. simpl in *. apply diff_remove_2 in Fr. assumption. apply not_eq_sym. assumption. reflexivity. assumption. assumption.
                    assumption. apply notin_union. apply notin_union_1 in Fr. assumption. apply notin_union. simpl. apply notin_remove_3. reflexivity. apply notin_singleton_2. assumption.
                    assumption. apply notin_union. apply fv_nom_remove. apply notin_union_1 in Fr0. assumption. apply notin_remove_2. apply notin_union_2 in Fr0. apply notin_union_1 in Fr0.
                    assumption. apply notin_union_2 in Fr0. apply notin_union_2 in Fr0. assumption.
               **** rewrite Habs'. pose proof m_subst_abs_neq as Habs''. specialize (Habs'' ([x := e2] swap z w e1) e3 z w w). rewrite Habs''.
                    apply aeq_abs_same. rewrite swap_id. rewrite H. apply aeq_m_subst_out. apply m_subst_notin. apply fv_nom_swap. apply notin_union_2 in Fr. apply notin_union_2 in Fr.
                    apply notin_union_1 in Fr. simpl in *. apply diff_remove_2 in Fr. assumption. apply not_eq_sym. assumption. reflexivity. assumption. assumption.
                    assumption. apply notin_union. apply notin_union_1 in Fr. assumption. apply notin_union. simpl. apply notin_remove_3. reflexivity. apply notin_singleton_2. assumption.
                    assumption. apply notin_union. apply fv_nom_remove. apply notin_union_1 in Fr. assumption. apply notin_remove_2. apply notin_union_2 in Fr. apply notin_union_1 in Fr.
                    assumption. apply notin_union_2 in Fr. apply notin_union_2 in Fr. assumption.
      * pose proof m_subst_abs_neq as Habs. pick fresh w for (union (fv_nom e3) (union (fv_nom e2) (union (fv_nom (n_abs z e1)) (union (singleton x) (singleton y))))). specialize (Habs e1 e2 x z w).
        apply aeq_trans with ([y := e3] n_abs w ([x := e2] swap z w e1)).
        ** apply aeq_m_subst_out. apply Habs.
           *** apply not_eq_sym. assumption.
           *** apply notin_union. 
               **** apply notin_union_2 in Fr. apply notin_union_1 in Fr. assumption.
               **** apply notin_union.
                    ***** apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_1 in Fr. assumption.
                    ***** apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_1 in Fr. assumption.
        ** pose proof m_subst_abs_neq as Habs'. specialize (Habs' e1 e3 y z w). apply aeq_trans with ([x := [y := e3] e2] n_abs w ([y := e3] swap z w e1)).
           *** pick fresh w' for (union (fv_nom e3) (union (fv_nom e2) (union (fv_nom (n_abs y e1)) (union (singleton x) (union (singleton w) (singleton y)))))). destruct (z == w'). 
               **** subst. pose proof m_subst_abs_neq as Habs''. specialize (Habs'' ([x := e2] swap w' w e1) e3 y w w'). rewrite Habs''. 
                    ***** pose proof m_subst_abs_neq as Habs'''. specialize (Habs''' ([y := e3] swap w' w e1) ([y := e3] e2) x w w'). rewrite Habs'''.
                    ****** apply aeq_abs_same. unfold m_subst in *. pose proof swap_subst_rec_fun as Hsubst. specialize (Hsubst w w' x (swap w' w e1) e2). apply aeq_trans with (subst_rec_fun (subst_rec_fun (swap w' w e1) e2 x) e3 y).
                    ******* pose proof aeq_m_subst_out as Hout. unfold m_subst in *. apply Hout. rewrite Hsubst. unfold swap_var. destruct (x == w).
                    ******** subst. apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_1 in Fr. apply notin_singleton_1 in Fr. contradiction.
                    ******** destruct (x == w').
                    ********* subst. apply notin_union_2 in Fr0. apply notin_union_2 in Fr0. apply notin_union_2 in Fr0. apply notin_union_1 in Fr0. apply notin_singleton_1 in Fr0. contradiction.
                    ********* pose proof aeq_m_subst_eq as Heq. unfold m_subst in *. apply Heq. 
                    ********** rewrite (swap_symmetric _ w w'). rewrite (swap_involutive _ w' w). apply aeq_sym. apply swap_reduction.
                    *********** pose proof Fr0 as H0. apply notin_union_2 in Fr0. apply notin_union_2 in Fr0. apply notin_union_1 in Fr0. simpl in Fr0. apply diff_remove_2 in Fr0.
                    ************ assumption. 
                    ************ apply not_eq_sym. repeat apply notin_union_2 in H0. apply notin_singleton_1 in H0. assumption.
                    *********** apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_1 in Fr. simpl in Fr. apply diff_remove_2 in Fr.
                    ************ assumption. 
                    ************ apply not_eq_sym. apply notin_union_2 in Fr0. apply notin_union_2 in Fr0. apply notin_union_2 in Fr0. apply notin_union_2 in Fr0. apply notin_union_1 in Fr0. apply notin_singleton_1 in Fr0. apply not_eq_sym. assumption.
                    ********** apply swap_reduction.
                    *********** apply notin_union_2 in Fr. apply notin_union_1 in Fr. assumption.
                    *********** apply notin_union_2 in Fr0. apply notin_union_1 in Fr0. assumption.
                    ******* pose proof swap_subst_rec_fun as Hsubst'. specialize (Hsubst' w w' y (swap w' w e1) e3). apply aeq_trans with (subst_rec_fun (subst_rec_fun (swap w' w e1) e3 y) (subst_rec_fun e2 e3 y) x).
                    ******** apply H.
                    ********* reflexivity.
                    ********* assumption.
                    ********* assumption.
                    ******** pose proof aeq_m_subst_out as Hout. unfold m_subst in *. apply Hout. rewrite Hsubst'. unfold swap_var. destruct (y == w).
                    ********* subst. repeat apply notin_union_2 in Fr. apply notin_singleton_1 in Fr. contradiction.
                    ********* destruct (y == w').
                    ********** subst. repeat apply notin_union_2 in Fr. apply notin_singleton_1 in Fr. contradiction.
                    ********** pose proof aeq_m_subst_eq as Heq. unfold m_subst in *. apply Heq.
                    *********** rewrite (swap_symmetric _ w w'). rewrite swap_involutive. apply swap_reduction.
                    ************ pose proof Fr0 as H0. apply notin_union_2 in Fr0. apply notin_union_2 in Fr0. apply notin_union_1 in Fr0. simpl in Fr0. apply diff_remove_2 in Fr0.
                    ************* assumption. 
                    ************* apply not_eq_sym. repeat apply notin_union_2 in H0. apply notin_singleton_1 in H0. assumption.
                    ************ apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_1 in Fr. simpl in Fr. apply diff_remove_2 in Fr.
                    ************* assumption. 
                    ************* apply not_eq_sym. apply notin_union_2 in Fr0. apply notin_union_2 in Fr0. apply notin_union_2 in Fr0. apply notin_union_2 in Fr0. apply notin_union_1 in Fr0. apply notin_singleton_1 in Fr0. apply not_eq_sym. assumption.
                    *********** apply aeq_sym. apply swap_reduction.
                    ************ apply notin_union_1 in Fr. assumption.
                    ************ apply notin_union_1 in Fr0. assumption.
                    ****** apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_1 in Fr. apply notin_singleton_1 in Fr. assumption.
                    ****** apply notin_union.
                    ******* apply fv_nom_remove.
                    ******** apply notin_union_1 in Fr0. assumption.
                    ******** apply notin_remove_2. apply notin_union_2 in Fr0. apply notin_union_1 in Fr0. assumption.
                    ******* apply notin_union.
                    ******** simpl. apply notin_remove_2. apply fv_nom_remove. 
                    ********* apply notin_union_1 in Fr0. assumption.
                    ********* apply notin_remove_2. apply fv_nom_swap. apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_1 in Fr. simpl in Fr. apply diff_remove_2 in Fr.
                    ********** assumption. 
                    ********** apply not_eq_sym. apply notin_union_2 in Fr0. apply notin_union_2 in Fr0. apply notin_union_2 in Fr0. apply notin_union_2 in Fr0. apply notin_union_1 in Fr0. apply notin_singleton_1 in Fr0. apply not_eq_sym. assumption.
                    ******** apply notin_union_2 in Fr0. apply notin_union_2 in Fr0. apply notin_union_2 in Fr0. apply notin_union_1 in Fr0. assumption.
                    ***** repeat apply notin_union_2 in Fr. apply notin_singleton_1 in Fr. assumption.
                    ***** apply notin_union.
                    ****** apply notin_union_1 in Fr0. assumption. 
                    ****** apply notin_union. 
                    ******* simpl. apply notin_remove_2. apply fv_nom_remove. 
                    ******** apply notin_union_2 in Fr0. apply notin_union_1 in Fr0. assumption.
                    ******** apply notin_remove_2. apply fv_nom_swap. apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_1 in Fr. simpl in Fr. apply diff_remove_2 in Fr.
                    ********** assumption. 
                    ********** apply not_eq_sym. apply notin_union_2 in Fr0. apply notin_union_2 in Fr0. apply notin_union_2 in Fr0. apply notin_union_2 in Fr0. apply notin_union_1 in Fr0. apply notin_singleton_1 in Fr0. apply not_eq_sym. assumption.
                    ******* repeat apply notin_union_2 in Fr0. assumption.
               **** destruct (w == z).
                    ***** subst. pose proof m_subst_abs_neq as Habs''. specialize (Habs'' ([x := e2] swap z z e1) e3 y z w'). pose proof m_subst_abs_neq as Habs'''. specialize (Habs''' ([y := e3] swap z z e1) ([y := e3] e2) x z w'). rewrite Habs''. 
                    ****** rewrite Habs'''.
                    ******* apply aeq_abs_same. unfold m_subst in *. pose proof swap_subst_rec_fun as Hswap. specialize (Hswap z w' x (swap z z e1) e2). pose proof swap_subst_rec_fun as Hswap'. specialize (Hswap' z w' y (swap z z e1) e3).
                            apply aeq_trans with (subst_rec_fun (subst_rec_fun (swap w' z e1) e2 x) e3 y).
                    ******** pose proof aeq_m_subst_out as Hout. unfold m_subst in *. apply Hout. rewrite Hswap. unfold swap_var. destruct (x == z).
                    ********* subst. contradiction.
                    ********* destruct (x == w'). 
                    ********** subst. apply notin_union_2 in Fr0. apply notin_union_2 in Fr0. apply notin_union_2 in Fr0. apply notin_union_1 in Fr0. apply notin_singleton_1 in Fr0. contradiction.
                    ********** pose proof aeq_m_subst_eq as Heq. unfold m_subst in *. apply Heq.
                    *********** rewrite swap_id. rewrite (swap_symmetric _ z w'). apply aeq_refl.
                    *********** apply swap_reduction.
                    ************ apply notin_union_2 in Fr. apply notin_union_1 in Fr. assumption.
                    ************ apply notin_union_2 in Fr0. apply notin_union_1 in Fr0. assumption.
                    ******** apply aeq_trans with (subst_rec_fun (subst_rec_fun (swap w' z e1) e3 y) (subst_rec_fun e2 e3 y) x).
                    ********* apply H.
                    ********** reflexivity.
                    ********** assumption.
                    ********** assumption.
                    ********* pose proof aeq_m_subst_eq as Heq. unfold m_subst in *. apply Heq.
                    ********** rewrite Hswap'. unfold swap_var. destruct (y == z).
                    *********** subst. repeat apply notin_union_2 in Fr. apply notin_singleton_1 in Fr. contradiction.
                    *********** destruct (y == w').
                    ************ subst. repeat apply notin_union_2 in Fr0. apply notin_singleton_1 in Fr0. contradiction.
                    ************ apply Heq. 
                    ************* rewrite swap_id. rewrite (swap_symmetric _ w' z). reflexivity.
                    ************* apply aeq_sym. apply swap_reduction. 
                    ************** apply notin_union_1 in Fr. assumption.
                    ************** apply notin_union_1 in Fr0. assumption.
                    ********** apply aeq_refl.
                    ******* apply not_eq_sym. assumption.
                    ******* apply notin_union.
                    ******** apply fv_nom_remove.
                    ********* apply notin_union_1 in Fr0. assumption.
                    ********* apply notin_remove_2. apply notin_union_2 in Fr0. apply notin_union_1 in Fr0. assumption.
                    ******** apply notin_union.
                    ********* simpl. rewrite swap_id. apply notin_remove_2. apply fv_nom_remove.
                    ********** apply notin_union_1 in Fr0. assumption.
                    ********** pose proof Fr0 as H1. apply notin_remove_2. apply notin_union_2 in Fr0. apply notin_union_2 in Fr0. apply notin_union_1 in Fr0. simpl in Fr0. apply diff_remove_2 in Fr0. 
                    *********** assumption.
                    *********** repeat apply notin_union_2 in H1. apply notin_singleton_1 in H1. apply not_eq_sym. assumption.
                    ********* apply notin_union_2 in Fr0. apply notin_union_2 in Fr0. apply notin_union_2 in Fr0. apply notin_union_1 in Fr0. assumption.
                    ****** assumption.
                    ****** apply notin_union.
                    ******* apply notin_union_1 in Fr0. assumption.
                    ******* apply notin_union. 
                    ******** apply notin_remove_2. rewrite swap_id. apply fv_nom_remove.
                    ********* apply notin_union_2 in Fr0. apply notin_union_1 in Fr0. assumption.
                    ********* pose proof Fr0 as H1. apply notin_remove_2. apply notin_union_2 in Fr0. apply notin_union_2 in Fr0. apply notin_union_1 in Fr0. simpl in Fr0. apply diff_remove_2 in Fr0.
                    ********** assumption.
                    ********** repeat apply notin_union_2 in H1. apply notin_singleton_1 in H1. apply not_eq_sym. assumption.
                    ******** repeat apply notin_union_2 in Fr0. assumption.
                    ***** pose proof m_subst_abs_neq as Habs''. specialize (Habs'' ([x := e2] swap z w e1) e3 y w w'). rewrite Habs''.
                    ****** pose proof m_subst_abs_neq as Habs'''. specialize (Habs''' ([y := e3] swap z w e1) ([y := e3] e2) x w w'). rewrite Habs'''.
                    ******* apply aeq_abs_same. unfold m_subst. pose proof swap_subst_rec_fun as Hswap. specialize (Hswap w w' x (swap z w e1) e2). apply aeq_trans with (subst_rec_fun (subst_rec_fun (swap w' z e1) e2 x) e3 y).
                    ******** pose proof aeq_m_subst_out as Hout. unfold m_subst in *. apply Hout. rewrite Hswap. unfold swap_var. destruct (x == w).
                    ********* subst. apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_1 in Fr. apply notin_singleton_1 in Fr. contradiction.
                    ********* destruct (x == w').
                    ********** subst. apply notin_union_2 in Fr0. apply notin_union_2 in Fr0. apply notin_union_2 in Fr0. apply notin_union_1 in Fr0. apply notin_singleton_1 in Fr0. contradiction.
                    ********** pose proof aeq_m_subst_eq as Heq. unfold m_subst in *. rewrite (swap_symmetric _ w w'). rewrite (swap_symmetric _ z w). apply Heq. 
                    *********** apply aeq_swap_swap.
                    ************ pose proof Fr0 as H1. apply notin_union_2 in Fr0. apply notin_union_2 in Fr0. apply notin_union_1 in Fr0. simpl in Fr0. apply diff_remove_2 in Fr0.
                    ************* assumption. 
                    ************* apply not_eq_sym. repeat apply notin_union_2 in H1. apply notin_singleton_1 in H1. assumption.
                    ************ pose proof Fr as H1. apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_1 in Fr. simpl in Fr. apply diff_remove_2 in Fr.
                    ************* assumption. 
                    ************* apply not_eq_sym. apply notin_union_2 in Fr0. apply notin_union_2 in Fr0. apply notin_union_2 in Fr0. apply notin_union_2 in Fr0. apply notin_union_1 in Fr0. apply notin_singleton_1 in Fr0. apply not_eq_sym. assumption.
                    *********** apply swap_reduction.
                    ************ apply notin_union_2 in Fr. apply notin_union_1 in Fr. assumption.
                    ************ apply notin_union_2 in Fr0. apply notin_union_1 in Fr0. assumption.
                    ******** pose proof swap_subst_rec_fun as Hswap'. specialize (Hswap' w w' y (swap w z e1) e3). apply aeq_trans with (subst_rec_fun (subst_rec_fun (swap w' z e1) e3 y) (subst_rec_fun e2 e3 y) x). 
                    ********* unfold m_subst. apply H.
                    ********** reflexivity.
                    ********** assumption. 
                    ********** assumption.
                    ********* pose proof aeq_m_subst_eq as Hsubst. unfold m_subst in *. apply Hsubst. rewrite (swap_symmetric _ z w). rewrite Hswap'.
                    ********** unfold swap_var. destruct (y == w).
                    *********** subst. repeat apply notin_union_2 in Fr. apply notin_singleton_1 in Fr. contradiction. 
                    *********** destruct (y == w'). 
                    ************ subst. repeat apply notin_union_2 in Fr0. apply notin_singleton_1 in Fr0. contradiction.
                    ************ apply Hsubst. 
                    ************* apply aeq_sym. rewrite (swap_symmetric _ w w'). apply aeq_swap_swap.
                    ************** apply notin_union_2 in Fr0. apply notin_union_2 in Fr0. apply notin_union_1 in Fr0. simpl in Fr0. apply diff_remove_2 in Fr0.
                    *************** assumption.
                    *************** apply not_eq_sym. assumption.
                    ************** apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_1 in Fr. simpl in Fr. apply diff_remove_2 in Fr.
                    *************** assumption.
                    *************** assumption.
                    ************* apply aeq_sym. apply swap_reduction.
                    ************** apply notin_union_1 in Fr. assumption.
                    ************** apply notin_union_1 in Fr0. assumption.
                    ********** apply aeq_refl.
                    ******* apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_1 in Fr. apply notin_singleton_1 in Fr. assumption.
                    ******* apply notin_union.
                    ******** apply fv_nom_remove. 
                    ********* apply notin_union_1 in Fr0. assumption.
                    ********* apply notin_remove_2. apply notin_union_2 in Fr0. apply notin_union_1 in Fr0. assumption.
                    ******** apply notin_union. simpl. apply notin_remove_2. apply fv_nom_remove. 
                    ********* apply notin_union_1 in Fr0. assumption.
                    ********* apply notin_remove_2. apply fv_nom_remove_swap.
                    ********** apply notin_union_2 in Fr0. apply notin_union_2 in Fr0. apply notin_union_2 in Fr0. apply notin_union_2 in Fr0. apply notin_union_1 in Fr0. apply notin_singleton_1 in Fr0. apply not_eq_sym. assumption.
                    ********** apply not_eq_sym. assumption.
                    ********** pose proof Fr0 as H1. apply notin_union_2 in Fr0. apply notin_union_2 in Fr0. apply notin_union_1 in Fr0. simpl in Fr0. apply diff_remove_2 in Fr0.
                    *********** assumption.
                    *********** repeat apply notin_union_2 in H1. apply notin_singleton_1 in H1. apply not_eq_sym. assumption.
                    ********* apply notin_union_2 in Fr0. apply notin_union_2 in Fr0. apply notin_union_2 in Fr0. apply notin_union_1 in Fr0. assumption.
               ****** repeat apply notin_union_2 in Fr. apply notin_singleton_1 in Fr. assumption.
               ****** apply notin_union. 
                      ******* apply notin_union_1 in Fr0. assumption.
                      ******* apply notin_union. 
                      ******** simpl. apply notin_remove_2. apply fv_nom_remove.
                      ********* apply notin_union_2 in Fr0. apply notin_union_1 in Fr0. assumption.
                      ********* apply notin_remove_2. apply fv_nom_remove_swap. 
                      ********** apply notin_union_2 in Fr0. apply notin_union_2 in Fr0. apply notin_union_2 in Fr0. apply notin_union_2 in Fr0. apply notin_union_1 in Fr0. apply notin_singleton_1 in Fr0. apply not_eq_sym. assumption.
                      ********** apply not_eq_sym. assumption.
                      ********** pose proof Fr0 as H1. apply notin_union_2 in Fr0. apply notin_union_2 in Fr0. apply notin_union_1 in Fr0. simpl in Fr0. apply diff_remove_2 in Fr0.
                      *********** assumption.
                      *********** repeat apply notin_union_2 in H1. apply notin_singleton_1 in H1. apply not_eq_sym. assumption.
                      ******** repeat apply notin_union_2 in Fr0. assumption.
           *** apply aeq_m_subst_out. apply aeq_sym. apply Habs'.
               **** assumption.
               **** apply notin_union.
               ***** apply notin_union_1 in Fr. assumption.
               ***** apply notin_union.
               ****** apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_1 in Fr. assumption.
               ****** repeat apply notin_union_2 in Fr. assumption.  

    (** The case of the application is quite simple to solve. It consisted of applying the auxiliary lemma of removing the application from inside the meta-substitution. **)

  - intros e2 x e3 y Hneq Hfv. repeat rewrite m_subst_app. pose proof aeq_app as H. specialize (H ([y := e3] ([x := e2] e1_1)) ([y := e3] ([x := e2] e1_2)) ([x := [y := e3] e2] ([y := e3] e1_1)) ([x := [y := e3] e2] ([y := e3] e1_2))). rewrite H. 
    + apply aeq_refl.
    + apply IHe1_1; assumption.
    + apply IHe1_2; assumption.

      (** In the explicit substitution case, we used the same approach used in the abstraction for the left side and the same as the application for the right side of the substitution. It consisted of comparing the variable in the meta substitution and the one in the substitution. We used the auxiliary lemmas on the equality and inequality of the meta-substitution applied to explicit substitutions and it was necessary to create new variables in each use of the inequality. This is due to the atempt of removing the explicit substitution from inside the meta-substitution. When tis removal was made, the proof consisted in proving a similar case for the abstraction in the left side of the explicit substitution and the one similar to the application was used for the right part of it.**)

  - intros e2 x e3 y Hneq Hfv. case (z == x).
    + intro Heq. subst. rewrite m_subst_sub_eq. assert (Haeq: ([y := e3] n_sub e1_1 x ([x := e2] e1_2)) =a ([x := [y := e3] e2] ([y := e3] n_sub e1_1 x e1_2))).
      * pose proof m_subst_sub_neq as Hsubneq. pick fresh w for (union (fv_nom (n_sub e1_1 x e1_2)) (union (fv_nom e2) (union (fv_nom e3) (union (singleton x) (singleton y))))).
        specialize (Hsubneq e1_1 ([x := e2] e1_2) e3 y x w). pose proof Hneq as H'. apply not_eq_sym in H'. apply Hsubneq in H'. rewrite H'.
        ** pose proof m_subst_sub_neq as Hsubneq'. pick fresh w' for (union (fv_nom (n_sub e1_1 x e1_2)) (union (fv_nom e2) (union (fv_nom e3) (union (singleton x) (union (singleton w) (singleton y)))))).
           specialize (Hsubneq' e1_1 e1_2 e3 y x w). pose proof Hneq as H''. apply not_eq_sym in H''. apply Hsubneq' in H''. 
           *** apply aeq_trans with ([x := [y := e3] e2] (n_sub ([y := e3] swap x w e1_1) w ([y := e3] e1_2))).
               **** pose proof m_subst_sub_neq as Hsubneq''. specialize (Hsubneq'' ([y := e3] swap x w e1_1) ([y := e3] e1_2) ([y := e3] e2) x w w').
                    apply aeq_trans with (n_sub ([x := [y := e3] e2] swap w w' ([y := e3] swap x w e1_1)) w' ([x := [y := e3] e2] ([y := e3] e1_2))). 
                    ***** apply aeq_sub_diff.
                          ****** apply IHe1_1.
                                 ******* assumption.
                                 ******* assumption.
                          ****** apply notin_union_2 in Fr0. apply notin_union_2 in Fr0. apply notin_union_2 in Fr0. apply notin_union_2 in Fr0. apply notin_union_1 in Fr0.  
                                 apply notin_singleton_1 in Fr0. assumption.
                          ****** apply fv_nom_remove.
                                 ******* apply fv_nom_remove.
                                         ******** apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_1 in Fr. assumption.
                                         ******** apply notin_remove_2. apply notin_union_2 in Fr. apply notin_union_1 in Fr. assumption.
                                 ******* apply notin_remove_2. apply fv_nom_swap. apply fv_nom_remove.
                                         ******** apply notin_union_2 in Fr0. apply notin_union_2 in Fr0. apply notin_union_1 in Fr0. assumption.
                                         ******** apply notin_remove_2. apply fv_nom_remove_swap. 
                                                  ********* apply notin_union_2 in Fr0. apply notin_union_2 in Fr0. apply notin_union_2 in Fr0. apply notin_union_2 in Fr0. 
                                                            apply notin_union_1 in Fr0. apply notin_singleton_1 in Fr0. apply not_eq_sym. assumption.
                                                  ********* apply notin_union_2 in Fr0. apply notin_union_2 in Fr0. apply notin_union_2 in Fr0. apply notin_union_1 in Fr0. apply notin_singleton_1 in Fr0. apply not_eq_sym. assumption.
                                                  ********* pose proof Fr0 as H1. apply notin_union_1 in Fr0. simpl in Fr0. apply notin_union_1 in Fr0. apply diff_remove_2 in Fr0.
                                                  ********** assumption.
                                                  ********** apply notin_union_2 in H1.  apply notin_union_2 in H1.  apply notin_union_2 in H1.  apply notin_union_1 in H1. apply notin_singleton_1 in H1. apply not_eq_sym. assumption.
                          ****** pose proof swap_subst_rec_fun as Hswap. specialize (Hswap w' w x (swap w w' ([y := e3] swap x w e1_1)) ([y := e3] e2)).
                                 rewrite Hswap. pose proof swap_involutive as Hswap'. specialize (Hswap' ([y := e3] swap x w e1_1) w' w). pose proof swap_symmetric as Hswap''. 
                                 specialize (Hswap'' ([y := e3] swap x w e1_1) w' w). rewrite Hswap'' in Hswap'. rewrite Hswap'. unfold swap_var. destruct (x == w').
                                 ******* subst. unfold m_subst. pose proof swap_subst_rec_fun as Hswap'''. specialize (Hswap''' w' w y e2 e3). 
                                         apply aeq_trans with (subst_rec_fun (subst_rec_fun (swap w' w e1_1) e3 y) (subst_rec_fun (swap w' w e2) (swap w' w e3) (swap_var w' w y)) w).
                                         unfold swap_var. destruct (y == w').
                                         ******** subst. contradiction.
                                         ******** apply aeq_sym. apply m_subst_notin. pose proof fv_nom_remove as H1. unfold m_subst in H1. apply H1.
                                                  ********* apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_1 in Fr. assumption.
                                                  ********* apply notin_union_2 in Fr0. apply notin_union_2 in Fr0. apply notin_union_2 in Fr0. apply notin_union_1 in Fr0. apply notin_singleton_1 in Fr0. contradiction.
                                         ******** pose proof aeq_m_subst_in as H0. unfold m_subst in H0. apply H0. apply aeq_sym. apply Hswap'''.
                                 ******* destruct (x == w).
                                         ******** subst. rewrite swap_id. apply aeq_sym. pose proof m_subst_notin as H1. unfold m_subst in H1. rewrite H1. 
                                                  ********* apply aeq_refl.
                                                  ********* apply fv_nom_remove.
                                                            *********** apply notin_union_2 in Fr0. apply notin_union_2 in Fr0. apply notin_union_1 in Fr0. assumption.   
                                                            *********** apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_1 in Fr. apply notin_singleton_1 in Fr. contradiction.
                                         ******** apply aeq_sym. pose proof m_subst_notin as H1. unfold m_subst in H1. rewrite H1. 
                                                  ********* apply aeq_refl.
                                                  ********* apply fv_nom_remove.
                                                            *********** assumption.
                                                            *********** apply notin_remove_2. apply fv_nom_swap. apply notin_union_1 in Fr. simpl in Fr. simpl in Fr. apply notin_union_1 in Fr. apply diff_remove_2 in Fr.
                                                            ************ assumption.
                                                            ************ apply not_eq_sym. assumption.
                    *****  rewrite Hsubneq''.
                           ****** apply aeq_refl. 
                           ****** apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_1 in Fr. apply notin_singleton_1 in Fr. assumption.
                           ****** apply notin_union.
                                  ******* apply fv_nom_remove.
                                  ******** apply notin_union_2 in Fr0. apply notin_union_2 in Fr0. apply notin_union_1 in Fr0. assumption.
                                  ******** apply notin_remove_2. apply notin_union_2 in Fr0. apply notin_union_1 in Fr0. assumption.
                                  ******* apply notin_union. simpl.
                                  ******** apply notin_union.
                                  ********* apply notin_remove_2. apply fv_nom_remove. 
                                  ********** apply notin_union_2 in Fr0. apply notin_union_2 in Fr0. apply notin_union_1 in Fr0. assumption.                       
                                  ********** apply notin_remove_2. apply fv_nom_remove_swap. 
                                  *********** apply notin_union_2 in Fr0. apply notin_union_2 in Fr0. apply notin_union_2 in Fr0. apply notin_union_2 in Fr0. apply notin_union_1 in Fr0. apply notin_singleton_1 in Fr0. apply not_eq_sym. assumption.
                                  *********** apply notin_union_2 in Fr0. apply notin_union_2 in Fr0. apply notin_union_2 in Fr0. apply notin_union_1 in Fr0. apply notin_singleton_1 in Fr0. apply not_eq_sym. assumption.
                                  *********** pose proof Fr0 as H1. apply notin_union_1 in Fr0. simpl in Fr0. apply notin_union_1 in Fr0. apply diff_remove_2 in Fr0.
                                  ************ assumption.
                                  ************ apply notin_union_2 in H1. apply notin_union_2 in H1. apply notin_union_2 in H1. apply notin_union_1 in H1. apply notin_singleton_1 in H1. apply not_eq_sym. assumption.
                                  ********* apply fv_nom_remove. 
                                  ********** apply notin_union_2 in Fr0. apply notin_union_2 in Fr0. apply notin_union_1 in Fr0. assumption.
                                  ********** apply notin_remove_2. apply notin_union_1 in Fr0. simpl in Fr0. apply notin_union_2 in Fr0. assumption. 
                                  ******** apply notin_union_2 in Fr0. apply notin_union_2 in Fr0. apply notin_union_2 in Fr0. apply notin_union_1 in Fr0. assumption.
               **** apply aeq_m_subst_out. rewrite H''. apply aeq_refl. 
           *** apply notin_union.
               **** apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_1 in Fr. assumption.
               **** apply notin_union. 
                    ***** simpl. apply notin_union. 
                    ****** apply notin_remove_2. pose proof Fr as H1. apply notin_union_1 in Fr. simpl in Fr. apply notin_union_1 in Fr. apply diff_remove_2 in Fr.
                    ******* assumption.
                    ******* apply notin_union_2 in H1. apply notin_union_2 in H1. apply notin_union_2 in H1. apply notin_union_1 in H1. apply notin_singleton_1 in H1. apply not_eq_sym. assumption.                                  
                    ****** apply notin_union_1 in Fr. simpl in Fr. apply notin_union_2 in Fr. assumption.
                    ***** repeat apply notin_union_2 in Fr. assumption.
        ** apply notin_union_3.
           *** apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_1 in Fr. assumption.
           *** apply notin_union_3.
               **** simpl. apply notin_union. 
                    ***** apply notin_remove_2. pose proof Fr as H1. apply notin_union_1 in Fr. simpl in Fr. apply notin_union_1 in Fr. apply diff_remove_2 in Fr.
                    ****** assumption.
                    ****** apply notin_union_2 in H1. apply notin_union_2 in H1. apply notin_union_2 in H1. apply notin_union_1 in H1. apply notin_singleton_1 in H1. apply not_eq_sym. assumption.                                  
                    ***** apply fv_nom_remove.
                    ****** apply notin_union_2 in Fr. apply notin_union_1 in Fr. assumption.
                    ****** apply notin_remove_2. apply notin_union_1 in Fr. simpl in Fr. apply notin_union_2 in Fr. assumption.
               **** repeat apply notin_union_2 in Fr. assumption.
      * apply Haeq.
   + intro Hneq'. destruct (y == z).
      * subst. rewrite m_subst_sub_eq. pose proof m_subst_sub_neq as Hsub. pick fresh w for (union (fv_nom e3) (union (fv_nom e2) (union (fv_nom (n_sub e1_1 z e1_2)) (singleton x)))). specialize (Hsub e1_1 e1_2 e2 x z w).
        apply aeq_trans with ([z := e3] n_sub ([x := e2] swap z w e1_1) w ([x := e2] e1_2)). apply aeq_m_subst_out.
        ** apply Hsub.
           *** assumption.
           *** apply notin_union_2 in Fr. assumption.
        ** destruct (z == w).
           *** subst. rewrite m_subst_sub_eq. rewrite swap_id. pose proof m_subst_sub_neq as Hsub'. specialize (Hsub' e1_1 ([w := e3] e1_2) ([w := e3] e2) x w w).
               rewrite Hsub'. apply aeq_sub_same. rewrite swap_id. apply aeq_sym. apply aeq_m_subst_in. apply m_subst_notin. apply notin_union_2 in Fr. apply notin_union_1 in Fr. assumption.
               apply IHe1_1. assumption. assumption. assumption. apply notin_union. apply fv_nom_remove. apply notin_union_1 in Fr. assumption. apply notin_remove_3. reflexivity. simpl. apply notin_union. apply notin_union. apply notin_remove_3. reflexivity. apply fv_nom_remove. 
               apply notin_union_1 in Fr. assumption. apply notin_remove_3. reflexivity. repeat apply notin_union_2 in Fr. assumption. 
           *** pose proof m_subst_sub_neq as Hsub'. specialize (Hsub' e1_1 ([z := e3] e1_2) ([z := e3] e2) x z w). pick fresh w' for (union (fv_nom e3) (union (fv_nom e2) (union (fv_nom (n_sub e1_1 z e1_2)) (singleton x)))).
               destruct (w == w'). 
               **** subst. rewrite Hsub'. pose proof m_subst_sub_neq as Hsub''. specialize (Hsub'' ([x := e2] swap z w' e1_1) ([x := e2] e1_2) e3 z w' w'). rewrite Hsub''.
                    apply aeq_sub_same. rewrite swap_id. rewrite H. apply aeq_m_subst_out. apply m_subst_notin. apply fv_nom_swap. apply notin_union_2 in Fr. apply notin_union_2 in Fr.
                    apply notin_union_1 in Fr. simpl in *. apply notin_union_1 in Fr. apply diff_remove_2 in Fr. assumption. apply not_eq_sym. assumption. reflexivity. assumption. assumption.
                    apply IHe1_1. assumption. assumption. assumption. apply notin_union. apply notin_union_1 in Fr. assumption. apply notin_union. simpl. apply notin_union. apply notin_remove_3. reflexivity. apply fv_nom_remove. apply notin_union_2 in Fr. apply notin_union_1 in Fr. assumption.
                    apply notin_remove_2. apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_1 in Fr. simpl in Fr. apply notin_union_2 in Fr. assumption. apply notin_singleton. assumption. assumption. apply notin_union. apply fv_nom_remove. apply notin_union_1 in Fr0. 
                    assumption. apply notin_remove_2. apply notin_union_2 in Fr0. apply notin_union_1 in Fr0. assumption. apply notin_union. simpl. apply notin_union. apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_1 in Fr. simpl in Fr.
                    apply notin_union_1 in Fr. assumption. apply fv_nom_remove. apply notin_union_1 in Fr. assumption. apply notin_remove_2. apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_1 in Fr.
                    simpl in Fr. apply notin_union_2 in Fr. assumption. repeat apply notin_union_2 in Fr. assumption.
               **** rewrite Hsub'. pose proof m_subst_sub_neq as Hsub''. specialize (Hsub'' ([x := e2] swap z w e1_1) ([x := e2] e1_2) e3 z w w). rewrite Hsub''.
                    apply aeq_sub_same. rewrite swap_id. rewrite H. apply aeq_m_subst_out. apply m_subst_notin. apply fv_nom_swap. apply notin_union_2 in Fr. apply notin_union_2 in Fr.
                    apply notin_union_1 in Fr. simpl in *. apply notin_union_1 in Fr. apply diff_remove_2 in Fr. assumption. apply not_eq_sym. assumption. reflexivity. assumption. assumption.
                    apply IHe1_1. assumption. assumption. assumption. apply notin_union. apply notin_union_1 in Fr. assumption. apply notin_union. simpl. apply notin_union. apply notin_remove_3. reflexivity. apply fv_nom_remove. apply notin_union_2 in Fr. apply notin_union_1 in Fr. assumption.
                    apply notin_remove_2. apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_1 in Fr. simpl in Fr. apply notin_union_2 in Fr. assumption. apply notin_singleton. assumption. assumption. apply notin_union. apply fv_nom_remove. apply notin_union_1 in Fr. 
                    assumption. apply notin_remove_2. apply notin_union_2 in Fr. apply notin_union_1 in Fr. assumption. apply notin_union. simpl. apply notin_union. apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_1 in Fr. simpl in Fr.
                    apply notin_union_1 in Fr. assumption. apply fv_nom_remove. apply notin_union_1 in Fr. assumption. apply notin_remove_2. apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_1 in Fr.
                    simpl in Fr. apply notin_union_2 in Fr. assumption. repeat apply notin_union_2 in Fr. assumption.
      * pose proof m_subst_sub_neq as Hsub. pick fresh w for (union (fv_nom e3) (union (fv_nom e2) (union (fv_nom (n_sub e1_1 z e1_2)) (union (singleton x) (singleton y))))). specialize (Hsub e1_1 e1_2 e2 x z w).
        apply aeq_trans with ([y := e3] n_sub ([x := e2] swap z w e1_1) w ([x := e2] e1_2)).
        ** apply aeq_m_subst_out. apply Hsub.
           *** apply not_eq_sym. assumption.
           *** apply notin_union. 
               **** apply notin_union_2 in Fr. apply notin_union_1 in Fr. assumption.
               **** apply notin_union.
                    ***** apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_1 in Fr. assumption.
                    ***** apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_1 in Fr. assumption.
        ** pose proof m_subst_sub_neq as Hsub'. specialize (Hsub' e1_1 e1_2 e3 y z w). apply aeq_trans with ([x := [y := e3] e2] n_sub ([y := e3] swap z w e1_1) w ([y := e3] e1_2)).
           *** pick fresh w' for (union (fv_nom e3) (union (fv_nom e2) (union (fv_nom (n_sub e1_1 y e1_2)) (union (singleton x) (union (singleton w) (singleton y)))))). destruct (z == w'). 
               **** subst. pose proof m_subst_sub_neq as Hsub''. specialize (Hsub'' ([x := e2] swap w' w e1_1) ([x := e2] e1_2) e3 y w w'). rewrite Hsub''. 
                    ***** pose proof m_subst_sub_neq as Hsub'''. specialize (Hsub''' ([y := e3] swap w' w e1_1) ([y := e3] e1_2) ([y := e3] e2) x w w'). rewrite Hsub'''.
                    ****** apply aeq_sub_same. unfold m_subst in *. pose proof swap_subst_rec_fun as Hsubst. specialize (Hsubst w w' x (swap w' w e1_1) e2). apply aeq_trans with (subst_rec_fun (subst_rec_fun (swap w' w e1_1) e2 x) e3 y).
                    ******* pose proof aeq_m_subst_out as Hout. unfold m_subst in *. apply Hout. rewrite Hsubst. unfold swap_var. destruct (x == w).
                    ******** subst. apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_1 in Fr. apply notin_singleton_1 in Fr. contradiction.
                    ******** destruct (x == w').
                    ********* subst. apply notin_union_2 in Fr0. apply notin_union_2 in Fr0. apply notin_union_2 in Fr0. apply notin_union_1 in Fr0. apply notin_singleton_1 in Fr0. contradiction.
                    ********* pose proof aeq_m_subst_eq as Heq. unfold m_subst in *. apply Heq. 
                    ********** rewrite (swap_symmetric _ w w'). rewrite (swap_involutive _ w' w). apply aeq_sym. apply swap_reduction.
                    *********** pose proof Fr0 as H0. apply notin_union_2 in Fr0. apply notin_union_2 in Fr0. apply notin_union_1 in Fr0. simpl in Fr0. apply notin_union_1 in Fr0. apply diff_remove_2 in Fr0.
                    ************ assumption. 
                    ************ apply not_eq_sym. assumption.
                    *********** apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_1 in Fr. simpl in Fr. apply notin_union_1 in Fr. apply diff_remove_2 in Fr.
                    ************ assumption. 
                    ************ apply not_eq_sym. apply notin_union_2 in Fr0. apply notin_union_2 in Fr0. apply notin_union_2 in Fr0. apply notin_union_2 in Fr0. apply notin_union_1 in Fr0. apply notin_singleton_1 in Fr0. apply not_eq_sym. assumption.
                    ********** apply swap_reduction.
                    *********** apply notin_union_2 in Fr. apply notin_union_1 in Fr. assumption.
                    *********** apply notin_union_2 in Fr0. apply notin_union_1 in Fr0. assumption.
                    ******* pose proof swap_subst_rec_fun as Hsubst'. specialize (Hsubst' w w' y (swap w' w e1_1) e3). apply aeq_trans with (subst_rec_fun (subst_rec_fun (swap w' w e1_1) e3 y) (subst_rec_fun e2 e3 y) x).
                    ******** apply H.
                    ********* reflexivity.
                    ********* assumption.
                    ********* assumption.
                    ******** pose proof aeq_m_subst_out as Hout. unfold m_subst in *. apply Hout. rewrite Hsubst'. unfold swap_var. destruct (y == w).
                    ********* subst. repeat apply notin_union_2 in Fr. apply notin_singleton_1 in Fr. contradiction.
                    ********* destruct (y == w').
                    ********** subst. repeat apply notin_union_2 in Fr. apply notin_singleton_1 in Fr. contradiction.
                    ********** pose proof aeq_m_subst_eq as Heq. unfold m_subst in *. apply Heq.
                    *********** rewrite (swap_symmetric _ w w'). rewrite swap_involutive. apply swap_reduction.
                    ************ pose proof Fr0 as H0. apply notin_union_2 in Fr0. apply notin_union_2 in Fr0. apply notin_union_1 in Fr0. simpl in Fr0. apply notin_union_1 in Fr0. apply diff_remove_2 in Fr0.
                    ************* assumption. 
                    ************* apply not_eq_sym. repeat apply notin_union_2 in H0. apply notin_singleton_1 in H0. assumption.
                    ************ apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_1 in Fr. simpl in Fr. apply notin_union_1 in Fr. apply diff_remove_2 in Fr.
                    ************* assumption. 
                    ************* apply not_eq_sym. apply notin_union_2 in Fr0. apply notin_union_2 in Fr0. apply notin_union_2 in Fr0. apply notin_union_2 in Fr0. apply notin_union_1 in Fr0. apply notin_singleton_1 in Fr0. apply not_eq_sym. assumption.
                    *********** apply aeq_sym. apply swap_reduction.
                    ************ apply notin_union_1 in Fr. assumption.
                    ************ apply notin_union_1 in Fr0. assumption.
                    ******* apply IHe1_1.
                    ******** assumption.
                    ******** assumption.
                    ****** apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_1 in Fr. apply notin_singleton_1 in Fr. assumption.
                    ****** apply notin_union.
                    ******* apply fv_nom_remove.
                    ******** apply notin_union_1 in Fr0. assumption.
                    ******** apply notin_remove_2. apply notin_union_2 in Fr0. apply notin_union_1 in Fr0. assumption.
                    ******* apply notin_union.
                    ******** simpl. apply notin_union. 
                    ********* apply notin_remove_2. apply fv_nom_remove. 
                    ********** apply notin_union_1 in Fr0. assumption.
                    ********** apply notin_remove_2. apply fv_nom_swap. apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_1 in Fr. simpl in Fr. apply notin_union_1 in Fr. apply diff_remove_2 in Fr.
                    *********** assumption. 
                    *********** apply not_eq_sym. apply notin_union_2 in Fr0. apply notin_union_2 in Fr0. apply notin_union_2 in Fr0. apply notin_union_2 in Fr0. apply notin_union_1 in Fr0. apply notin_singleton_1 in Fr0. apply not_eq_sym. assumption.
                    ********* apply fv_nom_remove.
                    ********** apply notin_union_1 in Fr0. assumption.
                    ********** apply notin_remove_2. apply notin_union_2 in Fr0. apply notin_union_2 in Fr0. apply notin_union_1 in Fr0. simpl in Fr0. apply notin_union_2 in Fr0.  assumption.
                    ******** apply notin_union_2 in Fr0. apply notin_union_2 in Fr0. apply notin_union_2 in Fr0. apply notin_union_1 in Fr0. assumption.
                    ***** repeat apply notin_union_2 in Fr. apply notin_singleton_1 in Fr. assumption.
                    ***** apply notin_union.
                    ****** apply notin_union_1 in Fr0. assumption. 
                    ****** apply notin_union. 
                    ******* simpl. apply notin_union.
                    ******** apply notin_remove_2. apply fv_nom_remove.
                    ********* apply notin_union_2 in Fr0. apply notin_union_1 in Fr0. assumption.
                    ********* apply notin_remove_2. apply fv_nom_swap. apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_1 in Fr. simpl in Fr. apply notin_union_1 in Fr. apply diff_remove_2 in Fr.
                    ********** assumption. 
                    ********** apply not_eq_sym. apply notin_union_2 in Fr0. apply notin_union_2 in Fr0. apply notin_union_2 in Fr0. apply notin_union_2 in Fr0. apply notin_union_1 in Fr0. apply notin_singleton_1 in Fr0. apply not_eq_sym. assumption.
                    ******** apply fv_nom_remove. 
                    ********* apply notin_union_2 in Fr0. apply notin_union_1 in Fr0. assumption.
                    ********* apply notin_remove_2. apply notin_union_2 in Fr0. apply notin_union_2 in Fr0. apply notin_union_1 in Fr0. simpl in Fr0. apply notin_union_2 in Fr0. assumption.
                    ******* repeat apply notin_union_2 in Fr0. assumption.
               **** destruct (w == z).
                    ***** subst. pose proof m_subst_sub_neq as Hsub''. specialize (Hsub'' ([x := e2] swap z z e1_1) ([x := e2] e1_2) e3 y z w'). pose proof m_subst_sub_neq as Hsub'''. specialize (Hsub''' ([y := e3] swap z z e1_1) ([y := e3] e1_2) ([y := e3] e2) x z w'). rewrite Hsub''. 
                    ****** rewrite Hsub'''.
                    ******* apply aeq_sub_same. unfold m_subst in *. pose proof swap_subst_rec_fun as Hswap. specialize (Hswap z w' x (swap z z e1_1) e2). pose proof swap_subst_rec_fun as Hswap'. specialize (Hswap' z w' y (swap z z e1_1) e3).
                            apply aeq_trans with (subst_rec_fun (subst_rec_fun (swap w' z e1_1) e2 x) e3 y).
                    ******** pose proof aeq_m_subst_out as Hout. unfold m_subst in *. apply Hout. rewrite Hswap. unfold swap_var. destruct (x == z).
                    ********* subst. contradiction.
                    ********* destruct (x == w'). 
                    ********** subst. apply notin_union_2 in Fr0. apply notin_union_2 in Fr0. apply notin_union_2 in Fr0. apply notin_union_1 in Fr0. apply notin_singleton_1 in Fr0. contradiction.
                    ********** pose proof aeq_m_subst_eq as Heq. unfold m_subst in *. apply Heq.
                    *********** rewrite swap_id. rewrite (swap_symmetric _ z w'). apply aeq_refl.
                    *********** apply swap_reduction.
                    ************ apply notin_union_2 in Fr. apply notin_union_1 in Fr. assumption.
                    ************ apply notin_union_2 in Fr0. apply notin_union_1 in Fr0. assumption.
                    ******** apply aeq_trans with (subst_rec_fun (subst_rec_fun (swap w' z e1_1) e3 y) (subst_rec_fun e2 e3 y) x).
                    ********* apply H.
                    ********** reflexivity.
                    ********** assumption.
                    ********** assumption.
                    ********* pose proof aeq_m_subst_eq as Heq. unfold m_subst in *. apply Heq.
                    ********** rewrite Hswap'. unfold swap_var. destruct (y == z).
                    *********** subst. repeat apply notin_union_2 in Fr. apply notin_singleton_1 in Fr. contradiction.
                    *********** destruct (y == w').
                    ************ subst. repeat apply notin_union_2 in Fr0. apply notin_singleton_1 in Fr0. contradiction.
                    ************ apply Heq. 
                    ************* rewrite swap_id. rewrite (swap_symmetric _ w' z). reflexivity.
                    ************* apply aeq_sym. apply swap_reduction. 
                    ************** apply notin_union_1 in Fr. assumption.
                    ************** apply notin_union_1 in Fr0. assumption.
                    ********** apply aeq_refl.
                    ******** apply IHe1_1. 
                    ********* assumption.
                    ********* assumption.
                    ******* apply not_eq_sym. assumption.
                    ******* apply notin_union.
                    ******** apply fv_nom_remove.
                    ********* apply notin_union_1 in Fr0. assumption.
                    ********* apply notin_remove_2. apply notin_union_2 in Fr0. apply notin_union_1 in Fr0. assumption.
                    ******** apply notin_union.
                    ********* simpl. rewrite swap_id. apply notin_union. 
                    ********** apply notin_remove_2. apply fv_nom_remove.
                    *********** apply notin_union_1 in Fr0. assumption.
                    *********** pose proof Fr0 as H1. apply notin_remove_2. apply notin_union_2 in Fr0. apply notin_union_2 in Fr0. apply notin_union_1 in Fr0. simpl in Fr0. apply notin_union_1 in Fr0. apply diff_remove_2 in Fr0. 
                    ************ assumption.
                    ************ repeat apply notin_union_2 in H1. apply notin_singleton_1 in H1. apply not_eq_sym. assumption.
                    ********** apply fv_nom_remove.
                    *********** apply notin_union_1 in Fr0. assumption.
                    *********** apply notin_remove_2. apply notin_union_2 in Fr0. apply notin_union_2 in Fr0. apply notin_union_1 in Fr0. simpl in Fr0. apply notin_union_2 in Fr0. assumption.
                    ********* apply notin_union_2 in Fr0. apply notin_union_2 in Fr0. apply notin_union_2 in Fr0. apply notin_union_1 in Fr0. assumption.
                    ****** assumption.
                    ****** apply notin_union.
                    ******* apply notin_union_1 in Fr0. assumption.
                    ******* apply notin_union. 
                    ******** simpl. apply notin_union.
                    ********* apply notin_remove_2. rewrite swap_id. apply fv_nom_remove.
                    ********** apply notin_union_2 in Fr0. apply notin_union_1 in Fr0. assumption.
                    ********** pose proof Fr0 as H1. apply notin_remove_2. apply notin_union_2 in Fr0. apply notin_union_2 in Fr0. apply notin_union_1 in Fr0. simpl in Fr0. apply notin_union_1 in Fr0. apply diff_remove_2 in Fr0.
                    *********** assumption.
                    *********** repeat apply notin_union_2 in H1. apply notin_singleton_1 in H1. apply not_eq_sym. assumption.
                    ********* apply fv_nom_remove.
                    ********** apply notin_union_2 in Fr0. apply notin_union_1 in Fr0.  assumption.
                    ********** apply notin_remove_2. apply notin_union_2 in Fr0. apply notin_union_2 in Fr0. apply notin_union_1 in Fr0. simpl in Fr0. apply notin_union_2 in Fr0. assumption.
                    ******** repeat apply notin_union_2 in Fr0. assumption.
                    ***** pose proof m_subst_sub_neq as Hsub''. specialize (Hsub'' ([x := e2] swap z w e1_1) ([x := e2] e1_2) e3 y w w'). rewrite Hsub''.
                    ****** pose proof m_subst_sub_neq as Hsub'''. specialize (Hsub''' ([y := e3] swap z w e1_1) ([y := e3] e1_2) ([y := e3] e2) x w w'). rewrite Hsub'''.
                    ******* apply aeq_sub_same. unfold m_subst. pose proof swap_subst_rec_fun as Hswap. specialize (Hswap w w' x (swap z w e1_1) e2). apply aeq_trans with (subst_rec_fun (subst_rec_fun (swap w' z e1_1) e2 x) e3 y).
                    ******** pose proof aeq_m_subst_out as Hout. unfold m_subst in *. apply Hout. rewrite Hswap. unfold swap_var. destruct (x == w).
                    ********* subst. apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_1 in Fr. apply notin_singleton_1 in Fr. contradiction.
                    ********* destruct (x == w').
                    ********** subst. apply notin_union_2 in Fr0. apply notin_union_2 in Fr0. apply notin_union_2 in Fr0. apply notin_union_1 in Fr0. apply notin_singleton_1 in Fr0. contradiction.
                    ********** pose proof aeq_m_subst_eq as Heq. unfold m_subst in *. rewrite (swap_symmetric _ w w'). rewrite (swap_symmetric _ z w). apply Heq. 
                    *********** apply aeq_swap_swap.
                    ************ pose proof Fr0 as H1. apply notin_union_2 in Fr0. apply notin_union_2 in Fr0. apply notin_union_1 in Fr0. simpl in Fr0. apply notin_union_1 in Fr0. apply diff_remove_2 in Fr0.
                    ************* assumption. 
                    ************* apply not_eq_sym. repeat apply notin_union_2 in H1. apply notin_singleton_1 in H1. assumption.
                    ************ pose proof Fr as H1. apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_1 in Fr. simpl in Fr. apply notin_union_1 in Fr. apply diff_remove_2 in Fr.
                    ************* assumption. 
                    ************* apply not_eq_sym. apply notin_union_2 in Fr0. apply notin_union_2 in Fr0. apply notin_union_2 in Fr0. apply notin_union_2 in Fr0. apply notin_union_1 in Fr0. apply notin_singleton_1 in Fr0. apply not_eq_sym. assumption.
                    *********** apply swap_reduction.
                    ************ apply notin_union_2 in Fr. apply notin_union_1 in Fr. assumption.
                    ************ apply notin_union_2 in Fr0. apply notin_union_1 in Fr0. assumption.
                    ******** pose proof swap_subst_rec_fun as Hswap'. specialize (Hswap' w w' y (swap w z e1_1) e3). apply aeq_trans with (subst_rec_fun (subst_rec_fun (swap w' z e1_1) e3 y) (subst_rec_fun e2 e3 y) x). 
                    ********* unfold m_subst. apply H.
                    ********** reflexivity.
                    ********** assumption. 
                    ********** assumption.
                    ********* pose proof aeq_m_subst_eq as Hsubst. unfold m_subst in *. apply Hsubst. rewrite (swap_symmetric _ z w). rewrite Hswap'.
                    ********** unfold swap_var. destruct (y == w).
                    *********** subst. repeat apply notin_union_2 in Fr. apply notin_singleton_1 in Fr. contradiction. 
                    *********** destruct (y == w'). 
                    ************ subst. repeat apply notin_union_2 in Fr0. apply notin_singleton_1 in Fr0. contradiction.
                    ************ apply Hsubst. 
                    ************* apply aeq_sym. rewrite (swap_symmetric _ w w'). apply aeq_swap_swap.
                    ************** apply notin_union_2 in Fr0. apply notin_union_2 in Fr0. apply notin_union_1 in Fr0. simpl in Fr0. apply notin_union_1 in Fr0. apply diff_remove_2 in Fr0.
                    *************** assumption.
                    *************** apply not_eq_sym. assumption.
                    ************** apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_1 in Fr. simpl in Fr. apply notin_union_1 in Fr. apply diff_remove_2 in Fr.
                    *************** assumption.
                    *************** assumption.
                    ************* apply aeq_sym. apply swap_reduction.
                    ************** apply notin_union_1 in Fr. assumption.
                    ************** apply notin_union_1 in Fr0. assumption.
                    ********** apply aeq_refl.
                    ******** apply IHe1_1.
                    ********* assumption.
                    ********* assumption.
                    ******* apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_1 in Fr. apply notin_singleton_1 in Fr. assumption.
                    ******* apply notin_union.
                    ******** apply fv_nom_remove. 
                    ********* apply notin_union_1 in Fr0. assumption.
                    ********* apply notin_remove_2. apply notin_union_2 in Fr0. apply notin_union_1 in Fr0. assumption.
                    ******** apply notin_union. simpl. apply notin_union.
                    ********* apply notin_remove_2. apply fv_nom_remove. 
                    ********** apply notin_union_1 in Fr0. assumption.
                    ********** apply notin_remove_2. apply fv_nom_remove_swap.
                    *********** apply notin_union_2 in Fr0. apply notin_union_2 in Fr0. apply notin_union_2 in Fr0. apply notin_union_2 in Fr0. apply notin_union_1 in Fr0. apply notin_singleton_1 in Fr0. apply not_eq_sym. assumption.
                    *********** apply not_eq_sym. assumption.
                    *********** pose proof Fr0 as H1. apply notin_union_2 in Fr0. apply notin_union_2 in Fr0. apply notin_union_1 in Fr0. simpl in Fr0. apply notin_union_1 in Fr0. apply diff_remove_2 in Fr0.
                    ************ assumption.
                    ************ repeat apply notin_union_2 in H1. apply notin_singleton_1 in H1. apply not_eq_sym. assumption.
                    ********* apply fv_nom_remove.
                    ********** apply notin_union_1 in Fr0. assumption.
                    ********** apply notin_remove_2. apply notin_union_2 in Fr0. apply notin_union_2 in Fr0. apply notin_union_1 in Fr0. simpl in Fr0. apply notin_union_2 in Fr0. assumption.
                    ********* apply notin_union_2 in Fr0. apply notin_union_2 in Fr0. apply notin_union_2 in Fr0. apply notin_union_1 in Fr0. assumption.
               ****** repeat apply notin_union_2 in Fr. apply notin_singleton_1 in Fr. assumption.
               ****** apply notin_union. 
                      ******* apply notin_union_1 in Fr0. assumption.
                      ******* apply notin_union. 
                      ******** simpl. apply notin_union.
                      ********* apply notin_remove_2. apply fv_nom_remove.
                      ********** apply notin_union_2 in Fr0. apply notin_union_1 in Fr0. assumption.
                      ********** apply notin_remove_2. apply fv_nom_remove_swap. 
                      *********** apply notin_union_2 in Fr0. apply notin_union_2 in Fr0. apply notin_union_2 in Fr0. apply notin_union_2 in Fr0. apply notin_union_1 in Fr0. apply notin_singleton_1 in Fr0. apply not_eq_sym. assumption.
                      *********** apply not_eq_sym. assumption.
                      *********** pose proof Fr0 as H1. apply notin_union_2 in Fr0. apply notin_union_2 in Fr0. apply notin_union_1 in Fr0. simpl in Fr0. apply notin_union_1 in Fr0. apply diff_remove_2 in Fr0.
                      ************ assumption.
                      ************ repeat apply notin_union_2 in H1. apply notin_singleton_1 in H1. apply not_eq_sym. assumption.
                      ********* apply fv_nom_remove.
                      ********** apply notin_union_2 in Fr0. apply notin_union_1 in Fr0. assumption.
                      ********** apply notin_remove_2. apply notin_union_2 in Fr0. apply notin_union_2 in Fr0. apply notin_union_1 in Fr0. simpl in Fr0. apply notin_union_2 in Fr0. assumption.
                      ******** repeat apply notin_union_2 in Fr0. assumption.
           *** apply aeq_m_subst_out. apply aeq_sym. apply Hsub'.
               **** assumption.
               **** apply notin_union.
               ***** apply notin_union_1 in Fr. assumption.
               ***** apply notin_union.
               ****** apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_1 in Fr. assumption.
               ****** repeat apply notin_union_2 in Fr. assumption.  
 Qed.
