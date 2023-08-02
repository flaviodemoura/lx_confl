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

Lemma diff_remove_2: forall x y s,
  x <> y -> x `notin` remove y s -> x `notin` s.
Proof.
  intros. default_simp.
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

(** In this work, we present a formalization of the substitution lemma%\cite{barendregtLambdaCalculusIts1984}% in a general framework that extends the $\lambda$-calculus with an explicit substitution operator. The formalization is done in the Coq proof assistant%\cite{teamCoqProofAssistant2021}% and the source code is available at: %\vspace{0.25cm}%

 %\url{https://github.com/flaviodemoura/lx_confl/tree/m_subst_lemma} \vspace{0.25cm}%

The substitution lemma is an important result concerning the composition of the substitution operation, and is usually presented as follows in the context of the $\lambda$-calculus:

%\begin{tcolorbox}
 Let $t,u$ and $v$ be $\lambda$-terms. If $x\notin FV(v)$ ({\it i.e.} $x$ does not occur in the set of free variables of the term $v$) then $\metasub{\metasub{t}{x}{u}}{y}{v} =_\alpha \metasub{\metasub{t}{y}{v}}{x}{\metasub{u}{y}{v}}$.
\end{tcolorbox}%

This is a well known result already formalized in the context of the $\lambda$-calculus %\cite{berghoferHeadtoHeadComparisonBruijn2007}%. Nevertheless, in the context of $\lambda$-calculi with explicit substitutions its formalization is not straightforward due to the interaction between the metasubstitution and the explicit substitution operator. Our formalization is done in a nominal setting that uses the MetaLib%\footnote{\url{https://github.com/plclub/metalib}}% package of Coq, but no particular explicit substitution calculi is taken into account because the expected behaviour between the metasubstitution operation with the explicit substitutition constructor is the same regardless the calculus. The contributions of this work are twofold:

%\begin{enumerate}
\item The formalization is modular in the sense that no particular calculi with explicit substitutions is taken into account. Therefore, we believe that this formalization could be seen as a generic framework for proving properties of these calculi that uses the substitution lemma in the nominal setting\cite{kesnerPerpetualityFullSafe2008,nakazawaCompositionalConfluenceProofs2016,nakazawaPropertyShufflingCalculus2023};
\item A solution to a circularity problem in the proofs is given. It adds an axiom to the formalization that replaces the set equality by the syntactic equality. In this way, we are allowed to replace/rewrite sets of (free) variables by another sets of (free) variables in arbitrary contexts.
\end{enumerate}%

This document is built directly from a Coq script using the CoqDoc%\footnote{\url{https://coq.inria.fr/refman/using/tools/coqdoc.html}}% tool. In the following section, we present the general framework and the basics of the nominal approach. In Section 3, we present our definition of metasubstitution and some of its properties. In Section 4, we present the main theorem, %{\it i.e.}% the substitution lemma, and we conclude in Section 5.*)

(** * A syntactic extension of the $\lambda$-calculus *)

(** In this section, we present the framework of the formalization, which is based on a nominal approach%\cite{gabbayNewApproachAbstract1999}% where variables use names. In the nominal setting, variables are represented by atoms that are structureless entities with a decidable equality: 

<<
Parameter eq_dec : forall x y : atom, {x = y} + {x <> y}.
>>

%\noindent% therefore different names mean different atoms and different variables. The nominal approach is close to the usual paper and pencil notation used in $\lambda$-calculus lectures, whose grammar of terms is given by:

%\begin{equation}\label{lambda:grammar}
 t ::= x \mid \lambda_x.t \mid t\ t
\end{equation}%

%\noindent% and its main rule, named $\beta$-reduction, is given by:

%\begin{equation}\label{lambda:beta}
 (\lambda_x.t)\ u \to_{\beta} \metasub{t}{x}{u}
\end{equation}%
%\noindent% where $\metasub{t}{x}{u}$ represents the term obtained from $t$ after replacing all its free occurrences of the variable $x$ by $u$ in a way that renaming of bound variable is done in order to avoid variable capture. In other words, $\metasub{t}{x}{u}$ is a metanotation for a capture free substitution. For instance, the $\lambda$-term $(\lambda_x\lambda_y.x\ y)\ y$ has both bound and free occurrences of the variable $y$. In order to $\beta$-reduce it one has to replace (or substitute) the free variable $y$ for all free occurrences of the variable $x$ in the term $(\lambda_y.x\ y)$. But a straight substitution will capture the free variable $y$, %{\it i.e.}% this means that the free occurrence of $y$ before the $\beta$-reduction will become bound after the $\beta$-reduction step. A renaming of bound variables is done to avoid such capture, so in this example, one can take an $\alpha$-equivalent%\footnote{A formal definition of this notion will be given later in this section.}% term, say $(\lambda_z.x\ z)$, and perform the $\beta$-step correctly as $(\lambda_x\lambda_y.x\ y)\ y \to_{\beta} \lambda_z.y\ z$. The renaming of variables in the nominal setting is done via a name-swapping, which is formally defined as follows:

$\vswap{x}{y}{z} := \left\{ \begin{array}{ll}
y, & \mbox{ if } z = x; \\
x, & \mbox{ if } z = y; \\
z, & \mbox{ otherwise. } \\
\end{array}\right.$

This notion can be extended to $\lambda$-terms in a straightfoward way:

%\begin{equation}\label{def:swap}
\swap{x}{y}{t} := \left\{ \begin{array}{ll}
\vswap{x}{y}{z}, & \mbox{ if } t = z; \\
\lambda_{\vswap{x}{y}{z}}.\swap{x}{y}{t_1}, & \mbox{ if } t = \lambda_z.t_1; \\
\swap{x}{y}{t_1}\ \swap{x}{y}{t_2}, & \mbox{ if } t = t_1\ t_2\\
\end{array}\right.
\end{equation}%

In the previous example, one could apply a swap to avoid the variable capture in a way that, a swap is applied to the body of the abstraction before applying the metasubstitution to it: $(\lambda_x\lambda_y.x\ y)\ y \to_{\beta} \metasub{(\swap{y}{z}{(\lambda_y.x\ y)})}{x}{y} = \metasub{(\lambda_z.x\ z)}{x}{y} = \lambda_z.y\ z$. Could we have used a variable substitution instead of a swapping in the previous example? Absolutely. We could have done the reduction as $(\lambda_x\lambda_y.x\ y)\ y \to_{\beta} \metasub{(\metasub{(\lambda_y.x\ y)}{y}{z})}{x}{y} = \metasub{(\lambda_z.x\ z)}{x}{y} = \lambda_z.y\ z$, but as we will shortly see, variable substitution is not stable under $\alpha$-equivalence, while the swapping is stable under $\alpha$-equivalence, thereby rendering it a more fitting choice when operating modulo $\alpha$-equivalence.

In what follows, we will adopt a mixed-notation approach, intertwining metanotation with the equivalent Coq notation. This strategy aids in elucidating the proof steps of the upcoming lemmas, enabling a clearer and more detailed comprehension of each stage in the argumentation. The corresponding Coq code for the swapping of variables, named [swap_var], is defined as follows: *)

Definition vswap (x:atom) (y:atom) (z:atom) := if (z == x) then y else if (z == y) then x else z.

(** %\noindent% therefore, the swap $\vswap{x}{y}{z}$ is written in Coq as [vswap x y z]. A short example to acquaint ourselves with the Coq notation, let us show how we will write the proofs:*)

Lemma swap_var_id: forall x y, vswap x x y = y.
Proof.
  intros. unfold vswap. case (y == x); intros; subst; reflexivity. (** %\noindent{\bf Proof.}% The proof is done by case analysis, and it is straightforward in both cases, when [x = y] and [x <> y]. $\hfill\Box$ *)
Qed.

(** ** An explicit substitution operator *)

(** The extension of the swap operation to terms require an additional comment because we will not work with the grammar (%\ref{lambda:grammar}%), but rather, we will extend it with an explicit substitution operator:

%\begin{equation}\label{es:grammar}
  t ::= x \mid \lambda_x.t \mid t\ t \mid \esub{t}{x}{u}
\end{equation}%
%\noindent% where $[x := u] t$ represents a term with an operator that will be evaluated with specific rules of a calculus. The intended meaning of the explicit substitution is that it will simulate the metasubstitution. This formalization aims to be a generic framework applicable to any calculi with explicit substitutions in named notation for variables. Therefore, we will not specify rules about how one can simulate the metasubstitution, but it is important to be aware that this is not a trivial task as one can easily lose important properties of the original $\lambda$-calculus%\cite{melliesTypedLcalculiExplicit1995,guillaumeLambdaCalculusDoes2000}%.

Calculi with explicit substitutions are formalisms that deconstruct the metasubstitution operation into more granular steps, thereby functioning as an intermediary between the $\lambda$-calculus and its practical implementations. In other words, these calculi shed light on the execution models of higher-order languages. In fact, the development of a calculus with explicit substitutions faithful to the $\lambda$-calculus, in the sense of the preservation of some desired properties were the main motivation for such a long list of calculi with explicit substitutions invented in the last decades%\cite{abadiExplicitSubstitutions1991,blooPreservationStrongNormalisation1995,benaissaLambdaUpsilonCalculus1996,curienConfluencePropertiesWeak1996,munozConfluencePreservationStrong1996,kamareddineExtendingLambdaCalculusExplicit1997,blooExplicitSubstitutionEdge1999,davidLambdacalculusExplicitWeakening2001,kesnerTheoryExplicitSubstitutions2009}%.

The following inductive definition corresponds to the grammar (%\ref{es:grammar}%), where the explicit substitution constructor, named [n_sub], has a special notation. Instead of writing [n_sub t x u], we will write [[x := u] t] similarly to (%\ref{es:grammar}%). Therefore, [n_sexp] is used to denote the set of nominal expressions equipped with an explicit substitution operator, which, for simplicity, we will refer to as just "terms". *)

Inductive n_sexp : Set :=
 | n_var (x:atom)
 | n_abs (x:atom) (t:n_sexp)
 | n_app (t1:n_sexp) (t2:n_sexp)
 | n_sub (t1:n_sexp) (x:atom) (t2:n_sexp).
Notation "[ x := u ] t" := (n_sub t x u) (at level 60).

(** The [size] and the set [fv_nom] of the free variables of a term are defined as usual: *)

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

(** The action of a permutation on a term, written $\swap{x}{y}{t}$, is inductively defined as in (%\ref{def:swap}%) with the additional case for the explicit substitution operator:%\vspace{.5cm}%

$\swap{x}{y}{t} := \left\{ \begin{array}{ll}
\vswap{x}{y}{v}, & \mbox{ if } t \mbox{ is the variable } v; \\
\lambda_{\vswap{x}{y}{z}}. \swap{x}{y}{t_1}, & \mbox{ if } t = \lambda_z.t_1; \\
\swap{x}{y}{t_1}\ \swap{x}{y}{t_2}, & \mbox{ if } t = t_1\ t_2;\\
\esub{\swap{x}{y}{t_1}}{\vswap{x}{y}{z}}{\swap{x}{y}{t_2}}, & \mbox{ if } t = \esub{t_1}{z}{t_2}.
\end{array}\right.$ %\vspace{.5cm}%

The corresponding Coq definition is given by the following recursive function: *)

Fixpoint swap (x:atom) (y:atom) (t:n_sexp) : n_sexp :=
  match t with
  | n_var z     => n_var (vswap x y z)
  | n_abs z t1  => n_abs (vswap x y z) (swap x y t1)
  | n_app t1 t2 => n_app (swap x y t1) (swap x y t2)
  | n_sub t1 z t2 => n_sub (swap x y t1) (vswap x y z) (swap x y t2)
  end.

(* begin hide *)
Lemma swap_id : forall t x,
    swap x x t = t.
Proof.
  induction t; simpl; unfold vswap; default_simp.
Qed.

Lemma swap_eq: forall x y z w, vswap x y z = vswap x y w -> z = w.
Proof.
  intros x y z w H. unfold vswap in H. destruct (z == x).
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

Lemma swap_neq: forall x y z w, z <> w -> vswap x y z <> vswap x y w.
Proof.
  intros x y z w H1 H2. unfold vswap. destruct (z == x).
  - subst. apply swap_eq in H2. contradiction.
  - apply swap_eq in H2. contradiction.
Qed.
(* end hide *)

(** The [swap] function has many interesting properties, but we will focus on the ones that are more relevant to the proofs related to the substitution lemma. Nevertheless, all lemmas can be found in the source code of the formalization%\footnote{\url{https://github.com/flaviodemoura/lx_confl/tree/m_subst_lemma}}%. The next lemma shows that the [swap] function preserves the size of terms. It is proved by induction on the structure of the term [t]: *)

Lemma swap_size_eq : forall x y t, size (swap x y t) = size t.
Proof.
  induction t; simpl; auto.
Qed.

(* begin hide *)
Hint Rewrite swap_size_eq.

Lemma swap_symmetric : forall t x y, swap x y t = swap y x t.
Proof.
  induction t.
  - intros x' y. simpl. unfold vswap. default_simp.
  - intros x' y; simpl. unfold vswap. default_simp.
  - intros x y; simpl. rewrite IHt1. rewrite IHt2; reflexivity.
  - intros. simpl. unfold vswap. default_simp.
Qed.

Lemma swap_symmetric_2: forall x y x' y' t,
    x <> x' -> y <> y' -> x <> y'-> y <> x' -> swap x y (swap x' y' t) = swap x' y' (swap x y t). 
Proof.
  intros. induction t; simpl in *; unfold vswap in *; default_simp.
Qed.
(* end hide *)

(** The [swap] function is involutive, which is also proved done by structural induction on the term [t]: *)

Lemma swap_involutive : forall t x y, swap x y (swap x y t) = t.
Proof.
 induction t; intros; simpl; unfold vswap; default_simp.
Qed.

(** The shuffle property given by the following lemma is also proved by structural induction on the structure of [t]:*)
Lemma shuffle_swap : forall w y z t,
    w <> z -> y <> z ->
    (swap w y (swap y z t)) = (swap w z (swap w y t)).
Proof.
  induction t; intros; simpl; unfold vswap; default_simp.
Qed.

(* begin hide *)
Lemma shuffle_swap' : forall w y n z,
    w <> z -> y <> z ->
    (swap w y (swap y z n)) = (swap z w (swap y w n)).
Proof.
  induction n; intros; simpl; unfold vswap; default_simp.
Qed.
(* end hide *)

(** Equivariance is another important property of the [swap] function. It states that a swap can uniformly be propagated over the structure of a term:*)

Lemma vswap_equivariance : forall v x y z w, vswap x y (vswap z w v) = vswap (vswap x y z) (vswap x y w) (vswap x y v).
Proof.
  intros; unfold vswap; case(v == z); case (w == x); default_simp.
Qed.

Lemma swap_equivariance : forall t x y z w, swap x y (swap z w t) = swap (vswap x y z) (vswap x y w) (swap x y t).
Proof.
  induction t.
  - intros. unfold vswap. case (z == x0).
    -- case (w == x0).
       --- intros. rewrite swap_id. rewrite e; rewrite e0.
           rewrite swap_id. reflexivity.
       --- intros. case (w == y).
           + intros. rewrite swap_symmetric. rewrite e; rewrite e0.
             reflexivity.
           + intros. unfold swap. unfold vswap. default_simp.
    -- unfold swap. unfold vswap. intros. default_simp.
  - intros. simpl. rewrite IHt. unfold vswap.
    case (x == z).
    -- case (w == x0); default_simp.
    -- case (w == x0).
       --- default_simp.
       --- intros. case (x == w); intros; case (z == x0); default_simp.
  - intros. simpl. rewrite IHt1. rewrite IHt2. reflexivity.
  - intros. simpl. rewrite IHt1. rewrite IHt2. unfold vswap.
    default_simp.    
Qed.

(** If a variable, say [z], is not in the set of free variables of a term [t] and one swaps [z] with another variable, say [y], then [y] is not in the set of free variables of the term [t]. This is the content of the following lemma that can easily be proved using induction on the structure of the term [t]:*)
Lemma fv_nom_swap : forall z y t, z `notin` fv_nom t -> y `notin` fv_nom (swap y z t).
Proof.
  induction t; intros; simpl; unfold vswap; default_simp.
Qed.

(* begin hide *)
Lemma fv_nom_swap_2 : forall z y t,
  z `notin` fv_nom (swap y z t) -> y `notin` fv_nom t.
Proof.
  intros. induction t; simpl in *; unfold vswap in H; default_simp.
Qed.

Lemma fv_nom_swap_remove: forall t x y y0, x <> y ->  x <> y0 -> x `notin` fv_nom (swap y0 y t) -> x `notin` fv_nom t.
Proof.
  intros. induction t; simpl in *; unfold vswap in *; default_simp.
Qed.
    
Lemma fv_nom_remove_swap: forall t x y y0, x <> y ->  x <> y0 -> x `notin` fv_nom t -> x `notin` fv_nom (swap y0 y t).
  Proof.
    induction t; simpl in *; unfold vswap; default_simp.
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

(** We will use this induction principle to prove that if a certain variable, say [x'], is not in the set of free variables of a term [t] then the variable obtained after applying any swap to [x'] also is not in the set of free variables of the term obtained from [t] after applying the same swap to [t]: *)  
Lemma notin_fv_nom_equivariance : forall t x' x y, x' `notin` fv_nom t -> vswap x y x'  `notin` fv_nom (swap x y t).
Proof.
  induction t as [z | t1 z | t1 t2 | t1 z t2] using n_sexp_induction. (** %\noindent{\bf Proof.}% The proof is by induction on the size of the term [t].*)
  - intros x' x y Hfv. simpl in *. apply notin_singleton_1 in Hfv. apply notin_singleton. apply swap_neq. assumption. (** If [t] is a variable, say [z], then we have that [x' <> z] by hypothesis, and we conclude by lemma [swap_neq].*)
  - intros x' x y Hfv. simpl in *. apply notin_remove_1 in Hfv. destruct Hfv. (** If [t = n_abs z t1] then we have that $x' \notin fv(t1) \backslash \{z\}$ by hypothesis. This means that either [x' = z] or [x'] is not in $fv(t1)$, %{\it i.e.}% [fv_nom t1] in the Coq language.*)
    + subst. apply notin_remove_3. reflexivity. (** If [x' = z] then we have to prove that a certain element is not in a set where it was removed, and we are done. *)
    + apply notin_remove_2. specialize (H t1 x x). rewrite swap_id in H. apply H.
      * reflexivity.
      * assumption.
  - intros x' x y Hfv. simpl in *. apply notin_union.
    + apply IHt2. apply notin_union_1 in Hfv. assumption.
    + apply IHt1. apply notin_union_2 in Hfv. assumption. 
  - case (x' == y). (** If [x' <> x] then we compare [x'] with [y]. If they are equal then we are in the same situation of the previous case, and hence we conclude with an application of the lemma [fv_nom_swap]. *)
    + intro Heq. subst. apply fv_nom_swap. assumption.
    + intro Hneq. induction t as [z | z t1 | t1 t2 | t1 z t2]. (** If both [x] and [y] are different from [x'] then $\vswap{x}{y}{x'} = x'$ and hence, we have to prove that if [x'] is not in the set of free variables of [t] then [x'] is not in the set of free variables of [swap x y t]. This is done by induction on the structure of [t]. *)
      * simpl in *. apply notin_singleton_1 in Hfv. unfold vswap. default_simp. (** If [t] is a variable, say [z], then [x' <> z] because [x'] does not occur in the set of free variables of [t] by hypothesis. Therefore, [fv_nom (swap x y (n_var z))] is equal to one of these variables, and we conclude because all of them are different from [x']. *)
      * simpl in *. case (x' == z). (** If [t] is an abstraction, say [n_abs z t1], then  *)
        ** intro Heq. subst. apply notin_remove_1 in Hfv. simpl. unfold vswap. default_simp.
           + simpl. unfold vswap. default_simp.
           + simpl. default_simp.
           + simpl. unfold vswap. default_simp.
       --- assumption.
       --- assumption.
Qed. 

Lemma swap_remove_reduction: forall x y t,
    remove x (remove y (fv_nom (swap y x t))) [=] remove x (remove y (fv_nom t)).
Proof.
  induction t.
  - rewrite remove_symmetric. simpl. unfold vswap. default_simp.
    -- repeat rewrite remove_singleton_empty.
       repeat rewrite remove_empty. reflexivity.
    -- rewrite remove_symmetric. rewrite remove_singleton_empty.
       rewrite remove_symmetric. rewrite remove_singleton_empty.
       repeat rewrite remove_empty. reflexivity.
    -- rewrite remove_symmetric. reflexivity.
  - simpl. unfold vswap. default_simp.
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
  - simpl. unfold vswap. default_simp.
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
Proof. (** %\noindent {\bf Proof.}% The proof is by induction on the structure of [t].%\newline% *)
  intros x y t. induction t.
  (** %\noindent%$\bullet$ The first case is when [t] is a variable, say [x0]. By hypothesis [x0 <> x], and we need to show that [remove x (fv_nom (swap y x x0)) [=] remove y (fv_nom x0)]. There are two cases to consider: *)
  - intro Hfv. simpl in *. apply notin_singleton_1 in Hfv. unfold vswap. case (x0 == y).
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
    + subst. assert (H: vswap y x x = y).
      {
        unfold vswap. destruct (x == y).
        - assumption.
        - rewrite eq_dec_refl. reflexivity.
      }
      rewrite H. rewrite remove_symmetric. rewrite swap_symmetric. apply swap_remove_reduction.
    + unfold vswap. destruct (x0 == y).
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
    specialize (H1 (remove (vswap y x x0) (fv_nom (swap y x t1))) (fv_nom (swap y x t2)) x). rewrite H1.
    specialize (H2 (remove x0 (fv_nom t1)) (fv_nom t2) y). rewrite H2. apply Equal_union_compat.
    + unfold vswap. case (x0 == y); intros; subst.
      unfold vswap in H1. rewrite eq_dec_refl in H1. rewrite double_remove in *. apply IHt2 in Hfv. case (x == y); intros; subst.
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

(** ** $\alpha$-equivalence *)

(** As usual in the standard presentations of the $\lambda$-calculus, we work with terms modulo $\alpha$-equivalence. This means that $\lambda$-terms are identified up to the name of bound variables. For instance, all the terms $\lambda_x.x$, $\lambda_y.y$ and $\lambda_z.z$ are seen as the same term which corresponds to the identity function. Formally, the notion of $\alpha$-equivalence is defined by the following inference rules:

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

Each of these rules correspond to a constructor in the [aeq] inductive definition below: *)

Inductive aeq : n_sexp -> n_sexp -> Prop :=
| aeq_var : forall x, aeq (n_var x) (n_var x)
| aeq_abs_same : forall x t1 t2, aeq t1 t2 -> aeq (n_abs x t1)(n_abs x t2)
| aeq_abs_diff : forall x y t1 t2, x <> y -> x `notin` fv_nom t2 -> aeq t1 (swap y x t2) -> aeq (n_abs x t1) (n_abs y t2)
| aeq_app : forall t1 t2 t1' t2', aeq t1 t1' -> aeq t2 t2' -> aeq (n_app t1 t2) (n_app t1' t2')
| aeq_sub_same : forall t1 t2 t1' t2' x, aeq t1 t1' -> aeq t2 t2' -> aeq ([x := t2] t1) ([x := t2'] t1')
| aeq_sub_diff : forall t1 t2 t1' t2' x y, aeq t2 t2' -> x <> y -> x `notin` fv_nom t1' -> aeq t1 (swap y x t1') -> aeq ([x := t2] t1) ([y := t2'] t1').
Notation "t =a u" := (aeq t u) (at level 60).
(* begin hide *)
Hint Constructors aeq.
(* end hide *)

(** In what follows, we use a infix notation for $\alpha$-equivalence in the Coq code. Therefore, we write [t =a u] instead of [aeq t u]. The above notion defines an equivalence relation over the set [n_sexp] of nominal expressions with explicit substitutions, %{\it i.e.}% the [aeq] relation is reflexive, symmetric and transitive. *)
(* begin hide *)
Example aeq1 : forall x y, x <> y -> (n_abs x (n_var x)) =a (n_abs y (n_var y)).
Proof.
  intros.
  eapply aeq_abs_diff; auto.
  simpl; unfold vswap; default_simp.
Qed.

Lemma aeq_var_2 : forall x y, (n_var x) =a (n_var y) -> x = y.
Proof.
  intros. inversion H; subst. reflexivity.
Qed.
(* end hide *)
(** In addition, $\alpha$-equivalent terms have the same size, and the same set of free variables: *)

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
  - simpl. unfold vswap. case (x0 == x); intros; subst.
    -- apply aeq_abs_same. assumption.
    -- case (x0 == y); intros; subst.
       --- apply aeq_abs_same. assumption.
       --- apply aeq_abs_same. assumption.
  - simpl. unfold  vswap. default_simp.
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
           rewrite swap_equivariance. unfold vswap. default_simp.
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
  - simpl. unfold vswap. default_simp.
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
           rewrite swap_equivariance. unfold vswap. default_simp.
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
    -- simpl in H. unfold vswap in H. default_simp.
    -- simpl in H. inversion H.
    -- simpl in H. inversion H.
    -- simpl in H. inversion H.
  - intros. induction t2.
    -- simpl in H. inversion H.
    -- simpl in H. inversion H.
       --- unfold vswap in *. default_simp.
           + specialize (IHt1 t2 x0 y). apply aeq_abs_same.
             apply IHt1. assumption.
           + specialize (IHt1 t2 x0 y). apply aeq_abs_same.
             apply IHt1. assumption.
           + specialize (IHt1 t2 x0 y). apply aeq_abs_same.
             apply IHt1. assumption.
       --- unfold vswap in *. default_simp.
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
       --- simpl in *; unfold vswap in *. default_simp.
           + apply aeq_sub_same.
             ++ apply IHt1_1 with x0 y. assumption.
             ++ apply IHt1_2 with x0 y. assumption.
           + apply aeq_sub_same.
             ++ apply IHt1_1 with x0 y. assumption.
             ++ apply IHt1_2 with x0 y. assumption.
           + apply aeq_sub_same.
             ++ apply IHt1_1 with x0 y. assumption.
             ++ apply IHt1_2 with x0 y. assumption.
       --- simpl in *; unfold vswap in *. default_simp.
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

(** The key point of the nominal approach is that the swap operation is stable under $\alpha$-equivalence in the sense that, $t_1 =_\alpha t_2$ if, and only if $\swap{x}{y}{t_1} =_\alpha \swap{x}{y}{t_2}, \forall t_1, t_2, x, y$. Note that this is not true for renaming substitutions: in fact, $\lambda_x.z =_\alpha \lambda_y.z$, but $(\lambda_x.z)\msub{z}{x} = \lambda_x.x \neq_\alpha \lambda_y.x (\lambda_y.z)\msub{z}{x}$, assuming that $x \neq y$. This stability result is formalized as follows: *)

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
    unfold vswap.
    destruct (x == x'); subst.
    + apply notin_singleton_is_false in H1.
      contradiction.
    + destruct (x == y); subst.
      * apply notin_singleton_is_false in H2.
        contradiction. 
      * apply aeq_refl.
  - intros x' y H1 H2.
    simpl in *.
    unfold vswap.
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
    unfold vswap.
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

(** There are several interesting auxiliary properties that need to be proved before achieving the substitution lemma. In what follows, we refer only to the tricky or challenging ones, but the interested reader can have a detailed look in the source files. Note that, swaps are introduced in proofs by the rules $\mbox{\it aeq}\_\mbox{\it abs}\_\mbox{\it diff}$ and $\mbox{\it aeq}\_\mbox{\it sub}\_\mbox{\it diff}$. As we will see, the proof steps involving these rules are trick because a naïve strategy can easily get blocked in a branch without proof. The following lemma states the conditions for two swaps to be merged: *)

Lemma aeq_swap_swap: forall t x y z, z `notin` fv_nom t -> x `notin` fv_nom t -> (swap z x (swap x y t)) =a (swap z y t).
Proof.
  intros. case (x == z); intros; subst. (** %\noindent{\bf Proof.}% The proof is by case analysis on the variables [x], [y] and [z]. If [x = z] then  the external swap of the LHS is trivial, and the terms on both LHS and RHS are equal. *)
  - rewrite swap_id; apply aeq_refl.
  - case (y == z); intros; subst. (** When [x <> z] then we compare [y] and [z]. If [y = z] then we can use the fact that swap is involutive and reduce the LHS to [t], and the RHS also reduces to [t] since the swap is trivial. *)
    -- replace (swap x z t) with (swap z x t).
       --- rewrite swap_involutive; rewrite swap_id. apply aeq_refl.
       --- rewrite swap_symmetric; reflexivity.
    -- case (x == y); intros; subst. (** When [y <> z] then we compare [x] and [y]. If [x = y] then the internal swap of the LHS is trivial and both sides are equal to [swap z y t]. *)
       --- rewrite swap_id; apply aeq_refl.
       --- rewrite shuffle_swap. (** Finally, if [x <> y], %{\it i.e.}% all [x], [y] and [z] are different from each other, then *)
           + apply aeq_swap. apply swap_reduction; assumption.
           + apply aux_not_equal; assumption.
           + assumption.
Qed.

(** * The metasubstitution operation of the $\lambda$-calculus *)

(** The main operation of the $\lambda$-calculus is the $\beta$-reduction that express how to evaluate a function applied to a given argument: $(\lambda_x.t)\ u \to_{\beta} \metasub{t}{x}{u}$. In a less formal context, the concept of $\beta$-reduction means that the result of evaluating the function $(\lambda_x.t)$ with argument $u$ is obtained by substituting $u$ for the free ocurrences of the variable $x$ in $t$. Moreover, it is a capture free substitution in the sense that no free variable becomes bound after the substitution. This operation is in the meta level because it is outside the grammar of the $\lambda$-calculus, and that's why it is called metasubstitution. As a metaoperation, its definition usually comes with a degree of informality. For instance, Barendregt%\cite{barendregtLambdaCalculusIts1984}% defines it as follows: %\vspace{.5cm}%
$\metasub{t}{x}{u} = \left\{
 \begin{array}{ll}
  u, & \mbox{ if } t = x; \\
  y, & \mbox{ if } t = y \mbox{ and } x \neq y; \\
  \metasub{t_1}{x}{u}\ \metasub{t_2}{x}{u}, & \mbox{ if } t = \metasub{(t_1\ t_2)}{x}{u}; \\
  \lambda_y.(\metasub{t_1}{x}{u}), & \mbox{ if } t = \lambda_y.t_1.
 \end{array}\right.$ %\vspace{.5cm}%
%\noindent% where it is assumed the so called "Barendregt's variable convention": if $t_1, t_2, \ldots, t_n$ occur in a certain mathematical context (e.g. definition, proof), then in these terms all bound variables are chosen to be different from the free variables. This means that we are assumming that both $x \neq y$ and $y\notin fv(u)$ in the case $t = \lambda_y.t_1$. This approach is very convenient in informal proofs because it avoids having to rename bound variables. In order to formalize the capture free substitution of the $\lambda$-calculus, %{\it i.e.}% the metasubstitution, a renaming is performed whenever it is propagated inside a binder. In our case, there are two binders: the abstraction and the explicit substitution. 

Let $t$ and $u$ be terms, and $x$ a variable. The result of substituting $u$ for the free ocurrences of $x$ in $t$, written $t\msub{x}{u}$ is defined as follows:%\newline%
%\begin{equation}\label{msubst}
\metasub{t}{x}{u} = \left\{
 \begin{array}{ll}
  u, & \mbox{ if } t = x; \\
  y, & \mbox{ if } t = y \mbox{ and } x \neq y; \\
  \metasub{t_1}{x}{u}\ \metasub{t_2}{x}{u}, & \mbox{ if } t = \metasub{(t_1\ t_2)}{x}{u}; \\
  \lambda_x.t_1, & \mbox{ if } t = \lambda_x.t_1; \\
  \lambda_z.(\metasub{(\swap{y}{z}{t_1})}{x}{u}), & \mbox{ if } t = \lambda_y.t_1, x \neq y \mbox{ and } z\notin fv(\lambda_y.t_1)\cup fv(u) \cup \{x\}; \\
  \esub{t_1}{x}{\metasub{t_2}{x}{u}}, & \mbox{ if } t = \esub{t_1}{x}{t_2}; \\
  \esub{\metasub{(\swap{y}{z}{t_1})}{x}{u}}{z}{\metasub{t_2}{x}{u}}, & \mbox{ if } t = \esub{t_1}{y}{t_2}, x \neq y \mbox{ and } z\notin fv(\esub{t_1}{y}{t_2})\cup fv(u) \cup \{x\}.
 \end{array}\right.
\end{equation}%

Note that this function is not structurally recursive due to the swaps in the recursive calls. A structurally recursive version of the function [subst_rec_fun] can be found in the file [nominal.v] of the [Metalib] library%\footnote{\url{https://github.com/plclub/metalib}}%, but it uses the size of the term in which the substitution will be performed as an extra argument that decreases with each recursive call. We write [[x:=u]t] instead of [subst_rec_fun t u x] in the Coq code to represent $\metasub{t}{x}{u}$. The corresponding Coq code is as follows: *)

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
Notation "{ x := u } t" := (m_subst u x t) (at level 60).

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

(** The following lemma states that if $x \notin fv(t)$ then $\metasub{t}{x}{u} =_\alpha t$. In informal proofs the conclusion of this lemma is usually stated as a syntactic equality, %{\i.e.}% $\metasub{t}{x}{u} = t$ instead of the $\alpha$-equivalence, but due to the changes of the names of the bound variables when the metasubstitution is propagated inside an abstraction or inside an explicit substitution, syntactic equality does not hold here. *)

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

(** We will now prove some stability results for the metasubstitution w.r.t. $\alpha$-equivalence. More precisely, we will prove that if $t =_\alpha t'$ and $u =_\alpha u'$ then $\metasub{t}{x}{u} =_\alpha \metasub{t'}{x}{u'}$, where $x$ is any variable and $t, t', u$ and $u'$ are any [n_sexp] terms. This proof is split in two steps: firstly, we prove that if $u =_\alpha u'$ then $\metasub{t}{x}{u} =_\alpha \metasub{t}{x}{u'}, \forall x, t, u, u'$; secondly, we prove that if $t =_\alpha t'$ then $\metasub{t}{x}{u} =_\alpha \metasub{t'}{x}{u}, \forall x, t, t', u$. These two steps are then combined through the transitivity of the $\alpha$-equivalence relation. Nevertheless, this task were not straighforward. Let's follow the steps of our first trial.*)

Lemma aeq_m_subst_in_trial: forall t u u' x, u =a u' -> ([x := u] t) =a ([x := u'] t).
Proof.
  induction t using n_sexp_induction. (** %\noindent{\bf Proof.}% The proof is done by induction on the size of the term [t].*)
  - intros u u' x' Haeq. unfold m_subst. repeat rewrite subst_rec_fun_equation. destruct (x' == x).
    + assumption.
    + apply aeq_refl.
  - intros u u' x Haeq. unfold m_subst in *. repeat rewrite subst_rec_fun_equation. destruct (x == z). (** The interesting case is when [t] is an abstraction, %{\it i.e.}% $t = \lambda_y.t_1$. We need to prove that $\metasub{(\lambda_y.t_1)}{x}{u} =_\alpha \metasub{(\lambda_y.t_1)}{x}{u'}$.*)      
    + apply aeq_refl. (** If $x = y$ then the result is trivial.*)
    + destruct (atom_fresh (union (fv_nom u) (union (fv_nom (n_abs z t)) (singleton x)))). destruct (atom_fresh (union (fv_nom u') (union (fv_nom (n_abs z t)) (singleton x)))). case (x0 == x1). (** Suppose $x \neq y$. The metasubstitution will be propagated inside the abstraction on each side of the $\alpha$-equation, after generating a new name for each side. The new goal is then $\lambda_{x_0}.\metasub{(\swap{y}{x_0}{t_1})}{x}{u} =_\alpha \lambda_{x_1}.\metasub{(\swap{y}{x_1}{t_1})}{x}{u'}$, where $x_0 \notin fv(\lambda_y.t_1) \cup fv(u) \cup \{x\}$ and $x_1 \notin fv(\lambda_y.t_1) \cup fv(u') \cup \{x\}$. The variables $x_0$ and $x_1$ are either the same or different.*)
      * intro Heq. subst. apply aeq_abs_same. apply H. (** In the former case the result is trivial because $u =_\alpha u'$. *)
        ** reflexivity.
        ** assumption.
      * intro Hneq. apply aeq_abs_diff. (** In the latter case, $x_0 \neq x_1$ and we need to prove that $\metasub{(\swap{y}{x_0}{t_1})}{x}{u} =_\alpha \swap{x_0}{x_1}{(\metasub{(\swap{y}{x_1}{t_1})}{x}{u'})}$.*)
        ** assumption.
        ** admit.
        ** Abort. (** Therefore, we need to propagate the swap over the metasubstitution before been able to apply the induction hypothesis. The propagation of the swap over the metasubstitution is stated by the following lemma:

%\begin{lemma} Let $t,u$ be terms, and $x,y,z$ variables. Then
 $\swap{y}{z}{(\metasub{t}{x}{u})} =_\alpha \metasub{(\swap{y}{z}{t})}{\vswap{y}{z}{x}}{\swap{y}{z}{u}}$.
\end{lemma}%

%\noindent% whose corresponding Coq version is given by: %\newline% *)

Lemma swap_m_subst: forall t u x y z, swap y z ([x := u]t) =a ([(vswap y z x) := (swap y z u)] (swap y z t)).
Proof.
  induction t using n_sexp_induction. (** %\noindent{\bf Proof.}% The proof is by induction on the size of the term [t].*)
  - intros u x' y z. unfold m_subst. rewrite subst_rec_fun_equation. destruct (x' == x) eqn:H.
    + subst. simpl. rewrite subst_rec_fun_equation. rewrite eq_dec_refl. apply aeq_refl.
    + simpl. apply aeq_sym. rewrite subst_rec_fun_equation. clear H. apply (swap_neq y z) in n. destruct (vswap y z x' == vswap y z x).
      * contradiction.
      * apply aeq_refl.
  - intros u x y z'. unfold m_subst. rewrite subst_rec_fun_equation. destruct (x == z) eqn:Hxz. (** The interesting case is the abstraction, where we need to prove that $\swap{y}{z}{(\metasub{(\lambda_w.t_1)}{x}{u})} =_\alpha \metasub{(\swap{y}{z}{\lambda_w.t_1})}{\vswap{y}{z}{x}}{\swap{y}{z}{u}}$. On the left hand side, we can propagate the metasubstitution over the abstraction in the case that $x \neq w$ (the other is straighforward) and the new goal after the propagation of the swap over the abstraction is $\lambda_{\vswap{y}{z}{w'}}.\swap{y}{z}{(\metasub{\swap{w}{w'}{t_1}}{x}{u})} =_\alpha \metasub{(\lambda_{\vswap{y}{z}{w}}.\swap{y}{z}{t_1})}{\vswap{y}{z}{x}}{\swap{y}{z}{u}}$, where $w' \notin fv(\lambda_w.t_1) \cup fv(u) \cup \{x\}$.*)
    + subst. simpl. rewrite subst_rec_fun_equation. rewrite eq_dec_refl. apply aeq_refl.
    + destruct (atom_fresh (union (fv_nom u) (union (fv_nom (n_abs z t)) (singleton x)))). simpl. clear Hxz. pose proof n as Hxz. apply (swap_neq y z') in n. apply aeq_sym. rewrite subst_rec_fun_equation. destruct (vswap y z' x == vswap y z' z).
      * contradiction.
      * destruct (atom_fresh
       (union (fv_nom (swap y z' u))
          (union (fv_nom (n_abs (vswap y z' z) (swap y z' t))) (singleton (vswap y z' x))))). case (x1 == (vswap y z' x0)). (** Now we propagate the metasubstitution over the abstraction in the right hand side term. Since $x\neq w$, we get $\vswap{y}{z}{x} \neq \vswap{y}{z}{w}$ and a renaming is necessary. After the renaming to a new name, say $w''$, such that $w'' \notin fv(\lambda_{\vswap{y}{z}{w}}.\swap{y}{z}{t_1}) \cup fv(\swap{y}{z}{u}) \cup \{\vswap{y}{z}{x}\}$, we get the following goal $\lambda_{\vswap{y}{z}{w'}}.\swap{y}{z}{(\metasub{\swap{w}{w'}{t_1}}{x}{u})} =_\alpha \lambda_{w''}.\metasub{(\swap{w''}{\vswap{y}{z}{w}}{(\swap{y}{z}{t_1})})}{\vswap{y}{z}{x}}{\swap{y}{z}{u}}$. We consider two cases: either $w'' = \vswap{y}{z}{w'}$ or $w'' \neq \vswap{y}{z}{w'}$.*) 
        ** intro Heq. subst. apply aeq_abs_same. unfold m_subst in *. apply aeq_sym. rewrite <- swap_equivariance. apply H. reflexivity. 
        ** intro Hneq. apply aeq_abs_diff.
           *** assumption.
           *** admit.
           *** apply aeq_sym. unfold m_subst in H. apply aeq_trans with (swap (vswap y z' x0) x1 (subst_rec_fun (swap y z' (swap z x0 t)) (swap y z' u) (vswap y z' x))). (** In the former case, we can apply the rule $\mbox{\it aeq}\_\mbox{\it abs}\_\mbox{\it same}$ and we get $\swap{y}{z}{(\metasub{(\swap{w}{w'}{t_1})}{x}{u})} =_\alpha \metasub{(\swap{w''}{\vswap{y}{z}{w}}{(\swap{y}{z}{t_1})})}{\vswap{y}{z}{x}}{\swap{y}{z}{u}}$ that can be proved by the induction hypothesis.*)
               **** apply aeq_swap. rewrite H.
                    ***** apply aeq_refl. Abort. (** When $w'' \neq \vswap{y}{z}{w'}$, the application of the rule $\mbox{\it aeq}\_\mbox{\it abs}\_\mbox{\it diff}$ generates the goal $\swap{w''}{\vswap{y}{z}{w'}}{\swap{y}{z}{(\metasub{\swap{w}{w'}{t_1}}{x}{u})}} =_\alpha \metasub{(\swap{w''}{\vswap{y}{z}{w}}{(\swap{y}{z}{t_1})})}{\vswap{y}{z}{x}}{\swap{y}{z}{u}}$. We can use the induction hypothesis to propagate the swap inside the metasubstitution, and then we get an $\alpha$-equality with metasubstitution as main operation on both sides, and whose correspondent components are $\alpha$-equivalent. In a more abstract way, we have to prove an $\alpha$-equality of the form $\metasub{t}{x}{u} =_\alpha \metasub{t'}{x}{u'}$, where $t =_\alpha t'$ and $u =_\alpha u'$. The problem is that we cannot rewrite $\alpha$-equalities inside metasubstitution unless we prove some special lemmas stating the compatibilities between them using the [Equations] library or something similar. Alternatively, if we decide to analise the metasubtitution componentwise, %{\it i.e.}% as stated in a lemma similar to [aeq_m_subst_in_trial], we get a circular proof problem because both [aeq_m_subst_in_trial] and [swap_m_subst] depend on each other to be proved. We will present a solution that do not use any additional library, but it adds the following axiom to the formalization:*)
                  
Axiom Eq_implies_equality: forall s s': atoms, s [=] s' -> s = s'.

(** This axiom transform a set equality into a syntactic equality. This will allow us to rewrite sets of atoms in a more flexible way. To show how it works, we will start proving the lemma [aeq_m_subst_in] without the need of the lemma [swap_m_subst]:*)

Lemma aeq_m_subst_in: forall t u u' x, u =a u' -> ([x := u] t) =a ([x := u'] t).
Proof.
  induction t using n_sexp_induction. (** %\noindent{\bf Proof.}% The proof is by induction on the size of the term [t].*)
  - intros u u' x' Haeq. pose proof Haeq as Hfv. apply aeq_fv_nom in Hfv. apply Eq_implies_equality in Hfv. unfold m_subst in *. repeat rewrite subst_rec_fun_equation. destruct (x' == x).
    + assumption.
    + reflexivity. 
  - intros u u' x Haeq. pose proof Haeq as Hfv. apply aeq_fv_nom in Hfv. apply Eq_implies_equality in Hfv. unfold m_subst in *. repeat rewrite subst_rec_fun_equation. rewrite Hfv. destruct (atom_fresh (union (fv_nom u') (union (fv_nom (n_abs z t)) (singleton x)))). destruct (x == z). (** The interesting case is the abstraction. We have by hypothesis that $u =_\alpha u'$ therefore both $u$ and $u'$ have the same set of free variables by lemma [aeq_fv_nom]. With the axiom [Eq_implies_equality], we can replace the set $fv(u)$ by $fv(u')$, or vice-versa, in such a way that instead of generating two new names for the propagation of the metasusbstitutions inside the abstractions, we need just one new name and there is no more the case where the binders of the abstractions were different names. *)
      * apply aeq_refl.
      * apply aeq_abs_same. apply H.
        ** reflexivity.
        ** assumption.
  - intros u u' x Haeq. unfold m_subst in *. rewrite subst_rec_fun_equation. apply aeq_sym. rewrite subst_rec_fun_equation. apply aeq_app.
    + apply IHt1. apply aeq_sym. assumption.
    + apply IHt2. apply aeq_sym. assumption.
  - intros u u' x Haeq. unfold m_subst in *. rewrite subst_rec_fun_equation. apply aeq_sym. rewrite subst_rec_fun_equation. pose proof Haeq as Hfv. apply aeq_fv_nom in Hfv. apply Eq_implies_equality in Hfv. rewrite Hfv. destruct (atom_fresh (union (fv_nom u') (union (fv_nom (n_sub t1 z t2)) (singleton x)))). destruct (x == z). (** The case of the explicit substitution is similar, and with this strategy we avoid the rules $\mbox{\it aeq}\_\mbox{\it abs}\_\mbox{\it diff}$ and $\mbox{\it aeq}\_\mbox{\it sub}\_\mbox{\it diff}$ that introduce swappings. $\hfill\Box$*)
    + apply aeq_sub_same.
      * apply aeq_refl.
      * apply IHt1. apply aeq_sym. assumption.
    + apply aeq_sub_same.
      * apply H.
        ** reflexivity.
        ** apply aeq_sym. assumption.
      * apply IHt1. apply aeq_sym. assumption.
Qed. (** %\newline% *)
       
(* begin hide *)
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
(* end hide *)

(** The next lemma, named [aeq_m_subst_out] will benefit the strategy used in the previous proof, but it is not straightfoward. In the proof below, we will mostly use Coq notation, instead of the metanotation of the previous proof. We believe that at this point of the work, even the readers not familiar with Coq, can easily understand the Coq code interleaved with metanotation. *)
Lemma aeq_m_subst_out: forall t t' u x, t =a t' -> ([x := u] t) =a ([x := u] t').
Proof.
  induction t as [y | t1 y | t1 t2 | t1 y t2] using n_sexp_induction . (** %\noindent{\bf Proof.}% The proof is by induction on the size of the term [t]. *)
  - intros t' u x' Haeq. inversion Haeq; subst. apply aeq_refl.
  - intros t' u x Haeq. inversion Haeq; subst. (** The interesting case is the abstraction. The are two cases based on the definition of the $\alpha$-equivalence relation: either the binders have the same name or they are different. *)
    + pose proof Haeq as Hfv. apply aeq_fv_nom in Hfv. simpl in *. apply Eq_implies_equality in Hfv. unfold m_subst in *. repeat rewrite subst_rec_fun_equation. simpl. rewrite Hfv. destruct (atom_fresh (union (fv_nom u) (union (remove y (fv_nom t2)) (singleton x)))). destruct (x == y). (** In the former case, we have to prove [ ([x := u] n_abs y t1) =a ([x := u] n_abs y t2)] assumming that [t1 =a t2]. In both sides of the $\alpha$-equation, the metasubstitutition need to be propagated over the abstraction, and according to our definition of metasubstitution, one name will be generated for each propagation. The new name to be generate for the term [[x := u] (n_abs y t1)] (lhs) is such that it is not in the set $fv(\lambda_y.t_1)\cup fv(u) \cup \{x\}$, while the new name to be generated for the term [[x := u] (n_abs y t2)] (rhs) is such that it is not in the set $fv(\lambda_y.t_2)\cup fv(u) \cup \{x\}$. Since [t1 =a t2], by lemma [aeq_fv_nom] the set of free variables of [t1] is equal to the set of free variables of [t2], and therefore, we can generate just one new name for both propagations of the metasubstitution. *)
      * assumption.
      * apply aeq_abs_same. apply H. (** If this new name is [x0] then the new goal to be proved is [n_abs x0 (subst_rec_fun (swap y x0 t1) u x) =a n_abs x0 (subst_rec_fun (swap y x0 t2) u x)], which can be proved by the induction hypothesis. *)
        ** reflexivity.
        ** apply aeq_swap. assumption.
    + pose proof Haeq as Hfv. apply aeq_fv_nom in Hfv. simpl in *. apply Eq_implies_equality in Hfv. unfold m_subst in *. case (y == x).
      * intro Heq. subst. rewrite subst_rec_fun_equation. rewrite eq_dec_refl. rewrite subst_rec_fun_equation. destruct (x == y0). (** If [y = x] then [x <> y0] and the metasubstitution [[x := u]] has no effect on the LHS, but it can be propagated on the RHS, %{\it i.e.}% over the abstraction [(n_abs y0 t2)] but it also has no effect in [t2] because [x] does not occur free in [t2]. *)
        ** contradiction.
        ** destruct (atom_fresh (union (fv_nom u) (union (fv_nom (n_abs y0 t2)) (singleton x)))). apply aeq_trans with (n_abs x0 (swap y0 x0 t2)).
           *** apply aeq_trans with (n_abs y0 t2).
               **** assumption.
               **** case (x0 == y0).
                    ***** intro Heq. subst. rewrite swap_id. apply aeq_refl.
                    ***** intro Hneq. pose proof n0 as Hx0. apply notin_union_2 in n0. apply notin_union_1 in n0. simpl in n0. apply notin_remove_1 in n0. destruct n0.
                    ****** symmetry in H0. contradiction.
                    ****** apply aeq_abs_diff.
                    ******* apply aux_not_equal. assumption.
                    ******* apply fv_nom_swap. assumption.
                    ******* rewrite (swap_symmetric _ y0 x0). rewrite swap_involutive. apply aeq_refl.
           *** apply aeq_abs_same. apply aeq_sym. apply m_subst_notin. repeat apply notin_union_2 in n0. apply notin_singleton_1 in n0. apply fv_nom_remove_swap; assumption. 
      * intro Hneq. case (y0 == x). (** If [y <> x] then the metasubstitution can be propagated over the abstraction of the LHS, and similarly we compare [x] with [y0] to see what happens in the RHS. *)
        ** intro Heq. apply aeq_sym in Haeq. apply aeq_abs_notin in Haeq.
           *** symmetry in Heq. subst. apply aeq_sym. rewrite subst_rec_fun_equation. rewrite eq_dec_refl. apply aeq_sym. apply aeq_trans with (n_abs y t1).
               **** apply m_subst_notin. simpl. apply notin_remove_2. assumption.
               **** apply aeq_abs_diff; assumption. (** When [y0 = x] then the metasubstitution has no effect on the abstraction of the RHS. On the LHS the metasubstitution is propagated since [y <> x] but, as in the previous case, it has no effect in [t1] because [y0] does not occur free in [t1].*)
           *** apply aux_not_equal. assumption.
        ** intro Hneq'. repeat rewrite subst_rec_fun_equation. simpl. rewrite Hfv. destruct (atom_fresh (union (fv_nom u) (union (remove y0 (fv_nom t2)) (singleton x)))). destruct (x == y). (** Now we have to prove that [[x := u](n_abs y t1) =a [x := u](n_abs y0 t2)], when [y <> x], [y0 <> x] and [n_abs y t1 =a n_abs y0 t2]. Since the set of free variables of [n_abs y t1] is equal to the set of free variables of [n_abs y0 t2], we can as in the previous case generate only one new name, say [x0] that fulfill the condition to propagate the metasubstitution on both sides of the $\alpha$-equation. More precisely, $x_0 \notin fv(\lambda_y.t1) \cup fv(u) \cup \{x\}$, and the goal to be proved is [n_abs x0 ([x := u](swap y x0 t1)) =a n_abs x0 ([x := u](swap y0 x0 t2))].*)
           *** symmetry in e. contradiction.
           *** destruct (x == y0).
               **** symmetry in e. contradiction.
               **** apply  aeq_abs_same. apply H. (** As just one new name was generated, there is no case where the binders of the abstractions are different. Remember that abstractions with different binders were the cause of the circularity problem in the proofs because the application of the rule [aeq_abs_diff] introduces a new swap that will be outside the metasubstitution in this case, whose solution would require a lemma of the form of [swap_m_subst]. Therefore, after an applycation of the rule [aeq_abs_same], we conclude with the induction hypothesis.*)
                    ***** reflexivity.
                    ***** apply (aeq_swap _ _ y x0) in H5. rewrite H5. case (x0 == y0).
                    ****** intro Heq. subst. rewrite swap_id. rewrite (swap_symmetric _ y y0). rewrite swap_involutive. apply aeq_refl.
                    ****** intro Hneq''. rewrite (swap_symmetric _ y x0). rewrite (swap_symmetric _ y0 y). rewrite (swap_symmetric _ y0 x0). apply notin_union_2 in n. apply notin_union_1 in n. apply notin_remove_1 in n. destruct n.
                    ******* symmetry in H0. contradiction.
                    ******* apply aeq_swap_swap; assumption.
  - intros t u x Haeq. inversion Haeq; subst. clear Haeq. unfold m_subst in *. rewrite subst_rec_fun_equation. apply aeq_sym. rewrite subst_rec_fun_equation. apply aeq_app.
    + apply aeq_sym. apply IHt2. assumption.
    + apply aeq_sym. apply IHt1. assumption.
  - intros t u x Haeq. inversion Haeq; subst. (** The explicit substitution operation is also interesting, but the proof strategy is similar to the one used in the abstraction case. $\hfill\Box$*)
    + unfold m_subst in *. rewrite subst_rec_fun_equation. apply aeq_sym. rewrite subst_rec_fun_equation. apply aeq_fv_nom in Haeq. apply Eq_implies_equality in Haeq. rewrite Haeq. destruct (atom_fresh (union (fv_nom u) (union (fv_nom (n_sub t1' t2 t2')) (singleton x)))). simpl in *. destruct (x == t2).
      * apply aeq_sub_same.
        ** apply aeq_sym. assumption.
        ** apply aeq_sym. apply IHt1. assumption.
      * apply aeq_sub_same.
        ** apply aeq_sym. apply H.
           *** reflexivity.
           *** apply aeq_swap. assumption.
        ** apply aeq_sym. apply IHt1. assumption.
    + unfold m_subst in *. rewrite subst_rec_fun_equation. apply aeq_sym. rewrite subst_rec_fun_equation. pose proof Haeq as Hfv. apply aeq_fv_nom in Hfv. apply Eq_implies_equality in Hfv. rewrite Hfv. destruct (atom_fresh (union (fv_nom u) (union (fv_nom (n_sub t1' y0 t2')) (singleton x)))). destruct (x == y0).
      * subst. destruct (y0 == t2).
        ** subst. contradiction.
        ** pose proof n as Hx0. repeat apply notin_union_2 in n. apply notin_singleton_1 in n. apply aeq_sym. apply aeq_sub_diff.
           *** apply IHt1. assumption.
           *** apply aux_not_equal. assumption.
           *** apply notin_union_2 in Hx0. apply notin_union_1 in Hx0. simpl in Hx0. apply notin_union_1 in Hx0. apply notin_remove_1 in Hx0. destruct Hx0.
               **** contradiction.
               ****assumption.
           *** apply aeq_trans with (swap t2 x0 t1).
               **** apply m_subst_notin. apply aeq_sym in Haeq. apply aeq_sub_notin in Haeq.
                    ***** apply fv_nom_remove_swap.
                    ****** assumption.
                    ****** apply aux_not_equal. assumption.
                    ****** assumption.
                    ***** assumption.
               **** apply aeq_trans with (swap t2 x0 (swap y0 t2 t1')).
                    ***** apply aeq_swap. assumption.
                    ***** rewrite (swap_symmetric _ t2 x0). rewrite (swap_symmetric _ y0 t2). rewrite (swap_symmetric _ y0 x0). apply aeq_swap_swap.
                    ****** apply notin_union_2 in Hx0. apply notin_union_1 in Hx0. simpl in Hx0. apply notin_union_1 in Hx0. apply notin_remove_1 in Hx0. destruct Hx0.
                    ******* contradiction.
                    ******* assumption.
                    ****** assumption.
      * destruct (x == t2).
        ** subst. pose proof n as Hx0. repeat apply notin_union_2 in n. apply notin_singleton_1 in n. apply aeq_sub_diff.
           *** apply aeq_sym. apply IHt1. assumption.
           *** apply aux_not_equal. assumption.
           *** rewrite <- Hfv in Hx0. apply notin_union_2 in Hx0. apply notin_union_1 in Hx0. simpl in Hx0. apply notin_union_1 in Hx0. apply notin_remove_1 in Hx0. destruct Hx0.
               **** contradiction.
               **** assumption.
           *** case (x0 == y0). 
               **** intro Heq. subst. rewrite swap_id. apply aeq_trans with t1'.
                    ***** apply m_subst_notin. assumption.
                    ***** apply (aeq_swap _ _ t2 y0) in H7. rewrite H7. rewrite (swap_symmetric _ t2 y0). rewrite swap_involutive. apply aeq_refl.
               **** intro Hneq. apply aeq_trans with (swap y0 x0 t1').
                    ***** apply m_subst_notin. apply fv_nom_remove_swap; assumption.
                    ***** apply (aeq_swap _ _ t2 x0) in H7. rewrite H7. apply aeq_sym. rewrite (swap_symmetric _ t2 x0). rewrite (swap_symmetric _ y0 t2). rewrite (swap_symmetric _ y0 x0). apply aeq_swap_swap.
                    ******  apply notin_union_2 in Hx0. apply notin_union_1 in Hx0. simpl in Hx0. apply notin_union_1 in Hx0. apply notin_remove_1 in Hx0. destruct Hx0.
                    ******* symmetry in H0. contradiction.
                    ******* assumption.
                    ****** assumption.
        ** apply aeq_sub_same.
           *** apply H.
               **** apply aeq_size in H7. symmetry. rewrite swap_size_eq in H7. assumption.
               **** case (x0 == y0). 
                    ***** intro Heq. subst. rewrite swap_id. apply (aeq_swap1 _ _ y0 t2) in H7. rewrite (swap_symmetric _ t2 y0). rewrite H7. rewrite swap_involutive. apply aeq_refl.
                    ***** intro Hneq. apply (aeq_swap1 _ _ t2 x0) in H7. rewrite H7. apply aeq_sym. rewrite (swap_symmetric _ t2 x0). rewrite (swap_symmetric _ y0 t2). rewrite (swap_symmetric _ y0 x0). apply aeq_swap_swap.
                    ****** apply notin_union_2 in n. apply notin_union_1 in n. simpl in n. apply notin_union_1 in n. apply notin_remove_1 in n. destruct n.
                    ******* symmetry in H0. contradiction.
                    ******* assumption.
                    ****** assumption.
           *** apply aeq_sym. apply IHt1. assumption.
Qed.

(** As a corollary, one can join the lemmas [aeq_m_subst_in] and [aeq_m_subst_out] as follows:*)

Corollary aeq_m_subst_eq: forall t t' u u' x, t =a t' -> u =a u' -> ([x := u] t) =a ([x := u'] t').
Proof.
  intros t t' u u' x H1 H2. apply aeq_trans with ([x:=u]t').
  - apply aeq_m_subst_out. assumption.
  - apply aeq_m_subst_in. assumption.
Qed.

(** Now, we show how to propagated a swap inside metasubstitutions using the decomposition of the metasubstitution provided by the corollary [aeq_m_subst_eq].%\newline% *)

Lemma swap_subst_rec_fun: forall x y z t u, swap x y (subst_rec_fun t u z) =a subst_rec_fun (swap x y t) (swap x y u) (vswap x y z).
Proof.
  (** %\noindent{\bf Proof.}% Firstly, we compare [x] and [y], since the case [x = y] is trivial.*)
  intros x y z t u. destruct (x == y). 
  - subst. repeat rewrite swap_id. rewrite vswap_id. apply aeq_refl.
    (** The proof proceeds by induction on the size of the term [t], assuming that [x <> y]. The tricky cases are the abstraction and explicit substitution. *)
  - generalize dependent u. generalize dependent z. generalize dependent y. generalize dependent x. induction t as  [y | t1 y | t1 t2 | t1 t2 y] using n_sexp_induction.    
    + intros x' y' Hneq z u. rewrite subst_rec_fun_equation. destruct (z == y).
      * subst. simpl swap at 2. rewrite subst_rec_fun_equation. rewrite eq_dec_refl. apply aeq_refl.
      * pose proof n as Hswap. apply (swap_neq x' y') in n. simpl swap at 2. rewrite subst_rec_fun_equation. destruct (vswap x' y' z == vswap x' y' y).
        ** contradiction.
        ** simpl swap. apply aeq_refl.
    + intros x y' Hneq z u. simpl. case (y == z). (** In the abstraction case, %{\it i.e.}% when $t = \lambda_{y'}.t_1$ then we must prove that [swap x y ([z := u](n_abs y' t1)) =a [(vswap x y z) := (swap x y u)](swap x y (n_abs y' t1))], and the induction hypothesis states that a swap can be propagated inside a metasubstitution whose body is a term with the same size as [t1]. Firstly, we compare the variables [y'] and [z] to check whether we should propagate the metasubstitution inside the abstraction of the LHS. *)
      * intro Heq. subst. repeat rewrite subst_rec_fun_equation. repeat rewrite eq_dec_refl. simpl. apply aeq_refl. (** When [y' = z] the metasubstitution is erased according to the definition %(\ref{msubst})% on both sides of the $\alpha$-equation and we are done.*)
      * intro Hneq'. repeat rewrite subst_rec_fun_equation. destruct (z == y). (** When [y' <> z] then the metasubstitutions on both sides of the $\alpha$-equation need to be propagated inside the corresponding abstractions. In order to do so, a new name need to be created. Note that in this case, it is not possible to create a unique name for both sides because the name of the LHS cannot belong to the set $fv(\lambda_y'.t_1) \cup fv(u) \cup \{z\}$, while the name of the RHS cannot belong to the set $fv(\swap{x}{y}{\lambda_y'.t_1}) \cup fv(\swap{x}{y}{u}) \cup \{\vswap{x}{y}{z}\}$.*)
        ** symmetry in e. contradiction.
        ** destruct (vswap x y' z == vswap x y' y).
           *** apply (swap_neq x y') in n. contradiction.
           *** simpl. destruct (atom_fresh (union (fv_nom u) (union (remove y (fv_nom t1)) (singleton z)))). destruct (atom_fresh (union (fv_nom (swap x y' u)) (union (remove (vswap x y' y) (fv_nom (swap x y' t1))) (singleton (vswap x y' z))))). simpl. case (x1 == vswap x y' x0). (** Let [x0] be a new name that is not in the set $fv(\lambda_y'.t_1) \cup fv(u) \cup \{z\}$, and [x1] a new name that is not in the set $fv(\swap{x}{y}{\lambda_y'.t_1}) \cup fv(\swap{x}{y}{u}) \cup \{\vswap{x}{y}{z}\}$. After renaming and propagating the metasubstitutions inside the abstractions, the current goal is [n_abs (vswap x y x0) (swap x y ([z := u](swap y' x0 t1))) =a n_abs x1 ([(vswap x y z) := (swap x y u)](swap (vswap x y y') x1 (swap x y t1)))]. We proceed by comparing [x1] with [(vswap x y x0)].*)
               **** intro Heq. subst. apply aeq_abs_same. rewrite H. rewrite <- swap_equivariance. apply aeq_refl. (** If [x1 = (vswap x y x0)] then we use the induction hypothesis to propagate the swap inside the metasubstitution in the LHS and the current goal is [[(vswap x y z) := (swap x y u)](swap x y (swap y' x0 t1)) =a
  [(vswap x y z) := (swap x y u)](swap (vswap x y y') (vswap x y x0) (swap x y t1))] that is proved by the swap equivariance lemma [swap_equivariance].*)
               ***** reflexivity.
               ***** assumption.
               **** intro Heq''. apply aeq_abs_diff. (** If [x1 <> (vswap x y x0)] then by the rule [aeq_abs_diff] we have to prove that the variable [vswap x y x0] is not in the set of free variables of the term [[(vswap x y z) := (swap x y u)](swap (vswap x y y') x1 (swap x y t1))] and that [swap x y ([z := u](swap y' x0 t1)) =a
  swap x1 (vswap x y' x0) ([(vswap x y z) := (swap x y' u)](swap (vswap x y' y) x1 (swap x y' t1)))].*)
                    ***** apply aux_not_equal. assumption.
                    ***** apply fv_nom_remove.
                    ****** apply notin_fv_nom_equivariance. apply notin_union_1 in n1. assumption.
                    ****** apply notin_remove_2. pose proof n1 as Hx0. case (y == x0).
                    ******** intro Heq. subst. apply fv_nom_swap. apply notin_union_2 in n2. apply notin_union_1 in n2. apply notin_remove_1 in n2. destruct n2.
                    ********* symmetry in H0. contradiction.
                    ********* assumption.
                    ******** intros Hneq'''. apply fv_nom_remove_swap.
                    ********* apply aux_not_equal. assumption.
                    ********* apply aux_not_equal. apply swap_neq. assumption.
                    ********* apply notin_union_2 in n1. apply notin_union_1 in n1. apply notin_remove_1 in n1. destruct n1.
                    ********** contradiction.
                    ********** apply notin_fv_nom_equivariance. assumption. (** The former condition is routine.*)
                    ***** rewrite H. (** The later condition is proved using the induction hypothesis twice to propagate the swaps inside the metasubstitutions on each side of the $\alpha$-equality. This swap has no effect on the variable of the metasubstitution, therefore we can apply lemma [aeq_m_subst_eq] and each generated case is proved by routine manipulation of swaps.*)
                    ****** apply aeq_sym. rewrite H.
                    ******* replace (vswap x1 (vswap x y' x0) (vswap x y' z)) with (vswap x y' z).
                    ******** apply aeq_m_subst_eq.
                    ********* rewrite (swap_symmetric _ x1 (vswap x y' x0)). rewrite (swap_symmetric _ (vswap x y' y) x1). case (x0 == y). 
                    *********** intro Heq. subst. rewrite (swap_symmetric _ (vswap x y' y) x1). rewrite swap_involutive. rewrite swap_id. apply aeq_refl.
                    *********** intro Hneq''. rewrite (swap_symmetric _ y x0). rewrite (swap_equivariance _ x y' x0 y). case (x1 == vswap x y' y). 
                    ************ intro Heq. subst. rewrite swap_id. apply aeq_refl.
                    ************ intro Hneq'''. apply aeq_swap_swap.
                    ************** apply notin_fv_nom_equivariance. apply notin_union_2 in n1. apply notin_union_1 in n1. apply notin_remove_1 in n1. destruct n1.
                    *************** symmetry in H0. contradiction.
                    *************** assumption.
                    ************** apply notin_union_2 in n2. apply notin_union_1 in n2. apply notin_remove_1 in n2. destruct n2.
                    *************** symmetry in H0. contradiction.
                    *************** assumption.
                    ********* apply swap_reduction.
                    ********** apply notin_union_1 in n2. assumption.
                    ********** apply notin_union_1 in n1. apply notin_fv_nom_equivariance. assumption.
                    ******** symmetry. unfold vswap at 1. destruct (vswap x y' z ==  x1).
                    ********* repeat apply notin_union_2 in n2. apply notin_singleton_1 in n2. contradiction.
                    ********* destruct (vswap x y' z == vswap x y' x0).
                    ********** repeat apply notin_union_2 in n1. apply notin_singleton_1 in n1. apply (swap_neq x y') in n1. contradiction.
                    ********** reflexivity.
                    ******* apply swap_size_eq.
                    ******* assumption.
                    ****** reflexivity.
                    ****** assumption.
    + intros x y H z u. rewrite subst_rec_fun_equation. simpl. apply aeq_sym. rewrite subst_rec_fun_equation. apply aeq_sym. apply aeq_app.
      * apply IHt2. assumption.
      * apply IHt1. assumption.
    + intros x y' Hneq z u. simpl. case (y == z). (** The case of the explicit substitution follows a similar strategy of the abstraction. The initial goal is to prove that [swap x y ([z := u](n_sub t1 y' t2)) =a [(vswap x y z) := (swap x y u)](swap x y (n_sub t1 y' t2))] and we start comparing the variables [y'] and [z].*)
      * intro Heq. subst. rewrite subst_rec_fun_equation. apply aeq_sym. rewrite subst_rec_fun_equation. repeat rewrite eq_dec_refl. simpl. apply aeq_sub_same. (** When [y' = z], the metasubstitution has no effect on the body of the metasubstitution but it can still be propagated to the term [t2]. Therefore, this case is proved using the induction hypothesis over [t2]. *)
        ** apply aeq_refl.
        ** apply aeq_sym. apply IHt1. assumption.
      * intro Hneq'. rewrite subst_rec_fun_equation. apply aeq_sym. rewrite subst_rec_fun_equation. destruct (z == y).
        ** symmetry in e. contradiction.
        ** destruct (vswap x y' z == vswap x y' y).
           *** apply (swap_neq x y') in n. contradiction.
           *** destruct (atom_fresh (union (fv_nom u) (union (fv_nom (n_sub t1 y t2)) (singleton z)))). destruct (atom_fresh (union (fv_nom (swap x y' u)) (union (fv_nom (n_sub (swap x y' t1) (vswap x y' y) (swap x y' t2))) (singleton (vswap x y' z))))). simpl in *. apply aeq_sym. case (x1 == vswap x y' x0). (** When [y' <> z], then the metasubstitutions are propagated on both sides of the $\alpha$-equation. Analogously to the abstraction case, one new name for each propagation is necessary. Let [x0] be a new name not in the set $fv(\esub{t1}{y'}{t2})\cup fv(u) \cup \{z\}$, and [x1], a new name not in the set $fv(\esub{\swap{x}{y}{t1}}{\vswap{x}{y}{y'}}{\swap{x}{y}{t2}})\cup fv(\swap{x}{y}{u}) \cup \{\vswap{x}{y}{z}\}$. After the propagation step, we have the goal [n_sub (swap x y ([z := u](swap y' x0 t1))) (vswap x y x0) (swap x y ([z := u]t2)) =a
  n_sub ([(vswap x y z) := (swap x y u)](swap (vswap x y y') x1 (swap x y t1))) x1
    ([(vswap x y z) := (swap x y u)](swap x y t2))]. We proceed by comparing [x1] and [(swap x y x0)].*)
               **** intro Heq. subst. apply aeq_sub_same. (** If [x1 = vswap x y x0] then after an application of the rule [aeq_sub_same], each component of the explicit substitution is proved by the induction hypothesis.*)
                    ***** rewrite <- swap_equivariance. apply H.
                    ****** reflexivity.
                    ****** assumption.
                    ***** apply IHt1. assumption.
               **** intro Hneq''. apply aeq_sub_diff.
                    ***** apply IHt1. assumption. (** If [x1 <> vswap x y x0] then we apply the rule [aeq_sub_diff] to decompose the explicit substitution in its components. The second component is straightforward  by the induction hypothesis.*)
                    ***** apply aux_not_equal. assumption.
                    ***** apply fv_nom_remove.
                    ****** apply notin_fv_nom_equivariance. apply notin_union_1 in n1. assumption.
                    ****** apply notin_remove_2. case (y == x0).
                    ******* intro Heq. subst. apply fv_nom_swap. apply notin_union_2 in n2. apply notin_union_1 in n2. apply notin_union_1 in n2. apply notin_remove_1 in n2. destruct n2.
                    ******** symmetry in H0. contradiction.
                    ******** assumption.
                    ******* intro Hneq'''. apply fv_nom_remove_swap.
                    ******** apply aux_not_equal. assumption.
                    ******** apply (swap_neq x y') in Hneq'''. apply aux_not_equal. assumption.
                    ******** apply notin_fv_nom_equivariance. apply notin_union_2 in n1. apply notin_union_1 in n1. apply notin_union_1 in n1. apply notin_remove_1 in n1. destruct n1.
                    ********* contradiction.
                    ********* assumption.
                    ***** rewrite H. (** The first component follows the strategy used in the abstraction case. The current goal, obtained after the application of the rule [aeq_sub_diff] is [swap x y ([z := u](swap y' x0 t1)) =a
  swap x1 (vswap x y x0) ([(vswap x y z) := (swap x y u)](swap (vswap x y y') x1 (swap x y t1)))]. The induction hypothesis is used twice to propagate the swap on both the LHS and RHS of the $\alpha$-equality. This swap has no effect on the variable of the metasubstitution, therefore we can apply lemma [aeq_m_subst_eq] and each generated case is proved by routine manipulation of swaps. $\hfill\Box$*)
                    ****** apply aeq_sym. rewrite H.
                    ******* replace (vswap x1 (vswap x y' x0) (vswap x y' z)) with (vswap x y' z).
                    ******** apply aeq_m_subst_eq.
                    ********* rewrite (swap_symmetric _ x1 (vswap x y' x0)). rewrite (swap_symmetric _ (vswap x y' y) x1). case (x0 == y). 
                    *********** intro Heq. subst. rewrite (swap_symmetric _ (vswap x y' y) x1). rewrite swap_involutive. rewrite swap_id. apply aeq_refl.
                    *********** intro Hneq'''. rewrite (swap_symmetric _ y x0). rewrite (swap_equivariance _ x y' x0 y). case (x1 == vswap x y' y). 
                    ************ intro Heq. subst. rewrite swap_id. apply aeq_refl.
                    ************ intro Hneq''''. apply aeq_swap_swap.
                    ************** apply notin_fv_nom_equivariance. apply notin_union_2 in n1. apply notin_union_1 in n1. apply notin_union_1 in n1. apply notin_remove_1 in n1. destruct n1.
                    *************** symmetry in H0. contradiction.
                    *************** assumption.
                    ************** apply notin_union_2 in n2. apply notin_union_1 in n2. apply notin_union_1 in n2. apply notin_remove_1 in n2. destruct n2.
                    *************** symmetry in H0. contradiction.
                    *************** assumption.
                    ********* apply swap_reduction.
                    ********** apply notin_union_1 in n2. assumption.
                    ********** apply notin_union_1 in n1. apply notin_fv_nom_equivariance. assumption.
                    ******** symmetry. unfold vswap at 1. destruct (vswap x y' z ==  x1).
                    ********* repeat apply notin_union_2 in n2. apply notin_singleton_1 in n2. contradiction.
                    ********* destruct (vswap x y' z == vswap x y' x0).
                    ********** repeat apply notin_union_2 in n1. apply notin_singleton_1 in n1. apply (swap_neq x y') in n1. contradiction.
                    ********** reflexivity.
                    ******* apply swap_size_eq.
                    ******* assumption.
                    ****** reflexivity.
                    ****** assumption.
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

(** The following lemmas state, respectively, what hapens when the variable in the meta-substitution is equal or different from the one in the abstraction. When it is equal, the meta-substitution is irrelevant. When they are different, we take a new variable that does not occur freely in the substituted term in the meta-substitution nor in the abstraction and is not the variable in the meta-substitution, and the abstraction of this new variable using the meta-substitution of the swap of the former variable in the meta-substitution is alpha-equivalent to the original meta-substitution of the abstraction. The proofs were straightforward from the definition of the meta-substitution, each case being respectively each one in the definition. %\newline%*)
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
      * rewrite swap_subst_rec_fun. replace (vswap z x0 x) with x.
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
        ** apply eq_sym. unfold vswap. destruct (x == z).
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

(** The following lemmas are the equivalent version of the two previous lemmas for the case of the explicit substitution. They state, respectively, what hapens when the variable in the meta-substitution is equal or different from the one in the explicit substitution. When it is equal, the meta-substitution is irrelevant on [t1], but it is applied to [e2]. When they are different, we take a new variable that does not occur freely in the substituted term in the meta-substitution nor in the substitution and is not the variable in the meta-substitution, and the explicit substitution of this new variable using the meta-substitution of the swap of the former variable in the meta-substitution in [e11] and the application of the original meta_substitution in [e12] is alpha-equivalent to the original meta-substitution of the explicit substitution. The proofs are straighforward from the definition of the meta-substitution, each case being respectively each one in the definition. %\newline%*)

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
      * rewrite swap_subst_rec_fun. replace (vswap z x0 x) with x.
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
        ** apply eq_sym. unfold vswap. destruct (x == z).
           *** subst. repeat apply notin_union_2 in H2. apply notin_singleton_1 in H2. contradiction.
           *** destruct (x == x0). 
               **** subst. repeat apply notin_union_2 in n0. apply notin_singleton_1 in n0. contradiction.
               **** reflexivity.
Qed.
 
(** * The substitution lemma for the metasubstitution *)

(** In the pure $\lambda$-calculus, the substitution lemma is probably the first non trivial property. In our framework, we have defined two different substitution operation, namely, the metasubstitution denoted by [[x:=u]t] and the explicit substitution that has [n_sub] as a constructor. In what follows, we present the main steps of our proof of the substitution lemma for the metasubstitution operation: *)

Lemma m_subst_lemma: forall e1 e2 x e3 y, x <> y -> x `notin` (fv_nom e3) -> ([y := e3]([x := e2]e1)) =a ([x := ([y := e3]e2)]([y := e3]e1)).
Proof.
  induction e1 using n_sexp_induction. (** %\noindent{\bf Proof.}% The proof is by induction on the size of the term [e1]. *)
- intros e2 x' e3 y Hneq Hfv. case (x == x').
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
  - intros e2 x e3 y Hxy Hfv. case (z == x). (** The interesting cases are the abstraction and the explicit substitution. In the abstraction case, the initial goal is [([y := e3] ([x := e2] n_abs z e1)) =a ([x := [y := e3] e2] ([y := e3] n_abs z e1))], assuming that [x <> y] and [x `notin` fv_nom e3]. We start comparing [z] with [x] aiming to apply the definition of the metasubstitution on the LHS of the goal.*)
    + intro Heq. subst. rewrite m_subst_abs_eq. apply aeq_sym. apply m_subst_notin. apply fv_nom_remove. (** When [z = x], the subterm [[x := e2](n_abs x e1)] reduces to [(n_abs x e1)] and then the LHS reduces to [([y := e3] n_abs x e1)]. The RHS reduces to the same term because [x] does not occur free neither in [(n_abs x e1)] nor in [e3].*)
        * assumption.
        * apply notin_remove_2. simpl. apply notin_remove_3. reflexivity.
    + intro Hneq. destruct (y == z). (* When [z <> x], then we compare [y] with [z].*)
      * subst. rewrite m_subst_abs_eq. pose proof m_subst_abs_neq as Habs. pick fresh w for (union (fv_nom e3) (union (fv_nom e2) (union (fv_nom (n_abs z e1)) (singleton x)))). specialize (Habs e1 e2 x z w).
        apply aeq_trans with ([z := e3] n_abs w ([x := e2] swap z w e1)). apply aeq_m_subst_out. (** When [y = z] then the subterm [([y := e3] n_abs z e1)] reduces to [(n_abs z e1)]. On the LHS, we propagate the internal metasubstitution over the abstraction taking a fresh name for the binder. The external metasubstitution cannot be propagated inside the abstraction because they have the same binder. The resulting terms are $\alpha$-equivalent, and although the strategy is similar to the one used in the lemmas [aeq_m_subst_in], [aeq_m_subst_out] and [swap_subst_rec_fun] the proof requires much more steps.*)
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
                    ******* pose proof aeq_m_subst_out as Hout. unfold m_subst in *. apply Hout. rewrite Hsubst. unfold vswap. destruct (x == w).
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
                    ******** pose proof aeq_m_subst_out as Hout. unfold m_subst in *. apply Hout. rewrite Hsubst'. unfold vswap. destruct (y == w).
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
                    ******** pose proof aeq_m_subst_out as Hout. unfold m_subst in *. apply Hout. rewrite Hswap. unfold vswap. destruct (x == z).
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
                    ********** rewrite Hswap'. unfold vswap. destruct (y == z).
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
                    ******** pose proof aeq_m_subst_out as Hout. unfold m_subst in *. apply Hout. rewrite Hswap. unfold vswap. destruct (x == w).
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
                    ********** unfold vswap. destruct (y == w).
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
  - intros e2 x e3 y Hneq Hfv. repeat rewrite m_subst_app. pose proof aeq_app as H. specialize (H ([y := e3] ([x := e2] e1_1)) ([y := e3] ([x := e2] e1_2)) ([x := [y := e3] e2] ([y := e3] e1_1)) ([x := [y := e3] e2] ([y := e3] e1_2))). rewrite H. 
    + apply aeq_refl.
    + apply IHe1_1; assumption.
    + apply IHe1_2; assumption.
  - intros e2 x e3 y Hneq Hfv. case (z == x). (** In the explicit substitution case, we used the same approach used in the abstraction for the left side and the same as the application for the right side of the substitution. It consisted of comparing the variable in the meta substitution and the one in the substitution. We used the auxiliary lemmas on the equality and inequality of the meta-substitution applied to explicit substitutions and it was necessary to create new variables in each use of the inequality. This is due to the atempt of removing the explicit substitution from inside the meta-substitution. When tis removal was made, the proof consisted in proving a similar case for the abstraction in the left side of the explicit substitution and the one similar to the application was used for the right part of it.$\hfill\Box$*)
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
                                 specialize (Hswap'' ([y := e3] swap x w e1_1) w' w). rewrite Hswap'' in Hswap'. rewrite Hswap'. unfold vswap. destruct (x == w').
                                 ******* subst. unfold m_subst. pose proof swap_subst_rec_fun as Hswap'''. specialize (Hswap''' w' w y e2 e3). 
                                         apply aeq_trans with (subst_rec_fun (subst_rec_fun (swap w' w e1_1) e3 y) (subst_rec_fun (swap w' w e2) (swap w' w e3) (vswap w' w y)) w).
                                         unfold vswap. destruct (y == w').
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
                    ******* pose proof aeq_m_subst_out as Hout. unfold m_subst in *. apply Hout. rewrite Hsubst. unfold vswap. destruct (x == w).
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
                    ******** pose proof aeq_m_subst_out as Hout. unfold m_subst in *. apply Hout. rewrite Hsubst'. unfold vswap. destruct (y == w).
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
                    ******** pose proof aeq_m_subst_out as Hout. unfold m_subst in *. apply Hout. rewrite Hswap. unfold vswap. destruct (x == z).
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
                    ********** rewrite Hswap'. unfold vswap. destruct (y == z).
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
                    ******** pose proof aeq_m_subst_out as Hout. unfold m_subst in *. apply Hout. rewrite Hswap. unfold vswap. destruct (x == w).
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
                    ********** unfold vswap. destruct (y == w).
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

(** * Conclusion and Future work*)

(** In this work, we presented a formalization of the substitution lemma in a framework that extends the $\lambda$-calculus with an explicit substitution operator. Calculi with explicit substitutions are important frameworks to study properties of the $\lambda$-calculus and have been extensively studied in the last decades%\cite{abadiExplicitSubstitutions1991,accattoliAbstractFactorizationTheorem2012,ayala-rinconComparingCalculiExplicit2002,ayala-rinconComparingImplementingCalculi2005,bonelliPerpetualityNamedLambda2001,fujitaChurchRosserTheoremCompositional2016}%. 
 
The formalization is modular in the sense that the explicit substitution operator is generic and could be instantiated with any calculi with  explicit substitutions in a nominal setting. The main contribution of this work, besides the formalization itself, is the solution to a circular proof problem. Several auxiliary (minor) results were not included in this document, but they are numerous and can be found in the source file of the formalization that is available in a GitHub repository from the following url %\url{https://github.com/flaviodemoura/lx_confl/tree/m_subst_lemma}%.

As future work, we plan to integrate this formalization with another one related to the Z property %\cite{fmm2021}% to prove properties of calculi with explicit substitutions such as confluence%\cite{nakazawaCompositionalConfluenceProofs2016,nakazawaCallbyvalue2017,kesnerPerpetualityFullSafe2008}%. *)
