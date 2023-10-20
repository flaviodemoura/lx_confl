(* Infrastructure *)
(* begin hide *)
Require Import Arith Lia.  Print LoadPath.
(* Metalib is in CP.2023.03.0~8.17~2023.08/lib/coq/user-contrib/Metalib *)
Require Export Metalib.Metatheory.
Require Export Metalib.LibDefaultSimp.
Require Export Metalib.LibLNgen.

Lemma strong_induction: forall (P:nat->Prop), (forall n, (forall m, m < n -> P m) -> P n) -> (forall n, P n).
Proof.
  intros Q IH n.
  assert (H := nat_ind (fun n => (forall m : nat, m < n -> Q m))).
  apply IH. apply H.
  - intros m Hlt; inversion Hlt.
  - intros n' H' m Hlt. apply IH. intros m0 Hlt'. apply H'. apply lt_n_Sm_le in Hlt.  apply lt_le_trans with m; assumption.
Qed.

Lemma diff_remove_2: forall x y s, x <> y -> x `notin` remove y s -> x `notin` s.
Proof.
  intros. default_simp.
Qed. 

Lemma aux_not_equal : forall (x:atom) (y:atom), x <> y -> y <> x.
Proof.
  intros. unfold not. intros. unfold not in H.
  assert (x = y). rewrite H0. reflexivity.
  contradiction.
Qed.

Lemma remove_singleton_empty: forall x, remove x (singleton x) [=] empty.
Proof.
  intros. rewrite AtomSetProperties.singleton_equal_add. rewrite AtomSetProperties.remove_add.
  - reflexivity.
  - apply notin_empty_1.
Qed.
  
Lemma remove_singleton: forall t1 t2, remove t1 (singleton t1) [=] remove t2 (singleton t2).
Proof.
  intros. repeat rewrite remove_singleton_empty. reflexivity.
Qed.

Lemma notin_singleton_is_false: forall x, x `notin` (singleton x) -> False.
Proof.
  intros. intros. apply notin_singleton_1 in H. contradiction.
Qed.

Lemma double_remove: forall x s, remove x (remove x s) [=] remove x s.
Proof.
  intros. pose proof AtomSetProperties.remove_equal.
  assert (x `notin` remove x s). apply AtomSetImpl.remove_1. reflexivity.
  specialize (H (remove x s) x). apply H in H0. assumption.
Qed.

Lemma remove_symmetric: forall x y s, remove x (remove y s) [=] remove y (remove x s).
Proof.
  intros. split.
  - intros. case (a == x); intros; case (a == y); intros; subst. apply AtomSetImpl.remove_3 in H.
    + rewrite double_remove. assumption.
    + apply remove_iff in H. inversion H. contradiction.
    + apply remove_iff in H. inversion H. apply remove_iff in H0. inversion H0. contradiction.
    + pose proof H. apply AtomSetImpl.remove_3 in H. apply AtomSetImpl.remove_2.
      * apply aux_not_equal; assumption.
      * apply AtomSetImpl.remove_2.
        ** apply aux_not_equal; assumption.
        ** apply AtomSetImpl.remove_3 in H. assumption.
  - intros. case (a == x); intros; case (a == y); intros; subst.
    + apply AtomSetImpl.remove_3 in H. rewrite double_remove. assumption.
    + apply remove_iff in H. inversion H. apply remove_iff in H0. inversion H0. contradiction.
    + apply remove_iff in H. inversion H. contradiction.
    + pose proof H. apply AtomSetImpl.remove_3 in H. apply AtomSetImpl.remove_2.
      * apply aux_not_equal; assumption.
      * apply AtomSetImpl.remove_2.
        ** apply aux_not_equal; assumption.
        ** apply AtomSetImpl.remove_3 in H. assumption.
Qed.

Lemma remove_empty: forall x, remove x empty [=] empty.
Proof.
  intros. pose proof notin_empty. specialize (H x). apply AtomSetProperties.remove_equal in H. assumption.
Qed.

Lemma diff_remove: forall x y s, x <> y -> x `notin` s -> x `notin` remove y s.
Proof.
  intros. apply notin_remove_2. assumption.
Qed.
(* end hide *)

(** * A syntactic extension of the $\lambda$-calculus *)

(** In this section, we present the framework of the formalization, which is based on a nominal approach %\cite{gabbayNewApproachAbstract2002}% where variables use names. In the nominal setting, variables are represented by atoms that are structureless entities with a decidable equality: 

<<
Parameter eq_dec : forall x y : atom, {x = y} + {x <> y}.
>>

%\noindent% therefore different names mean different atoms and different variables. The nominal approach is close to the usual paper and pencil notation used in $\lambda$-calculus, whose grammar of terms is given by:

%\begin{equation}\label{lambda:grammar}
 t ::= x \mid \lambda_x.t \mid t\ t
\end{equation}%

%\noindent% where $x$ represents a variable which is taken from an enumerable set, $\lambda_x.t$ is an abstraction, and $t\ t$ is an application. The abstraction is the only binding operator: in the expression $\lambda_x.t$, $x$ binds in $t$, called the scope of the abstraction. This means that all free occurrence of $x$ in $t$ is bound in $\lambda_x.t$. A variable that is not in the scope of an abstraction is free. A variable in a term is either bound or free, but note that a varible can occur both bound and free in a term, as in $(\lambda_y. y)\ y$.

The main rule of the $\lambda$-calculus, named $\beta$-reduction, is given by:

%\begin{equation}\label{lambda:beta}
 (\lambda_x.t)\ u \to_{\beta} \metasub{t}{x}{u}
\end{equation}%
%\noindent% where $\metasub{t}{x}{u}$ represents the result of substituting all free occurrences of variable $x$ in $t$ with $u$ in such a way that renaming of bound variable may be done in order to avoid the variable capture of free variables. We call $t$ the body of the metasubstitution, and $u$ its argument. In other words, $\metasub{t}{x}{u}$ is a metanotation for a capture free substitution. For instance, the $\lambda$-term $(\lambda_x\lambda_y.x\ y)\ y$ has both bound and free occurrences of the variable $y$, and in order to $\beta$-reduce it, one has to replace (or substitute) the free variable $y$ for all free occurrences of the variable $x$ in the term $(\lambda_y.x\ y)$. But a straight substitution will capture the free variable $y$, %{\it i.e.}% this means that the free occurrence of $y$ before the $\beta$-reduction will become bound after the $\beta$-reduction step. A renaming of bound variables may be done to avoid such a capture, so in this example, one can take an $\alpha$-equivalent%\footnote{A formal definition of this notion will be given later in this section.}% term, say $(\lambda_z.x\ z)$, and perform the $\beta$-step correctly as $(\lambda_x\lambda_y.x\ y)\ y \to_{\beta} \lambda_z.y\ z$. Renaming of variables in the nominal setting is done via a name-swapping, which is formally defined as follows:

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

In the previous example, one could apply a swap to avoid the variable capture in a way that, a swap is applied to the body of the abstraction before applying the metasubstitution to it: $(\lambda_x\lambda_y.x\ y)\ y \to_{\beta} \metasub{(\swap{y}{z}{(\lambda_y.x\ y)})}{x}{y} = \metasub{(\lambda_z.x\ z)}{x}{y} = \lambda_z.y\ z$. Could we have used a variable substitution instead of a swapping in the previous example? Absolutely. We could have done the reduction as $(\lambda_x\lambda_y.x\ y)\ y \to_{\beta} \metasub{(\metasub{(\lambda_y.x\ y)}{y}{z})}{x}{y} = \metasub{(\lambda_z.x\ z)}{x}{y} = \lambda_z.y\ z$, but as we will shortly see, variable substitution is not stable modulo $\alpha$-equivalence, while the swapping is, thereby rendering it a more fitting choice when operating with $\alpha$-classes.

In what follows, we will adopt a mixed-notation approach, intertwining metanotation with the equivalent Coq notation. This strategy aids in elucidating the proof steps of the upcoming lemmas, enabling a clearer and more detailed comprehension of each stage in the argumentation. The corresponding Coq code for the swapping of variables, named [vswap], is defined as follows: *)

Definition vswap (x:atom) (y:atom) (z:atom) := if (z == x) then y else if (z == y) then x else z.

(** %\noindent% therefore, the swap $\vswap{x}{y}{z}$ is written in Coq as [vswap x y z]. As a short example to acquaint ourselves with the Coq notation, let us show how we will write the proofs:*)

Lemma vswap_id: forall x y, vswap x x y = y.
Proof.
  intros. unfold vswap. case (y == x); intros; subst; reflexivity. (** %\noindent{\bf Proof.}% The proof is by case analysis, and it is straightforward in both cases, when [x = y] and [x <> y]. $\hfill\Box$ *)
Qed.

(** ** An explicit substitution operator *)

(** The extension of the swap operation to terms require an additional comment because we will not work with the grammar (%\ref{lambda:grammar}%), but rather, we will extend it with an explicit substitution operator:

%\begin{equation}\label{es:grammar}
  t ::= x \mid \lambda_x.t \mid t\ t \mid \esub{t}{x}{u}
\end{equation}%
%\noindent% where $[x := u] t$ represents a term with an operator that will be evaluated with specific rules of a substitution calculus. The intended meaning of the explicit substitution is that it will simulate the metasubstitution. This formalization aims to be a generic framework applicable to any calculi with explicit substitutions using a named notation for variables. Therefore, we will not specify rules about how one can simulate the metasubstitution, but it is important to be aware that this is not a trivial task as one can easily lose important properties of the original $\lambda$-calculus %\cite{melliesTypedLcalculiExplicit1995b,guillaumeCalculusDoesNot2000}%.

Calculi with explicit substitutions are formalisms that deconstruct the metasubstitution operation into finer-grained steps, thereby functioning as an intermediary between the $\lambda$-calculus and its practical implementations. In other words, these calculi shed light on the execution models of higher-order languages. In fact, the development of a calculus with explicit substitutions faithful to the $\lambda$-calculus, in the sense of the preservation of some desired properties were the main motivation for such a long list of calculi with explicit substitutions invented in the last decades %\cite{abadiExplicitSubstitutions1991,roseExplicitSubstitutionNames2011,benaissaLnCalculusExplicit1996,curienConfluencePropertiesWeak1996,munozConfluencePreservationStrong1996,kamareddineExtendingLcalculusExplicit1997a,blooExplicitSubstitutionEdge1999,davidLambdacalculusExplicitWeakening2001,kesnerTheoryExplicitSubstitutions2009a}%.

The following inductive definition corresponds to the grammar (%\ref{es:grammar}%), where the explicit substitution constructor, named [n_sub], has a special notation. Instead of writing [n_sub t x u], we will write [[x := u] t] similarly to (%\ref{es:grammar}%). Accordingly, [n_sexp] denotes the set of nominal $\lambda$-expressions equipped with an explicit substitution operator, which, for simplicity, we will refer to as just "terms". *)

Inductive n_sexp : Set :=
| n_var (x:atom)
| n_abs (x:atom) (t:n_sexp)
| n_app (t1:n_sexp) (t2:n_sexp)
| n_sub (t1:n_sexp) (x:atom) (t2:n_sexp).
(* begin hide *)
Notation "[ x := u ] t" := (n_sub t x u) (at level 60).
(* end hide *)

(** The [size] of a term, also written as $|t|$, and the set [fv_nom] of the free variables of a term are defined as usual: *)

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
Lemma swap_id : forall t x, swap x x t = t.
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

Lemma swap_eq': forall x y z w, z = w -> swap x y z = swap x y w.
Proof.
  intros x y z w H. subst. reflexivity.
Qed.
(* end hide *)

(** The [swap] function has many interesting properties, but we will focus on the ones that are more relevant to the proofs related to the substitution lemma. Nevertheless, all lemmas can be found in the source code of the formalization%\footnote{\url{https://flaviomoura.info/files/msubst.v}}%. The next lemmas are simple properties that are all proved by induction on the structure of term [t]: *)

Lemma swap_neq: forall x y z w, z <> w -> vswap x y z <> vswap x y w.
Proof.
  intros x y z w H1 H2. unfold vswap. destruct (z == x).
  - subst. apply swap_eq in H2. contradiction.
  - apply swap_eq in H2. contradiction.
Qed.

Lemma swap_size_eq : forall x y t, size (swap x y t) = size t.
Proof.
  induction t; simpl; auto.
Qed.

(* begin hide *)
#[export] Hint Rewrite swap_size_eq.
(* end hide *)

Lemma swap_symmetric : forall t x y, swap x y t = swap y x t.
Proof.
  induction t.
  - intros x' y. simpl. unfold vswap. default_simp.
  - intros x' y; simpl. unfold vswap. default_simp.
  - intros x y; simpl. rewrite IHt1. rewrite IHt2; reflexivity.
  - intros. simpl. unfold vswap. default_simp.
Qed.

(* begin hide *)
Lemma swap_comm: forall t x y x' y', x <> x' -> y <> y' -> x <> y'-> y <> x' -> swap x y (swap x' y' t) = swap x' y' (swap x y t). 
Proof.
  induction t; simpl in *; unfold vswap in *; default_simp.
Qed.
(* end hide *)

Lemma swap_involutive : forall t x y, swap x y (swap x y t) = t.
Proof.
 induction t; intros; simpl; unfold vswap; default_simp.
Qed.

Lemma shuffle_swap : forall w y z t, w <> z -> y <> z -> (swap w y (swap y z t)) = (swap w z (swap w y t)).
Proof.
  induction t; intros; simpl; unfold vswap; default_simp.
Qed.

(* begin hide *)
Lemma shuffle_swap' : forall w y n z, w <> z -> y <> z -> (swap w y (swap y z n)) = (swap z w (swap y w n)).
Proof.
  induction n; intros; simpl; unfold vswap; default_simp.
Qed.

Lemma vswap_equivariance : forall v x y z w, vswap x y (vswap z w v) = vswap (vswap x y z) (vswap x y w) (vswap x y v).
Proof.
  intros; unfold vswap; case(v == z); case (w == x); default_simp.
Qed.
(* end hide *)

Lemma swap_equivariance : forall t x y z w, swap x y (swap z w t) = swap (vswap x y z) (vswap x y w) (swap x y t).
Proof.
  induction t.
  - intros. unfold vswap. case (z == x0).
    -- case (w == x0).
       --- intros. rewrite swap_id. rewrite e; rewrite e0. rewrite swap_id. reflexivity.
       --- intros. case (w == y).
           + intros. rewrite swap_symmetric. rewrite e; rewrite e0. reflexivity.
           + intros. unfold swap. unfold vswap. default_simp.
    -- unfold swap. unfold vswap. intros. default_simp.
  - intros. simpl. rewrite IHt. unfold vswap.
    case (x == z).
    -- case (w == x0); default_simp.
    -- case (w == x0).
       --- default_simp.
       --- intros. case (x == w); intros; case (z == x0); default_simp.
  - intros. simpl. rewrite IHt1. rewrite IHt2. reflexivity.
  - intros. simpl. rewrite IHt1. rewrite IHt2. unfold vswap. default_simp.    
Qed.

Lemma fv_nom_swap : forall z y t, z `notin` fv_nom t -> y `notin` fv_nom (swap y z t).
Proof.
  induction t; intros; simpl; unfold vswap; default_simp.
Qed.

(* begin hide *)
Lemma fv_nom_swap_2 : forall z y t, z `notin` fv_nom (swap y z t) -> y `notin` fv_nom t.
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

(** The standard proof strategy used so far is induction on the structure of terms. Nevertheless, the builtin induction principle automatically generated in Coq for the inductive definition [n_sexp] is not strong enough due to swappings:

<<
forall P :n_sexp -> Prop,
 (forall x:atom, P(n_var x)) ->
 (forall (x:atom) (t:n_sexp), P t -> P(n_abs x t)) ->
 (forall t1:n_sexp, P t1 -> forall t2:n_sexp, P t2 -> P(n_app t1 t2)) ->
 (forall t1:n_sexp, P t1 -> forall (x:atom) (t2:n_sexp), P t2 -> P([x:=t2]t1)) ->
       forall t:n_sexp, P t
>>

In fact, in general, the induction hypothesis in the abstraction case (resp. explicit substitution case) refers to the body [t] of the abstraction (resp. [t1] of the explicit substitution), while the goal involves a swap acting on the body of the abstraction (resp. explicit substitution). In order to circunvet this problem, we defined a customized induction principle based on the size of terms: *)

Lemma n_sexp_induction: forall P : n_sexp -> Prop, (forall x, P (n_var x)) ->
 (forall t1 z, (forall t2 x y, size t2 = size t1 -> P (swap x y t2)) -> P (n_abs z t1)) ->
 (forall t1 t2, P t1 -> P t2 -> P (n_app t1 t2)) ->
 (forall t1 t3 z, P t3 -> (forall t2 x y, size t2 = size t1 -> P (swap x y t2)) -> P (n_sub t1 z t3)) -> (forall t, P t).
Proof.
  intros P Hvar Habs Happ Hsub t. remember (size t) as n. generalize dependent t. induction n using strong_induction. intro t; case t.
  - intros x Hsize. apply Hvar.
  - intros x t' Hsize. apply Habs. intros t'' x1 x2 Hsize'. apply H with (size t'').
    + rewrite Hsize'. rewrite Hsize. simpl. apply Nat.lt_succ_diag_r.
    + symmetry. apply swap_size_eq.
  - intros. apply Happ.
    + apply H with ((size t1)).
      ++ simpl in Heqn. rewrite Heqn. apply le_lt_n_Sm. apply le_plus_l.
      ++ reflexivity.
    + apply H with ((size t2)).
      ++ simpl in Heqn. rewrite Heqn. apply le_lt_n_Sm. apply le_plus_r.
      ++ reflexivity.
  - intros. apply Hsub.
    + apply H with ((size t2)).
      ++ simpl in Heqn. rewrite Heqn. apply le_lt_n_Sm. apply le_plus_r.
      ++ reflexivity.
    + intros. apply H with ((size (swap x0 y t0))).
      ++ rewrite swap_size_eq. rewrite H0. simpl in Heqn. rewrite Heqn. apply le_lt_n_Sm. apply le_plus_l.
      ++ reflexivity.
Qed. 

(** %\noindent% which states that in order to conclude that a certain property $P$ holds for all terms, we need to prove that:
%\begin{enumerate}
 \item $P$ must hold for any variable;
 \item If $P$ holds for the term $\swap{x}{y}{t_2}$, where $t_1$ and $t_2$ have the same size, then it also holds for the abstraction $\lambda_z.t_1,\forall x, y, z, t_1$ and $t_2$;
 \item If $P$ holds for the terms $t_1$ and $t_2$ the it also holds for the application $t_1\ t_2$;
 \item If $P$ holds for the term $t_3$ and for the term $\swap{x}{y}{t_2}$, where $t_1$ and $t_2$ have the same size, then it also holds for the explicit substitution $\esub{t_1}{z}{t_3},\forall x, y, z, t_1, t_2$ and $t_3$.
\end{enumerate}%

The following lemma is a first example of the use of the [n_sexp_induction] principle: *)  

Lemma notin_fv_nom_equivariance: forall t x' x y, x' `notin` fv_nom t -> vswap x y x'  `notin` fv_nom (swap x y t).
Proof.
  induction t as [z | z t1 | t1 IHt1 t2 IHt2 | t1 IHt1 z t2 IHt2 ].
  - intros x' x y Hfv. simpl in *. apply notin_singleton_1 in Hfv. apply notin_singleton. apply swap_neq. assumption.
  - intros x' x y H. simpl. simpl in H. apply notin_remove_1 in H. destruct H.
    + subst. apply notin_remove_3. reflexivity.
    + apply notin_remove_2. apply IHt1. assumption.
  - intros x' x y Hfv. simpl in *. apply notin_union. 
    + apply IHt1. apply notin_union_1 in Hfv. assumption.
    + apply IHt2. apply notin_union_2 in Hfv. assumption. 
  - intros x' x y Hfv. simpl in *. apply notin_union. 
    + apply notin_union_1 in Hfv. apply notin_remove_1 in Hfv. destruct Hfv. 
      * subst. apply notin_remove_3. reflexivity.
      * apply notin_remove_2. apply IHt1. assumption.
    + apply IHt2. apply notin_union_2 in Hfv. assumption. 
Qed.
      
(*  induction t as [z | t1 z | t1 t2 | t1 t2 z ] using n_sexp_induction. 
  - intros x' x y Hfv. simpl in *. apply notin_singleton_1 in Hfv. apply notin_singleton. apply swap_neq. assumption. 
  - intros x' x y Hfv. simpl in *. apply notin_remove_1 in Hfv. destruct Hfv. 
    + subst. apply notin_remove_3. reflexivity. 
    + apply notin_remove_2. specialize (H t1 x x). rewrite swap_id in H. apply H. 
      * reflexivity.
      * assumption.
  - intros x' x y Hfv. simpl in *. apply notin_union. 
    + apply IHt2. apply notin_union_1 in Hfv. assumption.
    + apply IHt1. apply notin_union_2 in Hfv. assumption. 
  - intros x' x y Hfv. simpl in *. apply notin_union. 
    + apply notin_union_1 in Hfv. apply notin_remove_1 in Hfv. destruct Hfv. 
      * subst. apply notin_remove_3. reflexivity.
      * apply notin_remove_2. specialize (H t1 x x). rewrite swap_id in H. apply H.
        ** reflexivity.
        ** assumption.
    + apply notin_union_2 in Hfv. apply IHt1; assumption. 
Qed. This is not a good example. The justification below is wrong. *)
(** %\noindent{\bf Proof.}% Note that in the paper and pencil notation, this lemma states that: %\newline%

If $x' \notin fv\_nom(t)$ then $\vswap{x}{y}{x'} \notin fv\_nom(\swap{x}{y}{t})$.%\newline%

%\noindent% The proof is by induction on the size of the term $t$.
%\begin{enumerate} \item If $t$ is a variable, say $z$, then $x' \neq z$ by hypothesis, and we need to prove that $\vswap{x}{y}{x'} \neq \vswap{x}{y}{z}$. We conclude by lemma $swap\_neq$. \item If is an abstraction, say $t = \lambda_z. t_1$, then we have by induction hypothesis that if $x' \notin \swap{x}{y}{t_2}$ then $\vswap{x_0}{y_0}{x'} \notin \swap{x_0}{y_0}{\swap{x}{y}{t_2}}$ for any term $t_2$ with the same size as $t_1$, and any variables $x, y, x_0$ and $y_0$. At this point is important to notice that an structural induction would generate an induction hypothesis with $t_1$ only, which is not strong enough to prove the goal $\vswap{x}{y}{x'} \notin fv\_nom(\swap{x}{y}{\lambda_z. t_1})$ that has $\swap{x}{y}{t_1}$ (and not $t_1$ alone!) after the propagation of the swap. In addition, we have by hypothesis that $x' \notin fv\_nom(t_1) \backslash \{z\}$. This means that either $x' = z$ or $x' \notin fv\_nom(t_1)$, and there are two subcases: \begin{enumerate} \item If $x' = z$ then the goal is $\vswap{x}{y}{z} \notin fv\_nom(\swap{x}{y}{\lambda_z. t_1}) \Leftrightarrow$ $\vswap{x}{y}{z} \notin fv\_nom(\lambda_{\vswap{x}{y}{z}}. \swap{x}{y}{t_1}) \Leftrightarrow$\newline $\vswap{x}{y}{z} \notin fv\_nom(\swap{x}{y}{t_1})\backslash \{\vswap{x}{y}{z}\}$ we are done by lemma $notin\_remove\_3$.\footnote{This is a lemma from Metalib library and it states that {\tt forall (x y : atom) (s : atoms), x = y -> y `notin` remove x s}.} \item Otherwise, $x' \notin fv\_nom(t_1)$, and we conclude using the induction hypothesis taking $x_0=x$, $y_0=y$ and the universally quantified variables $x$ and $y$ of the internal swap as the same variable (it does not matter which one). \end{enumerate} \item The application case is straightforward from the induction hypothesis. \item The case of the explicit substitution, {\it i.e.} when $t = \esub{t_1}{z}{t_2}$, we have to prove that $\vswap{x}{y}{x'} \notin fv\_nom(\swap{x}{y}{(\esub{t_1}{z}{t_2})})$. We then propagate the swap over the explicit substitution operator and show, by the definition of $fv\_nom$, we have to prove that both $\vswap{x}{y}{x'} \notin (fv\_nom (\swap{x}{y}{t_1}))\backslash \{\vswap{x}{y}{z}\}$ and $\vswap{x}{y}{x'} \notin fv\_nom (\swap{x}{y}{t_2})$. \begin{enumerate} \item In the former case, the hypothesis $x' \notin fv\_nom(t_1)\backslash \{z\}$ generates two subcases, either $x' = z$ or $x'\notin fv\_nom(t_1)$, and we conclude with the same strategy of the abstraction case. \item The later case is straightforward by the induction hypothesis. $\hfill\Box$ \end{enumerate}\end{enumerate}%*)

(** The other direction is also true, but we skip the proof that is also by induction on the size of term [t]:*)

Lemma notin_fv_nom_remove_swap: forall t x' x y, vswap x y x' `notin` fv_nom (swap x y t) -> x' `notin` fv_nom t.
Proof.
  induction t as [z | z t1 | t1 IHt1 t2 IHt2 | t1 IHt1 z t2 IHt2 ].
  - intros x' x y Hfv. simpl in *. apply notin_singleton_1 in Hfv. apply notin_singleton. intro Hneq. subst. contradiction.
  - intros x' x y Hfv. simpl in *. apply notin_remove_1 in Hfv. destruct Hfv.
    + apply swap_eq in H. subst. apply notin_remove_3. reflexivity.
    + apply notin_remove_2. apply IHt1 with x y. assumption.
  - intros x' x y Hfv. simpl in *. apply notin_union.
    + apply IHt1 with x y. apply notin_union_1 in Hfv. assumption.
    + apply IHt2 with x y. apply notin_union_2 in Hfv. assumption.
  - intros x' x y Hfv. simpl in *. apply notin_union.
    + apply notin_union_1 in Hfv. case (x' == z).
      * intro Heq. subst. apply notin_remove_3. reflexivity.
      * intro Hneq. apply notin_remove_1 in Hfv. destruct Hfv.
        ** apply swap_eq in H. symmetry in H. contradiction.
        ** apply notin_remove_2. apply IHt1 with x y. assumption.
    + apply IHt2 with x y. apply notin_union_2 in Hfv. assumption.
Qed.  
  
(*  induction t as [z | t1 z | t1 t2 | t1 t2 z ] using n_sexp_induction.
  - intros x' x y Hfv. simpl in *. apply notin_singleton_1 in Hfv. apply notin_singleton. intro Hneq. subst. contradiction.
  - intros x' x y Hfv. simpl in *. apply notin_remove_1 in Hfv. destruct Hfv.
    + apply swap_eq in H0. subst. apply notin_remove_3. reflexivity.
    + apply notin_remove_2. specialize (H t1 x x). rewrite swap_id in H. apply H with x y.
      * reflexivity.
      * assumption.
  - intros x' x y Hfv. simpl in *. apply notin_union.
    + apply IHt2 with x y. apply notin_union_1 in Hfv. assumption.
    + apply IHt1 with x y. apply notin_union_2 in Hfv. assumption.
  - intros x' x y Hfv. simpl in *. apply notin_union.
    + apply notin_union_1 in Hfv. case (x' == z).
      * intro Heq. subst. apply notin_remove_3. reflexivity.
      * intro Hneq. apply notin_remove_1 in Hfv. destruct Hfv.
        ** apply swap_eq in H0. symmetry in H0. contradiction.
        ** specialize (H t1 x x). rewrite swap_id in H. apply notin_remove_2. apply H with x y.
           *** reflexivity.
           *** assumption.
    + apply IHt1 with x y. apply notin_union_2 in Hfv. assumption.
Qed. Induction on the size not needed here also! *)       

(* begin hide *)
Lemma swap_remove_reduction: forall x y t, remove x (remove y (fv_nom (swap y x t))) [=] remove x (remove y (fv_nom t)).
Proof.
  induction t.
  - rewrite remove_symmetric. simpl. unfold vswap. default_simp.
    -- repeat rewrite remove_singleton_empty. repeat rewrite remove_empty. reflexivity.
    -- rewrite remove_symmetric. rewrite remove_singleton_empty. rewrite remove_symmetric. rewrite remove_singleton_empty. repeat rewrite remove_empty. reflexivity.
    -- rewrite remove_symmetric. reflexivity.
  - simpl. unfold vswap. default_simp.
    -- rewrite double_remove. rewrite remove_symmetric. rewrite double_remove. rewrite remove_symmetric. assumption.
    -- rewrite double_remove. symmetry. rewrite remove_symmetric. rewrite double_remove.
       rewrite remove_symmetric. symmetry. assumption.
    -- assert (remove y (remove x0 (fv_nom (swap y x t))) [=] remove x0 (remove y (fv_nom (swap y x t)))). {
         rewrite remove_symmetric. reflexivity.
       }
       assert (remove y (remove x0 (fv_nom  t)) [=] remove x0 (remove y (fv_nom t))). {
         rewrite remove_symmetric. reflexivity.
       }
       rewrite H; rewrite H0. rewrite remove_symmetric. symmetry. rewrite remove_symmetric. rewrite IHt. reflexivity.       
  - simpl. repeat rewrite remove_union_distrib. apply Equal_union_compat.
    -- assumption.
    -- assumption.
  - simpl. unfold vswap. default_simp.
    -- repeat rewrite remove_union_distrib. apply Equal_union_compat.
       --- rewrite remove_symmetric. rewrite double_remove. rewrite double_remove. rewrite remove_symmetric. assumption.
       --- assumption.
    -- repeat rewrite remove_union_distrib. apply Equal_union_compat.
       --- rewrite double_remove. symmetry. rewrite remove_symmetric. rewrite double_remove. rewrite remove_symmetric. symmetry. assumption.
       --- assumption.
    -- repeat rewrite remove_union_distrib. apply Equal_union_compat.
       --- assert (remove y (remove x0 (fv_nom (swap y x t1))) [=] remove x0 (remove y (fv_nom (swap y x t1)))). {
         rewrite remove_symmetric. reflexivity.
           }
           assert (remove y (remove x0 (fv_nom  t1)) [=] remove x0 (remove y (fv_nom t1))). {
         rewrite remove_symmetric. reflexivity.
           }
           rewrite H; rewrite H0. rewrite remove_symmetric. symmetry. rewrite remove_symmetric. symmetry. rewrite IHt1. reflexivity.
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

(** As usual in the standard presentations of the $\lambda$-calculus, we work with terms modulo $\alpha$-equivalence. This means that $\lambda$-terms are identified up to renaming of bound variables. For instance, all terms $\lambda_x.x$, $\lambda_y.y$ and $\lambda_z.z$ are seen as the same term which corresponds to the identity function. Formally, the notion of $\alpha$-equivalence is defined by the following inference rules:

 
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

Each of these rules correspond to a constructor in the [aeq] inductive definition below:*)

Inductive aeq : n_sexp -> n_sexp -> Prop :=
| aeq_var : forall x, aeq (n_var x) (n_var x)
| aeq_abs_same : forall x t1 t2, aeq t1 t2 -> aeq (n_abs x t1)(n_abs x t2)
| aeq_abs_diff : forall x y t1 t2, x <> y -> x `notin` fv_nom t2 -> aeq t1 (swap y x t2) ->
  aeq (n_abs x t1) (n_abs y t2)
| aeq_app : forall t1 t2 t1' t2', aeq t1 t1' -> aeq t2 t2' -> aeq (n_app t1 t2) (n_app t1' t2')
| aeq_sub_same : forall t1 t2 t1' t2' x, aeq t1 t1' -> aeq t2 t2' -> aeq ([x := t2] t1) ([x := t2'] t1')
| aeq_sub_diff : forall t1 t2 t1' t2' x y, aeq t2 t2' -> x <> y -> x `notin` fv_nom t1' -> aeq t1 (swap y x t1') ->
  aeq ([x := t2] t1) ([y := t2'] t1').
(* begin hide *)
Notation "t =a u" := (aeq t u) (at level 60).

#[export] Hint Constructors aeq.
(* end hide *)

(** In what follows, we use a infix notation for $\alpha$-equivalence in the Coq code. Therefore, we write [t =a u] instead of [aeq t u]. The above notion defines an equivalence relation over the set [n_sexp] of nominal expressions with explicit substitutions, %{\it i.e.}% the [aeq] relation is reflexive, symmetric and transitive (proofs in the source file%\footnote{\url{https://flaviomoura.info/files/msubst.v}}%). In addition, $\alpha$-equivalent terms have the same size, and the same set of free variables: *)
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
  induction 1.
  - reflexivity.
  - simpl. rewrite IHaeq. reflexivity.
  - simpl. inversion H1; subst; rewrite IHaeq; apply remove_fv_swap; assumption.
  - simpl. rewrite IHaeq1; rewrite IHaeq2. reflexivity.
  - simpl. rewrite IHaeq1; rewrite IHaeq2. reflexivity.
  - simpl. pose proof remove_fv_swap.
    specialize (H3 x y t1'). apply H3 in H1.
    inversion H2; subst; rewrite IHaeq1; rewrite IHaeq2; rewrite H1; reflexivity.
Qed.

(**
   Sets are represented by lists, and these lists are built exactly the same way for $\alpha$-equivalent terms. Therefore, the sets [fv_nom t1] and [fv_nom t2] are syntactically equal. This is the content of the following lemma that has a key hole in this formalization.
 *)

Lemma remove_singleton_empty_eq: forall x, remove x (singleton x) = empty.
Proof.
  Admitted.

Lemma remove_singleton_neq: forall x y, x <> y -> remove x (singleton y) = singleton y.
Proof.  
Admitted.

Lemma remove_swap_fv_nom: forall t x y, x `notin` (fv_nom t) -> remove x (fv_nom (swap y x t)) = remove y (fv_nom t). 
Proof.
  induction t as [z | z t1 | t1 IHt1 t2 IHt2 | t1 IHt1 z t2 IHt2].
  - intros x y Hfv. simpl in *. unfold vswap. destruct (z == y).
    + subst. repeat rewrite remove_singleton_empty_eq. reflexivity.
    + destruct (z == x).
      * subst. apply notin_singleton_1 in Hfv. contradiction.
      * rewrite remove_singleton_neq.
        ** rewrite remove_singleton_neq.
           *** reflexivity.
           *** apply aux_not_equal. assumption.
        ** apply aux_not_equal. assumption.
  - intros x y Hfv. simpl in *.
  Admitted.

Lemma aeq_fv_nom_eq : forall t1 t2, t1 =a t2 -> fv_nom t1 = fv_nom t2.
Proof.
  induction 1.
  - reflexivity.
  - simpl. rewrite IHaeq. reflexivity.
  - simpl. rewrite IHaeq. apply remove_swap_fv_nom. assumption.
  - simpl. rewrite IHaeq1. rewrite IHaeq2. reflexivity.
  - simpl. rewrite IHaeq1. rewrite IHaeq2. reflexivity.
  - simpl. rewrite IHaeq1. f_equal. rewrite IHaeq2. apply remove_swap_fv_nom. assumption.
Qed.
    
(* begin hide *)
Lemma aeq_refl : forall n, n =a n.
Proof.
  induction n; auto.
Qed.

Lemma aeq_swap1: forall t1 t2 x y, t1 =a t2 -> (swap x y t1) =a (swap x y t2).
Proof.
  induction 1.
  - apply aeq_refl.
  - simpl. apply aeq_abs_same. assumption.
  - simpl. apply (swap_neq x y) in H. apply aeq_abs_diff.
    + assumption.
    + apply notin_fv_nom_equivariance. assumption.
    + rewrite <- swap_equivariance. apply IHaeq.
  - simpl. apply aeq_app; assumption.
  - simpl. apply aeq_sub_same; assumption.
  - simpl. apply (swap_neq x y) in H0. apply aeq_sub_diff.
    + assumption.
    + assumption.
    + apply notin_fv_nom_equivariance. assumption.
    + rewrite <- swap_equivariance. apply IHaeq2.
Qed.

Lemma aeq_abs_notin: forall t1 t2 x y, x <> y ->  n_abs x t1 =a n_abs y t2 -> x `notin` fv_nom t2.
Proof.
  intros t1 t2 x y Hneq Haeq. inversion Haeq; subst.
  - contradiction.
  - assumption.
Qed.

Lemma aeq_swap2: forall t1 t2 x y, (swap x y t1) =a (swap x y t2) -> t1 =a t2.
Proof.
  induction t1.
  - intros t x' y H. inversion H; subst. apply (aeq_swap1 _ _ x' y) in H. repeat rewrite swap_involutive in H. assumption.
  - intros t x' y H. inversion H; subst.
    + apply (aeq_swap1 _ _ x' y) in H. repeat rewrite swap_involutive in H. assumption.
    + apply (aeq_swap1 _ _ x' y) in H. repeat rewrite swap_involutive in H. assumption.
  - intros t x y H. simpl in *. inversion H; subst. apply (aeq_swap1 _ _ x y) in H. simpl in H. repeat rewrite swap_involutive in H. assumption.
  - intros t x' y H. inversion H; subst.
    + apply (aeq_swap1 _ _ x' y) in H. repeat rewrite swap_involutive in H. assumption.
    + apply (aeq_swap1 _ _ x' y) in H. repeat rewrite swap_involutive in H. assumption.
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

(** The key point of the nominal approach is that the swap operation is stable under $\alpha$-equivalence in the sense that, $t_1 =_\alpha t_2$ if, and only if $\swap{x}{y}{t_1} =_\alpha \swap{x}{y}{t_2}, \forall t_1, t_2, x, y$. Note that this is not true for renaming substitutions: in fact, $\lambda_x.z =_\alpha \lambda_y.z$, but $\metasub{(\lambda_x.z)}{z}{x} = \lambda_x.x \neq_\alpha \metasub{\lambda_y.x (\lambda_y.z)}{z}{x}$, assuming that $x \neq y$. This stability result is formalized as follows:*)

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
(* end hide *)

(** When both variables in a swap do not occur free in a term, it eventually renames only bound variables, %{\it i.e.}% the action of this swap results in a term that is $\alpha$-equivalent to the original term. This is the content of the following lemma:*)

Lemma swap_reduction: forall t x y, x `notin` fv_nom t -> y `notin` fv_nom t -> (swap x y t) =a  t.
Proof. 
  induction t.
  - intros x' y H1 H2. simpl. unfold vswap. destruct (x == x'); subst.
    + apply notin_singleton_is_false in H1. contradiction.
    + destruct (x == y); subst.
      * apply notin_singleton_is_false in H2. contradiction. 
      * apply aeq_refl.
  - intros x' y H1 H2. simpl in *. unfold vswap. apply notin_remove_1 in H1. apply notin_remove_1 in H2. destruct H1.
    + destruct (x == x').
      * subst. destruct H2.
        ** subst. rewrite swap_id. apply aeq_refl.
        ** apply aeq_abs; assumption.
      * contradiction.
    + destruct (x == x').
      * subst. destruct H2.
        ** subst. rewrite swap_id. apply aeq_refl.
        ** apply aeq_abs; assumption.
      * destruct H2.
        ** subst. rewrite eq_dec_refl. rewrite swap_symmetric. apply aeq_abs; assumption.
        ** destruct (x == y).
           *** subst. rewrite swap_symmetric. apply aeq_abs; assumption.
           *** apply aeq_abs_same. apply IHt; assumption.
  - intros x y H1 H2. simpl in *. assert (H1' := H1). apply notin_union_1 in H1. apply notin_union_2 in H1'. assert (H2' := H2).  apply notin_union_1 in H2. apply notin_union_2 in H2'. apply aeq_app.
    + apply IHt1; assumption.
    + apply IHt2; assumption.
  - intros x' y H1 H2. simpl in *. assert (H1' := H1). apply notin_union_1 in H1. apply notin_union_2 in H1'. assert (H2' := H2). apply notin_union_1 in H2. apply notin_union_2 in H2'. apply notin_remove_1 in H1. apply notin_remove_1 in H2. unfold vswap. destruct H1.
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
      * subst. destruct H2.
        ** subst. repeat rewrite swap_id. apply aeq_refl.
        ** case (x' == y); intros; subst.
           *** repeat rewrite swap_id. apply aeq_refl.
           *** apply aeq_sub_diff.
           **** apply IHt2; assumption.
           **** apply aux_not_equal; assumption.
           **** assumption.
           **** apply aeq_refl.
      * destruct H2.
        ** subst. rewrite eq_dec_refl. rewrite swap_symmetric. replace (swap x' y t2) with (swap y x' t2).
               **** apply aeq_sub_diff.
               ***** apply IHt2; assumption.
               ***** apply aux_not_equal; assumption.
               ***** assumption.
               ***** apply aeq_refl.
               **** apply swap_symmetric.             
        ** destruct (x == y).
           *** subst. rewrite swap_symmetric. replace (swap x' y t2) with (swap y x' t2).
               **** apply aeq_sub_diff.
               ***** apply IHt2; assumption.
               ***** apply aux_not_equal; assumption.
               ***** assumption.
               ***** apply aeq_refl.
               **** apply swap_symmetric.
           *** rewrite swap_symmetric. replace (swap x' y t2) with (swap y x' t2).
               **** apply aeq_sub_same.
                    ***** apply IHt1; assumption.
                    ***** apply IHt2; assumption.
               **** apply swap_symmetric.
Qed.

(* begin hide *)
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

(** There are several other interesting auxiliary properties that need to be proved before achieving the substitution lemma. In what follows, we refer only to the tricky or challenging ones, but the interested reader can have a detailed look in the source file. Note that, swaps are introduced in proofs by the rules $\mbox{\it aeq}\_\mbox{\it abs}\_\mbox{\it diff}$ and $\mbox{\it aeq}\_\mbox{\it sub}\_\mbox{\it diff}$. As we will see, the proof steps involving these rules are trick because a naïve strategy can easily get blocked in a branch without proof. We conclude this section, with a lemma that gives the conditions for two swaps with a common variable to be merged: *)

Lemma aeq_swap_swap: forall t x y z, z `notin` fv_nom t -> x `notin` fv_nom t -> (swap z x (swap x y t)) =a (swap z y t).
Proof.
  intros t x y z Hfv Hfv'. case (z == y). 
  - intro Heq. subst. rewrite swap_id. rewrite (swap_symmetric _ y x). rewrite swap_involutive. apply aeq_refl. 
  - intro Hneq. case (x == y). 
    + intro Heq. subst. rewrite swap_id. apply aeq_refl. 
    + intro Hneq'. rewrite shuffle_swap. 
      * apply aeq_swap. apply swap_reduction; assumption.
      * assumption.
      * assumption.
Qed. (** %\noindent{\bf Proof.}% Before commenting this proof, we state the lemma with the pencil and paper (meta)notation: %\newline%

If $z\notin fv\_nom(t)$ and $x \notin fv\_nom(t)$ then $\swap{z}{x}{\swap{x}{y}{t}} =_{\alpha} \swap{z}{y}{t}$.%\newline%

%\noindent% Initially, observe the similarity of the left hand side (LHS) of the $\alpha$-equation with the lemma [shuffle_swap]:

$\forall w\ y\ z\ t, w \neq z \to y \neq z \to \swap{w}{y}{(\swap{y}{z}{t})} = \swap{w}{z}{(\swap{w}{y}{t})}$

In order to use it, we need to have that both [z <> y] and [x <> y]. We start comparing [z] and [y]: %\begin{enumerate} \item If $z = y$ then the right hand side (RHS) reduces to $t$ because the swap is trivial, and the LHS also reduces to $t$ since swap is involutive. \item When $z \neq y$ then we proceed by comparing $x$ and $y$: \begin{enumerate} \item If $x = y$ then both sides of the $\alpha$-equation reduces to $\swap{z}{y}{t}$, and we are done. \item Finally, when $x \neq y$, we can apply the lemma $shuffle\_swap$, and use lemma $aeq\_swap$ to reduce the current goal to $\swap{z}{x}{t} =_{\alpha} t$, and we conclude by lemma $swap\_reduction$ since both $z$ and $x$ are not in the set of free variables of the term $t$. $\hfill\Box$ \end{enumerate}\end{enumerate}%*) 

(** * The metasubstitution operation of the $\lambda$-calculus *)

(** As presented in Section 2, the main operation of the $\lambda$-calculus is the $\beta$-reduction %(\ref{lambda:beta})% that expresses how to evaluate a function applied to an argument. The $\beta$-contractum $\metasub{t}{x}{u}$ represents a capture free in the sense that no free variable becomes bound by the application of the metasubstitution. This operation is in the meta level because it is outside the grammar of the $\lambda$-calculus (and hence its name). In %\cite{barendregtLambdaCalculusIts1984a}%, Barendregt defines it as follows:

%\vspace{.5cm}%
$\metasub{t}{x}{u} = \left\{
 \begin{array}{ll}
  u, & \mbox{ if } t = x; \\
  y, & \mbox{ if } t = y \mbox{ and } x \neq y; \\
  \metasub{t_1}{x}{u}\ \metasub{t_2}{x}{u}, & \mbox{ if } t = t_1\ t_2; \\
  \lambda_y.(\metasub{t_1}{x}{u}), & \mbox{ if } t = \lambda_y.t_1.
 \end{array}\right.$ %\vspace{.5cm}%

%\noindent% where it is assumed the so called "Barendregt's variable convention":

%\begin{tcolorbox}
 If $t_1, t_2, \ldots, t_n$ occur in a certain mathematical context (e.g. definition, proof), then in these terms all bound variables are chosen to be different from the free variables.  
\end{tcolorbox}%

This means that we are assumming that both $x \neq y$ and $y\notin fv(u)$ in the case $t = \lambda_y.t_1$. This approach is very convenient in informal proofs because it avoids having to rename bound variables. In order to formalize the capture free substitution, %{\it i.e.}% the metasubstitution, there are different possible approaches. In our case, we perform a renaming of bound variables whenever the metasubstitution is propagated inside a binder. In our case, there are two binders: abstractions and explicit substitutions.

Let $t$ and $u$ be terms, and $x$ a variable. The result of substituting $u$ for the free ocurrences of $x$ in $t$, written $\metasub{t}{x}{u}$ is defined as follows:%\newline%
%\begin{equation}\label{msubst}
\metasub{t}{x}{u} = \left\{
 \begin{array}{ll}
  u, & \mbox{ if } t = x; \\
  y, & \mbox{ if } t = y\ (x \neq y); \\
  \metasub{t_1}{x}{u}\ \metasub{t_2}{x}{u}, & \mbox{ if } t = t_1\ t_2; \\
  \lambda_x.t_1, & \mbox{ if } t = \lambda_x.t_1; \\
  \lambda_z.(\metasub{(\swap{y}{z}{t_1})}{x}{u}), & \mbox{ if } t = \lambda_y.t_1, x \neq y \mbox{ and } z\notin fv(t)\cup fv(u) \cup \{x\}; \\
  \esub{t_1}{x}{\metasub{t_2}{x}{u}}, & \mbox{ if } t = \esub{t_1}{x}{t_2}; \\
  \esub{\metasub{(\swap{y}{z}{t_1})}{x}{u}}{z}{\metasub{t_2}{x}{u}}, & \mbox{ if } t = \esub{t_1}{y}{t_2}, x \neq y \mbox{ and } z\notin fv(t)\cup fv(u) \cup \{x\}.
 \end{array}\right.
\end{equation}%

%\noindent% and the corresponding Coq code is as follows: *)

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
    n_sub (subst_rec_fun (swap y z t1) u x) z (subst_rec_fun t2 u x) end.
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
(* end hide *)

(** Note that this function is not structurally recursive due to the swaps in the recursive calls, and that's why we need to provide the size of the term $t$ as the measure parameter. Alternatively, a structurally recursive version of the function [subst_rec_fun] can be found in the file [nominal.v] of the [Metalib] library%\footnote{\url{https://github.com/plclub/metalib}}%. It has the size of the term as an explicit parameter in which the substitution will be performed, and hence one has to deal with the size of the term in each recursive call. We write [{x:=u}t] instead of [subst_rec_fun t u x], and refer to it just as "metasubstitution".*)

(* begin hide *)
Lemma m_subst_var_eq: forall u x, {x := u}(n_var x) = u.
Proof.
  intros u x. unfold m_subst. rewrite subst_rec_fun_equation. rewrite eq_dec_refl. reflexivity.
Qed.

Lemma m_subst_var_neq: forall u x y, x <> y -> {y := u}(n_var x) = n_var x.
Proof.
  intros u x y H. unfold m_subst. rewrite subst_rec_fun_equation. destruct (y == x) eqn:Hxy.
  - subst. contradiction.
  - reflexivity.
Qed.

Lemma m_subst_app: forall t1 t2 u x, {x := u}(n_app t1 t2) = n_app ({x := u}t1) ({x := u}t2).
Proof.
  intros t1 t2 u x. unfold m_subst. rewrite subst_rec_fun_equation. reflexivity.
Qed.

Lemma aeq_trans: forall t1 t2 t3, t1 =a t2 -> t2 =a t3 -> t1 =a t3.
Proof.
(* intros t1 t2 t3 H. generalize dependent t3. induction H.
  - intros t3 H. assumption.
  - intros t3 H1. inversion H1; subst.
    + apply aeq_abs_same. apply IHaeq. assumption.
    + apply aeq_abs_diff.
      * assumption.
      * assumption.
      * apply IHaeq. assumption.
  - intros t3 H2. inversion H2; subst.
    + apply aeq_abs_diff.
      * assumption.
      * apply aeq_fv_nom in H6. rewrite <- H6. assumption.
      * apply IHaeq. apply aeq_swap1. assumption.
    + case (x == y0).
      * intro Heq; subst. apply aeq_abs_same. apply IHaeq. rewrite (swap_symmetric _ y y0). apply (aeq_swap2 _ _ y0 y). rewrite swap_involutive. assumption.
      * intro Hneq. apply aeq_abs_diff.
        ** assumption.
        ** apply aeq_fv_nom in H8. rewrite H8 in H0. apply fv_nom_swap_remove in H0; assumption.
        ** apply IHaeq. *)

    
(*  induction t1 as [x | x t11 | t11 IHt11 t12 IHt12 | t11 IHt11 x t12 IHt12].
  - intros t2 t3 H1 H2. inversion H1; subst. assumption.
  - intros t2 t3 H1 H2. inversion H1; subst.
    + inversion H2; subst.
      * apply aeq_abs_same. apply IHt11 with t0; assumption.
      * apply aeq_abs_diff.
        ** assumption.
        ** assumption.
        ** apply IHt11 with t0; assumption.
    + inversion H2; subst.
      * apply aeq_abs_diff.
        ** assumption.
        ** apply aeq_fv_nom in H7. rewrite <- H7; assumption. 
        ** apply IHt11 with (swap y x t0).
           *** assumption.
           *** apply aeq_swap1; assumption.
      * case (x == y0).
        ** intro Heq; subst. apply aeq_abs_same. apply IHt11 with (swap y0 y t0).
           *** rewrite (swap_symmetric _ y0 y). assumption.
           *** apply (aeq_swap1 _ _  y0 y) in H9. rewrite swap_involutive in H9. assumption. 
        ** intro Hneq. apply aeq_abs_diff.
               *** assumption.
               *** apply (aeq_swap1 _ _  y0 y) in H9. rewrite swap_involutive in H9. apply aeq_fv_nom in H9. rewrite <- H9. apply fv_nom_remove_swap; assumption.
               *** apply IHt11 with (swap y x t0).
                   **** assumption.
                   **** apply (aeq_swap _ _ y x). rewrite swap_involutive. rewrite (swap_symmetric _ y0 y) in H9. rewrite (swap_symmetric _ y0 x). apply aeq_sym. pose proof aeq_swap_swap as H. rewrite H9. *)

  
  induction t1 as [x | t11 x | t11 t12 | t11 t12 x] using n_sexp_induction.
  - intros t2 t3 H1 H2. inversion H1; subst. assumption.
  - intros t2 t3 H1 H2. inversion H1; subst.
    + inversion H2; subst.
      * apply aeq_abs_same. replace t11 with (swap x x t11).
        ** apply H with t0.
           *** reflexivity.
           *** rewrite swap_id; assumption.
           *** assumption.
        ** apply swap_id.
      * apply aeq_abs_diff.
        ** assumption.
        ** assumption.
        ** apply aeq_sym.
           apply H with t0.
           *** apply eq_trans with (size t0).
               **** apply aeq_size in H8. rewrite swap_size_eq in H8. symmetry; assumption.
               **** apply aeq_size in H5. symmetry; assumption.
           *** apply aeq_sym; assumption.
           *** apply aeq_sym; assumption.
    + inversion H2; subst.
      * apply aeq_abs_diff.
        ** assumption.
        ** apply aeq_fv_nom in H8. rewrite <- H8; assumption. 
        ** apply aeq_sym. apply H with (swap y x t0).
           *** apply eq_trans with (size t0).
               **** apply aeq_size in H8. symmetry; assumption.
               **** apply aeq_size in H7. rewrite H7. rewrite swap_size_eq. reflexivity.
           *** apply aeq_sym. apply aeq_swap1; assumption.
           *** apply aeq_sym; assumption.
      * case (x == y0).
        ** intro Heq; subst. apply aeq_abs_same. apply (aeq_swap1 _ _  y0 y) in H10. rewrite swap_involutive in H10. apply aeq_sym. replace t2 with (swap y y t2).
           *** apply H with (swap y0 y t0).
               **** apply aeq_size in H7. rewrite  H7. apply aeq_size in H10. rewrite swap_symmetric. symmetry. assumption.
               **** apply aeq_sym. rewrite swap_id; assumption.
               **** apply aeq_sym. rewrite swap_symmetric; assumption.
           *** apply swap_id.             
        ** intro Hneq. apply aeq_fv_nom in H10. assert (H5' := H5). rewrite H10 in H5'. apply fv_nom_swap_remove in H5'.           
           *** apply aeq_abs_diff.
               **** assumption.
               **** assumption.
               **** apply aeq_sym. apply H with (swap y x t0).
                    ***** apply aeq_size in H1. apply aeq_size in H2. simpl in *. inversion H1; subst. inversion H2; subst. symmetry. assumption.
                    ***** inversion H2; subst.
                    ****** apply aeq_swap. apply aeq_sym. assumption.
                    ****** apply (aeq_swap _ _ y x). rewrite swap_involutive. apply H with (swap y0 y t2).
                    ******* simpl. apply aeq_size in H14. rewrite swap_size_eq in *. rewrite <- H14. apply aeq_size in H7. rewrite swap_size_eq in H7. symmetry. assumption.
                    ******* rewrite (swap_symmetric _  y0 x). rewrite (swap_symmetric _ y0 y). apply aeq_swap_swap; assumption.
                    ******* apply aeq_sym. assumption.
                    ***** apply aeq_sym; assumption.
           *** assumption.
           *** assumption.
  - intros t2 t3 H1 H2. inversion H1; subst. inversion H2; subst. apply aeq_app. 
    + apply IHt12 with t1'; assumption. 
    + apply IHt1_1 with t2'; assumption. 
  - intros t2 t3 H1 H2. inversion H1; subst.
    + inversion H2; subst.
      * apply aeq_sub_same.
        ** specialize (H t11 x x). rewrite swap_id in H. apply H with t1'.
           *** reflexivity.
           *** assumption.
           *** assumption.
        ** apply IHt1_1 with t2'; assumption.
      * apply aeq_sub_diff.
        ** apply IHt1_1 with t2'; assumption.
        ** assumption.
        ** assumption.
        ** apply (aeq_swap _ _ y x). rewrite swap_involutive. apply H with (swap y x t1').
           *** reflexivity.
           *** apply aeq_swap. assumption.
           *** apply (aeq_swap _ _ y x). rewrite swap_involutive. assumption.
    + inversion H2; subst.            
      * apply aeq_sub_diff.
        ** apply IHt1_1 with t2'; assumption.
        ** assumption.
        ** apply aeq_fv_nom in H10. rewrite H10 in H8. assumption.
        ** apply (aeq_swap _ _ y x). rewrite swap_involutive. apply H with t1'.
           *** reflexivity.
           *** apply (aeq_swap _ _ y x). rewrite swap_involutive. assumption.
           *** assumption.
      * case (x == y0); intros; subst.
        ** apply aeq_sub_same.
           *** apply (aeq_swap _ _ y0 y). apply H with t1'.
               **** reflexivity.
               **** apply (aeq_swap _ _ y0 y). rewrite swap_involutive. rewrite (swap_symmetric _ y0 y). assumption.
               **** assumption.
           *** apply IHt1_1 with t2'; assumption.
        ** apply aeq_sub_diff.
           *** apply IHt1_1 with t2'; assumption.
           *** assumption.
           *** apply aeq_fv_nom in H13. rewrite H13 in H8. apply fv_nom_swap_remove in H8.
               **** assumption.
               **** assumption.
               **** assumption.
           *** apply (aeq_swap _ _ y x). apply H with t1'.
               **** reflexivity.
               ****  apply (aeq_swap _ _ y x). rewrite swap_involutive. assumption.
               **** apply aeq_sym. apply H with (swap y y0 t1'0).
                    ***** apply aeq_size in H9. rewrite swap_size_eq in *. rewrite H9. apply aeq_size in H13. rewrite H13. rewrite swap_size_eq. reflexivity.
                    ***** rewrite (swap_symmetric _ y0 x). apply aeq_swap_swap.
                    ****** assumption.
                    ****** apply aeq_fv_nom in H13. rewrite H13 in H8. apply fv_nom_swap_remove in H8; assumption.
                    ***** apply aeq_sym. rewrite (swap_symmetric _ y y0). assumption.
Qed.

Require Import Setoid Morphisms.

#[export] Instance Equivalence_aeq: Equivalence aeq.
Proof.
  split.
  - unfold Reflexive. apply aeq_refl.
  - unfold Symmetric. apply aeq_sym.
  - unfold Transitive. apply aeq_trans.
Qed.
(* end hide *)

(** The following lemma states that if $x \notin fv(t)$ then $\metasub{t}{x}{u} =_\alpha t$. In informal proofs the conclusion of this lemma is usually stated as a syntactic equality, %{\i.e.}% $\metasub{t}{x}{u} = t$ instead of the $\alpha$-equivalence, but the function [subst_rec_fun] renames bound variables whenever the metasubstitution is propagated inside an abstraction or an explicit substitution, even in the case that the metasubstitution has no effect in the subterm it is propagated, as long as the variables of the metasubstitution and the binder (abstraction or explicit substitution) are different of each other. That's why the syntactic equality does not hold here. *)

Lemma m_subst_notin: forall t u x, x `notin` fv_nom t -> {x := u}t =a t.
Proof.
  induction t as [y | t1 y | t1 t2 | t1 t2 y ] using n_sexp_induction. 
  - intros u x Hfv. simpl in *. apply notin_singleton_1 in Hfv. rewrite m_subst_var_neq.
    + apply aeq_refl.
    + assumption.
  - intros u x Hfv. simpl in *. unfold m_subst in *. rewrite subst_rec_fun_equation. destruct (x == y). 
    + subst. apply aeq_refl. 
    + destruct (atom_fresh (union (fv_nom u) (union (fv_nom (n_abs y t1)) (singleton x)))) as [z]. case (z == y). 
      * intro Heq. subst. apply aeq_abs_same. apply aeq_trans with (swap y y t1).
        ** apply H. 
           *** reflexivity.
           *** rewrite swap_id. apply notin_remove_1 in Hfv. destruct Hfv.
               **** symmetry in H0. contradiction.
               **** assumption.
        ** rewrite swap_id. apply aeq_refl. 
      * intro Hneq. apply aeq_abs_diff. 
        ** assumption.
        ** apply notin_union_2 in n0. apply notin_union_1 in n0. simpl in n0. apply notin_remove_1 in n0. destruct n0.
           *** subst. contradiction.
           *** assumption.
        ** apply H.
           *** reflexivity.
           *** apply notin_remove_1 in Hfv. destruct Hfv.
               **** symmetry in H0. contradiction.
               **** repeat apply notin_union_2 in n0. apply notin_singleton_1 in n0. apply fv_nom_remove_swap; assumption.
  - intros u x Hfv. unfold m_subst in *. simpl in *. rewrite subst_rec_fun_equation. apply aeq_app.
    + apply IHt2. apply notin_union_1 in Hfv. assumption.
    + apply IHt1. apply notin_union_2 in Hfv. assumption.
  - intros u x Hfv. simpl in *. unfold m_subst in *. rewrite subst_rec_fun_equation. destruct (atom_fresh (union (fv_nom u) (union (fv_nom (n_sub t1 y t2)) (singleton x)))). destruct (x == y). 
    + subst. apply aeq_sub_same.
      * apply aeq_refl.
      * apply notin_union_2 in Hfv. apply IHt1. assumption.
    + case (x0 == y).
      * intro Heq. subst. apply aeq_sub_same.
        ** apply aeq_trans with (swap y y t1). apply H.
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
(** %\noindent{\bf Proof.}% The proof is done by induction on the size of the term [t] using [n_sexp_induction] defined above. The interesting cases are the abstraction and the explicit substituion. We focus in the abstraction case, %{\it i.e.}% when $t = \lambda_y.t_1$, where the goal to be proven is $\metasub{(\lambda_y.t_1)}{x}{u} =_\alpha \lambda_y.t_1$. We consider two cases: %\begin{enumerate} \item If $x = y$ the result is trivial because both LHS and RHS are equal to $\lambda_y.t_1$ \item If $x \neq y$ , we have to prove that $\lambda_z. \metasub{\swap{y}{z}{t_1}}{x}{u} =_{\alpha} \lambda_y. t_1$, where $z$ is a fresh name not in the set $fv\_nom(u)\cup fv\_nom(\lambda_y.t_1)\cup \{x\}$. The induction hypothesis express the fact that every term with the same size as the body $t_1$ of the abstraction  satisfies the property to be proven: $\forall t', |t'| = |t_1| \to \forall u\ x'\ x_0\ y_0, x' \notin fv(\swap{x_0}{y_0}{t'}) \to \metasub{(\swap{x_0}{y_0}{t'})}{x'}{u} =_\alpha \swap{x}{y}{t'}$. Therefore, according to the definition of the metasubstitution (function [subst_rec_fun]), the variable $y$ will be renamed to $z$, and the metasubstitution is propagated inside the abstraction resulting in the following goal: $\lambda_z.\metasub{(\swap{z}{y}{t_1})}{x}{u} =_\alpha \lambda_y.t_1$. Since $z \notin fv\_nom(\lambda_y.t_1) = fv\_nom(t_1)\backslash \{y\}$, there are two cases to consider, either $z = y$ or $z \in fv(t_1)$:
\begin{enumerate}
 \item $z = y$: In this case, we are done by the induction hypothesis taking $x_0=y_0=y$, for instance.
 \item $z \neq y$: In this case, we can apply the rule $\mbox{\it aeq}\_\mbox{\it abs}\_\mbox{\it diff}$, resulting in the goal $\metasub{(\swap{y}{z}{t_1})}{x}{u} =_\alpha \swap{y}{z}{t_1}$ which holds by the induction hypothesis, since $|\swap{z}{y}{t_1}| = |t_1|$ and $x \notin fv\_nom(\swap{y}{z}{t_1})$ because $x \neq z$, $x \neq y$ and $x \notin fv\_nom(t_1)$.
\end{enumerate}
\end{enumerate}%

The explicit substitution case is also interesting, %{\it i.e.}% if $t = \esub{t_1}{y}{t_2}$, but it follows a similar strategy used in the abstraction case for $t_1$. For $t_2$ the result follows from the induction hypothesis. $\hfill\Box$*)

(* begin hide *)
Lemma m_subst_abs: forall t u x y, {x := u}(n_abs y t) =a if (x == y) then (n_abs y t) else let (z,_) := atom_fresh (fv_nom u `union` fv_nom (n_abs y t) `union` {{x}}) in n_abs z (subst_rec_fun (swap y z t) u x).
Proof.
  intros t u x y. destruct (x == y).
  - subst. unfold m_subst. rewrite subst_rec_fun_equation. rewrite eq_dec_refl. apply aeq_refl.
  - unfold m_subst. rewrite subst_rec_fun_equation. destruct (x == y).
    + simpl. contradiction.
    + destruct (atom_fresh (union (fv_nom u) (union (fv_nom (n_abs y t)) (singleton x)))). apply aeq_refl.
Qed.

Lemma m_subst_sub: forall t1 t2 u x y, {x := u}(n_sub t1 y t2) =a if (x == y) then (n_sub t1 y ({x := u}t2)) else let (z,_) := atom_fresh (fv_nom u `union` fv_nom (n_sub t1 y t2) `union` {{x}}) in n_sub ({x := u}(swap y z t1)) z ({x := u}t2).
Proof.
  intros. destruct (x == y).
  - subst. unfold m_subst. rewrite subst_rec_fun_equation. rewrite eq_dec_refl. apply aeq_refl.
  - unfold m_subst. rewrite subst_rec_fun_equation. destruct (x == y).
    + simpl. contradiction.
    + simpl. destruct (atom_fresh (union (fv_nom u) (union (fv_nom (n_sub t1 y t2)) (singleton x)))). apply aeq_refl.
Qed.
(* end hide *)

(** The following lemmas concern the expected behaviour of the metasubstitution when the metasubstitution's variable is equal to the abstraction's variable. Their proofs are straightforward from the definition [subst_rec_fun]. The corresponding version when the metasubstitution's variable is different from the abstraction's variable will be presented later. %\newline%*)

Lemma m_subst_abs_eq: forall u x t, {x := u}(n_abs x t) = n_abs x t.
Proof.
  intros u x t. unfold m_subst. rewrite subst_rec_fun_equation. rewrite eq_dec_refl. reflexivity.
Qed.

Lemma m_subst_sub_eq: forall u x t1 t2, {x := u}(n_sub t1 x t2) = n_sub t1 x ({x := u}t2).
Proof.
  intros u x t1 t2. unfold m_subst. rewrite subst_rec_fun_equation. rewrite eq_dec_refl. reflexivity.
Qed.

(* begin hide *)
Lemma fv_nom_remove: forall t u x y, y `notin` fv_nom u -> y `notin` remove x (fv_nom t) -> y `notin` fv_nom ({x := u}t).
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
        ** subst. apply notin_remove_3'; reflexivity.
        ** apply notin_union_1 in H. apply notin_remove_2. assumption.
    + apply IHn0.
      * assumption.
      * apply notin_remove_1 in H1. destruct H1. 
        ** subst. apply notin_remove_3'. reflexivity.
        ** apply notin_union_2 in H. apply notin_remove_2. assumption.
  - simpl in *. apply notin_union_3. 
    + apply notin_remove_1 in H1. destruct H1.
      * subst. apply notin_remove_3'. reflexivity.
      * simpl. apply notin_union_1 in H. assumption.
    + apply IHn. 
      * assumption. 
      * apply notin_remove_1 in H1. destruct H1.
        ** subst. apply notin_remove_3'. reflexivity.
        ** simpl. apply notin_union_2 in H. apply notin_remove_2. assumption.
  - simpl in *. apply notin_remove_1 in H1. destruct H1.
    + subst. apply notin_union_3.
      * case (y == z).
        ** intros Heq. subst. apply notin_remove_3'; reflexivity.
        ** intros Hneq. apply notin_remove_2. clear e1. apply notin_union_2 in _x0. apply notin_union_1 in _x0. 
           apply IHn.
          *** assumption.
          *** apply notin_remove_3; reflexivity.
      * simpl. apply IHn0. 
        ** assumption.
        ** apply notin_remove_3; reflexivity.
    + simpl. apply notin_union_3.
      * case (y == z). 
        ** intro Heq. subst. apply notin_remove_3; reflexivity.
        ** intro Hneq. apply notin_remove_2. apply notin_union_1 in H. apply IHn.
            *** assumption.
            *** apply notin_remove_1 in H. destruct H.
                **** simpl. subst. apply notin_remove_2. apply fv_nom_swap. clear e1. apply notin_union_2 in _x0. apply notin_union_1 in _x0. apply notin_union_1 in _x0. apply notin_remove_1 in _x0. destruct _x0.
                     ***** contradiction.
                     ***** assumption.
                **** apply notin_remove_2. case (y == y0). 
                     ***** intro Heq. subst. apply fv_nom_swap. clear e1. apply notin_union_2 in _x0. apply notin_union_1 in _x0. apply notin_union_1 in _x0. apply notin_remove_1 in _x0. destruct _x0.
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
(* end hide*)
                 
(** We will now prove some stability results for the metasubstitution w.r.t. $\alpha$-equivalence. More precisely, we will prove that if $t =_\alpha t'$ and $u =_\alpha u'$ then $\metasub{t}{x}{u} =_\alpha \metasub{t'}{x}{u'}$, where $x$ is a variable and $t, t', u$ and $u'$ are terms. This proof is split in two cases: firstly, we prove that if $u =_\alpha u'$ then $\metasub{t}{x}{u} =_\alpha \metasub{t}{x}{u'}, \forall x, t, u, u'$; secondly, we prove that if $t =_\alpha t'$ then $\metasub{t}{x}{u} =_\alpha \metasub{t'}{x}{u}, \forall x, t, t', u$. These two cases are then combined through the transitivity of the $\alpha$-equivalence relation. Nevertheless, this task was not straighforward. Let's follow the steps of our first trial.*)

Lemma aeq_m_subst_in_trial: forall t u u' x, u =a u' -> ({x := u}t) =a ({x := u'}t).
Proof.
  induction t as [y | t1 y | t1 t2 | t1 t2 y ] using n_sexp_induction. 
  - intros u u' x Haeq. unfold m_subst. repeat rewrite subst_rec_fun_equation. destruct (x == y).
    + assumption.
    + apply aeq_refl.
  - intros u u' x Haeq. unfold m_subst in *. repeat rewrite subst_rec_fun_equation. destruct (x == y).       
    + apply aeq_refl. 
    + destruct (atom_fresh (union (fv_nom u) (union (fv_nom (n_abs y t1)) (singleton x)))) as [x0]. destruct (atom_fresh (union (fv_nom u') (union (fv_nom (n_abs y t1)) (singleton x)))) as [x1]. case (x0 == x1). 
      * intro Heq. subst. apply aeq_abs_same. apply H. 
        ** reflexivity.
        ** assumption.
      * intro Hneq. apply aeq_abs_diff. 
        ** assumption.
        ** admit.
        ** Abort. (** %\noindent{\bf Proof.}% The proof is done by induction on the size of term [t], and we will focus on the abstraction case, %{\it i.e.}% $t = \lambda_y.t_1$. The goal in this case is $\metasub{(\lambda_y.t_1)}{x}{u} =_\alpha \metasub{(\lambda_y.t_1)}{x}{u'}$. %\begin{enumerate} \item If $x = y$ then the result is trivial by lemma $m\_subst\_abs\_eq$. \item If $x \neq y$ then we need two fresh names in order to propagate the metasubstitution inside the abstractions on each side of the $\alpha$-equation. Let $x_0$ be a fresh name not in the set $fv\_nom(u) \cup fv\_nom(\lambda_y. t_1)\cup \{x\}$, and $x_1$ be a fresh name not in the set $fv\_nom(u') \cup fv\_nom(\lambda_y. t_1)\cup \{x\}$. After propagating the metasubstitution we need to prove $\lambda_{x_0}.\metasub{(\swap{y}{x_0}{t_1})}{x}{u} =_\alpha \lambda_{x_1}.\metasub{(\swap{y}{x_1}{t_1})}{x}{u'}$, and we proceed by comparing $x_0$ and $x_1$: \begin{enumerate} \item If $x_0 = x_1$ then we are done by the induction hypothesis. \item Otherwise, we need to apply the rule $aeq\_abs\_diff$ and the goal is $\metasub{(\swap{y}{x_0}{t_1})}{x}{u} =_\alpha \swap{x_0}{x_1}{(\metasub{(\swap{y}{x_1}{t_1})}{x}{u'})}$. But in order to proceed we need to know how to propagate the swap inside the metasubstitution, which is the content of the following lemma: \end{enumerate}\end{enumerate}%*)

Lemma swap_m_subst: forall t u x y z, swap y z ({x := u}t) =a ({(vswap y z x) := (swap y z u)}(swap y z t)).
Proof.
  induction t as [w | t1 w | t1 t2 | t1 t2 w ] using n_sexp_induction. 
  - intros u x y z. unfold m_subst. rewrite subst_rec_fun_equation. destruct (x == w).
    + subst. simpl. rewrite subst_rec_fun_equation. rewrite eq_dec_refl. apply aeq_refl.
    + simpl. apply aeq_sym. rewrite subst_rec_fun_equation. apply (swap_neq y z) in n. destruct (vswap y z x == vswap y z w).
      * contradiction.
      * apply aeq_refl.
  - intros u x y z. unfold m_subst. rewrite subst_rec_fun_equation. destruct (x == w). 
    + subst. simpl. rewrite subst_rec_fun_equation. rewrite eq_dec_refl. apply aeq_refl. 
    + destruct (atom_fresh (union (fv_nom u) (union (fv_nom (n_abs w t1)) (singleton x)))) as [w0]. simpl. pose proof n as Hxz. apply (swap_neq y z) in n. apply aeq_sym. rewrite subst_rec_fun_equation. destruct (vswap y z x == vswap y z w).
      * contradiction.
      * destruct (atom_fresh
       (union (fv_nom (swap y z u))
          (union (fv_nom (n_abs (vswap y z w) (swap y z t1))) (singleton (vswap y z x))))) as [w1]. case (w1 == (vswap y z w0)).  
        ** intro Heq. subst. apply aeq_abs_same. unfold m_subst in *. apply aeq_sym. 
           rewrite <- swap_equivariance. apply H. reflexivity. 
        ** intro Hneq. apply aeq_abs_diff.
           *** assumption.
           *** admit.
           *** apply aeq_sym. unfold m_subst in H. apply aeq_trans with (swap (vswap y z w0) w1 (subst_rec_fun (swap y z (swap w w0 t1)) (swap y z u) (vswap y z x))). 
               **** apply aeq_swap. rewrite H.
               ***** apply aeq_refl.
               ***** reflexivity.
               **** rewrite H.
               ***** unfold vswap at 3. destruct (vswap y z x == vswap y z w0).
               ****** unfold vswap in e. destruct (x == y).
               ******* destruct (w0 == y). 
               ******** subst. repeat apply notin_union_2 in n0. apply notin_singleton_1 in n0. contradiction.
               ******** subst. destruct (w0 == z). 
               ********* subst. contradiction.
               ********* subst. contradiction.
               ******* destruct (x == z). 
               ******** subst. destruct (w0 == y).
               ********* subst. contradiction.
               ********* destruct (w0 == z).  
               ********** subst. repeat apply notin_union_2 in n0. apply notin_singleton_1 in n0. contradiction.
               ********** subst. contradiction.
               ******** destruct (w0 == y).
               ********* subst. contradiction.
               ********* destruct (w0 == z).
               ********** subst. contradiction.
               ********** subst. repeat apply notin_union_2 in n0. apply notin_singleton_1 in n0. contradiction.
               ****** destruct (vswap y z x == w1). 
               ******* rewrite e in *. repeat apply notin_union_2 in n2. apply notin_singleton_1 in n2. contradiction.
               ******* Abort. (** %\noindent{\bf Proof.}% We write the statement of the lemma in metanotation before starting the proof:%\newline%

$\forall t\ u\ x\ y\ z, \swap{y}{z}{(\metasub{t}{x}{u})} =_{\alpha} \metasub{\swap{y}{z}{t}}{\vswap{y}{z}{x}}{\swap{y}{z}{u}}$%\newline%

 The proof is by induction on the size of the term [t], and again we will focus only on the abstraction case, %{\it i.e.}% when $t = \lambda_w. t_1$. The goal in this case is $\swap{y}{z}{(\metasub{(\lambda_w.t_1)}{x}{u})} =_{\alpha} \metasub{(\swap{y}{z}{\lambda_w.t_1})}{\vswap{y}{z}{x}}{\swap{y}{z}{u}}$, and we proceed by comparing $x$ and $w$. %\begin{enumerate} \item If $x = w$ the $\alpha$-equality is trivial. \item If $x \neq w$ then we need a fresh name, say $w_0$, to be able to propagate the metasubstitution inside the abstraction on the LHS of the $\alpha$-equation. The variable $w_0$ is taken such that it is not in the set $fv\_nom(u)\cup fv\_nom(\lambda_w. t_1) \cup \{x\}$, and we get the goal $\lambda_{\vswap{y}{z}{w_0}}.\swap{y}{z}{(\metasub{\swap{w}{w_0}{t_1}}{x}{u})} =_{\alpha} \metasub{(\lambda_{\vswap{y}{z}{w}}.\swap{y}{z}{t_1})}{\vswap{y}{z}{x}}{\swap{y}{z}{u}}$. Now we propagate the metasubstitution over the abstraction in the RHS of the goal. Since $x\neq w$ implies $\vswap{y}{z}{x} \neq \vswap{y}{z}{w}$, we need another fresh name, say $w_1$, not in the set $fv\_nom(\swap{y}{z}{u}) \cup fv\_nom(\lambda_{\vswap{y}{z}{w}}.\swap{y}{z}{t_1}) \cup \{\vswap{y}{z}{x}\}$, and after the propagation we need to prove that $\lambda_{\vswap{y}{z}{w_0}}.\swap{y}{z}{(\metasub{\swap{w}{w_0}{t_1}}{x}{u})} =_{\alpha} \lambda_{w_1}.\metasub{(\swap{w_1}{\vswap{y}{z}{w}}{(\swap{y}{z}{t_1})})}{\vswap{y}{z}{x}}{\swap{y}{z}{u}}$. We consider two cases: either $w_1 = \vswap{y}{z}{w_0}$ or $w_1 \neq \vswap{y}{z}{w_0}$. In the former case, we apply the rule $\mbox{\it aeq}\_\mbox{\it abs}\_\mbox{\it same}$ and we are done by the induction hypothesis. When $w_1 \neq \vswap{y}{z}{w_0}$, the application of the rule $\mbox{\it aeq}\_\mbox{\it abs}\_\mbox{\it diff}$ generates the goal

\begin{equation}\label{ext:swap}\swap{w_1}{\vswap{y}{z}{w_0}}{\swap{y}{z}{(\metasub{\swap{w}{w_0}{t_1}}{x}{u})}} =_{\alpha} \metasub{(\swap{w_1}{\vswap{y}{z}{w}}{(\swap{y}{z}{t_1})})}{\vswap{y}{z}{x}}{\swap{y}{z}{u}} \end{equation}

We can use the induction hypothesis to propagate the swap inside the metasubstitution, and then we get an $\alpha$-equality with metasubstitution as main operation on both sides, whose corresponding components are $\alpha$-equivalent. In a more abstract way, we have to prove an $\alpha$-equality of the form $\metasub{t}{x}{u} =_\alpha \metasub{t'}{x}{u'}$, where $t =_\alpha t'$ and $u =_\alpha u'$, but this is exactly what we were trying to prove  in the previous lemma. \end{enumerate}% Therefore, we are in a circular problem because both [aeq_m_subst_in_trial] and [swap_m_subst] depend on each other to be proved!

Our solution to this problem consists in taking advantage of the fact that $\alpha$-equivalent terms have the same set of free variables (see lemma [aeq_fv_nom]), and noting that the external swap in the LHS of (%\ref{ext:swap}%) was generated by the application of the rule [aeq_abs_diff] because the abstractions have different bindings. Let's go back to the proof of lemma [aeq_m_subst_in]: *)

(* The problem is that we cannot rewrite $\alpha$-equalities inside metasubstitution unless we prove some special lemmas stating the compatibilities between them using the [Equations] library or something similar. We will present a solution that do not use any additional library, but it adds the following axiom to the formalization:

 Axiom Eq_implies_equality: forall s s': atoms, s [=] s' -> s = s'.

This axiom transforms a set equality into a syntactic equality. This will allow us to rewrite sets of atoms in a more flexible way. To show how it works, we will start proving the lemma [aeq_m_subst_in] without the need of the lemma [swap_m_subst]:
(* begin hide *)
Axiom Eq_implies_equality: forall t1 t2, t1 =a t2 -> fv_nom t1 = fv_nom t2.
(* end hide *) 
*)
Lemma aeq_m_subst_in: forall t u u' x, u =a u' -> ({x := u}t) =a ({x := u'}t).
Proof.
  induction t as [y | t1 y | t1 t2 | t1 t2 y ] using n_sexp_induction. 
  - intros u u' x Haeq. unfold m_subst. repeat rewrite subst_rec_fun_equation. destruct (x == y).
    + assumption.
    + apply aeq_refl.
  - intros u u' x Haeq. unfold m_subst in *. repeat rewrite subst_rec_fun_equation. destruct (x == y). 
    + apply aeq_refl. 
    + pose proof Haeq as Hfv. apply aeq_fv_nom_eq in Hfv. rewrite Hfv. destruct (atom_fresh (union (fv_nom u') (union (fv_nom (n_abs y t1)) (singleton x)))). apply aeq_abs_same. apply H. 
      * reflexivity.
      * assumption.
  - intros u u' x Haeq. unfold m_subst in *. rewrite subst_rec_fun_equation. apply aeq_sym. rewrite subst_rec_fun_equation. apply aeq_app.
    + apply IHt2. apply aeq_sym. assumption.
    + apply IHt1. apply aeq_sym. assumption.
  - intros u u' x Haeq. case (x == y).
    + intro Heq. subst. repeat rewrite m_subst_sub_eq. apply aeq_sub_same.
      * apply aeq_refl.
      * apply IHt1. assumption.
    + intro Hneq. unfold m_subst in *. rewrite subst_rec_fun_equation. apply aeq_sym. rewrite subst_rec_fun_equation. destruct (x == y).
      * contradiction.
      * pose proof Haeq as Hfv. apply aeq_fv_nom_eq in Hfv. rewrite Hfv. destruct (atom_fresh (union (fv_nom u') (union (fv_nom ([y := t2]t1)) (singleton x)))). apply aeq_sub_same.     
        ** apply H.
           *** reflexivity.
           *** apply aeq_sym. assumption.
        ** apply IHt1. apply aeq_sym. assumption.
Qed. (** %\noindent{\bf Proof.}% We go directly to the abstraction case. When $t = \lambda_y.t_1$, the goal is $\metasub{(\lambda_y.t_1)}{x}{u} =_\alpha \metasub{(\lambda_y.t_1)}{x}{u'}$. If $x \neq y$ then the fresh name needed for the LHS must not belong to the set $fv\_nom(u) \cup fv\_nom(\lambda_y. t_1)\cup \{x\}$, while the fresh name for the RHS must not belong to $fv\_nom(u' ) \cup fv\_nom(\lambda_y. t_1)\cup \{x\}$. These sets differ only by the subsets $fv\_nom(u)$ and $fv\_nom(u' )$. Nevertheless, these subsets are equal because $u$ and $u'$ are $\alpha$-equivalent (see lemma [aeq_fv_nom]). Concretely, the current goal is as follows:

<<
 (let (z, _) := atom_fresh (union (fv_nom u) (union (fv_nom (n_abs y t1))
         (singleton x))) in n_abs z (subst_rec_fun (swap y z t1) u x)) =a
 (let (z, _) := atom_fresh (union (fv_nom u') (union (fv_nom (n_abs y t1))
            (singleton x))) in n_abs z (subst_rec_fun (swap y z t1) u' x))
>>

%\noindent% where the sets $fv\_nom(u)$ and $fv\_nom(u')$ appear in different $let$ expressions, each one is responsible for generating one fresh name. But since these sets are equal, if one could replace $fv\_nom(u)$ by $fv\_nom(u')$ (or vice-versa) then only one fresh name is generated after evaluating the [atom_fresh] function. Nevertheless, the only way that we managed to do such replacement was by adding the following axiom:

<<
Axiom Eq_implies_equality: forall t1 t2, t1 =a t2 -> fv_nom t1 = fv_nom t2.
>>

This axiom is similar to lemma [aeq_fv_nom] where the set equality [[=]] was replaced by the syntactic (Leibniz) equality [=]. Now, we can generate just one fresh name and propagate the metasubstitution on both sides of the goal, and we are done by the induction hypothesis. The case of the explicit substitution is similar, and with this strategy we avoid both the rules $\mbox{\it aeq}\_\mbox{\it abs}\_\mbox{\it diff}$ and $\mbox{\it aeq}\_\mbox{\it sub}\_\mbox{\it diff}$ that introduce swappings. $\hfill\Box$*)
       
(* begin hide *)
Lemma aeq_sub_notin: forall t1 t1' t2 t2' x y, x <> y ->  n_sub t1 x t2 =a n_sub t1' y t2' -> x `notin` fv_nom t1'.
Proof.
  intros t1 t1' t2 t2' x y Hneq Haeq. inversion Haeq; subst.
  - contradiction.
  - assumption.
Qed.
(* end hide *)

(** The next lemma, named [aeq_m_subst_out] will benefit the strategy used in the previous proof, but it is not straightfoward.*)

Lemma aeq_m_subst_out: forall t t' u x, t =a t' -> ({x := u}t) =a ({x := u}t').
Proof.
    (* 
  induction 1.
  - apply aeq_refl.
  - case (x == x0).
    + intro Heq. subst. repeat rewrite m_subst_abs_eq. apply aeq_abs_same. assumption.
    + intro Hneq. unfold m_subst. repeat rewrite subst_rec_fun_equation. destruct (x == x0).
      * subst. contradiction.
      * pose proof H as Hfv. apply aeq_fv_nom in Hfv. apply aeq_fv_nom_eq in Hfv. simpl. rewrite Hfv. destruct (atom_fresh (union (fv_nom u) (union (remove x0 (fv_nom t2)) (singleton x)))). apply aeq_abs_same. *)
  induction t as [y | t1 y | t1 t2 | t1 t2 y] using n_sexp_induction. 
  - intros t' u x Haeq. inversion Haeq; subst. apply aeq_refl.
  - intros t' u x Haeq. inversion Haeq; subst. 
    + case (x == y).  
      * intro Heq. subst. repeat rewrite m_subst_abs_eq. assumption. 
      * intro Hneq. unfold m_subst in *. repeat rewrite subst_rec_fun_equation. destruct (x == y).
        ** contradiction.
        ** simpl. pose proof H3 as Haeq'. apply aeq_fv_nom_eq in H3. rewrite H3. destruct (atom_fresh (union (fv_nom u) (union (remove y (fv_nom t2)) (singleton x)))) as [z]. apply aeq_abs_same. apply H.
           *** reflexivity. 
           *** apply aeq_swap1. assumption. 
    + case (x == y). 
      * intro Heq. subst. rewrite m_subst_abs_eq. unfold m_subst in *. rewrite subst_rec_fun_equation. destruct (y == y0).
        ** contradiction.
        ** destruct (atom_fresh (union (fv_nom u) (union (fv_nom (n_abs y0 t2)) (singleton y)))) as [x]. apply aeq_trans with (n_abs x (swap y0 x t2)).
           *** apply aeq_trans with (n_abs y0 t2). 
               **** assumption.
               **** case (x == y0).
                    ***** intro Heq. subst. rewrite swap_id. apply aeq_refl.
                    ***** intro Hneq. apply aeq_abs_diff.
                    ****** apply aux_not_equal. assumption.
                    ****** apply fv_nom_swap. apply notin_union_2 in n0. apply notin_union_1 in n0. simpl in n0. apply notin_remove_1 in n0. destruct n0.
                    ******* symmetry in H0. contradiction.
                    ******* assumption.
                    ****** rewrite (swap_symmetric _ y0 x). rewrite swap_involutive. apply aeq_refl.
           *** apply aeq_abs_same. apply aeq_sym. apply m_subst_notin. repeat apply notin_union_2 in n0. apply notin_singleton_1 in n0. apply fv_nom_remove_swap; assumption. 
      * intro Hneq. case (x == y0).
        ** intro Heq. subst. rewrite m_subst_abs_eq. apply aeq_trans with (n_abs y t1).
           *** apply m_subst_notin. apply aeq_sym in Haeq. apply aeq_abs_notin in Haeq.
               ****  simpl. apply notin_remove_2. assumption.
               **** assumption.
           *** assumption.
        ** intro Hneq'. unfold m_subst in *. repeat rewrite subst_rec_fun_equation. destruct (x == y).
           *** contradiction.
           *** destruct (x == y0).
               **** contradiction.
               **** pose proof Haeq as Hfv. apply aeq_fv_nom_eq in Hfv. rewrite Hfv. destruct (atom_fresh (union (fv_nom u) (union (fv_nom (n_abs y0 t2)) (singleton x)))) as [x0]. apply  aeq_abs_same. apply H. 
                    ***** reflexivity.
                    ***** apply (aeq_swap _ _ y x0) in H5. rewrite H5. case (x0 == y0).
                    ****** intro Heq. subst. rewrite swap_id. rewrite (swap_symmetric _ y y0). rewrite swap_involutive. apply aeq_refl.
                    ****** intro Hneq''. rewrite (swap_symmetric _ y x0). rewrite (swap_symmetric _ y0 y). rewrite (swap_symmetric _ y0 x0). apply aeq_swap_swap.
                    ******* apply notin_union_2 in n1. apply notin_union_1 in n1. simpl in n1. apply notin_remove_1 in n1. destruct n1.
                    ******** symmetry  in H0. contradiction.
                    ******** assumption.
                    ******* assumption. 
  - intros t u x Haeq. inversion Haeq; subst. clear Haeq. unfold m_subst in *. rewrite subst_rec_fun_equation. apply aeq_sym. rewrite subst_rec_fun_equation. apply aeq_app.
    + apply aeq_sym. apply IHt2. assumption.
    + apply aeq_sym. apply IHt1. assumption.
  - intros t u x Haeq. (*  Initially, the goal is [({x := u} ([y := t2] t1)) =a ({x := u} t)], and according to the definition of $\alpha$-equivalence, there are 2 subcases.*) inversion Haeq; subst. (* %\newline {\bf 1.}% In the first subcase, [t = ([y := t2'] t1')] with [t1 =a t1'] and [t2 =a t2'].*)
    + case (x == y). (* As in the abstraction case, we start comparing [x] and [y].*)
      * intro Heq. subst. (* When [x = y], the proof is trivial because both metasubstitutions are removed by applying lemma [m_subst_sub_eq] twice, and we get the following goal: [([y := {y := u} t2] t1) =a ([y := {y := u} t2'] t1')]*) repeat rewrite m_subst_sub_eq. apply aeq_sub_same. (* We compare the corresponding components of the explicit substitution via the constructor [aeq_sub_same], and the first case is trivial since [t1 =a t1'].*)
        ** assumption.
        ** apply IHt1. assumption. (* In order to show that [({y := u} t2) =a ({y := u} t2')], we apply the induction hypothesis.*)
      * intro Hneq. (* When [x <> y], we propagate the metasubstitutions inside the explicit substitution on both sides.*) unfold m_subst in *. rewrite subst_rec_fun_equation. apply aeq_sym. rewrite subst_rec_fun_equation. destruct (x == y).
        ** contradiction.
        ** pose proof H4 as Hfvt1. apply aeq_fv_nom_eq in Hfvt1. pose proof H5 as Hfvt2. apply aeq_fv_nom_eq in Hfvt2. simpl. rewrite Hfvt1. rewrite Hfvt2. destruct (atom_fresh (union (fv_nom u) (union (union (remove y (fv_nom t1')) (fv_nom t2')) (singleton x)))). (* As [t1 =a t1'] and [t2 =a t2'], we have that [fv_nom t1 = fv_nom t1'] and [fv_nom t2 = fv_nom t2'], and we need just one fresh name, say [x0], to do these propagations, as long as [x0] does not belong to the set $fv(u)\cup fv(\metasub{t_1'}{y}{t_2'})\cup \{x\}$. The goal after the propagation is [([x0 := {x := u}t2'] {x := u}(swap y x0 t1')) =a ([x0 := {x := u}t2] {x := u}(swap y x0 t1))], and we proceed by a componentwise comparison via constructor [aeq_sub_same].*) apply aeq_sub_same.
           *** apply H. (* Each subcase is proved by the induction hypothesis.*)
               **** apply aeq_size in H4. symmetry. assumption.
               **** apply aeq_swap. apply aeq_sym. assumption.
           *** apply aeq_sym. apply IHt1. assumption.
    + case (x == y). (* %\newline {\bf 2.}% In the second subcase, the goal is [({x := u} ([y := t2] t1)) =a ({x := u} ([y0 := t2'] t1'))] with [y <> y0]. We proceed by comparing [x] and [y].*)
      * intro Heq. subst. (* If [x = y] then the metasubstitution of the LHS only propagates to the subterm [t2].*) rewrite m_subst_sub_eq. case (y == y0). 
        ** intro Heq. subst. contradiction. 
        ** intro Hneq. (* In the RHS, the metasubstitution is propagated to both subterms because [x = y <> y0].*) unfold m_subst in *. apply aeq_sym. rewrite subst_rec_fun_equation. destruct (y == y0).
           *** contradiction.
           *** destruct (atom_fresh (union (fv_nom u) (union (fv_nom ([y0 := t2'] t1')) (singleton y)))). (* To do so, we take a fresh name [x] that is not in the set $fv(u) \cup fv(\esub{t_1'}{y_0}{t_2'})$. We proceed by comparing componentwise according to the constructor [aeq_sub_diff].*) apply aeq_sub_diff.
               **** apply aeq_sym. apply IHt1. assumption. (* The proof that [{y := u}t2 =a {y := u}t2'] is straightforward by the induction hypothesis.*)
               **** repeat apply notin_union_2 in n0. apply notin_singleton_1 in n0. apply aux_not_equal. assumption.
               **** pose proof n0 as Hfv. apply notin_union_2 in n0. apply notin_union_1 in n0. simpl in n0. apply notin_union_1 in n0. apply (aeq_swap1 _ _ y0 y) in H7. rewrite swap_involutive in H7. apply aeq_fv_nom in H7. rewrite <- H7 in n0. rewrite <- H7 in H6. case (x == y0).
                    ***** intro Heq. subst. apply fv_nom_swap_2 in H6. assumption.
                    ***** intro Hneq'. apply notin_remove_1 in n0.
                    ****** destruct n0.
                    ******* symmetry in H0. contradiction.
                    ******* apply fv_nom_swap_remove in H0.
                    ******** assumption.
                    ******** repeat apply notin_union_2 in Hfv. apply notin_singleton_1 in Hfv. apply aux_not_equal. assumption.
                    ******** assumption.
               **** apply aeq_trans with (swap y0 x t1'). (* The proof that [{y := u}(swap y0 x t1') =a swap y x t1] is done by lemma [m_subst_notin] since [y <> y0], [y <> x] and [y] is not in $fv(t_1')$.*)
                    ***** apply m_subst_notin. apply fv_nom_remove_swap.
                    ****** repeat apply notin_union_2 in n0. apply notin_singleton_1 in n0. assumption.
                    ****** assumption.
                    ****** assumption.
                    ***** apply (aeq_swap1 _ _ y x) in H7. rewrite H7.  apply aeq_sym. rewrite (swap_symmetric _ y x). rewrite (swap_symmetric _ y0 y). rewrite (swap_symmetric _ y0 x). case (x == y0).
                    ****** intro Heq. subst. rewrite (swap_symmetric _ y0 y). rewrite swap_involutive. rewrite swap_id. apply aeq_refl.
                    ****** intro Hneq'. apply aeq_swap_swap.
                    ******* apply notin_union_2 in n0. apply notin_union_1 in n0. simpl in n0. apply notin_union_1 in n0. apply notin_remove_1 in n0. destruct n0.
                    ******** symmetry in H0. contradiction.
                    ******** assumption.
                    ******* assumption.  
      * intro Hneq. (* When [x <> y], we start with the following goal: [({x := u} ([y := t2] t1)) =a ({x := u} ([y0 := t2'] t1'))]. We proceed by comparing [x] and [y0].*) case (x == y0).
        ** intro Heq. subst. (* When [x = y0], the strategy is similar to the previous case [x = y] and [x <> y0].*) rewrite m_subst_sub_eq. unfold m_subst. rewrite subst_rec_fun_equation. destruct (y0 == y).
           *** contradiction.
           *** destruct (atom_fresh (union (fv_nom u) (union (fv_nom ([y := t2] t1)) (singleton y0)))). apply aeq_sub_diff.
               **** apply IHt1. assumption. 
               **** repeat apply notin_union_2 in n0. apply notin_singleton_1 in n0. apply aux_not_equal. assumption.
               **** pose proof n0 as Hfv. apply notin_union_2 in n0. apply notin_union_1 in n0. simpl in n0. apply notin_union_1 in n0. apply (aeq_swap1 _ _ y0 y) in H7. rewrite swap_involutive in H7. apply aeq_fv_nom in H7. rewrite <- H7. case (x == y).
                    ***** intro Heq. subst. rewrite (swap_symmetric _ y0 y). apply fv_nom_swap. apply aeq_sym in Haeq. apply aeq_sub_notin in Haeq.
                    ****** assumption.
                    ****** assumption.
                    ***** intro Hneq'. apply notin_remove_1 in n0. destruct n0.
                    ******* symmetry in H0. contradiction.
                    ******* apply fv_nom_remove_swap.
                    ******** assumption.
                    ******** repeat apply notin_union_2 in Hfv. apply notin_singleton_1 in Hfv. apply aux_not_equal. assumption.
                    ******** assumption.
               **** apply aeq_trans with (swap y x t1). 
                    ***** apply m_subst_notin. apply aeq_sym in Haeq. apply aeq_sub_notin in Haeq. 
                    ****** apply fv_nom_remove_swap.
                    ******* repeat apply notin_union_2 in n0. apply notin_singleton_1 in n0. assumption.
                    ******* assumption.
                    ******* assumption.
                    ****** assumption.
                    ***** apply (aeq_swap1 _ _ y x) in H7. rewrite H7. rewrite (swap_symmetric _ y x). rewrite (swap_symmetric _ y0 y). rewrite (swap_symmetric _ y0 x). case (x == y).
                    ****** intro Heq. subst. rewrite swap_id. apply aeq_refl.
                    ****** intro Hneq'. apply aeq_swap_swap.
                    *******  pose proof n0 as Hfv. apply notin_union_2 in n0. apply notin_union_1 in n0. simpl in n0. apply notin_union_1 in n0. apply notin_remove_1 in n0. destruct n0.
                    ******** symmetry in H0. contradiction.
                    ******** apply aeq_swap in H7. apply aeq_sym in H7. apply (aeq_swap1 _ _ y0 y) in H7. rewrite swap_involutive in H7. apply aeq_fv_nom in H7. rewrite H7. apply fv_nom_remove_swap.
                    ********* assumption.  
                    ********* repeat apply notin_union_2 in Hfv. apply notin_singleton_1 in Hfv. apply aux_not_equal. assumption.
                    ********* assumption.
                    ******* assumption.
        ** intro Hneq'. (* The last case is when [x <> y] and [x <> y0]. The current goal is [({x := u} ([y := t2] t1)) =a ({x := u} ([y0 := t2'] t1'))].*) unfold m_subst in *. rewrite subst_rec_fun_equation. destruct (x == y).
           *** contradiction.
           *** apply aeq_sym. rewrite subst_rec_fun_equation. destruct (x == y0).
               **** contradiction.
               ****  apply aeq_fv_nom_eq in Haeq. simpl in *. rewrite Haeq. destruct (atom_fresh (union (fv_nom u) (union (union (remove y0 (fv_nom t1')) (fv_nom t2')) (singleton x)))). (* We take a fresh name [x0] that is not in the set $fv(u)\cup fv(\esub{t_1'}{y_0}{t_2'})\cup \{ x \}$, and propagate the metasubstitutions inside the explicit substitutions according to the definition of the metasubstitution. The current goal is [([x0 := {x := u}t2']({x := u}(swap y0 x0 t1'))) =a
  ([x0 := {x := u}t2]({x := u}(swap y x0 t1)))], and we proceed using the constructor [aeq_sub_same]. Each subcase is proved by the induction hypothesis. *) apply aeq_sub_same.
                    ***** apply H.
                    ****** apply aeq_size in H7. rewrite swap_size_eq in H7. symmetry. assumption.
                    ****** apply (aeq_swap1 _ _ y x0) in H7. rewrite H7. apply aeq_sym. rewrite (swap_symmetric _ y x0). rewrite (swap_symmetric _ y0 y). rewrite (swap_symmetric _ y0 x0). case (x0 == y0).
                    ******* intro Heq. subst. rewrite (swap_symmetric _ y0 y). rewrite swap_involutive. rewrite swap_id. apply aeq_refl.
                    ******* intro Hneq''. apply aeq_swap_swap.
                    ******** apply notin_union_2 in n1. apply notin_union_1 in n1. apply notin_union_1 in n1. apply notin_remove_1 in n1. destruct n1. subst. contradiction.
                    ********* assumption.
                    ******** assumption.
                    ***** apply aeq_sym. apply IHt1. assumption.
Qed. (** %\noindent{\bf Proof.}% The proof is by induction on the size of the term [t]. Note that induction on the hypothesis [t =a t'] does not work due to a similar problem involving swaps that appears when structural induction on [t] is used. The abstraction and the explicit substitution are the interesting cases.

In the abstraction case, we need to prove that $\metasub{(\lambda_y.t_1)}{x}{u} =_{\alpha} \metasub{t'}{x}{u}$, where $\lambda_y. t_1 =_{\alpha} t'$ by hypothesis. Therefore, $t'$ must be an abstraction, and according to our definition of $\alpha$-equivalence there are two possible subcases: %\begin{enumerate} \item In the first subcase, $t' = \lambda_y.t_2$, where $t_1 =_{\alpha} t_2$, and hence the current goal is $\metasub{(\lambda_y.t_1)}{x}{u} =_{\alpha} \metasub{(\lambda_y.t_2)}{x}{u}$. We proceed by comparing $x$ and $y$:
\begin{enumerate}
 \item If $x = y$ then, we are done by using twice lemma $m\_subst\_abs\_eq$.
 \item When $x \neq y$, then we need to propagate the metasubstitution on both sides of the goal. On the LHS, we need a fresh name that is not in the set $fv(u)\cup fv(\lambda_y.t_1) \cup \{x\}$, while for the RHS, the fresh name cannot belong to the set $fv(u)\cup fv(\lambda_y.t_2) \cup \{x\}$. From the hypothesis $t_1 =_{\alpha} t_2$, we know, by lemma $aeq\_fv\_nom$, that the sets $fv\_nom(t_1)$ and  $fv\_nom(t_2)$ are equal. Therefore, we can take just one fresh name, say $z$, and propagate both metasubstitutions over abstractions with the same binding, and we conclude with the induction hypothesis.
\end{enumerate}
\item In the second subcase, $t' = \lambda_{y_0}.t_2$, where $t_1 =_{\alpha} \swap{y_0}{y}{t_2}$ and $y \neq y_0$. The current goal is $$\metasub{(\lambda_y.t_1)}{x}{u} =_{\alpha} \metasub{(\lambda_{y_0}.t_2)}{x}{u}$$ and we proceed by comparing $x$ and $y$:
\begin{enumerate}
 \item If $x = y$ then the goal simplifies to $\lambda_y.t_1 =_{\alpha} \metasub{(\lambda_{y_0}.t_2)}{x}{u}$ by lemma $m\_subst\_abs\_eq$, and we pick a fresh name $x$, that is not in the set $fv\_nom(u) \cup fv\_nom(\lambda_{y_0}.t_2) \cup \{y\}$, and propagate the metasubstitution on the RHS of the goal, resulting in the new goal $\lambda_y. t_1 =_{\alpha} \lambda_x.\metasub{(\swap{y_0}{x}{t_2})}{y}{u}$. Note that the metasubstitution on the RHS has no effect in the term $\swap{y_0}{x}{t_2}$ because $y \neq y_0$, $y \neq x$ and $y$ does not occur free in $t_2$ and we conclude by hypothesis.
\item If $x \neq y$ then we proceed by comparing $x$ and $y_0$ on the RHS, and the proof, when $x = y_0$, is analogous to the previous subcase. When both $x \neq y$ and $x \neq y_0$ then we need to propagate the metasubstitution on both sides of the goal $\metasub{(\lambda_y.t_1)}{x}{u} =_{\alpha} \metasub{(\lambda_{y_0}.t_2)}{x}{u}$. We have that $\lambda_y.t_1 =_{\alpha} \lambda_{y_0}.t_2$ and hence the sets $fv\_nom(\lambda_y.t_1)$ and $fv\_nom(\lambda_{y_0}.t_2)$ are equal. Therefore, only one fresh name, say $x_0$, that is not in the set $x_0 \notin fv\_nom(u) \cup fv\_nom(\lambda_{y_0}.t_2) \cup \{x\}$ is enough to fulfill the conditions for propagating the metasubstitutions on both sides of the goal, and we are done by the induction hypothesis.
\end{enumerate}
\item The explicit substitution operation is also interesting, but we will not comment because we are running out of space. $\hfill\Box$
\end{enumerate}%*)
   
(** As a corollary, one can join the lemmas [aeq_m_subst_in] and [aeq_m_subst_out] as follows:*)

Corollary aeq_m_subst_eq: forall t t' u u' x, t =a t' -> u =a u' -> ({x := u}t) =a ({x := u'}t').
Proof.
  intros t t' u u' x H1 H2. apply aeq_trans with ({x:=u}t').
  - apply aeq_m_subst_out. assumption.
  - apply aeq_m_subst_in. assumption.
Qed.

(** Now, we show how to propagate a swap inside metasubstitutions using the decomposition of the metasubstitution provided by the corollary [aeq_m_subst_eq].%\newline% *)

Lemma swap_subst_rec_fun: forall x y z t u, swap x y ({z := u}t) =a ({(vswap x y z) := (swap x y u)}(swap x y t)).
Proof.
  intros x y z t u. destruct (x == y). 
  - subst. repeat rewrite swap_id. rewrite vswap_id. apply aeq_refl.
  - generalize dependent u. generalize dependent z. generalize dependent y. generalize dependent x. induction t as  [y' | t1 y' | t1 t2 | t1 t2 y'] using n_sexp_induction.    
    + intros x y Hneq z u. unfold m_subst. rewrite subst_rec_fun_equation. destruct (z == y').
      * subst. simpl swap at 2. rewrite subst_rec_fun_equation. rewrite eq_dec_refl. apply aeq_refl.
      * pose proof n as Hswap. apply (swap_neq x y) in n. simpl swap at 2. rewrite subst_rec_fun_equation. destruct (vswap x y z == vswap x y y').
        ** contradiction.
        ** simpl swap. apply aeq_refl.
    + intros x y Hneq z u. simpl. case (y' == z). 
      * intro Heq. subst. repeat rewrite m_subst_abs_eq. simpl. apply aeq_refl. 
      * intro Hneq'. unfold m_subst in *. repeat rewrite subst_rec_fun_equation. destruct (z == y').
        ** symmetry in e. contradiction.
        ** destruct (vswap x y z == vswap x y y').
           *** apply (swap_neq x y) in n. contradiction.
           *** simpl. destruct (atom_fresh (union (fv_nom u) (union (remove y' (fv_nom t1)) (singleton z)))) as [x0]. destruct (atom_fresh (union (fv_nom (swap x y u)) (union (remove (vswap x y y') (fv_nom (swap x y t1))) (singleton (vswap x y z))))) as [x1]. simpl. case (x1 == vswap x y x0).
               **** intro Heq. subst. apply aeq_abs_same. rewrite H. 
                    ***** rewrite <- swap_equivariance. apply aeq_refl.
                    ***** reflexivity.
                    ***** assumption.
               **** intro Heq''. apply aeq_abs_diff.  
                    ***** apply aux_not_equal. assumption.
                    ***** apply fv_nom_remove.
                    ****** apply notin_fv_nom_equivariance. apply notin_union_1 in n1. assumption.
                    ****** apply notin_remove_2. pose proof n1 as Hx0. case (y' == x0).
                    ******** intro Heq. subst. apply fv_nom_swap. apply notin_union_2 in n2. apply notin_union_1 in n2. apply notin_remove_1 in n2. destruct n2.
                    ********* symmetry in H0. contradiction.
                    ********* assumption.
                    ******** intros Hneq'''. apply fv_nom_remove_swap.
                    ********* apply aux_not_equal. assumption.
                    ********* apply aux_not_equal. apply swap_neq. assumption.
                    ********* apply notin_union_2 in n1. apply notin_union_1 in n1. apply notin_remove_1 in n1. destruct n1.
                    ********** contradiction.
                    ********** apply notin_fv_nom_equivariance. assumption. 
                    ***** rewrite H. 
                    ****** apply aeq_sym. rewrite H.
                    ******* replace (vswap x1 (vswap x y x0) (vswap x y z)) with (vswap x y z).
                    ******** apply aeq_m_subst_eq.
                    ********* rewrite (swap_symmetric _ x1 (vswap x y x0)). rewrite (swap_symmetric _ (vswap x y y') x1). case (x0 == y'). 
                    *********** intro Heq. subst. rewrite (swap_symmetric _ (vswap x y y') x1). rewrite swap_involutive. rewrite swap_id. apply aeq_refl.
                    *********** intro Hneq''. rewrite (swap_symmetric _ y' x0). rewrite (swap_equivariance _ x y x0 y'). case (x1 == vswap x y y'). 
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
                    ******** symmetry. unfold vswap at 1. destruct (vswap x y z ==  x1).
                    ********* repeat apply notin_union_2 in n2. apply notin_singleton_1 in n2. contradiction.
                    ********* destruct (vswap x y z == vswap x y x0).
                    ********** repeat apply notin_union_2 in n1. apply notin_singleton_1 in n1. apply (swap_neq x y) in n1. contradiction.
                    ********** reflexivity.
                    ******* apply swap_size_eq.
                    ******* assumption.
                    ****** reflexivity.
                    ****** assumption.
    + intros x y H z u. unfold m_subst in *. rewrite subst_rec_fun_equation. simpl. apply aeq_sym. rewrite subst_rec_fun_equation. apply aeq_sym. apply aeq_app.
      * apply IHt2. assumption.
      * apply IHt1. assumption.
    + intros x y Hneq z u. simpl. case (y' == z). (* The case of the explicit substitution follows a similar strategy of the abstraction. The initial goal is to prove that [swap x y ({z := u}(n_sub t1 y' t2)) =a {(vswap x y z) := (swap x y u)}(swap x y (n_sub t1 y' t2))] and we start comparing the variables [y'] and [z].*)
      * intro Heq. subst. repeat rewrite m_subst_sub_eq. simpl. apply aeq_sub_same. (* When [y' = z], the metasubstitution has no effect on the body of the metasubstitution but it can still be propagated to the term [t2]. Therefore, this case is proved using the induction hypothesis over [t2]. *)
        ** apply aeq_refl.
        ** apply IHt1. assumption.
      * intro Hneq'. unfold m_subst. rewrite subst_rec_fun_equation. apply aeq_sym. rewrite subst_rec_fun_equation. destruct (z == y').
        ** symmetry in e. contradiction.
        ** destruct (vswap x y z == vswap x y y').
           *** apply (swap_neq x y) in n. contradiction.
           *** destruct (atom_fresh (union (fv_nom u) (union (fv_nom (n_sub t1 y' t2)) (singleton z)))). destruct (atom_fresh (union (fv_nom (swap x y u)) (union (fv_nom (n_sub (swap x y t1) (vswap x y y') (swap x y t2))) (singleton (vswap x y z))))). simpl in *. apply aeq_sym. case (x1 == vswap x y x0). (* When [y' <> z], then the metasubstitutions are propagated on both sides of the $\alpha$-equation. Analogously to the abstraction case, one new name for each propagation is created. Let [x0] be a new name not in the set $fv(\esub{t1}{y'}{t2})\cup fv(u) \cup \{z\}$, and [x1], a new name not in the set $fv(\esub{\swap{x}{y}{t1}}{\vswap{x}{y}{y'}}{\swap{x}{y}{t2}})\cup fv(\swap{x}{y}{u}) \cup \{\vswap{x}{y}{z}\}$. After the propagation step, we have the goal [[(vswap x y x0) := (swap x y ({z := u}t2))](swap x y ({z := u}(swap y' x0 t1))) =a
  [x1 := ({(vswap x y z) := (swap x y u)}(swap x y t2))]({(vswap x y z) := (swap x y u)}(swap (vswap x y y') x1 (swap x y t1)))]. We proceed by comparing [x1] and [(swap x y x0)].*)
               **** intro Heq. subst. apply aeq_sub_same. (* If [x1 = vswap x y x0] then after an application of the rule [aeq_sub_same], we are done by the induction hypothesis for both the body and the argument of the explicit substitution.*)
                    ***** rewrite <- swap_equivariance. apply H.
                    ****** reflexivity.
                    ****** assumption.
                    ***** apply IHt1. assumption.
               **** intro Hneq''. apply aeq_sub_diff.
                    ***** apply IHt1. assumption. (* If [x1 <> vswap x y x0] then we apply the rule [aeq_sub_diff] to decompose the explicit substitution in its components. The second component is straightforward  by the induction hypothesis.*)
                    ***** apply aux_not_equal. assumption.
                    ***** apply fv_nom_remove.
                    ****** apply notin_fv_nom_equivariance. apply notin_union_1 in n1. assumption.
                    ****** apply notin_remove_2. case (y' == x0).
                    ******* intro Heq. subst. apply fv_nom_swap. apply notin_union_2 in n2. apply notin_union_1 in n2. apply notin_union_1 in n2. apply notin_remove_1 in n2. destruct n2.
                    ******** symmetry in H0. contradiction.
                    ******** assumption.
                    ******* intro Hneq'''. apply fv_nom_remove_swap.
                    ******** apply aux_not_equal. assumption.
                    ******** apply (swap_neq x y) in Hneq'''. apply aux_not_equal. assumption.
                    ******** apply notin_fv_nom_equivariance. apply notin_union_2 in n1. apply notin_union_1 in n1. apply notin_union_1 in n1. apply notin_remove_1 in n1. destruct n1.
                    ********* contradiction.
                    ********* assumption.
                    ***** unfold m_subst in *. rewrite H. (* The first component follows the strategy used in the abstraction case. The current goal, obtained after the application of the rule [aeq_sub_diff] is [swap x y ({z := u}(swap y' x0 t1)) =a
  swap x1 (vswap x y x0) ({(vswap x y z) := (swap x y u)}(swap (vswap x y y') x1 (swap x y t1)))]. The induction hypothesis is used twice to propagate the swap on both the LHS and RHS of the $\alpha$-equality. This swap has no effect on the variable [z] of the metasubstitution, therefore we can apply lemma [aeq_m_subst_eq], and each generated case is proved by routine manipulation of swaps. *)
                    ****** apply aeq_sym. rewrite H.
                    ******* replace (vswap x1 (vswap x y x0) (vswap x y z)) with (vswap x y z).
                    ******** apply aeq_m_subst_eq.
                    ********* rewrite (swap_symmetric _ x1 (vswap x y x0)). rewrite (swap_symmetric _ (vswap x y y') x1). case (x0 == y'). 
                    *********** intro Heq. subst. rewrite (swap_symmetric _ (vswap x y y') x1). rewrite swap_involutive. rewrite swap_id. apply aeq_refl.
                    *********** intro Hneq'''. rewrite (swap_symmetric _ y' x0). rewrite (swap_equivariance _ x y x0 y'). case (x1 == vswap x y y'). 
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
                    ******** symmetry. unfold vswap at 1. destruct (vswap x y z ==  x1).
                    ********* repeat apply notin_union_2 in n2. apply notin_singleton_1 in n2. contradiction.
                    ********* destruct (vswap x y z == vswap x y x0).
                    ********** repeat apply notin_union_2 in n1. apply notin_singleton_1 in n1. apply (swap_neq x y) in n1. contradiction.
                    ********** reflexivity.
                    ******* apply swap_size_eq.
                    ******* assumption.
                    ****** reflexivity.
                    ****** assumption.
Qed.
(** %\noindent{\bf Proof.}% Firstly, we write the lemma in metanotation: $\forall x\ y\ z\ t\ u, \swap{x}{y}{\metasub{t}{z}{u}} =_{\alpha} \metasub{\swap{x}{y}{t}}{\vswap{x}{y}{z}}{\swap{x}{y}{u}}$. Next, we compare $x$ and $y$, since the case $x = y$ is trivial. When $x \neq y$, the proof proceeds by induction on the size of the term $t$. The tricky cases are the abstraction and explicit substitution, and we comment just the former case. If $t = \lambda_{y'}.t_1$ then we must prove that $\swap{x}{y}{\metasub{(\lambda_{y'}.t_1)}{z}{u} =_{\alpha} \metasub{\swap{x}{y}{(\lambda{y'}.t_1)}}{\vswap{x}{y}{z}}{\swap{x}{y}{u}}}$. Firstly, we compare the variables $y'$ and $z$ according to the definition of the metasubstitution:                                          %\begin{enumerate}
\item When $y' = z$ the metasubstitution is erased according to the definition (\ref{msubst}) on both sides of the goal and we are done.
\item When $y' \neq z$ then the metasubstitutions on both sides of the goal need to be propagated inside the corresponding abstractions. In order to do so, a new name need to be created. Note that in this case, it is not possible to create a unique name for both sides because the two sets are different. In fact, in the LHS the fresh name cannot belong to the set $fv\_nom(\lambda_y'.t_1) \cup fv\_nom(u) \cup \{z\}$, while the name of the RHS cannot belong to the set $fv\_nom(\swap{x}{y}{\lambda_y'.t_1}) \cup fv\_nom(\swap{x}{y}{u}) \cup \{\vswap{x}{y}{z}\}$. Let $x_0$ be a fresh name that is not in the set $fv\_nom(\lambda_y'.t_1) \cup fv\_nom(u) \cup \{z\}$, and $x_1$ a fresh name that is not in the set $fv\_nom(\swap{x}{y}{\lambda_y'.t_1}) \cup fv\_nom(\swap{x}{y}{u}) \cup \{\vswap{x}{y}{z}\}$. After the propagation of the metasubstitutions, we have to prove that $\lambda_{\vswap{x}{y}{x0}}.(\swap{x}{y}{(\metasub{(\swap{y'}{x_0}{t_1})}{z}{u})} =_{\alpha} \lambda_{x_1}.(\metasub{\swap{(\vswap{x}{y}{y'})}{x_1}{(\swap{x}{y}{t_1})}}{\vswap{x}{y}{z}}{\swap{x}{y}{u}})$. We proceed by comparing $x_1$ with $\vswap{x}{y}{x_0}$.
\begin{enumerate}
\item If $x_1 = \vswap{x}{y}{x_0}$ then we use the induction hypothesis to propagate the swap inside the metasubstitution in the LHS, and we get the goal $\metasub{(\swap{x}{y}{(\swap{y'}{x_0}{t_1})})}{\vswap{x}{y}{z}}{\swap{x}{y}{u}}  =_{\alpha}
  \metasub{(\swap{(\vswap{x}{y}{y'})}{(\vswap{x}{y}{x_0})}{(\swap{x}{y}{t_1})})}{\vswap{x}{y}{z}}{\swap{x}{y}{u}}$ that is proved by the swap equivariance lemma $swap\_equivariance$.
 \item If $x_1 \neq \vswap{x}{y}{x_0}$ then by the rule $aeq\_abs\_diff$ we have to prove that the variable $\vswap{x}{y}{x_0}$ is not in the set of free variables of the term $\metasub{(\swap{\vswap{x}{y}{y'}}{x_1}{\swap{x}{y}{t_1}})}{\vswap{x}{y}{z}}{\swap{x}{y}{u}}$ and that $\swap{x}{y}{(\metasub{(\swap{y'}{x_0}{t_1})}{z}{u})} =_{\alpha}
  \swap{x_1}{(\vswap{x}{y}{x_0})}{(\metasub{(\swap{(\vswap{x}{y}{y'})}{x_1}{(\swap{x}{y}{t_1})})}{\vswap{x}{y}{z}}{\swap{x}{y}{u}}}$. The former condition is routine. The later condition is proved using the induction hypothesis twice to propagate the swaps inside the metasubstitutions on each side of the $\alpha$-equality. This swap has no effect on the variable $z$ of the metasubstitution because $x_1$ is different from $\vswap{x}{y}{z}$, and $x_0$ is different from $z$. Therefore we can apply lemma $aeq\_m\_subst\_eq$, and each generated case is proved by routine manipulation of swaps.
\end{enumerate} $\hfill\Box$
\end{enumerate}%*) 

(** The following two lemmas toghether with lemmas [m_subst_abs_eq] and [m_subst_sub_eq] are essential in simplifying the propagations of metasubstitution. They are presented here because they depend on lemma [swap_subst_rec_fun]. *)

Lemma m_subst_abs_neq: forall t u x y z, x <> y -> z `notin` fv_nom u `union` fv_nom (n_abs y t) `union` {{x}} -> {x := u}(n_abs y t) =a n_abs z ({x := u}(swap y z t)).
Proof.
  intros t u x y z H1 H2. unfold m_subst. rewrite subst_rec_fun_equation. destruct (x == y).
  - subst. contradiction.
  - destruct (atom_fresh (union (fv_nom u) (union (fv_nom (n_abs y t)) (singleton x)))). case (x0 == z).
    + intro Heq. subst. apply aeq_refl.
    + intro Hneq. apply aeq_abs_diff.
      * assumption.
      * apply fv_nom_remove.
        ** apply notin_union_1 in n0. assumption.
        ** simpl in *. case (x0 == y).
           *** intro Heq. subst. apply notin_remove_2. apply fv_nom_swap. apply notin_union_2 in H2. apply notin_union_1 in H2. simpl in H2. apply notin_remove_1 in H2. destruct H2.
               **** contradiction.
               **** assumption.
           *** intro Hneq'. apply notin_remove_2. apply notin_union_2 in n0. apply notin_union_1 in n0. apply notin_remove_1 in n0. destruct n0.
               **** symmetry in H. contradiction.
               **** apply fv_nom_remove_swap; assumption.
      * apply aeq_sym. apply aeq_trans with (subst_rec_fun (swap z x0 (swap y z t)) (swap z x0 u) (vswap z x0 x)).
        ** apply swap_subst_rec_fun.
        ** replace (vswap z x0 x) with x.
           *** apply aeq_m_subst_eq.
               **** rewrite (swap_symmetric _ z x0). rewrite (swap_symmetric _ y z). rewrite (swap_symmetric _ y x0). case (x0 == y).
                    ***** intro Heq. subst. rewrite (swap_symmetric _ y z). rewrite swap_involutive. rewrite swap_id. apply aeq_refl.
                    ***** intro Hneq'. case (z == y).
                    ****** intro Heq. subst. rewrite swap_id. apply aeq_refl.
                    ****** intro Hneq''. apply aeq_swap_swap.
                    ******* apply notin_union_2 in n0. apply notin_union_1 in n0. simpl in n0. apply notin_remove_1 in n0. destruct n0.
                    ******** symmetry in H. contradiction.
                    ******** assumption.
                    ******* apply notin_union_2 in H2. apply notin_union_1 in H2. simpl in H2. apply notin_remove_1 in H2. destruct H2.
                    ******** symmetry in H. contradiction.
                    ******** assumption.
               **** apply swap_reduction.
                    ***** apply notin_union_1 in H2. assumption.
                    ***** apply notin_union_1 in n0. assumption.
           *** unfold vswap. repeat apply notin_union_2 in H2. apply notin_singleton_1 in H2. repeat apply notin_union_2 in n0. apply notin_singleton_1 in n0. default_simp.
Qed.               

Lemma m_subst_sub_neq : forall t1 t2 u x y z, x <> y -> z `notin` fv_nom u `union` fv_nom ([y := t2]t1) `union` {{x}} -> {x := u}([y := t2]t1) =a ([z := ({x := u}t2)]({x := u}(swap y z t1))).
Proof.
  intros t1 t2 u x y z H1 H2. unfold m_subst. rewrite subst_rec_fun_equation. destruct (x == y). 
  - contradiction.
  - destruct (atom_fresh (union (fv_nom u) (union (fv_nom ([y := t2]t1)) (singleton x)))). destruct (x0 == z).
    + subst. apply aeq_refl.
    + apply aeq_sub_diff.
      * apply aeq_refl.
      * assumption.
      * apply fv_nom_remove. 
        ** apply notin_union_1 in n0. assumption.
        ** simpl in *. case (x0 == y). 
           *** intro Heq. subst. apply notin_remove_2. apply fv_nom_swap. apply notin_union_2 in H2. apply notin_union_1 in H2. apply notin_union_1 in H2. apply notin_remove_1 in H2. destruct H2.
               **** contradiction.
               **** assumption.
           *** intro Hneq. apply notin_remove_2. apply fv_nom_remove_swap. 
               **** assumption.
               **** assumption.
               **** apply notin_union_2 in n0. apply notin_union_1 in n0. apply notin_union_1 in n0. apply diff_remove_2 in n0; assumption.
      * apply aeq_sym. apply aeq_trans with (subst_rec_fun (swap z x0 (swap y z t1)) (swap z x0 u) (vswap z x0 x)). 
        ** apply swap_subst_rec_fun.
        ** replace (vswap z x0 x) with x. 
           *** apply aeq_m_subst_eq. 
               **** rewrite (swap_symmetric _ z x0). rewrite (swap_symmetric _ y z). rewrite (swap_symmetric _ y x0). simpl in *. case (x0 == y).
                    ***** intro Heq. subst. rewrite (swap_symmetric _ y z). rewrite swap_involutive. rewrite swap_id. apply aeq_refl.
                    ***** intro Hneq. case (z == y). 
                    ****** intro Heq. subst. rewrite swap_id. apply aeq_refl.
                    ****** intro Hneq'. apply aeq_swap_swap.
                    ******* apply notin_union_2 in n0. apply notin_union_1 in n0. apply notin_union_1 in n0. apply notin_remove_1 in n0. destruct n0.
                    ******** symmetry in H. contradiction.
                    ******** assumption.
                    ******* apply notin_union_2 in H2. apply notin_union_1 in H2. apply notin_union_1 in H2. apply notin_remove_1 in H2. destruct H2.
                    ******** symmetry in H. contradiction.
                    ******** assumption.
               **** apply swap_reduction.
                    ***** apply notin_union_1 in H2. assumption.
                    ***** apply notin_union_1 in n0. assumption.
           *** unfold vswap. repeat apply notin_union_2 in H2. apply notin_singleton_1 in H2. repeat apply notin_union_2 in n0. apply notin_singleton_1 in n0. default_simp.
Qed.

(* In fact, the need of the lemma [swap_subst_rec_fun] in the proofs of the two previous lemmas is justified by the fact that when the $\alpha$-equation involves abstractions with different binders, or explicit substitutions with different binders, the rules [aeq_abs_diff] and [aeq_sub_diff] introduce swaps that are outside the metasubstitutions. *)

(* This is the intended behaviour of the metasubstitution *)
(* Lemma fv_nom_metasub: forall t u x,  x `notin` (fv_nom t) ->  fv_nom ({x := u}t) [=] fv_nom t.
Proof. 
  induction t.
  - intros u x' Hfv. simpl in *. apply notin_singleton_1 in Hfv. unfold m_subst. rewrite subst_rec_fun_equation. destruct (x' == x).
    + subst. contradiction.
    + simpl. reflexivity.
  - intros u x' Hfv. simpl in *. case (x' == x).
    + intro Heq. subst. rewrite m_subst_abs_eq. simpl. reflexivity.
    + intro Hneq. unfold m_subst in *. rewrite subst_rec_fun_equation. destruct (x' == x).
      * contradiction.
      * destruct (atom_fresh (union (fv_nom u) (union (fv_nom (n_abs x t)) (singleton x')))). simpl. case (x0 == x).
        ** intro Heq. subst. apply AtomSetProperties.Equal_remove. rewrite swap_id. apply IHt. apply notin_remove_1 in Hfv. destruct Hfv.
           *** symmetry in H. contradiction.
           *** assumption.
        ** intro Hneq'. apply notin_remove_1 in Hfv. destruct Hfv.
           *** symmetry in H. contradiction.
           *** apply (IHt u) in H. apply notin_union_2 in n0. apply notin_union_1 in n0. simpl in n0. apply notin_remove_1 in n0. destruct n0.
               **** symmetry in H0. contradiction.
               **** apply (IHt u) in H0. Admitted. *)             

(* The substitution lemma *)

(** In the pure $\lambda$-calculus, the substitution lemma is probably the first non trivial property. In our framework, we have defined two different substitution operators, namely, the metasubstitution denoted by $\metasub{t}{x}{u}$ and the explicit substitution, written as $\esub{t}{x}{u}$. In what follows, we present the main steps of our proof of the substitution lemma for [n_sexp] terms, %{\it i.e.}% for nominal terms with explicit substitutions. *)

Lemma m_subst_lemma: forall t1 t2 t3 x y, x <> y -> x `notin` (fv_nom t3) ->
                     ({y := t3}({x := t2}t1)) =a ({x := ({y := t3}t2)}({y := t3}t1)).
Proof.
  induction t1 as  [z | t11 z | t11 t12 | t11 t12 z] using n_sexp_induction. 
- intros t2 t3 x y Hneq Hfv. case (x == z).
  + intro Heq. subst. rewrite m_subst_var_eq. case (y == z).
      * intro Heq. subst. contradiction.
      * intro Hneq'. rewrite m_subst_var_neq.
        ** rewrite m_subst_var_eq. apply aeq_refl.
        ** assumption.
  + intro Hneq'. case (x == z).
      * intro Heq. subst. contradiction.
      * intro Hneq''. rewrite m_subst_var_neq.
        ** case (y == z). 
           *** intro Heq. subst. rewrite m_subst_var_eq. apply aeq_sym. apply m_subst_notin. assumption.
           *** intro Hneq'''. repeat rewrite m_subst_var_neq.
               **** apply aeq_refl.
               **** apply aux_not_equal. assumption.
               **** apply aux_not_equal. assumption.
        ** apply aux_not_equal. assumption.
- intros t2 t3 x y Hneq Hfv. case (z == x). 
    + intro Heq. subst. rewrite m_subst_abs_eq. apply aeq_sym. apply m_subst_notin. apply fv_nom_remove. 
        * assumption.
        * apply notin_remove_2. simpl. apply notin_remove_3. reflexivity.
    + intro Hneq'. destruct (y == z). 
      * subst. rewrite m_subst_abs_eq. pose proof m_subst_abs_neq as Habs. pick fresh w for (union (fv_nom t3) (union (fv_nom t2) (union (fv_nom (n_abs z t11)) (singleton x)))). specialize (Habs t11 t2 x z w). apply aeq_trans with ({z := t3} n_abs w ({x := t2} swap z w t11)). 
        ** apply aeq_m_subst_out. apply Habs. 
           *** assumption.
           *** apply notin_union_2 in Fr. assumption.
        ** destruct (z == w). 
           *** subst. rewrite swap_id. rewrite m_subst_abs_eq. pose proof m_subst_abs_neq as H'. specialize (H' t11 ({w := t3}t2) x w w). rewrite swap_id in H'. rewrite H'.
               **** apply aeq_abs_same. assert (Fr' := Fr). apply notin_union_2 in Fr'. apply notin_union_1 in Fr'. apply aeq_m_subst_in. apply aeq_sym. apply m_subst_notin. assumption.
               **** assumption.
               **** apply notin_union.
                    ***** apply fv_nom_remove.
                    ****** apply notin_union_1 in Fr. assumption.
                    ****** apply notin_remove_3. reflexivity.
                    ***** apply notin_union.
                    ****** simpl. apply notin_remove_3. reflexivity.
                    ****** apply notin_singleton. assumption.
           *** pose proof m_subst_abs_neq as Habs'. specialize (Habs' t11 ({z := t3}t2) x z w). rewrite Habs'. 
               **** pose proof m_subst_abs_neq as H'. specialize (H' ({x := t2} swap z w t11) t3 z w w). rewrite swap_id in H'. rewrite H'.
                    ***** apply aeq_abs_same. apply aeq_trans with ({x := {z := t3} t2}({z := t3}(swap z w t11))).
                    ****** apply H.
                    ******* reflexivity.
                    ******* assumption.
                    ******* assumption.
                    ****** apply aeq_m_subst_out. apply m_subst_notin. apply fv_nom_swap. apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_1 in Fr. simpl in Fr. apply notin_remove_1 in Fr. destruct Fr.
                    ******* contradiction.
                    ******* assumption.
                    ***** assumption.
                    *****  apply notin_union.
                    ****** apply notin_union_1 in Fr. assumption.
                    ****** apply notin_union.
                    ******* simpl. apply notin_remove_3. reflexivity.
                    ******* apply notin_singleton. assumption.
               **** apply aux_not_equal. assumption.
               **** apply notin_union.
                    ***** apply fv_nom_remove.
                    ****** apply notin_union_1 in Fr. assumption.
                    ****** apply notin_remove_2. apply notin_union_2 in Fr. apply notin_union_1 in Fr. assumption. 
                    ***** apply notin_union.
                    ****** simpl. apply notin_remove_2. apply notin_union_2 in Fr. apply notin_union_2 in Fr.  apply notin_union_1 in Fr. simpl in Fr. apply diff_remove_2 in Fr.
                    ******* assumption.
                    ******* apply not_eq_sym. assumption.
                    ****** apply notin_singleton. repeat apply notin_union_2 in Fr. apply notin_singleton_1 in Fr. assumption.          
      * pose proof m_subst_abs_neq as Habs. pick fresh w for (union (fv_nom t3) (union (fv_nom t2) (union (fv_nom (n_abs z t11)) (union (singleton x) (singleton y))))). specialize (Habs t11 t2 x z w). apply aeq_trans with ({y := t3} n_abs w ({x := t2} swap z w t11)). 
        *** apply aeq_m_subst_out. apply Habs.
            **** apply aux_not_equal. assumption.
            **** apply notin_union_2 in Fr. pose proof AtomSetProperties.union_assoc as H'. specialize (H' (fv_nom (n_abs z t11)) (singleton x) (singleton y)). rewrite <- H' in Fr. rewrite <- AtomSetProperties.union_assoc in Fr. apply notin_union_1 in Fr. assumption.
        *** pose proof m_subst_abs_neq as Habs'. specialize (Habs' ({x := t2} swap z w t11) t3 y w w). rewrite swap_id in Habs'. rewrite Habs'. 
        **** pose proof m_subst_abs_neq as Habs''. specialize (Habs'' t11 t3 y z w). apply aeq_trans with ({x := {y := t3} t2} (n_abs w ({y := t3} swap z w t11))).
        ***** pose proof m_subst_abs_neq as Habs'''. specialize (Habs''' ({y := t3} swap z w t11) ({y := t3} t2) x w w). rewrite swap_id in Habs'''. rewrite Habs'''. 
        ****** apply aeq_abs_same. apply H.
        ******* reflexivity.
        ******* assumption.
        ******* assumption.
        ****** apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_1 in Fr. apply notin_singleton_1 in Fr. assumption.
        ****** apply notin_union.
        ******* apply fv_nom_remove.
        ******** apply notin_union_1 in Fr. assumption.
        ******** apply notin_union_2 in Fr. apply notin_union_1 in Fr. apply notin_remove_2. assumption.
        ******* apply notin_union.
        ******** simpl. apply notin_remove_3. reflexivity.
        ******** apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_1 in Fr. assumption.
        ***** apply aeq_m_subst_out. apply aeq_sym. apply Habs''.
        ****** assumption.
        ****** apply notin_union.
        ******* apply notin_union_1 in Fr. assumption.
        ******* apply notin_union.
        ******** apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_1 in Fr. assumption.
        ******** repeat apply notin_union_2 in Fr. assumption. 
        **** repeat apply notin_union_2 in Fr. apply notin_singleton_1 in Fr. assumption.
        **** apply notin_union.
        ***** apply notin_union_1 in Fr. assumption.
        ***** apply notin_union.
        ****** simpl. apply notin_remove_3. reflexivity.
        ****** repeat apply notin_union_2 in Fr. assumption. (** %\noindent{\bf Proof.}% The proof is by induction on the size of [t1]. The interesting cases are the abstraction and the explicit substitution. We focus on the former, %{\it i.e.}% $t1= \lambda_z.t_1'$, whose initial goal is

$\metasub{(\metasub{(\lambda_z.t_1')}{x}{t_2})}{y}{t_3} =_{\alpha} \metasub{(\metasub{(\lambda_z .t_1')}{y}{t_3})}{x}{\metasub{t_2}{y}{t_3}}$

%\noindent% assuming that $x \neq y$ and $x \notin fv\_nom(t_3)$. The induction hypothesis generated by this case states that the lemma holds for any term of the size of $t_1'$, %{\it i.e.}% any term with the same size of the body of the abstraction. We start comparing $z$ with $x$ aiming to apply the definition of the metasubstitution on the LHS of the goal. %\begin{enumerate}
\item When $z = x$, the subterm $\metasub{\lambda_x.t_1'}{x}{t_2}$ reduces to $\lambda_x.t_1'$ by lemma $m\_subst\_abs\_eq$, and then the LHS reduces to $\metasub{\lambda_x.t_1'}{y}{t_3}$. The RHS $\metasub{\metasub{\lambda_x.t_1'}{y}{t_3}}{x}{\metasub{t_2}{y}{t_3}}$ also reduces to it because $x$ does not occur free neither in $\lambda_x.t_1'$ nor in $t_3$, and we are done.
\item When $z \neq x$, then we compare $y$ with $z$.
\begin{enumerate}
 \item When $y = z$, the subterm $\metasub{(\lambda_z.t_1')}{y}{t_3}$ can be simplified to $\lambda_z.t_1'$, by lemma $m\_subst\_abs\_eq$. On the LHS, we propagate the internal metasubstitution over the abstraction taking a fresh name $w$ not in the set $fv\_nom(\lambda_z.t_1') \cup fv\_nom(t_3) \cup fv\_nom(t_2) \cup \{x\}$, where the goal is $\metasub{(\lambda_w.(\metasub{\swap{z}{w}{t_1'}}{x}{t_2}))}{z}{t_3} =_{\alpha} \metasub{(\lambda_z.t_1')}{x}{\metasub{t_2}{z}{t_3}}$. We proceed by comparing $z$ and $w$: \begin{enumerate}
\item If $z = w$ then the current goal simplifies to

$\metasub{(\lambda_w.(\metasub{t_1'}{x}{t_2}))}{w}{t_3} =_{\alpha} \metasub{(\lambda_w.t_1')}{x}{\metasub{t_2}{w}{t_3}}$

We can propagate the metasubstitution on the RHS and there is no need for a fresh name since the variable $w$ fullfil the condition required by lemma $m\_subst\_abs\_neq$. We conclude with lemmas $aeq\_m\_subst\_in$ and $m\_subst\_notin$.
\item If $z \neq w$ then we can propagate the metasubstitutions on both sides of the goal taking $w$ as the fresh name that fullfil the conditions of lemma $m\_subst\_abs\_neq$. We proceed with $aeq\_abs\_same$, and conclude by the induction hypothesis.
\end{enumerate}
\item If $y \neq z$ then we follow a similar strategy that avoids unnecessary generation of fresh names. In this way, we take a fresh $w$ that is not in the set $fv\_nom(t_3)\cup fv\_nom(t_2)\cup fv\_nom(\lambda_z.t_1')\cup \{x\}\cup \{y\}$, and propagate the metasubstitution inside the abstraction resulting in the goal $\lambda_w. (\metasub{(\metasub{\swap{z}{w}{t_1'}}{x}{t_2})}{y}{t_3} =_{\alpha} \lambda_w. (\metasub{(\metasub{\swap{z}{w}{t_1'}}{y}{t_3})}{x}{\metasub{t_2}{y}{t_3}}$. We conclude by the induction hypothesis. $\hfill\Box$
\end{enumerate}
\end{enumerate}%*) 
- intros t2 t3 x y Hneq Hfv. repeat rewrite m_subst_app. apply aeq_app. 
  + apply IHt12; assumption.
  + apply IHt1_1; assumption.
- intros t2 t3 x y Hneq Hfv. (* In the explicit substitution case, the initial goal is [({y := t3} ({x := t2} ([z := t12] t11))) =a ({x := {y := t3} t2} ({y := t3} ([z := t12] t11)))], and we start comparing [x] and [z]. *) case (z == x).
  + intro Heq. subst. rewrite m_subst_sub_eq. (* When [z = x], the LHS [({y := t3} ({x := t2} ([z := t12] t11)))] reduces to [([x := {x := t2} t12] t11)], but differently to the abstraction case, the external metasubstitution of the RHS cannot be ignored because [x] may occur free in [t12], and it will therefore be propagated over the explicit substitution. We then need a fresh name, say [w], that is not in the set $fv(t_3)\cup fv(t_2) \cup fv(\esub{t_{11}}{x}{t_{12}}) \cup \{y\}$. We use lemma [m_subst_sub_neq] to perform the propagation.*) pick fresh w for (union (fv_nom t3) (union (fv_nom t2) (union (fv_nom ([x := t12]t11)) (singleton y)))). pose proof m_subst_sub_neq as Hsubneq. specialize (Hsubneq t11 t12 t3 y x w). apply aeq_trans with ({x := {y := t3} t2} ([w := {y := t3} t12] ({y := t3} swap x w t11))).
    * case (x == w). (* We proceed by comparing [x] and [w] because if they are equal the external metasubstitution of the RHS can be removed as in the abstraction case.*)
      ** intro Heq. subst. rewrite m_subst_sub_eq. rewrite swap_id. pose proof m_subst_sub_neq as Hsubneq'. specialize (Hsubneq' t11 ({w := t2} t12) t3 y w w). rewrite Hsubneq'. (* The current goal is [({y := t3} ([w := {w := t2} t12] t11)) =a ([w := {w := {y := t3} t2} ({y := t3} t12)] ({y := t3} t11))], and the next step is to propagate the external metasubstitution of the LHS without the need of a new name.*)
         *** apply aeq_sub_same. (* As the same name [w] is used on both sides, we can proceed with [aeq_sub_same]. *)
             **** rewrite swap_id. apply aeq_refl. (* The first subcase is trivial.*)
             **** apply IHt1_1; assumption. (* And the second is proved by the induction hypothesis for [t12].*)
         *** apply aux_not_equal. assumption.
         *** apply notin_union.
             **** apply notin_union_1 in Fr. assumption.
             **** apply notin_union.
                  ***** simpl. apply notin_union.
                  ****** apply notin_remove_3. reflexivity.
                  ****** apply fv_nom_remove.
                  *******  apply notin_union_2 in Fr. apply notin_union_1 in Fr. assumption.
                  ******* apply notin_remove_3. reflexivity.
                  ***** repeat apply notin_union_2 in Fr. assumption.
      ** intro Hneq'. (* When [x <> w], then we can propagate the external metasubstitutions on both sides of the current goal [({y := t3} ([x := {x := t2} t12] t11)) =a ({x := {y := t3} t2} ([w := {y := t3} t12] ({y := t3} swap x w t11)))]. We use two different instances of [m_subst_sub_neq], and on both cases we use the fresh name [w] that was already created.*) pose proof m_subst_sub_neq as Hsubneq'. specialize (Hsubneq' ({y := t3} swap x w t11) ({y := t3} t12) ({y := t3} t2) x w w). rewrite swap_id in Hsubneq'. rewrite Hsubneq'. 
         *** pose proof m_subst_sub_neq as Hsubneq''. specialize (Hsubneq'' t11 ({x := t2} t12) t3 y x w). rewrite Hsubneq''.
             **** apply aeq_sub_same. (* Again, since we have used the same fresh name [w] on both sides of the $\alpha$-equation, we proceed with [aeq_sub_same].*)
                  ***** apply aeq_sym. apply m_subst_notin. (* In the first subcase, we need to prove that [({y := t3} swap x w t11) =a ({x := {y := t3} t2} ({y := t3} swap x w t11))], and we conclude with [m_subst_notin], since [x] does not occur free in [({y := t3} swap x w t11)].*) apply fv_nom_remove.
                  ******* assumption.
                  ******* apply notin_remove_2. apply fv_nom_swap. apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_1 in Fr. simpl in Fr. apply notin_union_1 in Fr. apply notin_remove_1 in Fr. destruct Fr.
                  ******** contradiction.
                  ******** assumption.
             ***** apply IHt1_1; assumption. (* The second subcase is proved by the induction hypothesis on [t12].*)
         **** apply aux_not_equal. assumption.
         **** apply notin_union.
                  ***** apply notin_union_1 in Fr. assumption.
                  ***** apply notin_union.
                  ****** simpl. apply notin_union.
                  ******* apply notin_remove_2. apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_1 in Fr. simpl in Fr. apply notin_union_1 in Fr. apply notin_remove_1 in Fr. destruct Fr.
                  ******** contradiction.
                  ******** assumption.
                  ******* apply fv_nom_remove.
                  ******** apply notin_union_2 in Fr. apply notin_union_1 in Fr. assumption.
                  ******** apply notin_remove_2. apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_1 in Fr. simpl in Fr. apply notin_union_2 in Fr. assumption.
                  ****** repeat apply notin_union_2 in Fr. assumption.
         *** assumption.
         *** apply notin_union.
             **** apply fv_nom_remove.
                  ***** apply notin_union_1 in Fr. assumption.
                  ***** apply notin_remove_2. apply notin_union_2 in Fr. apply notin_union_1 in Fr. assumption.
                  **** apply notin_union.
                       ***** simpl. apply notin_union.
                       ****** apply notin_remove_3. reflexivity.
                       ****** apply fv_nom_remove.
                       ******* apply notin_union_1 in Fr. assumption.
                       ******* apply notin_remove_2. apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_1 in Fr. simpl in Fr. apply notin_union_2 in Fr. assumption.
                       ***** apply notin_singleton. assumption.
    * apply aeq_m_subst_out. rewrite Hsubneq.                 
      ** apply aeq_sub_same.
         *** apply aeq_refl.
         *** apply aeq_refl.
      ** apply aux_not_equal. assumption.
      ** apply notin_union.
         *** apply notin_union_1 in Fr. assumption.
         *** apply notin_union.
             **** simpl. apply notin_union.
                  ***** case (w == x).
                  ****** intro Heq. subst. apply notin_remove_3. reflexivity.
                  ****** intro Hneq'. apply notin_remove_2. apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_1 in Fr. simpl in Fr. apply notin_union_1 in Fr. apply notin_remove_1 in Fr. destruct Fr.
                  ******* symmetry in H0. contradiction.
                  ******* assumption.
                  ***** apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_1 in Fr. simpl in Fr. apply notin_union_2 in Fr. assumption.
             **** repeat apply notin_union_2 in Fr. assumption.
  + intro Hneq'. pick fresh w for (union (fv_nom t3) (union (fv_nom t2) (union (fv_nom ([z := t12]t11)) (union (singleton x) (singleton y))))). (* When [z <> x], then we take a fresh name [w] such that it is not in the set $fv(t_3)\cup fv(t_2) \cup fv(\esub{t_{11}}{z}{t_{12}})\cup \{x\} \cup \{y\}$. The current goal is [({y := t3} ({x := t2} ([z := t12] t11))) =a ({x := {y := t3} t2} ({y := t3} ([z := t12] t11)))] and we start propagating the internal metasubstitution. Let's start with the LHS.*) pose proof m_subst_sub_neq as Hsubneq. specialize (Hsubneq t11 t12 t2 x z w). apply aeq_trans with ({y := t3} ([w := {x := t2} t12] ({x := t2} swap z w t11))).
    * apply aeq_m_subst_out. pose proof m_subst_sub_neq as Hsubneq'. specialize (Hsubneq' t11 t12 t2 x z w). rewrite Hsubneq'.
      ** apply aeq_refl.
      ** apply aux_not_equal. assumption.
      ** apply notin_union.
         *** apply notin_union_2 in Fr. apply notin_union_1 in Fr. assumption.
         *** apply notin_union.
             **** simpl. apply notin_union.
                  ***** case (w == z).
                  ****** intro Heq. subst. apply notin_remove_3. reflexivity.
                  ****** intro Hneq''. apply notin_remove_2. apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_1 in Fr. simpl in Fr. apply notin_union_1 in Fr. apply notin_remove_1 in Fr. destruct Fr.
                  ******* symmetry in H0. contradiction.
                  ******* assumption.
                  ***** apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_1 in Fr. simpl in Fr. apply notin_union_2 in Fr. assumption.
             **** apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_1 in Fr. assumption.
    * case (y == z). (* After the propagation, we get the following goal [({y := t3} ([w := {x := t2} t12] ({x := t2} swap z w t11))) =a ({x := {y := t3} t2} ({y := t3} ([z := t12] t11)))]. We now compare [y] and [z], and propagate the internal metasubstitution of the RHS.*)
      ** intro Heq. subst. rewrite m_subst_sub_eq. (* When [y = z], we have the goal [({z := t3} ([w := {x := t2} t12] ({x := t2} swap z w t11))) =a ({x := {z := t3} t2} ([z := {z := t3} t12] t11))]. The next step is to propagate the external metasubstitutions on both sides of the current goal. To do so, we will use the same fresh name [w] on both propagations.*) pose proof m_subst_sub_neq as Hsubneq'. specialize (Hsubneq' ({x := t2} swap z w t11) ({x := t2} t12) t3 z w w). rewrite swap_id in Hsubneq'. rewrite Hsubneq'.
         *** pose proof m_subst_sub_neq as Hsubneq''. specialize (Hsubneq'' t11 ({z := t3} t12) ({z := t3} t2) x z w). rewrite Hsubneq''.
             **** apply aeq_sub_same.
                  ***** apply aeq_trans with ({x := {z := t3} t2} ({z := t3}(swap z w t11))).
                  ****** apply H.
                  ******* reflexivity.
                  ******* assumption.
                  ******* assumption.
                  ****** apply aeq_m_subst_out. apply m_subst_notin. apply fv_nom_swap. pose proof Fr as Fr'. repeat apply notin_union_2 in Fr'. apply notin_singleton_1 in Fr'. apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_1 in Fr. simpl in Fr. apply notin_union_1 in Fr. apply notin_remove_1 in Fr. destruct Fr.
                  ******* contradiction.
                  ******* assumption.
                  ***** apply IHt1_1; assumption.
                  **** assumption.
                  **** apply notin_union.
                       ***** apply fv_nom_remove.
                       ****** apply notin_union_1 in Fr. assumption.
                       ******  apply notin_remove_2. apply notin_union_2 in Fr. apply notin_union_1 in Fr. assumption.
                       ***** apply notin_union.
                       ****** simpl. apply notin_union.
                       ******* pose proof Fr as Fr'. repeat apply notin_union_2 in Fr'. apply notin_singleton_1 in Fr'. apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_1 in Fr. simpl in Fr. apply notin_union_1 in Fr. apply notin_remove_1 in Fr. destruct Fr.
                       ******** contradiction.
                       ******** apply notin_remove_2. assumption.
                       ******* apply fv_nom_remove.
                       ******** apply notin_union_1 in Fr. assumption.
                       ******** apply notin_remove_2. apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_1 in Fr. simpl in Fr. apply notin_union_2 in Fr. assumption.
                       ****** apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_1 in Fr. assumption.
         *** repeat apply notin_union_2 in Fr. apply notin_singleton_1 in Fr. assumption.
         *** apply notin_union.
             **** apply notin_union_1 in Fr. assumption.
             **** apply notin_union.
                  ***** simpl. apply notin_union.
                  ****** apply notin_remove_3. reflexivity.
                  ****** apply fv_nom_remove.
                  ******* apply notin_union_2 in Fr. apply notin_union_1 in Fr. assumption.
                  ******* apply notin_remove_2. apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_1 in Fr. simpl in Fr. apply notin_union_2 in Fr. assumption.
                  ***** repeat apply notin_union_2 in Fr. assumption.                
      ** intro Hneq''. (* When [y <> z], we again propagate all the metasubstitutions, one in the LHS and two in the RHS, using the same fresh name [w] for all of them.*) pose proof m_subst_sub_neq as Hsubneq'. specialize (Hsubneq' t11 t12 t3 y z w). apply aeq_trans with ({x := {y := t3} t2} ([w := {y := t3} t12] ({y := t3} swap z w t11))).
         ***  pose proof m_subst_sub_neq as Hsubneq''. specialize (Hsubneq'' ({x := t2} swap z w t11) ({x := t2} t12) t3 y w w). rewrite swap_id in Hsubneq''. rewrite Hsubneq''.
              **** pose proof m_subst_sub_neq as Hsubneq'''. specialize (Hsubneq''' ({y := t3} swap z w t11) ({y := t3} t12) ({y := t3} t2) x w w). rewrite swap_id in Hsubneq'''. rewrite Hsubneq'''.
                   ***** apply aeq_sub_same.
                   ****** apply H.
                   ******* reflexivity.
                   ******* assumption.
                   ******* assumption.
                   ****** apply IHt1_1.
                   ******* assumption.
                   ******* assumption.
                   ***** apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_1 in Fr. apply notin_singleton_1 in Fr. assumption.
                   ***** apply notin_union.
                   ****** apply fv_nom_remove.
                   ******* apply notin_union_1 in Fr. assumption.
                   ******* apply notin_remove_2. apply notin_union_2 in Fr. apply notin_union_1 in Fr. assumption.
                   ****** apply notin_union.
                   ******* simpl. apply notin_union.
                   ******** apply notin_remove_3. reflexivity.
                   ******** apply fv_nom_remove.
                   ********* apply notin_union_1 in Fr. assumption.
                   ********* apply notin_remove_2. apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_1 in Fr. simpl in Fr. apply notin_union_2 in Fr. assumption.
                   ******* apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_1 in Fr. assumption.                 
                   **** repeat apply notin_union_2 in Fr. apply notin_singleton_1 in Fr. assumption.
                   **** apply notin_union.
                        ***** apply notin_union_1 in Fr. assumption.
                        ***** apply notin_union.
                        ****** simpl. apply notin_union.
                        ******* apply notin_remove_3. reflexivity.
                        ******* apply fv_nom_remove.
                        ******** apply notin_union_2 in Fr. apply notin_union_1 in Fr. assumption.
                        ******** apply notin_remove_2. apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_1 in Fr. simpl in Fr. apply notin_union_2 in Fr. assumption.
                        ****** repeat apply notin_union_2 in Fr. assumption.
         *** apply aeq_m_subst_out. apply aeq_sym. apply Hsubneq'.
             **** assumption.
             **** apply notin_union.
                  ***** apply notin_union_1 in Fr. assumption.
                  ***** apply notin_union.
                  ****** simpl. apply notin_union.
                  ******* case (w == z).
                  ******** intro Heq. subst. apply notin_remove_3. reflexivity.
                  ******** intro Hneq'''. apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_1 in Fr. simpl in Fr. apply notin_union_1 in Fr. apply notin_remove_1 in Fr. destruct Fr.
                  ********* symmetry in H0. contradiction.
                  ********* apply notin_remove_2. assumption.
                  ******* apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_1 in Fr. simpl in Fr. apply notin_union_2 in Fr. assumption.
                  ****** repeat apply notin_union_2 in Fr. assumption.
Qed.

