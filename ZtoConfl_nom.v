(* begin hide *)
Require Import lambda_es.
Definition Rel (A: Type) := A -> A -> Prop.
(* end hide *)

(** * A Formalization that Z property implies confluence in a nominal context. *)

Inductive refltrans (R: Rel n_sexp) : Rel n_sexp :=
| refl: forall a, refltrans R a a
| rtrans: forall a b c, R a b -> refltrans R b c -> refltrans R a c
| refl_aeq: forall a b, a =a b -> refltrans R a b
| rtrans_aeq: forall a b c, a =a b -> refltrans R b c -> refltrans R a c.
                               
Lemma refltrans_composition {R: Rel n_sexp}: forall t u v, refltrans R t u -> refltrans R u v -> refltrans R t v.
Proof.
  intros t u v H1 H2. induction H1.
  - assumption.
  - apply rtrans with b.
    + assumption.
    + apply IHrefltrans; assumption.
  - apply rtrans_aeq with b; assumption.
  - apply rtrans_aeq with b.
    + assumption.
    + apply IHrefltrans; assumption.
Qed.

Lemma refltrans_composition3 (R: Rel n_sexp): forall t u v, refltrans R t u -> refltrans R v t -> refltrans R v u.
Proof.
  intros t u v H1 H2. apply refltrans_composition with t; assumption.
Qed.
    
(* not needed
Lemma refltrans_composition2 {A} (R: Rel A): forall t u v, refltrans R t u -> R u v -> refltrans R t v.
Proof.
  intros t u v H1 H2. induction H1.
  - apply rtrans with v.
    + assumption.
    + apply refl.
  - apply IHrefltrans in H2.
    apply rtrans with b; assumption.
Qed. 

Lemma trans_to_refltrans {A:Type} (R: Rel A): forall a b, trans R a b -> refltrans R a b.
Proof.
  intros a b Htrans.
  induction Htrans.
  - apply rtrans with b.
    + assumption.
    + apply refl.
  - apply rtrans with b; assumption.
Qed. *)
(* end hide *)
(** The reflexive transitive closure of a relation is used to define
    the notion of confluence: no matter how the reduction is done, the
    result will always be the same. In other words, every divergence
    is joinable as stated by the following diagram:

    $\centerline{\xymatrix{ & a \ar@{->>}[dl] \ar@{->>}[dr] & \\ b
    \ar@{.>>}[dr] & & c \ar@{.>>}[dl] \\ & d & }}$

Formally, this means that if an expression $a$ can be reduced in two
different ways to $b$ and $c$, then there exists an expression $d$
such that both $b$ and $c$ reduce to $d$. The existential
quantification is expressed by the dotted lines in the diagram. This
notion is defined in the Coq system as follows: *)

Definition Confl (R: Rel n_sexp) := forall a b c, (refltrans R) a b -> (refltrans R) a c -> (exists d, (refltrans R) b d /\ (refltrans R) c d).

(** In %\cite{dehornoy2008z}%, V. van Oostrom gives a sufficient condition
for an ARS to be confluent. This condition is based on the $\textit{Z
  Property}$ that is defined as follows:

%\begin{definition} Let $(A,\to_R)$ be an ARS. A mapping $f:A \to A$ satisfies the Z property for $\to_R$, if $a \to_R b$ implies
$b \tto_R f a  \tto_R f b$, for any $a, b \in A$. 
\end{definition}%

The name of the property comes from the following diagrammatic
representation of this definition:
    
$\xymatrix{ a \ar[r]_R & b \ar@{.>>}[dl]^R\\ f a \ar@{.>>}[r]_R & f
    b \\ }$

If a function [f] satisfies the Z property for $\to_R$ then
we say that [f] is Z for $\to_R$, and the corresponding Coq
definition is given by the following predicate: *)

Definition f_is_Z (R: Rel n_sexp) (f: n_sexp -> n_sexp) := forall a b, R a b -> ((refltrans R)  b (f a) /\ (refltrans R) (f a) (f b)).

(** Alternatively, an ARS $(A,\to_R)$ satisfies the Z property if there
exists a mapping $f:A \to A$ such that $f$ is Z for $\to_R$: *)

Definition Z_prop (R: Rel n_sexp) := exists f, forall a b, R a b -> ((refltrans R) b (f a) /\ (refltrans R) (f a) (f b)).

Lemma Z_implies_a_fa: forall R f a, f_is_Z R f -> refltrans R a (f a). 
Proof.
  Admitted.

Lemma Z_implies_fa_fb: forall R f a b, f_is_Z R f -> refltrans R a b -> refltrans R (f a) (f b). 
Proof.
  Admitted.

Lemma Z_implies_aeq: forall R f a b, f_is_Z R f -> a =a b -> refltrans R b (f a). 
Proof.
  Admitted.

(** The first contribution of this work is a constructive proof of the fact that the Z property implies confluence. Our proof uses nested induction, and hence it differs from the one in %\cite{kesnerTheoryExplicitSubstitutions2009}% (that follows %\cite{dehornoy2008z}%) and the one in %\cite{felgenhauerProperty2016}% in the sense that it does not rely on the analyses of whether a term is in normal form or not, avoiding the necessity of the law of the excluded middle. As a result, we have an elegant inductive proof of the fact that if an ARS satisfies the Z property then it is confluent. *)

Theorem Z_prop_implies_Confl: forall R, Z_prop R -> Confl R.
Proof.
  intros R HZ_prop. unfold Z_prop, Confl in *. intros a b c Hrefl1 Hrefl2. destruct HZ_prop as [f HZ_prop]. generalize dependent c. induction Hrefl1 as [| a a' b | a b | a a' b].
  - intros c Hrefl2. exists c; split. 
    + assumption. 
    + apply refl. 
  - intros c Hrefl2. assert (H' := H). apply HZ_prop in H'. destruct H' as [H' H''].
    assert (Hafa': refltrans R a (f a')).
    { apply rtrans with a'. - assumption. - apply refltrans_composition with (f a); assumption. } clear H H'' Hafa'. generalize dependent b. induction Hrefl2 as [| a a'' c | a c | a a'' c].
    + intros b Hrefl1 IHHrefl1. specialize (IHHrefl1 (f a)). assert (Ha'fa := H'). apply IHHrefl1 in H'. destruct H' as [d']. exists d'. split.
      * apply H.
      * apply refltrans_composition with (f a).
        ** apply Z_implies_a_fa. unfold f_is_Z. apply HZ_prop.
        ** apply H.
    + intros b Hrefl1 IHHrefl1. apply HZ_prop in H. apply IHHrefl2.
      * apply refltrans_composition with (f a).
        ** assumption.
        ** apply H.
      * assumption.
      * apply IHHrefl1.
    + intros b Hrefl1 IHHrefl1. assert (Hcfa: refltrans R c (f a)). { apply Z_implies_aeq. - unfold f_is_Z. apply HZ_prop. - assumption. } specialize (IHHrefl1 (f a)). apply IHHrefl1 in H'. destruct H' as [d H']. exists d. split.
      * apply H'.
      * apply refltrans_composition with (f a).
        ** assumption.
        ** apply H'.
    + intros b Hrefl1 IHHrefl1. assert (Ha''fa: refltrans R a'' (f a)). { apply Z_implies_aeq. - unfold f_is_Z. apply HZ_prop. - assumption. } specialize (IHHrefl1 (f a)). apply IHHrefl1 in H'. destruct H' as [d' H']. destruct H' as [H' H'']. admit.
  - admit.
  - Admitted.
    

(** %\comm{Let $R$ be a relation over $A$ that satisfies
    the Z property, which will be denoted by $HZ\_prop$ for future
    reference.}% *)
(** %\comm{Unfolding both definitions of
  $Z\_prop$ and $Confl$, we get the following proof context:

     \includegraphics[scale=0.5]{figs/fig3.png} }% *)
(** %\comm{Let $a, b$ and $c$ be elements of
     the set $A$, $Hrefl1$ the hypothesis that $a \tto_R b$, and
     $Hrefl2$ the hypothesis that $a\tto_R c$. We need to prove that
     there exists $d$ such that $b\tto_R d$ and $c\tto_R d$.}% *)
(** %\comm{We know from the hypothesis
     $HZ\_prop$ that there exists a mapping $f$ that is Z. Let's call
     $g$ this mapping, and we get following proof context:

      %\includegraphics[scale=0.6]{figs/fig4.png}%

      The proof proceeds by nested induction, firstly on the length of
      the reduction from $a$ to $b$, and then on the length of the
      reduction from $a$ to $c$.}% *)(** %\comm{Before the first induction,
      i.e. induction on $Hrefl1$, the element $c$ needs to be
      generalized so that it can be afterwards instantiated with any
      reduct of $a$.}% *)
  (** %\comm{The induction on $Hrefl1$ corresponds to
       induction on the reflexive transitive closure of the relation
       $R$, and since $refltrans$ has two rules, the goal splits in
       two subgoals, one for each possible way of constructing $a
       \tto_R b$.}% *)
  
(** %\comm{In the first case, we have that $b = a$ since
    we are in the reflexive case. This means that we have to prove
    that there exists $d$, such that $a \tto_R d$ and $c \tto_R d$.}% *)
(** %\comm{Taking $d$ as $c$, the proof is simplified to $a
    \tto_R c$ and $c \tto_R c$.}% *)(** %\comm{The first component is exactly the hypothesis
        $Hrefl2$ and }% *) (** %\comm{$c \tto_R c$ corresponds to an application of
        the $refl$ axiom.}% *)

        (** The interesting part of the proof is then given by the
        inductive case, i.e. when $a\tto_R b$ is generated by the rule
        [(rtrans)]. In this case, the reduction from [a] to [b] is
        done in at least one step, therefore there must exists an
        element $a'$ such that the following diagram holds.

        % \[\xymatrix{ & & a \ar@{->}[dl] \ar@{->>}[dr] & \\ & a'
        \ar@{->>}[dl] & & c \ar@{.>>}[ddll] \\ b \ar@{.>>}[dr] & & &
        \\ & d & & }\] % 

        (* The corresponding proof context is as follows:

        %\includegraphics[scale=0.6]{figs/fig5.png}% *)

        The induction hypothesis states that every divergence from
        $a'$ that reduces to $b$ from one side converges: [IHHrefl1]
        : $\forall c_0 : A, a'\tto_R c_0 \to (\exists d : A, b\tto_R d
        \land c_0\tto_R d$). Now, we'd like apply induction on the
        hypothesis [Hrefl2] (a\tto_R c), but the current proof context has the
        hypothesis [H]: $a\to_R a'$ ([a] reduces to [a'] in one step),
        and hence it is the sole hypothesis depending on [a] in the
        current proof context. If we were to apply induction on [Hrefl2] now, 
        the generated induction hypothesis [IHrefl2] would assume that there is 
        a term $a''$ such that $a \to_R a'' \tto_R c$ and would require that 
        $a'' \to_R a'$, which is generally false. In order to circumvent 
        this problem, we need to discard the hypothesis [H] from our proof 
        context, and replace it by another relevant information derived from 
        the Z property as shown in what follows. *)
(** %\comm{Let $c_0$ be a reduct of $a$, and $Hrefl2$
    be the hypothesis $a \tto_R c_0$. So the reduction $a\tto_R c$ in
    the above diagram is now $a\tto_R c_0$ due to a renaming of
    variables automatically done by the Coq system. In addition, the
    reduction $a \to_R a' \tto_R b$ is now $a\to_R b \tto_R c$, as
    shown below:

    \includegraphics[scale=0.5]{figs/fig5-1.png}

    Before applying induction to $Hrefl2$: $a \tto_R c_0$, we will derive 
    $b\tto_R (g\ a)$ and $a\tto_R (g\ a)$ from the proof context so we can
    discard the hypothesis $H$: $a\to_R$.}% *)
(** %\comm{We call $Hbga$ the reduction
    $b\tto_R (g\ a)$ that is directly obtained from the Z property.}% *)(** %\comm{Call $Haga$ the
        reduction $a\tto_R (g\ a)$, and prove it using the
        transitivity of $\tto_R$, since $a \to_R b$ and $b \tto_R (g\
        a)$. Diagrammatically, we change from the situation on the
        top to the bottomone on the right:

        \xymatrix{ & & a \ar@{->>}[ddrr]_R \ar@{->}[dl]^R & & \\ & b
        \ar@{->>}[dl]^R & & & \\ c \ar@{.>>}[ddrr]_R & & & & c_0
        \ar@{.>>}[ddll]^R \\ & & & & \\ & & d & & } 

        \xymatrix{ & & a \ar@{->>}[ddrr]_R \ar@{->>}[dd]_R & & \\ & b
        \ar@{->>}[dl]^R \ar@{->>}[dr]_R & & & \\ c \ar@{.>>}[ddrr]_R &
        & (g \; a) & & c_0 \ar@{.>>}[ddll]^R \\ & & & & \\ & & d & &} }% *) (** %\comm{At this point we can remove
      the hypothesis $H$ from the context, and generalize $b$. Doing so, 
      we generalize $IHHrefl1$, which, in conjunction with the hypotheses 
      that depend on a (namely, $Hrefl2$, $Hbga$, and $Haga$), will form 
      the four necessary conditions for use of the second inductive 
      hypothesis, $IHHrefl2$.}% *)
(** %\comm{Now we are ready to start the induction on
    the reduction $a\tto_R c_0$, and we have two subgoals.}% *)(** %\comm{The first subgoal corresponds
        to the reflexive case that is closed by the induction
        hypothesis $IHHrefl1$:

        \[\xymatrix{ & & a \ar@{->>}[dd]^{H2} & & \\ & b
        \ar@{->>}[dl]_{Hrefl1} \ar@{->>}[dr]^{H1} & & & \\ c
        \ar@{.>>}[dr] & IHHrefl1 & (g \; a) \ar@{.>>}[dl] & & \\ & d &
        &&}\] }% *)
      (** %\comm{In order to apply $IHHrefl1$, we instantiate $c_0$ with $(g\
      a)$.}% *)
      (** %\comm{Therefore, there exists an element, say $x$,
      such that both $c\tto_R x$ and $(g\ a) \tto_R x$.}% *)
     (** %\comm{We then take $x$ to show that $c\tto_R x$ and $a
      \tto_R x$.}% *)
     (** %\comm{Note that $c\tto_R x$ is already an hypothesis,
        and we are done.}% *)
     (**
      %\comm{The proof of $a \tto_R x$ is done by the transitivity of
      $\tto_R$ taking $(g\ a)$ as the intermediate step.}% *)
     (** %\comm{The second subgoal corresponds
        to the case in which $a\tto_R c_0$ is generated by the rule
        $(rtrans)$. Therefore, there exists a term $b$ such that
        $a\to_R b$ and $b \tto_R c_0$. The corresponding proof context
        after introducing the universally quantified variable $b0$,
        the hypothesis $Hrefl1$ and the induction hypothesis
        $IHHrefl1$ generated by the first outer induction and the fact
        that $b0 \tto_R (g\ a)$ is given by:

        \includegraphics[scale=0.48]{figs/fig7.png} }% *)
(** %\comm{The second goal, i.e. the inductive case is 
      the consequent on $IHHrefl2$, so we can apply $IHHrefl2$ to prove it. Doing so, 
      we must prove the antecedent of $IHHrefl2$, which consists of four separate 
      hypotheses that we must prove. Those hypotheses are as follows:}% *)
(** %\comm{1. $b \tto_R (g\ b)$: This is proved by the transitivity of the
      reflexive transitive closure of $R$ using the
      hypothesis (H: $a\to_R b$) and $HZ\_prop$: $\forall a\
      b: a \to_R b \to (b \tto_R (g\ a) \land (g\ a) \tto_R (g\ b))$.}% *)
(** %\comm{2. $b0 \tto_R c$: This is exactly the
          hypothesis $Hrefl1$.}% *)
(** %\comm{3. $\forall c0: b0 \tto_R c0 \to (\exists d:
            c \tto_R d \land c0 \tto_R d)$: This is exactly the
            induction hypothesis $IHHrefl1$.}% *)
(** %\comm{4. $b0 \tto_R (g\ b)$: This is proved by the transitivity of
      the reflexive transitive closure of $R$ using the
      hypothesis $H'$: $b0 \tto_R (g\ a)$ and the fact that
      $(g\ a) \tto_R (g\ b)$ that is obtained from the fact that
      $R$ satisfies the Z property (hypothesis
      $HZ\_prop$).}% *)

(*
Definition SemiConfl {A:Type} (R: Rel A) := forall a b c, R a b -> (refltrans R) a c -> (exists d, (refltrans R) b d /\ (refltrans R) c d).

Theorem Z_prop_implies_SemiConfl {A:Type}: forall R: Rel A, Z_prop R -> SemiConfl R.
(* begin hide *)
Proof.
  intros R HZ_prop.
  unfold Z_prop in HZ_prop.
  unfold SemiConfl.
  destruct HZ_prop.
  intros a b c Hrefl Hrefl'.
  assert (Haxa: refltrans R a (x a)).
  { apply rtrans with b.  - assumption.  - apply H.  assumption.  }
  apply H in Hrefl.
  destruct Hrefl.
  clear H1.
  generalize dependent b.
  induction Hrefl'.
  - intros.
    exists (x a).
    split; assumption.
  - intros.
    destruct IHHrefl' with b0.
    + apply refltrans_composition with (x a); apply H; assumption.
    + apply refltrans_composition with (x b).
      * apply refltrans_composition with (x a).
        ** assumption.
        ** apply H.
           assumption.
      * apply refl.
    + exists x0.
      assumption.
Qed.
(* end hide *)

Theorem Semi_equiv_Confl {A: Type}: forall R: Rel A, Confl R <-> SemiConfl R.
(* begin hide *)
Proof.
  unfold Confl.
  unfold SemiConfl.
  intro R.
  split.
  - intros.
    apply H with a.
    + apply rtrans with b.
      * assumption.
      * apply refl.
    + assumption.
  - intros.
    generalize dependent c.
    induction H0.
    + intros.
      exists c.
      split.
      * assumption.
      * apply refl.
    + intros.
      specialize (H a).
      specialize (H b).
      specialize (H c0).
      apply H in H0.
      * destruct H0.
        destruct H0.
        apply IHrefltrans in H0.
        destruct H0.
        destruct H0.
        exists x0.
        split.
        ** assumption.
        ** apply refltrans_composition with x; assumption.
      * assumption.
Qed.
(* end hide *)

Corollary Zprop_implies_Confl_via_SemiConfl {A:Type}: forall R: Rel A, Z_prop R -> Confl R.
(* begin hide *)
Proof.
  intros R HZ_prop.
  apply Semi_equiv_Confl.
  generalize dependent HZ_prop.
  apply Z_prop_implies_SemiConfl.
Qed.
(* end hide *)
 *)

(** * An extension of the Z property: Compositional Z *)

Definition f_is_weak_Z (R R': Rel n_sexp) (f: n_sexp -> n_sexp) := forall a b, R a b -> ((refltrans R') b (f a) /\ (refltrans R') (f a) (f b)).

Definition comp {A} (f1 f2: A -> A) := fun x:A => f1 (f2 x).
Notation "f1 # f2" := (comp f1 f2) (at level 40).

Inductive union {A} (red1 red2: Rel A) : Rel A :=
| union_left: forall a b, red1 a b -> union red1 red2 a b
| union_right: forall a b, red2 a b -> union red1 red2 a b.
Notation "R1 !_! R2" := (union R1 R2) (at level 40).

Lemma union_or {A}: forall (r1 r2: Rel A) (a b: A), (r1 !_! r2) a b <-> (r1 a b) \/ (r2 a b).
(* begin hide *)
Proof.
  intros r1 r2 a b; split.
  - intro Hunion.
    inversion Hunion; subst.
    + left; assumption.
    + right; assumption.
  - intro Hunion.
    inversion Hunion.
    + apply union_left; assumption.
    + apply union_right; assumption.
Qed.
(* end hide *)
Require Import Setoid.
Require Import ZArith.

Lemma equiv_refltrans: forall (R R1 R2: Rel n_sexp), (forall x y, R x y <-> (R1 !_! R2) x y) -> forall x y, refltrans (R1 !_! R2) x y -> refltrans R x y.
(* begin hide *)
Proof.
  intros R R1 R2 H1 x y H2. induction H2.
  - apply refl.
  - apply rtrans with b.
    + apply H1. assumption.
    + assumption.
  - apply refl_aeq; assumption.
  - apply rtrans_aeq with b; assumption.
  Qed.
(* end hide *)

Definition Z_comp (R :Rel n_sexp) := exists (R1 R2: Rel n_sexp) (f1 f2: n_sexp -> n_sexp), (forall x y, R x y <-> (R1 !_! R2) x y) /\ f_is_Z R1 f1 /\ (forall a b, R1 a b -> (refltrans R) ((f2 # f1) a) ((f2 # f1) b)) /\ (forall a b, b = f1 a -> (refltrans R) b (f2 b)) /\ (f_is_weak_Z R2 R (f2 # f1)).

Lemma refltrans_union: forall (R R' :Rel n_sexp) (a b: n_sexp), refltrans R a b -> refltrans (R !_! R') a b.
(* begin hide *)
Proof.
  intros R R' a b Hrefl. induction Hrefl.
  - apply refl.
  - apply rtrans with b.
    + apply union_left. assumption.
    + assumption.
  - apply refl_aeq; assumption.
  - apply rtrans_aeq with b; assumption.
Qed.
(* end hide *)

Require Import Setoid.
Lemma refltrans_union_equiv: forall (R R1 R2 : Rel n_sexp), (forall (x y : n_sexp), (R x y <-> (R1 !_! R2) x y)) -> forall (x y: n_sexp), refltrans (R1 !_! R2) x y -> refltrans R x y.
(* begin hide *)
Proof.
  intros R R1 R2 H1 x y H2. induction H2.
  - apply refl.
  - apply rtrans with b.
    + apply H1. assumption.
    + assumption.
  - apply refl_aeq; assumption.
  - apply rtrans_aeq with b; assumption.
Qed.
(* end hide *)

Theorem Z_comp_implies_Z_prop: forall (R :Rel n_sexp), Z_comp R -> Z_prop R.
(* begin hide *)
Proof.
  intros R H. unfold Z_prop. unfold Z_comp in H. destruct H as [ R1 [ R2 [f1 [f2 [Hunion [H1 [H2 [H3 H4]]]]]]]]. exists (f2 # f1). intros a b HR. apply Hunion in HR. inversion HR; subst. 
  - clear HR. split.
    + apply refltrans_composition with (f1 a).
      * apply H1 in H.
        destruct H as [Hb Hf].
        apply (refltrans_union R1 R2) in Hb.
        apply refltrans_union_equiv with R1 R2.
        ** apply Hunion.
        ** apply Hb.
      * apply H3 with a; reflexivity.
    + apply H2; assumption. 
  - apply H4; assumption.
Qed.
(* end hide *)

(** Now we can use the proofs of the theorems [Z_comp_implies_Z_prop]
and [Z_prop_implies_Confl] to conclude that compositional Z is a
sufficient condition for confluence. *)

Corollary Z_comp_is_Confl: forall (R: Rel n_sexp), Z_comp R -> Confl R.
(* begin hide *)
Proof.
  intros R H. apply Z_comp_implies_Z_prop in H. apply Z_prop_implies_Confl; assumption.
Qed.
(* end hide *)

Theorem Z_comp_thm: forall (R R1 R2: Rel n_sexp) (f1 f2: n_sexp -> n_sexp), (forall x y, R x y <-> (R1 !_! R2) x y) /\ f_is_Z R1 f1 /\ (forall a b, R1 a b -> (refltrans R) ((f2 # f1) a) ((f2 # f1) b)) /\ (forall a b, b = f1 a -> (refltrans R) b (f2 b)) /\ (f_is_weak_Z R2 R (f2 # f1)) -> f_is_Z R (f2 # f1).
(* begin hide *)
Proof.
  intros R R1 R2 f1 f2 H. destruct H as [Hunion [H1 [H2 [H3 H4]]]]. unfold f_is_Z. intros a b Hab. apply Hunion in Hab. inversion Hab; subst. 
  - clear Hab; split. apply refltrans_composition with (f1 a).
    assert (Hbf1a: refltrans (R1 !_! R2) b (f1 a)).
    { apply refltrans_union. apply H1; assumption. }
    apply equiv_refltrans with R1 R2.
    + assumption.
    + assumption.
    + apply H3 with a; reflexivity.
    + apply H2; assumption.
  - unfold comp. assert (H' := H). apply H4 in H. assumption. 
Qed. 
(* end hide *)

Corollary Z_comp_eq_corol: forall (R R1 R2: Rel n_sexp) (f1 f2: n_sexp -> n_sexp), (forall x y, R x y <-> (R1 !_! R2) x y) /\ (forall a b, R1 a b -> (f1 a) = (f1 b)) /\ (forall a, (refltrans R1) a (f1 a)) /\ (forall b a, a = f1 b -> (refltrans R) a (f2 a)) /\ (f_is_weak_Z R2 R (f2 # f1)) -> f_is_Z R (f2 # f1).
(* begin hide *)
Proof.
  intros R R1 R2 f1 f2 H. destruct H as [Hunion [H1 [H2 [H3 H4]]]]. pose proof (Z_comp_thm := Z_comp_thm R R1 R2 f1 f2). apply Z_comp_thm. split.
  - assumption.
  - split.
    + unfold f_is_Z. intros a b Hab. split.
      * apply H1 in Hab. rewrite Hab. apply H2.
      * apply H1 in Hab. rewrite Hab. apply refl.
    + split.
      * intros a b Hab. unfold comp. apply H1 in Hab. rewrite Hab. apply refl.
      * split; assumption.
Qed.
(* end hide *)

Definition Z_comp_eq (R :Rel n_sexp) := exists (R1 R2: Rel n_sexp) (f1 f2: n_sexp -> n_sexp), (forall x y, R x y <-> (R1 !_! R2) x y) /\ (forall a b, R1 a b -> (f1 a) = (f1 b)) /\ (forall a, (refltrans R1) a (f1 a)) /\ (forall b a, a = f1 b -> (refltrans R) a (f2 a)) /\ (f_is_weak_Z R2 R (f2 # f1)).

Lemma Z_comp_eq_implies_Z_comp: forall (R : Rel n_sexp), Z_comp_eq R -> Z_comp R.
(* begin hide *)
Proof.
  intros R Heq. unfold Z_comp_eq in Heq. destruct Heq as [R1 [R2 [f1 [f2 [Hunion [H1 [H2 [H3 H4]]]]]]]]. unfold Z_comp. exists R1, R2, f1, f2. split.
  - assumption.
  - split.
    + unfold f_is_Z.
      intros a b H; split.
      * apply H1 in H. rewrite H. apply H2.
      * apply H1 in H. rewrite H. apply refl.
    + split.
      * intros a b H. unfold comp. apply H1 in H. rewrite H. apply refl.
      * split; assumption.
Qed.
(* end hide *)

Lemma Z_comp_eq_implies_Z_prop: forall (R : Rel n_sexp), Z_comp_eq R -> Z_prop R.
(* begin hide *)
Proof.
  intros R Heq. unfold Z_comp_eq in Heq. destruct Heq as [R1 [R2 [f1 [f2 [Hunion [H1 [H2 [H3 H4]]]]]]]]. unfold Z_prop. exists (f2 # f1). intros a b Hab. split.
  - apply Hunion in Hab. inversion Hab; subst.
    + unfold comp. apply H1 in H. rewrite H. apply refltrans_composition with (f1 b).
      * assert (H5: refltrans R1 b (f1 b)).
        { apply H2. }
        apply refltrans_union_equiv with R1 R2.
        ** assumption.
        ** apply refltrans_union. assumption.
      * apply H3 with b. reflexivity.
    + apply H4. assumption.
  - apply Hunion in Hab. inversion Hab; subst.
    + unfold comp. apply H1 in H. rewrite H. apply refl.
    + apply H4. assumption.
Qed.
(* end hide *)
