(** * SMTLIB.Eval : Evaluation of SMT-LIB Terms *)

(** The relation [⟦ t : σ ⟧(Σ, A, V) ⇓ v], which is [eval Σ A V σ t v] —
    under signature [Σ], in structure [A], with variables valued by [V], the
    term [t] evaluates at sort [σ] to the domain element [v] — and its
    metatheory.  This is Definition 11,
    _interpretation of terms_, indexed as [[t]]_I is by a structure and a
    valuation; [sat] and [entails] at the foot of the file are Definition 14.

    Evaluation is a _relation_ rather than a function because SMT-LIB gives a
    quantifier its classical meaning: [∃(x:σ) t] denotes true exactly when some
    witness makes the body true, which no structural recursion over the term can
    decide.  It is nonetheless a partial function of its arguments
    ([eval_deterministic]) and it is defined on every well-sorted term in a
    structure whose datatype sorts are constructed ([eval_total]).

    A [valuation] is a finite map from variables to a sort together with a
    value of that sort, so a variable's sort is read from the valuation, and
    a variable the valuation does not define evaluates to nothing.  A
    signature's variable sorts enter only through
    [valuation_well_sorted Σ.(sorts) V], which says [V] defines every variable
    [Σ] declares, at the declared sort; sort uniqueness, determinism and
    totality take it as a premise.

    _Arrangement._  Valuations come first, then the relation, followed by the
    facts about terms and patterns that this file happens to own but that are
    about other subjects.  The metatheory then runs: small introduction and
    inversion lemmas, moving an evaluation to another valuation, sort
    uniqueness, determinism, renaming and substitution, totality, and
    satisfaction. *)

From SMTLIB Require Import Utils Signature Theory Symbols Term Sorting.
From stdpp Require Import functions stringmap.
From Stdlib Require Import Logic.Eqdep_dec ClassicalEpsilon Classical.
From Equations Require Import Equations.

Open Scope smt_scope.

(** * Valuations *)

(** A valuation gives each variable it defines a sort and a value of that
    sort.  Definition 11 keys a valuation on variable–sort pairs instead;
    the two agree on everything a term can observe, since a term reads each
    variable at the one sort its sorting declares (README.md, under
    Definition 11).  Extending a valuation is stdpp's [<[x := existT σ v]>]
    for one binder, which shadows whatever [x] had, and
    [list_to_map (zip xs (hlist_to_list vs)) ∪ V] for a binder list.  A
    [Notation] rather than a [Definition], so that stdpp applies to it without
    unfolding.  The value type is [sigT A.(domain)] rather than
    [{σ : sort & A.(domain) σ}], because that is the type [existT σ v]
    elaborates at, and a lookup rewrites only where the two agree
    syntactically. *)
Notation valuation A := (gmap var (sigT A.(domain))).

(** The sorting a valuation carries. *)
Definition valuation_sorting {A : structure} (V : valuation A) : sorting :=
  projT1 <$> V.

(** [V] is a valuation for [S]: defined, at the declared sort, wherever [S]
    declares a variable.  It may define other variables too. *)
Definition valuation_well_sorted {A : structure} (S : sorting) (V : valuation A)
  : Prop :=
  S ⊆ valuation_sorting V.

Theorem valuation_well_sorted_lookup :
  forall A S (V : valuation A) x σ,
    valuation_well_sorted S V ->
    S !! x = Some σ ->
    exists v, V !! x = Some (existT σ v).
Proof.
  intros A S V x σ HV Hx.
  pose proof (lookup_weaken _ _ _ _ Hx HV) as Hx'.
  apply lookup_fmap_Some in Hx' as ([σ' v] & Hσ & HVx). simpl in Hσ. subst σ'.
  exists v. exact HVx.
Qed.

Theorem valuation_well_sorted_insert :
  forall A S (V : valuation A) x σ (v : A.(domain) σ),
    valuation_well_sorted S V ->
    valuation_well_sorted (<[x := σ]> S) (<[x := existT σ v]> V).
Proof.
  intros A S V x σ v HV. unfold valuation_well_sorted, valuation_sorting.
  rewrite fmap_insert. simpl. apply insert_mono. exact HV.
Qed.

Theorem valuation_well_sorted_union_lookup_list_to_map :
  forall A S (V : valuation A) xs σs (vs : hlist A.(domain) σs),
    valuation_well_sorted S V ->
    valuation_well_sorted (list_to_map (zip xs σs) ∪ S)
      (list_to_map (zip xs (hlist_to_list vs)) ∪ V).
Proof.
  intros A S V xs σs vs HV. unfold valuation_well_sorted, valuation_sorting.
  rewrite map_fmap_union, fmap_list_to_map_zip, fmap_projT1_hlist_to_list.
  apply map_union_mono_l. exact HV.
Qed.

(** Every valuation is a valuation for the sorting it carries, which is the
    sorting to use when a derivation is built for the valuation at hand
    rather than given. *)
Theorem valuation_well_sorted_refl :
  forall A (V : valuation A), valuation_well_sorted (valuation_sorting V) V.
Proof. intros A V. unfold valuation_well_sorted. reflexivity. Qed.

Theorem valuation_sorting_insert :
  forall A (V : valuation A) x σ (v : A.(domain) σ),
    valuation_sorting (<[x := existT σ v]> V) = <[x := σ]> (valuation_sorting V).
Proof. intros A V x σ v. unfold valuation_sorting. by rewrite fmap_insert. Qed.

Lemma valuation_sorting_lookup :
  forall A (V : valuation A) x σ (v : A.(domain) σ),
    V !! x = Some (existT σ v) -> valuation_sorting V !! x = Some σ.
Proof.
  intros A V x σ v Hx. apply lookup_fmap_Some. exists (existT σ v). done.
Qed.

(** Discharges [valuation_well_sorted S V] where [S] and [V] are built alike
    by the same binders, from a base the context already relates or from
    [∅]. *)
Ltac solve_valuation_well_sorted :=
  first [ eassumption
        | apply valuation_well_sorted_refl
        | apply map_empty_subseteq
        | apply valuation_well_sorted_insert; solve_valuation_well_sorted
        | apply valuation_well_sorted_union_lookup_list_to_map;
          solve_valuation_well_sorted ].

(** * The Evaluation Relation *)

(** [⟦ t : σ ⟧(Σ, A, V) ⇓ v], which is [eval Σ A V σ t v], read: the term [t]
    has, at sort [σ], the meaning [v] in the interpretation built from the
    signature [Σ], the structure [A] and the valuation [V].  The brackets are
    Definition 11's [[t]]_I; the arrow is there because the meaning is a
    relation, so that a term may have none.  The sort is part of the judgment
    because the type of [v] depends on it. *)
Reserved Notation "⟦ t : σ ⟧( Σ , A , V ) ⇓ v"
  (at level 70, t at level 99, Σ, A, V at level 99,
   format "⟦  t  :  σ  ⟧( Σ ,  A ,  V )  ⇓  v").

(** [⟦ ts : σs ⟧*(Σ, A, V) ⇓ vs], which is [evals Σ A V σs ts vs], is the
    same judgment for an argument list: [ts] has, pointwise at the sorts [σs],
    the meanings [vs]. *)
Reserved Notation "⟦ ts : σs ⟧*( Σ , A , V ) ⇓ vs"
  (at level 70, ts at level 99, Σ, A, V at level 99,
   format "⟦  ts  :  σs  ⟧*( Σ ,  A ,  V )  ⇓  vs").

(** [eval Σ A V σ t v] and its companion [evals Σ A V σs ts vs] for
    argument lists.  One constructor per term former, named [E_T<Former>],
    except that each quantifier and each [TMatch] pattern shape needs two.

    _Why quantifiers need two rules._  A single-witness rule for [TExists] would
    relate [∃(x:σ') t] to whatever the body evaluates to at _some_ witness,
    which is every value in the body's range — the relation would stop being a
    function of the term.  Splitting into [E_TExists_true] and
    [E_TExists_false] states the classical reading directly: true when some
    witness makes the body true, false when every witness makes it false.
    [E_TForall_true] / [E_TForall_false] are the duals.  Nothing evaluates a
    quantifier whose body is neither, which is where partiality enters.

    _Why [TMatch] needs three._  [E_TMatch_PVar] takes the default arm;
    [E_TMatch_PApp_true] fires an arm whose constructor built the scrutinee
    value, and [E_TMatch_PApp_false] steps past an arm whose constructor did
    not.  The two [PApp] rules are mutually exclusive by their third premise,
    which is what makes matching deterministic at the level of arm selection.

    _Why the binder rules are cofinite._  [E_TExists], [E_TForall], [E_TLambda],
    [E_TLet] and the [TMatch] arms all evaluate their body after [term_open]ing
    it at fresh variables, universally quantified over everything outside a
    finite [L].  This is the locally-nameless idiom.

    _Why [evals] is a separate inductive._  A [TApp]'s arguments have
    heterogeneous sorts, so their values form an [hlist] rather than a list, and
    Rocq's generated induction principle does not descend through a [Forall2].
    Declaring the list case as a mutual inductive is what gives the argument
    subterms a usable inductive hypothesis — the same reason [Sorting.v] states
    its list premises by position rather than with [Forall2]. *)

Inductive eval (Σ : SMTLIB.Signature.signature) (A : structure)
  : valuation A -> forall σ, term -> A.(domain) σ -> Prop :=
| E_TFVar:
  forall V x σ (v : A.(domain) σ),
    V !! x = Some (existT σ v) ->
    ⟦ TFVar x : σ ⟧(Σ, A, V) ⇓ v

| E_TApp:
  forall V f σopt ts σs σ (vs : hlist A.(domain) σs) (v : A.(domain) σ),
    ⟦ ts : σs ⟧*(Σ, A, V) ⇓ vs ->
    option_Forall (fun σopt => σopt = σ) σopt ->
    monomorphic_rank Σ f σs σ ->
    let F := A.(interp) f σs σ in
    interp_apply A.(domain) F vs = v ->
    ⟦ TApp f σopt ts : σ ⟧(Σ, A, V) ⇓ v

| E_TExists_true:
  forall (L : gset var) V σ' t
         (v' : A.(domain) σ'),
    (forall x,
        x ∉ L ->
        let t' := term_open 0 [ TFVar x ] t in
        let V' := <[ x := existT σ' v' ]> V in
        ⟦ t' : σ_bool ⟧(Σ, A, V') ⇓ cast_sym A.(domain_σ_bool) true) ->
    ⟦ TExists σ' t : σ_bool ⟧(Σ, A, V) ⇓ cast_sym A.(domain_σ_bool) true

| E_TExists_false:
  forall (L : gset var) V σ' t,
    (forall x,
        x ∉ L ->
        forall (v' : A.(domain) σ'),
        let t' := term_open 0 [ TFVar x ] t in
        let V' := <[ x := existT σ' v' ]> V in
        ⟦ t' : σ_bool ⟧(Σ, A, V') ⇓ cast_sym A.(domain_σ_bool) false) ->
    ⟦ TExists σ' t : σ_bool ⟧(Σ, A, V) ⇓ cast_sym A.(domain_σ_bool) false

| E_TForall_true:
  forall (L : gset var) V σ' t,
    (forall x,
        x ∉ L ->
        forall (v' : A.(domain) σ'),
        let t' := term_open 0 [ TFVar x ] t in
        let V' := <[ x := existT σ' v' ]> V in
        ⟦ t' : σ_bool ⟧(Σ, A, V') ⇓ cast_sym A.(domain_σ_bool) true) ->
    ⟦ TForall σ' t : σ_bool ⟧(Σ, A, V) ⇓ cast_sym A.(domain_σ_bool) true

| E_TForall_false:
  forall (L : gset var) V σ' t
         (v' : A.(domain) σ'),
    (forall x,
        x ∉ L ->
        let t' := term_open 0 [ TFVar x ] t in
        let V' := <[ x := existT σ' v' ]> V in
        ⟦ t' : σ_bool ⟧(Σ, A, V') ⇓ cast_sym A.(domain_σ_bool) false) ->
    ⟦ TForall σ' t : σ_bool ⟧(Σ, A, V) ⇓ cast_sym A.(domain_σ_bool) false

| E_TLambda:
  forall (L : gset var) V σ1 t σ2
         (f : A.(domain) (τ_map σ1 σ2)),
    (forall x,
        x ∉ L ->
        let t' := term_open 0 [ TFVar x ] t in
        (forall (v' : A.(domain) σ1),
            let V' := <[ x := existT σ1 v' ]> V in
            ⟦ t' : σ2 ⟧(Σ, A, V') ⇓ cast (A.(domain_σ_map) σ1 σ2) f v')) ->
    ⟦ TLambda σ1 t : τ_map σ1 σ2 ⟧(Σ, A, V) ⇓ f

| E_TLet:
  forall (L : gset var) V σs ts σ t vs v,
    ⟦ ts : σs ⟧*(Σ, A, V) ⇓ vs ->
    (forall xs : list var,
        NoDup xs ->
        length xs = length ts ->
        list_to_set xs ## L ->
        let t' := term_open 0 (map TFVar xs) t in
        let V' := list_to_map (zip xs (hlist_to_list vs)) ∪ V in
        ⟦ t' : σ ⟧(Σ, A, V') ⇓ v) ->
    ⟦ TLet ts t : σ ⟧(Σ, A, V) ⇓ v

| E_TMatch_PVar:
  forall V σ t t' pts v,
    ⟦ TLet [t] t' : σ ⟧(Σ, A, V) ⇓ v ->
    ⟦ TMatch t ((PVar, t') :: pts) : σ ⟧(Σ, A, V) ⇓ v

| E_TMatch_PApp_true:
  forall V σ δ t c n t' pts v' v σs,
    monomorphic_rank Σ c σs δ ->
    ⟦ t : δ ⟧(Σ, A, V) ⇓ v' ->
    (* v' is in the range of the interpretation of c: *)
    (exists vs,
        let F := A.(interp) c σs δ in
        interp_apply A.(domain) F vs = v') ->
    let gs := Σ.(selectors_for_constructor) c in
    (** Annotate each selector application with the corresponding
        constructor parameter sort [σs!!i].  SMT-LIB leaves selector ranks
        ambiguous (a selector may be overloaded), so the bare
        [TApp g None [t]] form does not determine the bound sort; the
        [Some σ_i] annotation pins it via [S_TApp_annotated] and the
        [E_TApp] output-sort check, making [eval] deterministic on matches
        without forbidding selector or tester overloading.  README.md, under
        _Deterministic evaluation of match expressions_, states the oversight
        in the standard that this departs from. *)
    ⟦ TLet (map (fun '(g, σ_i) => TApp g (Some σ_i) [t]) (zip gs σs)) t'
      : σ ⟧(Σ, A, V) ⇓ v ->
    ⟦ TMatch t ((PApp c n, t') :: pts) : σ ⟧(Σ, A, V) ⇓ v

| E_TMatch_PApp_false:
  forall V σ δ t c n t' pts v' v σs,
    monomorphic_rank Σ c σs δ ->
    ⟦ t : δ ⟧(Σ, A, V) ⇓ v' ->
    (* v' is not in the range of the interpretation of c: *)
    (forall vs,
        let F := A.(interp) c σs δ in
        interp_apply A.(domain) F vs ≠ v') ->
    ⟦ TMatch t pts : σ ⟧(Σ, A, V) ⇓ v ->
    ⟦ TMatch t ((PApp c n, t') :: pts) : σ ⟧(Σ, A, V) ⇓ v

(** Evaluation of an argument list, pointwise, into an [hlist] over the
    corresponding sort list.  Mutual with [eval] so that the argument
    subterms of a [TApp] or [TLet] get an inductive hypothesis. *)
with evals (Σ : SMTLIB.Signature.signature) (A : structure)
  : valuation A -> forall σs, list term -> hlist A.(domain) σs -> Prop :=

| ES_nil : forall V,
    ⟦ [] : [] ⟧*(Σ, A, V) ⇓ HNil

| ES_cons : forall V σ σs t ts v vs,
    ⟦ t : σ ⟧(Σ, A, V) ⇓ v ->
    ⟦ ts : σs ⟧*(Σ, A, V) ⇓ vs ->
    ⟦ t :: ts : σ :: σs ⟧*(Σ, A, V) ⇓ HCons σ σs v vs

where "⟦ t : σ ⟧( Σ , A , V ) ⇓ v" := (eval Σ A V σ t v)
and "⟦ ts : σs ⟧*( Σ , A , V ) ⇓ vs" := (evals Σ A V σs ts vs).

(** The combined induction principle for the pair.  Every mutual induction
    below runs on [eval_combined_ind]; the two component schemes exist only to
    be combined. *)
Scheme eval_mind := Induction for eval Sort Prop
  with evals_mind := Induction for evals Sort Prop.
Combined Scheme eval_combined_ind from eval_mind, evals_mind.

(** * Inversion Principles *)

(** An [eval] derivation's value index depends on its sort index, so
    [inversion] leaves an [existT] equation between them, which it undoes
    with [Eqdep.inj_pair2] and so with the axiom [eq_rect_eq].  [destruct] on
    a derivation whose indices are all variables leaves no such equation, so
    each constructor shape is inverted once here, remembering only the term,
    and the tactic is not used on [eval] below.

    Where a constructor fixes an index that the statement leaves free — the
    sort of a [TLambda] or of a quantifier, the sort list of an [evals] —
    the conclusion is an [existT] over [sort] or [list sort], and those have
    decidable equality, so [Eqdep_dec.inj_pair2_eq_dec] strips them. *)

Section Inversion.

  Context (Σ : SMTLIB.Signature.signature) (A : structure).

  Theorem eval_TFVar_inv : forall (V : valuation A) x σ (v : A.(domain) σ),
      ⟦ TFVar x : σ ⟧(Σ, A, V) ⇓ v -> V !! x = Some (existT σ v).
  Proof.
    intros V x σ v Hev. remember (TFVar x) as t0 eqn:Ht.
    destruct Hev; try discriminate.
    injection Ht as <-. exact H.
  Qed.

  Theorem eval_TApp_inv :
    forall (V : valuation A) f σopt ts σ (v : A.(domain) σ),
      ⟦ TApp f σopt ts : σ ⟧(Σ, A, V) ⇓ v ->
      exists σs (vs : hlist A.(domain) σs),
        ⟦ ts : σs ⟧*(Σ, A, V) ⇓ vs /\
        option_Forall (fun σ' => σ' = σ) σopt /\
        monomorphic_rank Σ f σs σ /\
        interp_apply A.(domain) (A.(interp) f σs σ) vs = v.
  Proof.
    intros V f σopt ts σ v Hev. remember (TApp f σopt ts) as t0 eqn:Ht.
    destruct Hev; try discriminate.
    injection Ht as <- <- <-. eauto 10.
  Qed.

  Theorem eval_TLambda_inv : forall (V : valuation A) σ1 t σ (f : A.(domain) σ),
      ⟦ TLambda σ1 t : σ ⟧(Σ, A, V) ⇓ f ->
      exists (L : gset var) σ2 (g : A.(domain) (τ_map σ1 σ2)),
        existT σ f = existT (τ_map σ1 σ2) g /\
        forall x, x ∉ L -> forall v' : A.(domain) σ1,
            ⟦ term_open 0 [TFVar x] t : σ2 ⟧(Σ, A, <[x := existT _ v']> V)
              ⇓ cast (A.(domain_σ_map) σ1 σ2) g v'.
  Proof.
    intros V σ1 t σ f Hev. remember (TLambda σ1 t) as t0 eqn:Ht.
    destruct Hev; try discriminate.
    injection Ht as <- <-. exists L, σ2, f. split; [reflexivity | exact H].
  Qed.

  Theorem eval_TExists_inv :
    forall (V : valuation A) σ' t σ (v : A.(domain) σ),
      ⟦ TExists σ' t : σ ⟧(Σ, A, V) ⇓ v ->
      exists L : gset var,
        (exists v' : A.(domain) σ',
            existT σ v = existT σ_bool (cast_sym A.(domain_σ_bool) true) /\
            forall x, x ∉ L ->
              ⟦ term_open 0 [TFVar x] t : σ_bool ⟧(Σ, A, <[x := existT _ v']> V)
                ⇓ cast_sym A.(domain_σ_bool) true)
        \/ (existT σ v = existT σ_bool (cast_sym A.(domain_σ_bool) false) /\
            forall x, x ∉ L -> forall v' : A.(domain) σ',
              ⟦ term_open 0 [TFVar x] t : σ_bool ⟧(Σ, A, <[x := existT _ v']> V)
                ⇓ cast_sym A.(domain_σ_bool) false).
  Proof.
    intros V σ' t σ v Hev. remember (TExists σ' t) as t0 eqn:Ht.
    destruct Hev; try discriminate.
    - injection Ht as <- <-. exists L. left. exists v'.
      split; [reflexivity | exact H].
    - injection Ht as <- <-. exists L. right. split; [reflexivity | exact H].
  Qed.

  (** Inverting a true existential: there is a witness, and the body holds at
      it for every sufficiently fresh name.  The [false] rule cannot apply,
      since [true] and [false] are distinct domain elements. *)
  Corollary eval_TExists_true_inv :
    forall (V : valuation A) σ' t,
      ⟦ TExists σ' t : σ_bool ⟧(Σ, A, V) ⇓ cast_sym A.(domain_σ_bool) true ->
      exists (L : gset var) (v' : A.(domain) σ'),
        forall x, x ∉ L ->
          ⟦ term_open 0 [TFVar x] t : σ_bool ⟧(Σ, A, <[x := existT σ' v']> V)
            ⇓ cast_sym A.(domain_σ_bool) true.
  Proof.
    intros V σ' t Hex.
    destruct (eval_TExists_inv V σ' t σ_bool _ Hex)
      as (L & [(v' & _ & Hbody) | (Hval & _)]).
    - exists L, v'. exact Hbody.
    - exfalso. eapply cast_sym_true_neq_false.
      apply (Eqdep_dec.inj_pair2_eq_dec _ (fun x y => decide (x = y))) in Hval.
      exact Hval.
  Qed.

  Theorem eval_TForall_inv :
    forall (V : valuation A) σ' t σ (v : A.(domain) σ),
      ⟦ TForall σ' t : σ ⟧(Σ, A, V) ⇓ v ->
      exists L : gset var,
        (existT σ v = existT σ_bool (cast_sym A.(domain_σ_bool) true) /\
         forall x, x ∉ L -> forall v' : A.(domain) σ',
             ⟦ term_open 0 [TFVar x] t : σ_bool ⟧(Σ, A, <[x := existT _ v']> V)
               ⇓ cast_sym A.(domain_σ_bool) true)
        \/ (exists v' : A.(domain) σ',
               existT σ v = existT σ_bool (cast_sym A.(domain_σ_bool) false) /\
               forall x, x ∉ L ->
                 ⟦ term_open 0 [TFVar x] t
                   : σ_bool ⟧(Σ, A, <[x := existT _ v']> V)
                   ⇓ cast_sym A.(domain_σ_bool) false).
  Proof.
    intros V σ' t σ v Hev. remember (TForall σ' t) as t0 eqn:Ht.
    destruct Hev; try discriminate.
    - injection Ht as <- <-. exists L. left. split; [reflexivity | exact H].
    - injection Ht as <- <-. exists L. right. exists v'.
      split; [reflexivity | exact H].
  Qed.

  Corollary eval_TForall_true_inv :
    forall (V : valuation A) σ' t,
      ⟦ TForall σ' t : σ_bool ⟧(Σ, A, V) ⇓ cast_sym A.(domain_σ_bool) true ->
      exists L : gset var,
      forall x, x ∉ L -> forall (v' : A.(domain) σ'),
          ⟦ term_open 0 [ TFVar x ] t : σ_bool ⟧(Σ, A, <[x := existT _ v']> V)
            ⇓ cast_sym A.(domain_σ_bool) true.
  Proof.
    intros V σ' t Hev.
    destruct (eval_TForall_inv V σ' t σ_bool _ Hev)
      as (L & [[_ Hbody] | (v' & Hval & _)]).
    - exists L. exact Hbody.
    - (* E_TForall_false: the two value casts would have to agree. *)
      exfalso.
      apply (Eqdep_dec.inj_pair2_eq_dec _ (fun x y => decide (x = y))) in Hval.
      eapply cast_sym_true_neq_false. exact Hval.
  Qed.

  Theorem eval_TLet_inv : forall (V : valuation A) ts t σ (v : A.(domain) σ),
      ⟦ TLet ts t : σ ⟧(Σ, A, V) ⇓ v ->
      exists (L : gset var) σs (vs : hlist A.(domain) σs),
        ⟦ ts : σs ⟧*(Σ, A, V) ⇓ vs /\
        (forall xs, NoDup xs -> length xs = length ts -> list_to_set xs ## L ->
            ⟦ term_open 0 (map TFVar xs) t
              : σ ⟧(Σ, A, list_to_map (zip xs (hlist_to_list vs)) ∪ V) ⇓ v).
  Proof.
    intros V ts t σ v Hev. remember (TLet ts t) as t0 eqn:Ht.
    destruct Hev; try discriminate.
    injection Ht as <- <-. exists L, σs, vs. split; [exact H | exact H0].
  Qed.

  Theorem eval_TMatch_nil_inv : forall (V : valuation A) t σ (v : A.(domain) σ),
      ⟦ TMatch t [] : σ ⟧(Σ, A, V) ⇓ v -> False.
  Proof.
    intros V t σ v Hev. remember (TMatch t []) as t0 eqn:Ht.
    destruct Hev; discriminate.
  Qed.

  Theorem eval_TMatch_PVar_inv :
    forall (V : valuation A) t t' pts σ (v : A.(domain) σ),
      ⟦ TMatch t ((PVar, t') :: pts) : σ ⟧(Σ, A, V) ⇓ v ->
      ⟦ TLet [t] t' : σ ⟧(Σ, A, V) ⇓ v.
  Proof.
    intros V t t' pts σ v Hev.
    remember (TMatch t ((PVar, t') :: pts)) as t0 eqn:Ht.
    destruct Hev; try discriminate.
    injection Ht as <- <- <-. assumption.
  Qed.

  Theorem eval_TMatch_PApp_inv :
    forall (V : valuation A) t c n t' pts σ (v : A.(domain) σ),
      ⟦ TMatch t ((PApp c n, t') :: pts) : σ ⟧(Σ, A, V) ⇓ v ->
      exists δ σs (v' : A.(domain) δ),
        monomorphic_rank Σ c σs δ /\
        ⟦ t : δ ⟧(Σ, A, V) ⇓ v' /\
        ((exists vs, interp_apply A.(domain) (A.(interp) c σs δ) vs = v') /\
           ⟦ TLet (map (fun '(g, σ_i) => TApp g (Some σ_i) [t])
                     (zip (Σ.(selectors_for_constructor) c) σs)) t'
             : σ ⟧(Σ, A, V) ⇓ v
         \/ (forall vs, interp_apply A.(domain) (A.(interp) c σs δ) vs <> v') /\
              ⟦ TMatch t pts : σ ⟧(Σ, A, V) ⇓ v).
  Proof.
    intros V t c n t' pts σ v Hev.
    remember (TMatch t ((PApp c n, t') :: pts)) as t0 eqn:Ht.
    destruct Hev; try discriminate.
    - injection Ht as <- <- <- <- <-. exists δ, σs, v'.
      split; [exact H|]. split; [exact Hev1|].
      left. split; [exact H0 | exact Hev2].
    - injection Ht as <- <- <- <- <-. exists δ, σs, v'.
      split; [exact H|]. split; [exact Hev1|].
      right. split; [exact H0 | exact Hev2].
  Qed.

  Theorem evals_nil_sorts : forall (V : valuation A) σs vs,
      ⟦ [] : σs ⟧*(Σ, A, V) ⇓ vs -> σs = [].
  Proof.
    intros V σs vs H. remember ([] : list term) as ts eqn:Hts.
    destruct H; [reflexivity | discriminate].
  Qed.

  Theorem evals_cons_sigT :
    forall (V : valuation A) σs t ts (vs : hlist A.(domain) σs),
      ⟦ t :: ts : σs ⟧*(Σ, A, V) ⇓ vs ->
      exists σ σs' v vs',
        ⟦ t : σ ⟧(Σ, A, V) ⇓ v /\ ⟦ ts : σs' ⟧*(Σ, A, V) ⇓ vs' /\
        existT σs vs = existT (σ :: σs') (HCons σ σs' v vs').
  Proof.
    intros V σs t ts vs H. remember (t :: ts) as tl eqn:Htl.
    destruct H as [| V0 σ σs' t0 ts0 v vs' Hhd Htl2]; [discriminate|].
    injection Htl as <- <-. exists σ, σs', v, vs'. auto.
  Qed.

  Corollary evals_cons_inv :
    forall (V : valuation A) σ σs t ts (vs : hlist A.(domain) (σ :: σs)),
      ⟦ t :: ts : σ :: σs ⟧*(Σ, A, V) ⇓ vs ->
      exists v vs', vs = HCons σ σs v vs' /\
                    ⟦ t : σ ⟧(Σ, A, V) ⇓ v /\ ⟦ ts : σs ⟧*(Σ, A, V) ⇓ vs'.
  Proof.
    intros V σ σs t ts vs H.
    destruct (evals_cons_sigT V _ t ts vs H)
      as (σ0 & σs0 & v & vs0 & Hhd & Htl & Heq).
    pose proof (f_equal (@projT1 _ _) Heq) as Hidx. simpl in Hidx.
    injection Hidx as <- <-.
    apply (Eqdep_dec.inj_pair2_eq_dec _ (fun x y => decide (x = y))) in Heq.
    exists v, vs0. auto.
  Qed.

End Inversion.

(** * Basic Facts About Evaluation *)

(** Short results reading a constructor of [eval] or [evals] off in one
    direction or the other.  These are the vocabulary the rest of the file is
    written in. *)

(** A [TFVar] that evaluates at a well-formed monomorphic [σ] is declared at
    [σ] by the valuation's sorting, since [E_TFVar] reads its sort from the
    valuation. *)
Theorem eval_TFVar_has_sort :
  forall Σ A (V : valuation A) x σ (v : A.(domain) σ),
    sort_wf Σ σ ->
    monomorphic σ ->
    ⟦ TFVar x : σ ⟧(Σ, A, V) ⇓ v ->
    signature_with_sorts Σ (valuation_sorting V) ⊢ TFVar x : σ.
Proof.
  intros Σ A V x σ v Hwf Hmono Hev.
  apply eval_TFVar_inv in Hev.
  apply S_TFVar; [| exact Hwf | exact Hmono].
  change (valuation_sorting V !! x = Some σ).
  apply lookup_fmap_Some. exists (existT σ v). split; [reflexivity | exact Hev].
Qed.

(** A freshly inserted variable evaluates to the value inserted at it. *)
Theorem eval_inserted_TFVar :
  forall Σ A (V : valuation A) x σ (w : A.(domain) σ),
    ⟦ TFVar x : σ ⟧(Σ, A, <[x := existT σ w]> V) ⇓ w.
Proof. intros Σ A V x σ w. apply E_TFVar, lookup_insert_eq. Qed.

(** Evaluation transports along an equation of sorts and a heterogeneous
    equation of values.  The bridge between a goal stated at one sort and a
    hypothesis stated at another. *)
Theorem eval_value_heq :
  forall Σ A (V : valuation A) σ1 σ2 t
         (v1 : A.(domain) σ1) (v2 : A.(domain) σ2),
    σ1 = σ2 ->
    v1 ≅ v2 ->
    ⟦ t : σ1 ⟧(Σ, A, V) ⇓ v1 ->
    ⟦ t : σ2 ⟧(Σ, A, V) ⇓ v2.
Proof.
  intros Σ A V σ1 σ2 t v1 v2 Hσ Hv Hev.
  subst σ2. apply eq_of_heq in Hv. subst v2. exact Hev.
Qed.

(** An [evals] has as many sorts as it has terms. *)
Theorem evals_length :
  forall Σ A (V : valuation A) σs ts vs,
    ⟦ ts : σs ⟧*(Σ, A, V) ⇓ vs -> length σs = length ts.
Proof.
  intros Σ A V σs ts vs H. induction H; simpl; auto.
Qed.

(** From an [evals], the [i]-th argument term evaluates at the [i]-th
    sort to some value. *)
Theorem evals_nth :
  forall Σ A (V : valuation A) σs ts vs,
    ⟦ ts : σs ⟧*(Σ, A, V) ⇓ vs ->
    forall i t_i σ_i,
      ts !! i = Some t_i ->
      σs !! i = Some σ_i ->
      exists w, ⟦ t_i : σ_i ⟧(Σ, A, V) ⇓ w.
Proof.
  intros Σ A V σs ts vs H.
  induction H; intros i t_i σ_i Hts Hσs.
  - rewrite lookup_nil in Hts. discriminate.
  - destruct i as [|i'].
    + simpl in Hts, Hσs. injection Hts as <-. injection Hσs as <-.
      exists v. exact H.
    + simpl in Hts, Hσs. apply (IHevals i' t_i σ_i Hts Hσs).
Qed.

(** [evals_nth] at the value the [hlist] actually holds, rather than at
    some value: what a proof reading a constructor application apart needs,
    since the arguments it has to relate are the ones inside the [hlist]. *)
Theorem evals_lookup :
  forall Σ A (V : valuation A) σs ts (vs : hlist A.(domain) σs),
    ⟦ ts : σs ⟧*(Σ, A, V) ⇓ vs ->
    forall i t_i σ_i (w_i : A.(domain) σ_i),
      ts !! i = Some t_i ->
      hlist_lookup A.(domain) vs i = Some (existT σ_i w_i) ->
      ⟦ t_i : σ_i ⟧(Σ, A, V) ⇓ w_i.
Proof.
  intros Σ A V σs ts vs Hev.
  induction Hev; intros [|i] t_i σ_i w_i Ht Hw; simpl in *; try discriminate.
  - injection Ht as <-. injection Hw as Hw. subst σ_i.
    apply (Eqdep_dec.inj_pair2_eq_dec _ (fun x y => decide (x = y)))
    in H0. subst w_i. exact H.
  - eapply IHHev; eauto.
Qed.

(** The converse of [evals_nth]: at matching lengths, pointwise
    evaluation of the argument terms assembles into an [evals]. *)
Theorem evals_intro :
  forall Σ A (V : valuation A) σs ts,
    length σs = length ts ->
    (forall i t_i σ_i,
        ts !! i = Some t_i ->
        σs !! i = Some σ_i ->
        exists w, ⟦ t_i : σ_i ⟧(Σ, A, V) ⇓ w) ->
    exists vs, ⟦ ts : σs ⟧*(Σ, A, V) ⇓ vs.
Proof.
  intros Σ A V σs. induction σs as [|σ σs' IH]; intros ts Hlen Hpt.
  - destruct ts; [|discriminate]. exists HNil. constructor.
  - destruct ts as [|t ts']; [discriminate|].
    simpl in Hlen. injection Hlen as Hlen.
    destruct (Hpt 0 t σ eq_refl eq_refl) as (v & Hv).
    assert (Hpt' : forall i t_i σ_i,
               ts' !! i = Some t_i ->
               σs' !! i = Some σ_i ->
               exists w, ⟦ t_i : σ_i ⟧(Σ, A, V) ⇓ w)
      by (intros i t_i σ_i Hts Hσs;
          apply (Hpt (S i) t_i σ_i Hts Hσs)).
    destruct (IH ts' Hlen Hpt') as (vs & Hvs).
    exists (HCons σ σs' v vs). constructor; assumption.
Qed.

(** [E_TLet] with its cofinite premise packaged: to evaluate a [TLet] it is
    enough to evaluate the body at every distinct binder list of the right
    length avoiding [L]. *)
Theorem eval_TLet_NoDup_intro :
  forall Σ A (V : valuation A) σs ts σ t vs v (L : gset var),
    ⟦ ts : σs ⟧*(Σ, A, V) ⇓ vs ->
    (forall xs,
      NoDup xs ->
      length xs = length ts ->
      list_to_set xs ## L ->
      ⟦ term_open 0 (map TFVar xs) t
        : σ ⟧(Σ, A, list_to_map (zip xs (hlist_to_list vs)) ∪ V) ⇓ v) ->
    ⟦ TLet ts t : σ ⟧(Σ, A, V) ⇓ v.
Proof.
  intros Σ A V σs ts σ t vs v L Hts Hbody.
  eapply E_TLet; eauto.
Qed.

(** The mutual induction behind [eval_term_open_map_TFVar]. *)
Local Lemma eval_term_open_map_TFVar_mut_aux :
  forall Σ A,
  (forall (V : valuation A) σ t v
     (_ : ⟦ t : σ ⟧(Σ, A, V) ⇓ v),
   forall k xs,
     ⟦ term_open k (map TFVar xs) t : σ ⟧(Σ, A, V) ⇓ v)
  /\
  (forall (V : valuation A) σs ts vs
     (_ : ⟦ ts : σs ⟧*(Σ, A, V) ⇓ vs),
   forall k xs,
     ⟦ map (term_open k (map TFVar xs)) ts : σs ⟧*(Σ, A, V) ⇓ vs).
Proof.
  intros Σ A.
  apply eval_combined_ind.
  - (* E_TFVar *)
    intros V x σ v Hv k xs. simpl. constructor. exact Hv.
  - (* E_TApp *)
    intros V f σopt ts σs σ vs v Hts IHts Hσopt Hrank F Hv k xs.
    simpl. eapply E_TApp.
    + exact (IHts k xs).
    + exact Hσopt.
    + exact Hrank.
    + exact Hv.
  - (* E_TExists_true *)
    intros L V σ' t v' Hbody IHbody k xs.
    simpl. eapply E_TExists_true with (L := L) (v' := v').
    intros y Hy.
    change [TFVar y] with (map TFVar [y]).
    rewrite term_open_comm by lia.
    change (map TFVar [y]) with [TFVar y].
    specialize (IHbody y Hy) as Hih. simpl in Hih.
    exact (Hih (S k) xs).
  - (* E_TExists_false *)
    intros L V σ' t Hbody IHbody k xs.
    simpl. eapply E_TExists_false with (L := L).
    intros y Hy w.
    change [TFVar y] with (map TFVar [y]).
    rewrite term_open_comm by lia.
    change (map TFVar [y]) with [TFVar y].
    specialize (IHbody y Hy w) as Hih. simpl in Hih.
    exact (Hih (S k) xs).
  - (* E_TForall_true *)
    intros L V σ' t Hbody IHbody k xs.
    simpl. eapply E_TForall_true with (L := L).
    intros y Hy w.
    change [TFVar y] with (map TFVar [y]).
    rewrite term_open_comm by lia.
    change (map TFVar [y]) with [TFVar y].
    specialize (IHbody y Hy w) as Hih. simpl in Hih.
    exact (Hih (S k) xs).
  - (* E_TForall_false *)
    intros L V σ' t v' Hbody IHbody k xs.
    simpl. eapply E_TForall_false with (L := L) (v' := v').
    intros y Hy.
    change [TFVar y] with (map TFVar [y]).
    rewrite term_open_comm by lia.
    change (map TFVar [y]) with [TFVar y].
    specialize (IHbody y Hy) as Hih. simpl in Hih.
    exact (Hih (S k) xs).
  - (* E_TLambda *)
    intros L V σ1 t σ2 f Hbody IHbody k xs.
    simpl. eapply E_TLambda with (L := L).
    intros y Hy t_body w. unfold t_body.
    change [TFVar y] with (map TFVar [y]).
    rewrite term_open_comm by lia.
    change (map TFVar [y]) with [TFVar y].
    specialize (IHbody y Hy w) as Hih. simpl in Hih.
    exact (Hih (S k) xs).
  - (* E_TLet *)
    intros L V σs ts σ t vs v Hts IHts Hbody IHbody k xs.
    simpl. eapply E_TLet with (L := L) (vs := vs).
    + exact (IHts k xs).
    + intros ys Hndys Hlen Hys.
      rewrite length_map in Hlen.
      rewrite term_open_comm by lia.
      specialize (IHbody ys Hndys Hlen Hys) as Hih. simpl in Hih.
      exact (Hih (S k) xs).
  - (* E_TMatch_PVar *)
    intros V σ t t' pts v Hlet IHlet k xs.
    simpl. apply E_TMatch_PVar. exact (IHlet k xs).
  - (* E_TMatch_PApp_true *)
    intros V σ δ t c n t' pts v' v σs Hrank Hscrut IHscrut Hrange gs
           Hbody IHbody k xs.
    simpl. eapply E_TMatch_PApp_true.
    + exact Hrank.
    + exact (IHscrut k xs).
    + exact Hrange.
    + specialize (IHbody k xs). simpl in IHbody.
      rewrite map_map in IHbody.
      erewrite map_ext in IHbody; [exact IHbody|].
      intros [g σ_i]. reflexivity.
  - (* E_TMatch_PApp_false *)
    intros V σ δ t c n t' pts v' v σs Hrank Hscrut IHscrut Hrange
           Htail IHtail k xs.
    simpl. eapply E_TMatch_PApp_false.
    + exact Hrank.
    + exact (IHscrut k xs).
    + exact Hrange.
    + exact (IHtail k xs).
  - (* ES_nil *)
    intros V k xs. simpl. constructor.
  - (* ES_cons *)
    intros V σ σs t ts v vs Hev IHev Hts IHts k xs.
    simpl. constructor.
    + exact (IHev k xs).
    + exact (IHts k xs).
Qed.

(** Opening a term that already evaluates changes nothing, at any level and
    any variable list. *)
Corollary eval_term_open_map_TFVar :
  forall Σ A (V : valuation A) σ t v,
    ⟦ t : σ ⟧(Σ, A, V) ⇓ v ->
    forall k xs,
      ⟦ term_open k (map TFVar xs) t : σ ⟧(Σ, A, V) ⇓ v.
Proof.
  intros Σ A V σ t v Hev k xs.
  destruct (eval_term_open_map_TFVar_mut_aux Σ A) as [Hopen _].
  exact (Hopen V σ t v Hev k xs).
Qed.

(** The binders [xs] evaluate, in the context extended at [xs] by the value
    hlist [ws], to exactly [ws].  This is what recovers the interpretation of a
    define-fun's head application from its instantiated body equation. *)
Lemma evals_map_TFVar :
  forall Σ A (xs : list var) (σs : list sort)
         (V : valuation A) (ws : hlist A.(domain) σs),
    NoDup xs ->
    length xs = length σs ->
    ⟦ map TFVar xs : σs ⟧*(Σ, A, list_to_map (zip xs (hlist_to_list ws)) ∪ V)
      ⇓ ws.
Proof.
  intros Σ A xs.
  induction xs as [|x xs' IH]; intros σs V ws Hnodup Hlen.
  - destruct σs as [|σ0 σs']; [|discriminate Hlen].
    hlist_nil ws. constructor.
  - destruct σs as [|σ0 σs']; [discriminate Hlen|].
    hlist_cons ws. simpl in Hlen.
    apply NoDup_cons in Hnodup as [Hx_notin Hnodup'].
    assert (Hnone : (list_to_map (zip xs' (hlist_to_list ws)) : valuation A) !! x = None)
      by (apply lookup_list_to_map_zip_None; exact Hx_notin).
    simpl. rewrite <- insert_union_l, (insert_union_r _ _ _ _ Hnone).
    constructor.
    + apply E_TFVar. rewrite (lookup_union_r _ _ _ Hnone). apply lookup_insert_eq.
    + apply IH; [exact Hnodup' | lia].
Qed.

(** A list of variables evaluates to one sort list and one value hlist, under
    any valuation: each variable's sort and value are read from the
    valuation. *)
Lemma evals_map_TFVar_deterministic :
  forall Σ A (V : valuation A) (xs : list var) σs1 σs2
         (vs1 : hlist A.(domain) σs1) (vs2 : hlist A.(domain) σs2),
    ⟦ map TFVar xs : σs1 ⟧*(Σ, A, V) ⇓ vs1 ->
    ⟦ map TFVar xs : σs2 ⟧*(Σ, A, V) ⇓ vs2 ->
    σs1 = σs2 /\ vs1 ≅ vs2.
Proof.
  intros Σ A V xs.
  induction xs as [|x xs IH]; intros σs1 σs2 vs1 vs2 H1 H2; simpl in H1, H2.
  - apply evals_nil_sorts in H1 as ->. apply evals_nil_sorts in H2 as ->.
    hlist_nil vs1. hlist_nil vs2. split; reflexivity.
  - destruct (evals_cons_sigT Σ A V _ _ _ vs1 H1)
      as (σ1 & σs1' & v1 & vs1' & Hv1 & Hvs1 & E1).
    destruct (evals_cons_sigT Σ A V _ _ _ vs2 H2)
      as (σ2 & σs2' & v2 & vs2' & Hv2 & Hvs2 & E2).
    apply eval_TFVar_inv in Hv1, Hv2. rewrite Hv1 in Hv2. injection Hv2 as <- Hv.
    apply (Eqdep_dec.inj_pair2_eq_dec _ (fun x y => decide (x = y))) in Hv.
    subst v2.
    destruct (IH _ _ _ _ Hvs1 Hvs2) as [<- Hvs]. apply eq_of_heq in Hvs. subst vs2'.
    rewrite <- E2 in E1. apply eq_sigT_eq_dep in E1.
    split; [destruct E1; reflexivity | exact E1].
Qed.

(** * Transporting an Evaluation *)

(** An evaluation reads its valuation only at the term's free variables, so
    it moves to any valuation agreeing with the original there.  Weakening
    and strengthening are the one-variable cases, and they are the ones the
    binder cases of later inductions actually use. *)

(** ** Agreement on Free Variables *)

(** The mutual induction behind [eval_cong]. *)
Local Lemma eval_cong_mut_aux :
  forall Σ A,
  (forall (V1 : valuation A) σ t v
     (_ : ⟦ t : σ ⟧(Σ, A, V1) ⇓ v),
   forall (V2 : valuation A),
     (forall x, x ∈ fv t -> V1 !! x = V2 !! x) ->
     ⟦ t : σ ⟧(Σ, A, V2) ⇓ v)
  /\
  (forall (V1 : valuation A) σs ts vs
     (_ : ⟦ ts : σs ⟧*(Σ, A, V1) ⇓ vs),
   forall (V2 : valuation A),
     (forall x t, t ∈ ts -> x ∈ fv t -> V1 !! x = V2 !! x) ->
     ⟦ ts : σs ⟧*(Σ, A, V2) ⇓ vs).
Proof.
  intros Σ A.
  apply eval_combined_ind.
  - (* E_TFVar *)
    intros V x σ v Hx V2 Hval. apply E_TFVar.
    rewrite <- Hval; [exact Hx | simpl; set_solver].
  - (* E_TApp *)
    intros V f σopt ts σs σ vs v Hts IHts Hopt Hrank F Heq V2 Hval.
    eapply E_TApp; [|exact Hopt|exact Hrank|exact Heq].
    apply IHts. intros z t' Ht' Hz. apply Hval. simpl.
    apply elem_of_union_list. exists (fv t'). split; [|exact Hz].
    apply list_elem_of_fmap. exists t'. split; [reflexivity|exact Ht'].
  - (* E_TExists_true *)
    intros L V σ' t v' Hbody IHbody V2 Hval.
    apply E_TExists_true with (L := L) (v' := v').
    intros y Hy. simpl. apply (IHbody y Hy).
    intros z Hz. apply lookup_insert_agree. intros Hzy. apply Hval. simpl.
    pose proof (fv_term_open_TFVar1_subseteq t 0 y z Hz). set_solver.
  - (* E_TExists_false *)
    intros L V σ' t Hbody IHbody V2 Hval.
    apply E_TExists_false with (L := L).
    intros y Hy w. simpl. apply (IHbody y Hy w).
    intros z Hz. apply lookup_insert_agree. intros Hzy. apply Hval. simpl.
    pose proof (fv_term_open_TFVar1_subseteq t 0 y z Hz). set_solver.
  - (* E_TForall_true *)
    intros L V σ' t Hbody IHbody V2 Hval.
    apply E_TForall_true with (L := L).
    intros y Hy w. simpl. apply (IHbody y Hy w).
    intros z Hz. apply lookup_insert_agree. intros Hzy. apply Hval. simpl.
    pose proof (fv_term_open_TFVar1_subseteq t 0 y z Hz). set_solver.
  - (* E_TForall_false *)
    intros L V σ' t v' Hbody IHbody V2 Hval.
    apply E_TForall_false with (L := L) (v' := v').
    intros y Hy. simpl. apply (IHbody y Hy).
    intros z Hz. apply lookup_insert_agree. intros Hzy. apply Hval. simpl.
    pose proof (fv_term_open_TFVar1_subseteq t 0 y z Hz). set_solver.
  - (* E_TLambda *)
    intros L V σ1 t σ2 f Hbody IHbody V2 Hval.
    apply E_TLambda with (L := L).
    intros y Hy. simpl. intros w. apply (IHbody y Hy w).
    intros z Hz. apply lookup_insert_agree. intros Hzy. apply Hval. simpl.
    pose proof (fv_term_open_TFVar1_subseteq t 0 y z Hz). set_solver.
  - (* E_TLet *)
    intros L V σs ts σ t vs v Hts IHts Hbody IHbody V2 Hval.
    apply E_TLet with (L := L) (vs := vs).
    + apply IHts. intros z t' Ht' Hz. apply Hval. simpl.
      apply elem_of_union_r. apply elem_of_union_list.
      exists (fv t'). split; [|exact Hz].
      apply list_elem_of_fmap. exists t'. split; [reflexivity|exact Ht'].
    + intros xs Hndxs Hlen Hxs. simpl.
      pose proof (evals_length Σ A V σs ts vs Hts) as Hσslen.
      apply (IHbody xs Hndxs Hlen Hxs).
      intros z Hz. apply lookup_union_agree. intros Hnone. apply Hval. simpl.
      (* [z] is not a binder, since every binder is in the map's domain *)
      apply not_elem_of_list_to_map_2 in Hnone.
      rewrite fst_zip in Hnone by (rewrite length_hlist_to_list; lia).
      pose proof (fv_term_open_TFVar_subseteq t 0 xs z Hz) as Hzt.
      apply elem_of_union_l.
      apply elem_of_union in Hzt as [Hzt|Hzt]; [exact Hzt|].
      apply elem_of_list_to_set in Hzt. contradiction.
  - (* E_TMatch_PVar *)
    intros V σ t t' pts v Hlet IHlet V2 Hval.
    apply E_TMatch_PVar. apply IHlet.
    intros z Hz. apply Hval. simpl in Hz. simpl. set_solver.
  - (* E_TMatch_PApp_true *)
    intros V σ δ t c n t' pts v' v σs Hrank Ht IHt Hrange gs Hlet IHlet
      V2 Hval.
    eapply E_TMatch_PApp_true.
    + exact Hrank.
    + apply IHt. intros z Hz. apply Hval. simpl. set_solver.
    + exact Hrange.
    + apply IHlet. intros z Hz. apply Hval. simpl.
      pose proof (fv_TLet_selectors_subseteq gs σs t t' z Hz). set_solver.
  - (* E_TMatch_PApp_false *)
    intros V σ δ t c n t' pts v' v σs Hrank Ht IHt Hnot Hpts IHpts V2 Hval.
    eapply E_TMatch_PApp_false.
    + exact Hrank.
    + apply IHt. intros z Hz. apply Hval. simpl. set_solver.
    + exact Hnot.
    + apply IHpts. intros z Hz. apply Hval. simpl in Hz. simpl. set_solver.
  - (* ES_nil *)
    intros V V2 Hval. constructor.
  - (* ES_cons *)
    intros V σ σs t ts v vs Ht IHt Hts IHts V2 Hval.
    constructor.
    + apply IHt. intros z Hz. eapply Hval; [left|exact Hz].
    + apply IHts. intros z t' Ht' Hz. eapply Hval; [right; exact Ht'|exact Hz].
Qed.

(** Evaluation depends only on the valuation at the term's free variables. *)
Theorem eval_cong :
  forall Σ A (V1 V2 : valuation A) σ t (v : A.(domain) σ),
    (forall x, x ∈ fv t -> V1 !! x = V2 !! x) ->
    ⟦ t : σ ⟧(Σ, A, V1) ⇓ v <-> ⟦ t : σ ⟧(Σ, A, V2) ⇓ v.
Proof.
  intros Σ A V1 V2 σ t v Hag.
  destruct (eval_cong_mut_aux Σ A) as [Hev _].
  split; intros Heval; eapply Hev; [exact Heval | | exact Heval |].
  - exact Hag.
  - intros x Hx. symmetry. apply Hag, Hx.
Qed.

(** The argument-list form of [eval_cong]. *)
Theorem evals_cong :
  forall Σ A (V1 V2 : valuation A) σs ts vs,
    (forall x t, t ∈ ts -> x ∈ fv t -> V1 !! x = V2 !! x) ->
    ⟦ ts : σs ⟧*(Σ, A, V1) ⇓ vs <-> ⟦ ts : σs ⟧*(Σ, A, V2) ⇓ vs.
Proof.
  intros Σ A V1 V2 σs ts vs Hag.
  destruct (eval_cong_mut_aux Σ A) as [_ Hevs].
  split; intros Heval; eapply Hevs; [exact Heval | | exact Heval |].
  - exact Hag.
  - intros x t Ht Hx. symmetry. eapply Hag; eassumption.
Qed.

(** A closed term evaluates the same way under any valuation. *)
Corollary eval_closed_cong :
  forall Σ A (V1 V2 : valuation A) σ t v,
    closed t ->
    ⟦ t : σ ⟧(Σ, A, V1) ⇓ v ->
    ⟦ t : σ ⟧(Σ, A, V2) ⇓ v.
Proof.
  intros Σ A V1 V2 σ t v Hclosed Heval.
  apply (eval_cong Σ A V1 V2); [|exact Heval].
  intros x Hx. unfold closed in Hclosed. rewrite Hclosed in Hx. set_solver.
Qed.

(** ** Weakening *)

(** Extending the valuation at binders [xs] disjoint from [fv t] preserves
    evaluation. *)
Corollary eval_weaken :
  forall Σ A xs σs (V : valuation A) σ t v
         (vs : hlist A.(domain) σs),
    (list_to_set xs : gset var) ## fv t ->
    ⟦ t : σ ⟧(Σ, A, V) ⇓ v ->
    ⟦ t : σ ⟧(Σ, A, list_to_map (zip xs (hlist_to_list vs)) ∪ V) ⇓ v.
Proof.
  intros Σ A xs σs V σ t v vs Hfresh Hev.
  apply (eval_cong Σ A V); [|exact Hev].
  intros z Hz. symmetry. apply lookup_union_r, lookup_list_to_map_zip_None.
  rewrite <- (elem_of_list_to_set (C:=gset var)). set_solver.
Qed.

Corollary eval_weaken1 :
  forall Σ A (V : valuation A) σ t v (x : var) (σ' : sort)
         (w : A.(domain) σ'),
    x ∉ fv t ->
    ⟦ t : σ ⟧(Σ, A, V) ⇓ v ->
    ⟦ t : σ ⟧(Σ, A, <[ x := existT σ' w ]> V) ⇓ v.
Proof.
  intros Σ A V σ t v x σ' w Hfv Heval.
  apply (eval_cong Σ A V); [|exact Heval].
  intros z Hz. rewrite lookup_insert_ne; [reflexivity|]. intros ->. contradiction.
Qed.

(** ** Strengthening *)

(** Removing binders [xs] disjoint from [fv t] from the valuation preserves
    evaluation. *)
Corollary eval_strengthen :
  forall Σ A xs σs (V : valuation A) σ t v
         (vs : hlist A.(domain) σs),
    (list_to_set xs : gset var) ## fv t ->
    ⟦ t : σ ⟧(Σ, A, list_to_map (zip xs (hlist_to_list vs)) ∪ V) ⇓ v ->
    ⟦ t : σ ⟧(Σ, A, V) ⇓ v.
Proof.
  intros Σ A xs σs V σ t v vs Hfresh Hev.
  apply (eval_cong Σ A (list_to_map (zip xs (hlist_to_list vs)) ∪ V));
    [|exact Hev].
  intros z Hz. apply lookup_union_r, lookup_list_to_map_zip_None.
  rewrite <- (elem_of_list_to_set (C:=gset var)). set_solver.
Qed.

Corollary eval_strengthen1 :
  forall Σ A (V : valuation A) σ t v (x : var) (σ' : sort)
         (w : A.(domain) σ'),
    x ∉ fv t ->
    ⟦ t : σ ⟧(Σ, A, <[ x := existT σ' w ]> V) ⇓ v ->
    ⟦ t : σ ⟧(Σ, A, V) ⇓ v.
Proof.
  intros Σ A V σ t v x σ' w Hfv Heval.
  apply (eval_cong Σ A (<[ x := existT σ' w ]> V)); [|exact Heval].
  intros z Hz. rewrite lookup_insert_ne; [reflexivity|]. intros ->. contradiction.
Qed.

(** ** Across Signatures That Agree Except on Sorts *)

(** Evaluation reads a signature only for its ranks and its selectors, so it
    moves to any signature agreeing with it except on variable sorts
    ([signatures_agree_except_sorts]); in particular, between a signature and
    one with its variable sorts replaced. *)

(** The mutual induction behind [eval_cong_signature]. *)
Local Lemma eval_cong_signature_mut_aux :
  forall Σ1 A,
  (forall (V : valuation A) σ t v
     (_ : ⟦ t : σ ⟧(Σ1, A, V) ⇓ v),
   forall Σ2, signatures_agree_except_sorts Σ1 Σ2 ->
     ⟦ t : σ ⟧(Σ2, A, V) ⇓ v)
  /\
  (forall (V : valuation A) σs ts vs
     (_ : ⟦ ts : σs ⟧*(Σ1, A, V) ⇓ vs),
   forall Σ2, signatures_agree_except_sorts Σ1 Σ2 ->
     ⟦ ts : σs ⟧*(Σ2, A, V) ⇓ vs).
Proof.
  intros Σ1 A.
  apply eval_combined_ind.
  - (* E_TFVar *)
    intros V x σ v Hx Σ2 _. apply E_TFVar. exact Hx.
  - (* E_TApp *)
    intros V f σopt ts σs σ vs v Hts IHts Hopt Hrank F Heq Σ2 Hsym.
    eapply E_TApp; [exact (IHts Σ2 Hsym) | exact Hopt | | exact Heq].
    exact (monomorphic_rank_signatures_agree_except_sorts _ _ _ _ _ Hsym Hrank).
  - (* E_TExists_true *)
    intros L V σ' t v' Hbody IHbody Σ2 Hsym.
    apply E_TExists_true with (L := L) (v' := v').
    intros y Hy. exact (IHbody y Hy Σ2 Hsym).
  - (* E_TExists_false *)
    intros L V σ' t Hbody IHbody Σ2 Hsym.
    apply E_TExists_false with (L := L).
    intros y Hy w. exact (IHbody y Hy w Σ2 Hsym).
  - (* E_TForall_true *)
    intros L V σ' t Hbody IHbody Σ2 Hsym.
    apply E_TForall_true with (L := L).
    intros y Hy w. exact (IHbody y Hy w Σ2 Hsym).
  - (* E_TForall_false *)
    intros L V σ' t v' Hbody IHbody Σ2 Hsym.
    apply E_TForall_false with (L := L) (v' := v').
    intros y Hy. exact (IHbody y Hy Σ2 Hsym).
  - (* E_TLambda *)
    intros L V σ1 t σ2 f Hbody IHbody Σ2 Hsym.
    apply E_TLambda with (L := L).
    intros y Hy. simpl. intros w. exact (IHbody y Hy w Σ2 Hsym).
  - (* E_TLet *)
    intros L V σs ts σ t vs v Hts IHts Hbody IHbody Σ2 Hsym.
    apply E_TLet with (L := L) (vs := vs); [exact (IHts Σ2 Hsym) |].
    intros xs Hndxs Hlen Hxs. exact (IHbody xs Hndxs Hlen Hxs Σ2 Hsym).
  - (* E_TMatch_PVar *)
    intros V σ t t' pts v Hlet IHlet Σ2 Hsym.
    apply E_TMatch_PVar. exact (IHlet Σ2 Hsym).
  - (* E_TMatch_PApp_true *)
    intros V σ δ t c n t' pts v' v σs Hrank Hscrut IHscrut Hrange gs Hlet IHlet
      Σ2 Hsym.
    eapply E_TMatch_PApp_true;
      [ exact (monomorphic_rank_signatures_agree_except_sorts _ _ _ _ _
                 Hsym Hrank)
      | exact (IHscrut Σ2 Hsym) | exact Hrange |].
    subst gs. rewrite <-
      (signatures_agree_except_sorts_selectors_for_constructor _ _ Hsym).
    exact (IHlet Σ2 Hsym).
  - (* E_TMatch_PApp_false *)
    intros V σ δ t c n t' pts v' v σs Hrank Hscrut IHscrut Hrange Hrest IHrest
      Σ2 Hsym.
    eapply E_TMatch_PApp_false;
      [ exact (monomorphic_rank_signatures_agree_except_sorts _ _ _ _ _
                 Hsym Hrank)
      | exact (IHscrut Σ2 Hsym) | exact Hrange | exact (IHrest Σ2 Hsym) ].
  - (* ES_nil *)
    intros V Σ2 _. apply ES_nil.
  - (* ES_cons *)
    intros V σ σs t ts v vs Ht IHt Hts IHts Σ2 Hsym.
    apply ES_cons; [exact (IHt Σ2 Hsym) | exact (IHts Σ2 Hsym)].
Qed.

Theorem eval_cong_signature :
  forall Σ1 Σ2 A (V : valuation A) σ t (v : A.(domain) σ),
    signatures_agree_except_sorts Σ1 Σ2 ->
    ⟦ t : σ ⟧(Σ1, A, V) ⇓ v <-> ⟦ t : σ ⟧(Σ2, A, V) ⇓ v.
Proof.
  intros Σ1 Σ2 A V σ t v Hsym.
  pose proof (signatures_agree_except_sorts_sym _ _ Hsym) as Hsym'.
  split; intros Hev.
  - exact (proj1 (eval_cong_signature_mut_aux Σ1 A) V σ t v Hev Σ2 Hsym).
  - exact (proj1 (eval_cong_signature_mut_aux Σ2 A) V σ t v Hev Σ1 Hsym').
Qed.

(** The argument-list form of [eval_cong_signature]. *)
Theorem evals_cong_signature :
  forall Σ1 Σ2 A (V : valuation A) σs ts (vs : hlist A.(domain) σs),
    signatures_agree_except_sorts Σ1 Σ2 ->
    ⟦ ts : σs ⟧*(Σ1, A, V) ⇓ vs <-> ⟦ ts : σs ⟧*(Σ2, A, V) ⇓ vs.
Proof.
  intros Σ1 Σ2 A V σs ts vs Hsym.
  pose proof (signatures_agree_except_sorts_sym _ _ Hsym) as Hsym'.
  split; intros Hev.
  - exact (proj2 (eval_cong_signature_mut_aux Σ1 A) V σs ts vs Hev Σ2 Hsym).
  - exact (proj2 (eval_cong_signature_mut_aux Σ2 A) V σs ts vs Hev Σ1 Hsym').
Qed.

(** * Sort Uniqueness *)

(** An evaluation determines the sort it happens at, given a well-sortedness
    derivation for the same term.  This is needed before value determinism can
    even be stated for [TApp]: [monomorphic_rank] is not output-unique in
    general, so two evaluations of one application may pick different argument
    sort lists, and only the sorting derivation says they must agree. *)

(** Any sort list over which a selector-application body [evals]s must be
    the constructor's parameter sorts.  The [Some σ_i] annotations each
    application carries are what force this; README.md, under _Deterministic
    evaluation of match expressions_, says why selector ranks alone would
    not. *)
Lemma evals_selector_sorts :
  forall Σ A (V : valuation A) gs σs t σs_let vs,
    length gs = length σs ->
    ⟦ map (fun '(g, σ_i) => TApp g (Some σ_i) [t]) (zip gs σs)
      : σs_let ⟧*(Σ, A, V) ⇓ vs ->
    σs_let = σs.
Proof.
  intros Σ A V gs.
  induction gs as [|g gs' IH]; intros σs t σs_let vs Hlen Hargs.
  - destruct σs as [|σ0 σs']; [|simpl in Hlen; discriminate].
    simpl in Hargs. apply evals_nil_sorts in Hargs. exact Hargs.
  - destruct σs as [|σ0 σs']; [simpl in Hlen; discriminate|].
    simpl in Hargs.
    apply evals_cons_sigT in Hargs.
    destruct Hargs as (σ & σstl & v & vstl & Hhd & Htl & Heq).
    apply (f_equal (@projT1 _ _)) in Heq. simpl in Heq. subst σs_let.
    (* head: [eval ... σ (TApp g (Some σ0) [t]) v], so σ = σ0 *)
    apply eval_TApp_inv in Hhd.
    destruct Hhd as (σsa & vsa & _ & Hopt & _ & _).
    inversion Hopt; subst.
    f_equal.
    simpl in Hlen. injection Hlen as Hlen'.
    apply (IH σs' t σstl _ Hlen' Htl).
Qed.

(** Sort uniqueness for a [TMatch].

    The [PVar] arm binds a single variable at the scrutinee sort rather than a
    list at the constructor's parameter sorts, so it has a premise of its own;
    [eval_sort_TMatch_PApp] discharges that premise for a match with no
    [PVar] arm.

    [c ∈ constructors] must be supplied by the caller, who derives it from the
    match's coverage premises with
    [match_pattern_constructor_in_constructors]. *)
Lemma eval_sort_TMatch_PVar :
  forall Σ A S (V : valuation A) (L : gset var) pts t δ σ σ_ev
         (v : A.(domain) σ_ev),
    adt Σ δ ->
    valuation_well_sorted S V ->
    (forall c n t0 σs xs, (PApp c n, t0) ∈ pts ->
        monomorphic_rank Σ c σs δ -> NoDup xs -> length xs = n ->
        list_to_set xs ## L ->
        forall (σ' : sort) (v0 : A.(domain) σ') (V0 : valuation A),
        valuation_well_sorted (list_to_map (zip xs σs) ∪ S) V0 ->
        ⟦ term_open 0 (map TFVar xs) t0 : σ' ⟧(Σ, A, V0) ⇓ v0 -> σ' = σ) ->
    (forall x t', x ∉ L -> (PVar, t') ∈ pts ->
        forall (σ' : sort) (v0 : A.(domain) σ') (V0 : valuation A),
        valuation_well_sorted (<[x:=δ]> S) V0 ->
        ⟦ term_open 0 [TFVar x] t' : σ' ⟧(Σ, A, V0) ⇓ v0 -> σ' = σ) ->
    (forall c n t0, (PApp c n, t0) ∈ pts ->
        exists σs, monomorphic_rank Σ c σs δ /\ length σs = n) ->
    (forall c n t0, (PApp c n, t0) ∈ pts -> c ∈ Σ.(constructors)) ->
    (forall (σ' : sort) (v0 : A.(domain) σ'),
        ⟦ t : σ' ⟧(Σ, A, V) ⇓ v0 -> σ' = δ) ->
    ⟦ TMatch t pts : σ_ev ⟧(Σ, A, V) ⇓ v -> σ_ev = σ.
Proof.
  intros Σ A S V L pts t δ σ σ_ev v Hadt HV.
  revert σ_ev v.
  induction pts as [|[p t'] pts' IH];
    intros σ_ev v Hbody HbodyV Hex Hcon Hscrut Hev.
  - apply eval_TMatch_nil_inv in Hev. destruct Hev.
  - destruct p as [|c n].
    + (* PVar: body is [TLet [t] t'] *)
      apply eval_TMatch_PVar_inv, eval_TLet_inv in Hev.
      destruct Hev as (L0 & σsL & vsL & Hargs & Hbodylet).
      (* tsL = [t]; so σsL = [σ_t] where σ_t = result sort of t = δ *)
      apply evals_cons_sigT in Hargs.
      destruct Hargs as (σ_t & σstl & v_t & vstl & Hevt & Htl & Heq).
      apply evals_nil_sorts in Htl. subst σstl.
      assert (Hδt : σ_t = δ) by (apply (Hscrut σ_t v_t); exact Hevt).
      subst σ_t.
      apply (f_equal (@projT1 _ _)) in Heq as Hidx. simpl in Hidx. subst σsL.
      apply (Eqdep_dec.inj_pair2_eq_dec _ (fun x y => decide (x = y))) in Heq.
      subst vsL. hlist_nil vstl.
      (* instantiate body at a single fresh var x *)
      pose (x := fresh_string_of_set "" (L ∪ L0)).
      assert (Hxf : x ∉ (L ∪ L0)) by (apply fresh_string_of_set_fresh).
      apply not_elem_of_union in Hxf as [HxL HxL0].
      assert (Hdisj : list_to_set [x] ## L0)
        by (rewrite list_to_set_singleton; by apply disjoint_singleton_l).
      specialize (Hbodylet [x] (NoDup_singleton x) eq_refl Hdisj).
      cbv zeta in Hbodylet. cbn [hlist_to_list map] in Hbodylet.
      rewrite list_to_map_zip_singleton_union in Hbodylet.
      eapply (HbodyV x t' HxL); [apply list_elem_of_here | | exact Hbodylet].
      apply valuation_well_sorted_insert. exact HV.
    + (* PApp c n *)
      apply eval_TMatch_PApp_inv in Hev.
      destruct Hev as
        (δ0 & σs & v' & Hrank & Hevt & [[Hrange Hlet] | [Hnorange Hrest]]).
      * (* E_TMatch_PApp_true *)
        assert (Hδ : δ0 = δ) by (apply (Hscrut δ0 v'); exact Hevt).
        subst δ0.
        assert (Hcon_c : c ∈ Σ.(constructors)) by (apply (Hcon c n t'); left).
        assert (Hgslen : length (Σ.(selectors_for_constructor) c) = length σs)
          by (eapply monomorphic_rank_selector_length; eauto).
        destruct (Hex c n t') as (σs_ex & Hrank_ex & Hlen_ex); [left|].
        (* pin [n = length σs] via constructor-rank functionality.  Phrased
           with the variable on the left so the body-[TLet] inversion's
           [subst] rewrites [n] to [length σs] throughout — in particular in
           [Hbody_c]'s expected binder-count premise. *)
        assert (Hlen_n : n = length σs).
        { rewrite <- Hlen_ex. symmetry.
          eapply monomorphic_rank_constructor_length; eauto. }
        (* the body-sort hypothesis specialised at this branch, before
           [subst] can rename [t']. *)
        pose proof (Hbody c n t' σs) as Hbody_c.
        subst n.
        (* invert the body TLet *)
        apply eval_TLet_inv in Hlet.
        destruct Hlet as (L0 & σs0 & vs & Hargs & Hbodylet).
        (* the selector list pins σsL = σs0 *)
        assert (HσsL : σs0 = σs)
          by (eapply evals_selector_sorts; [exact Hgslen | exact Hargs]).
        subst σs0.
        (* instantiate body at fresh NoDup xs of length [length σs] *)
        pose (xs := fresh_strings_of_set "" (length σs) (L ∪ L0)).
        assert (Hndxs : NoDup xs) by (apply NoDup_fresh_strings_of_set).
        assert (Hlenxs : length xs = length σs)
          by (apply length_fresh_strings_of_set).
        pose proof (evals_length _ _ _ _ _ _ Hargs) as Hlents0.
        assert (Hdisj : list_to_set xs ## (L ∪ L0))
          by (apply fresh_strings_of_set_fresh; set_solver).
        apply disjoint_union_r in Hdisj as [HdisjL HdisjL0].
        rewrite <- Hlenxs in Hlents0.
        specialize (Hbodylet xs Hndxs Hlents0 HdisjL0).
        cbv zeta in Hbodylet.
        assert (Hlen_xs_ex : length xs = length σs_ex) by congruence.
        apply (Hbody_c xs (list_elem_of_here _ _) Hrank Hndxs Hlen_xs_ex HdisjL
                 _ _ _ (valuation_well_sorted_union_lookup_list_to_map
                          _ _ _ _ _ vs HV)
                 Hbodylet).
      * (* E_TMatch_PApp_false: recurse on pts' *)
        apply (IH σ_ev v).
        -- intros c1 n1 t1 σs1 xs1 Hin1.
           apply (Hbody c1 n1 t1 σs1 xs1). right. exact Hin1.
        -- intros x1 t1 Hx1 Hin1. apply (HbodyV x1 t1 Hx1). right. exact Hin1.
        -- intros c1 n1 t1 Hin1. apply (Hex c1 n1 t1). right. exact Hin1.
        -- intros c1 n1 t1 Hin1. apply (Hcon c1 n1 t1). right. exact Hin1.
        -- intros σ'1 v1 Hev1. apply (Hscrut σ'1 v1). exact Hev1.
        -- exact Hrest.
Qed.

(** The [S_TMatch_PApp] case of [eval_sort_TMatch_PVar]: with no [PVar]
    arm, that lemma's default-arm premise holds vacuously. *)
Corollary eval_sort_TMatch_PApp :
  forall Σ A S (V : valuation A) (L : gset var) pts t δ σ σ_ev
         (v : A.(domain) σ_ev),
    adt Σ δ ->
    valuation_well_sorted S V ->
    (forall c n t0 σs xs, (PApp c n, t0) ∈ pts ->
        monomorphic_rank Σ c σs δ -> NoDup xs -> length xs = n ->
        list_to_set xs ## L ->
        forall (σ' : sort) (v0 : A.(domain) σ') (V0 : valuation A),
        valuation_well_sorted (list_to_map (zip xs σs) ∪ S) V0 ->
        ⟦ term_open 0 (map TFVar xs) t0 : σ' ⟧(Σ, A, V0) ⇓ v0 -> σ' = σ) ->
    (forall c n t0, (PApp c n, t0) ∈ pts ->
        exists σs, monomorphic_rank Σ c σs δ /\ length σs = n) ->
    (forall c n t0, (PApp c n, t0) ∈ pts -> c ∈ Σ.(constructors)) ->
    (forall (σ' : sort) (v0 : A.(domain) σ'),
        ⟦ t : σ' ⟧(Σ, A, V) ⇓ v0 -> σ' = δ) ->
    (forall t', (PVar, t') ∉ pts) ->
    ⟦ TMatch t pts : σ_ev ⟧(Σ, A, V) ⇓ v -> σ_ev = σ.
Proof.
  intros Σ A S V L pts t δ σ σ_ev v Hadt HV Hbody Hex Hcon Hscrut HnoPVar Hev.
  eapply (eval_sort_TMatch_PVar Σ A S V L pts t δ σ σ_ev v);
    try eassumption.
  intros x t' Hx Hin. exfalso. exact (HnoPVar t' Hin).
Qed.

(** The sort list an [evals] chose is pinned by the sorts of its terms.
    The premise to supply is elementwise sort uniqueness for the terms of [ts];
    [eval_sort_of_well_sorted] is what discharges it from [term_has_sort]. *)
Lemma evals_sorts_eq :
  forall Σ A S (V : valuation A) ts σs σsX vsX,
    valuation_well_sorted S V ->
    length σs = length ts ->
    (forall i t_i σ_i, ts !! i = Some t_i -> σs !! i = Some σ_i ->
        forall σ' (w : A.(domain) σ') (V' : valuation A),
          valuation_well_sorted S V' ->
          ⟦ t_i : σ' ⟧(Σ, A, V') ⇓ w -> σ' = σ_i) ->
    ⟦ ts : σsX ⟧*(Σ, A, V) ⇓ vsX ->
    σsX = σs.
Proof.
  intros Σ A S V ts σs σsX vsX HV Hlen Hsorts HX.
  assert (HlenX : length σsX = length ts) by (eapply evals_length; eauto).
  apply list_eq. intros i.
  destruct (σsX !! i) as [σXi|] eqn:HXi;
  destruct (σs !! i) as [σi|] eqn:Hsi.
  - f_equal. destruct (ts !! i) as [t_i|] eqn:Hti.
    + destruct (evals_nth _ _ _ _ _ _ HX i t_i σXi Hti HXi) as [w Hw].
      apply (Hsorts i t_i σi Hti Hsi σXi w V HV Hw).
    + apply lookup_lt_Some in HXi. rewrite HlenX in HXi.
      apply lookup_ge_None in Hti. lia.
  - apply lookup_lt_Some in HXi. apply lookup_ge_None in Hsi.
    rewrite HlenX, <- Hlen in HXi. lia.
  - apply lookup_lt_Some in Hsi. apply lookup_ge_None in HXi.
    rewrite Hlen, <- HlenX in Hsi. lia.
  - reflexivity.
Qed.

(** A well-sorted term evaluates, under a valuation for its signature's
    variables, only at the sort it is well-sorted at.

    The result the whole determinism section rests on, and the reason
    [eval_deterministic] takes a sorting premise: without it the [TApp] case
    cannot pin the argument sorts that [E_TApp] chose existentially.  The
    valuation premise ties the sort a variable is read at to the sort the
    signature declares.  A binder case moves the body's evaluation to the
    extended signature its body is sorted under ([eval_cong_signature]). *)
Theorem eval_sort_of_well_sorted :
  forall Σ A (V : valuation A) t σ σ' (v : A.(domain) σ'),
    Σ ⊢ t : σ ->
    valuation_well_sorted Σ.(sorts) V ->
    ⟦ t : σ' ⟧(Σ, A, V) ⇓ v ->
    σ' = σ.
Proof.
  intros Σ A V t σ σ' v Hsort. revert σ' v V.
  induction Hsort; intros σ_ev v V HV Hev.
  - (* S_TFVar *)
    apply eval_TFVar_inv in Hev.
    destruct (valuation_well_sorted_lookup _ _ _ _ _ HV H) as [w Hw].
    rewrite Hw in Hev. injection Hev as Hσ _. symmetry. exact Hσ.
  - (* S_TApp *)
    apply eval_TApp_inv in Hev as (σs0 & vs0 & Hargs & _ & Hrank0 & _).
    symmetry. apply (H0 σ_ev).
    assert (Hσs_eq : σs0 = σs)
      by (eapply evals_sorts_eq; [exact HV | exact H1 | exact H3 | exact Hargs]).
    subst σs0. exact Hrank0.
  - (* S_TApp_annotated *)
    apply eval_TApp_inv in Hev as (σs0 & vs0 & _ & Hopt & _ & _).
    inversion Hopt; subst. reflexivity.
  - (* S_TLambda *)
    apply eval_TLambda_inv in Hev as (L0 & σ2' & g & Heq & Hbody).
    apply (f_equal (@projT1 _ _)) in Heq. simpl in Heq. subst σ_ev.
    f_equal.
    pose (x := fresh_string_of_set "" (L ∪ L0)).
    assert (Hxf : x ∉ (L ∪ L0)) by (apply fresh_string_of_set_fresh).
    apply not_elem_of_union in Hxf as [HxL HxL0].
    specialize (Hbody x HxL0 (domain_witness A σ1)).
    apply (eval_cong_signature (<[x := σ1]> Σ)) in Hbody;
      [| apply signatures_agree_except_sorts_insert].
    apply (H2 x HxL _ _ _ (valuation_well_sorted_insert _ _ _ _ _ _ HV) Hbody).
  - (* S_TExists *)
    apply eval_TExists_inv in Hev as (L0 & [(v' & Heq & _) | (Heq & _)]);
      apply (f_equal (@projT1 _ _)) in Heq; exact Heq.
  - (* S_TForall *)
    apply eval_TForall_inv in Hev as (L0 & [(Heq & _) | (v' & Heq & _)]);
      apply (f_equal (@projT1 _ _)) in Heq; exact Heq.
  - (* S_TLet *)
    apply eval_TLet_inv in Hev as (L0 & σs0 & vs0 & Hargs & Hbody).
    assert (Hσs0 : σs0 = σs)
      by (eapply evals_sorts_eq; [exact HV | exact H | exact H1 | exact Hargs]).
    subst σs0.
    pose (xs := fresh_strings_of_set "" (length ts) (L ∪ L0)).
    assert (Hndxs : NoDup xs) by (apply NoDup_fresh_strings_of_set).
    assert (Hlenxs : length xs = length ts) by (apply length_fresh_strings_of_set).
    assert (Hdisj : list_to_set xs ## (L ∪ L0))
      by (apply fresh_strings_of_set_fresh; set_solver).
    apply disjoint_union_r in Hdisj as [HdisjL HdisjL0].
    specialize (Hbody xs Hndxs Hlenxs HdisjL0).
    apply (eval_cong_signature (list_to_map (zip xs σs) ⊍ Σ)) in Hbody;
      [| apply signatures_agree_except_sorts_add_sorts].
    apply (H3 xs Hndxs Hlenxs HdisjL _ _ _
             (valuation_well_sorted_union_lookup_list_to_map _ _ _ _ _ vs0 HV)
             Hbody).
  - (* S_TMatch_PApp *)
    assert (HnoPVar : forall t', (PVar, t') ∉ pts).
    { intros t' Hin.
      apply (exact_coverage_no_PVar ps); [unfold cs in H2; exact H2|].
      apply list_elem_of_fmap. exists (PVar, t'). split; [reflexivity| exact Hin]. }
    assert (Hcon : forall c n t0, (PApp c n, t0) ∈ pts -> c ∈ Σ.(constructors)).
    { intros c n t0 Hin.
      eapply (match_pattern_constructor_in_constructors Σ pts δ s c n t0);
        eauto.
      rewrite <- H1. done. }
    assert (Hscrut : forall σ' (v0 : A.(domain) σ'),
                ⟦ t : σ' ⟧(Σ, A, V) ⇓ v0 -> σ' = δ)
      by (intros σ' v0 Hev'; eapply IHHsort; eauto).
    eapply (eval_sort_TMatch_PApp Σ A Σ.(sorts) V L pts t δ σ σ_ev v);
      [ exact H | exact HV | | exact H5 | exact Hcon | exact Hscrut | exact HnoPVar
      | exact Hev ].
    (* an arm's body is sorted under the signature extended by its binders *)
    intros c n t0 σs xs Hin Hrank Hnd Hlen Hdisj σ' v0 V0 HV0 Hev0.
    apply (eval_cong_signature (list_to_map (zip xs σs) ⊍ Σ)) in Hev0;
      [| apply signatures_agree_except_sorts_add_sorts].
    exact (H4 c n t0 σs xs Hin Hrank Hnd Hlen Hdisj σ' v0 V0 HV0 Hev0).
  - (* S_TMatch_PVar *)
    assert (Hcon : forall c n t0, (PApp c n, t0) ∈ pts -> c ∈ Σ.(constructors)).
    { intros c n t0 Hin.
      eapply (match_pattern_constructor_in_constructors Σ pts δ s c n t0);
        eauto. }
    assert (Hscrut : forall σ' (v0 : A.(domain) σ'),
                ⟦ t : σ' ⟧(Σ, A, V) ⇓ v0 -> σ' = δ)
      by (intros σ' v0 Hev'; eapply IHHsort; eauto).
    eapply (eval_sort_TMatch_PVar Σ A Σ.(sorts) V L pts t δ σ σ_ev v);
      [ exact H | exact HV | | | exact H7 | exact Hcon | exact Hscrut | exact Hev ].
    (* each arm's body is sorted under the signature extended by its binders *)
    + intros c n t0 σs xs Hin Hrank Hnd Hlen Hdisj σ' v0 V0 HV0 Hev0.
      apply (eval_cong_signature (list_to_map (zip xs σs) ⊍ Σ)) in Hev0;
        [| apply signatures_agree_except_sorts_add_sorts].
      exact (H4 c n t0 σs xs Hin Hrank Hnd Hlen Hdisj σ' v0 V0 HV0 Hev0).
    + intros x t' Hx Hin σ' v0 V0 HV0 Hev0.
      apply (eval_cong_signature (<[x := δ]> Σ)) in Hev0;
        [| apply signatures_agree_except_sorts_insert].
      exact (H6 x t' Hx Hin σ' v0 V0 HV0 Hev0).
Qed.

(** * Determinism *)

(** [eval] is a partial function of the signature, structure, valuation, sort
    and term, on well-sorted terms under a valuation for their signature's
    variables.  [eval_deterministic] is the result; the lemmas above it are one
    term former each, and take their case's inductive hypotheses as premises,
    so they are not facts worth using on their own. *)

(** Value determinism for argument lists at a fixed sort list, given
    determinism for each argument.  Both hlists live over the same [σs], so the
    conclusion is a plain equality rather than a heterogeneous one. *)
Lemma evals_vals_eq :
  forall Σ A (V : valuation A) ts σs
         (vs1 vs2 : hlist A.(domain) σs),
    length σs = length ts ->
    (forall i t_i σ_i, ts !! i = Some t_i -> σs !! i = Some σ_i ->
        forall (w1 w2 : A.(domain) σ_i),
          ⟦ t_i : σ_i ⟧(Σ, A, V) ⇓ w1 -> ⟦ t_i : σ_i ⟧(Σ, A, V) ⇓ w2 -> w1 = w2) ->
    ⟦ ts : σs ⟧*(Σ, A, V) ⇓ vs1 ->
    ⟦ ts : σs ⟧*(Σ, A, V) ⇓ vs2 ->
    vs1 = vs2.
Proof.
  intros Σ A V ts. induction ts as [|t0 ts' IHts];
    intros σs vs1 vs2 Hlen Hvd Hargs1 Hargs2.
  - apply evals_nil_sorts in Hargs1. subst σs.
    hlist_nil vs1. hlist_nil vs2. reflexivity.
  - pose proof Hargs1 as Hshape.
    apply evals_cons_sigT in Hshape.
    destruct Hshape as (σ & σs' & ? & ? & _ & _ & Hidx).
    apply (f_equal (@projT1 _ _)) in Hidx. simpl in Hidx. subst σs.
    apply evals_cons_inv in Hargs1, Hargs2.
    destruct Hargs1 as (w1 & vt1 & -> & Hhd1 & Htl1).
    destruct Hargs2 as (w2 & vt2 & -> & Hhd2 & Htl2).
    assert (Hhd : w1 = w2)
      by (apply (Hvd 0 t0 σ eq_refl eq_refl _ _ Hhd1 Hhd2)).
    subst w2. f_equal.
    simpl in Hlen. injection Hlen as Hlen'.
    eapply IHts; [ exact Hlen' | | exact Htl1 | exact Htl2 ].
    intros i t_i σ_i Hti Hσi. apply (Hvd (S i) t_i σ_i Hti Hσi).
Qed.

(** A single selector application is deterministic once its scrutinee is: both
    evaluations pick argument sort lists that the inner [eval] pins to
    [[δ_t]], the scrutinee values agree by hypothesis, and [interp] is a
    function. *)
Lemma eval_deterministic_selector_app_arm :
  forall Σ A (V : valuation A) g σ_i t δ_t
         (w1 w2 : A.(domain) σ_i),
    (forall (u1 u2 : A.(domain) δ_t),
        ⟦ t : δ_t ⟧(Σ, A, V) ⇓ u1 -> ⟦ t : δ_t ⟧(Σ, A, V) ⇓ u2 -> u1 = u2) ->
    (forall (σ' : sort) (u : A.(domain) σ'),
        ⟦ t : σ' ⟧(Σ, A, V) ⇓ u -> σ' = δ_t) ->
    ⟦ TApp g (Some σ_i) [t] : σ_i ⟧(Σ, A, V) ⇓ w1 ->
    ⟦ TApp g (Some σ_i) [t] : σ_i ⟧(Σ, A, V) ⇓ w2 ->
    w1 = w2.
Proof.
  intros Σ A V g σ_i t δ_t w1 w2 Htdet Htsort Hev1 Hev2.
  apply eval_TApp_inv in Hev1, Hev2.
  destruct Hev1 as (σsa & vsa & Hargsa & _ & _ & HFa).
  destruct Hev2 as (σsb & vsb & Hargsb & _ & _ & HFb).
  (* both bound-sort lists [σsa], [σsb] equal [[δ_t]] *)
  assert (Hsorts : forall σsX vsX, ⟦ [t] : σsX ⟧*(Σ, A, V) ⇓ vsX ->
                     σsX = [δ_t]).
  { intros σsX vsX HX.
    apply evals_cons_sigT in HX.
    destruct HX as (σX & σsX' & vX & vsX' & HetX & HtlX & Hidx).
    apply evals_nil_sorts in HtlX. subst σsX'.
    apply (f_equal (@projT1 _ _)) in Hidx. simpl in Hidx. subst σsX.
    f_equal. apply (Htsort σX vX). exact HetX. }
  pose proof (Hsorts _ _ Hargsa) as HsA.
  pose proof (Hsorts _ _ Hargsb) as HsB.
  subst σsa σsb.
  (* the two argument hlists agree (single selector arg = scrutinee) *)
  assert (Hvsab : vsa = vsb).
  { eapply (evals_vals_eq Σ A V [t] [δ_t] vsa vsb eq_refl);
      [|exact Hargsa|exact Hargsb].
    intros i t_i σ_i' Hti Hσi u1 u2 Hu1 Hu2.
    destruct i as [|i']; simpl in Hti, Hσi; [|discriminate].
    injection Hti as <-. injection Hσi as <-.
    apply (Htdet u1 u2); assumption. }
  subst vsb. rewrite <- HFa, <- HFb. reflexivity.
Qed.

(** The [TApp] case, with no result annotation.  Rank uniqueness is a premise
    here: nothing in an unannotated application pins the result sort. *)
Lemma eval_deterministic_TApp_arm :
  forall Σ A (V : valuation A) f ts σs σ (v1 v2 : A.(domain) σ),
    valuation_well_sorted Σ.(sorts) V ->
    monomorphic_rank Σ f σs σ ->
    (forall σ', monomorphic_rank Σ f σs σ' -> σ = σ') ->
    length σs = length ts ->
    (forall i t_i σ_i, ts !! i = Some t_i -> σs !! i = Some σ_i ->
        Σ ⊢ t_i : σ_i) ->
    (forall i t_i σ_i, ts !! i = Some t_i -> σs !! i = Some σ_i ->
        forall (V0 : valuation A) (w1 w2 : A.(domain) σ_i),
          valuation_well_sorted Σ.(sorts) V0 ->
          ⟦ t_i : σ_i ⟧(Σ, A, V0) ⇓ w1 -> ⟦ t_i : σ_i ⟧(Σ, A, V0) ⇓ w2 -> w1 = w2) ->
    ⟦ TApp f None ts : σ ⟧(Σ, A, V) ⇓ v1 ->
    ⟦ TApp f None ts : σ ⟧(Σ, A, V) ⇓ v2 ->
    v1 = v2.
Proof.
  intros Σ A V f ts σs σ v1 v2 HV Hrank Hrankfun Hlen Hws Hvd Hev1 Hev2.
  apply eval_TApp_inv in Hev1, Hev2.
  destruct Hev1 as (σs1 & vs1 & Hargs1 & _ & _ & HF1).
  destruct Hev2 as (σs2 & vs2 & Hargs2 & _ & _ & HF2).
  assert (Hσseq : forall σsX vsX, ⟦ ts : σsX ⟧*(Σ, A, V) ⇓ vsX -> σsX = σs).
  { intros σsX vsX HX.
    eapply evals_sorts_eq; [exact HV | exact Hlen | | exact HX].
    intros i t_i σ_i Hti Hsi σ' w V' HV' Hw.
    exact (eval_sort_of_well_sorted _ _ _ _ _ _ _ (Hws i t_i σ_i Hti Hsi) HV' Hw). }
  pose proof (Hσseq _ _ Hargs1) as Hs1. pose proof (Hσseq _ _ Hargs2) as Hs2.
  subst σs1 σs2. rewrite <- HF1, <- HF2. f_equal.
  apply (evals_vals_eq Σ A V ts σs vs1 vs2 Hlen); [|exact Hargs1|exact Hargs2].
  intros i t_i σ_i Hti Hσi w1 w2. exact (Hvd i t_i σ_i Hti Hσi V w1 w2 HV).
Qed.

(** The [TApp] case with a result annotation [Some σ].  Same argument, without
    the rank-uniqueness premise: the annotation pins the result sort. *)
Lemma eval_deterministic_TApp_arm_typed :
  forall Σ A (V : valuation A) f ts σs σ (v1 v2 : A.(domain) σ),
    valuation_well_sorted Σ.(sorts) V ->
    monomorphic_rank Σ f σs σ ->
    length σs = length ts ->
    (forall i t_i σ_i, ts !! i = Some t_i -> σs !! i = Some σ_i ->
        Σ ⊢ t_i : σ_i) ->
    (forall i t_i σ_i, ts !! i = Some t_i -> σs !! i = Some σ_i ->
        forall (V0 : valuation A) (w1 w2 : A.(domain) σ_i),
          valuation_well_sorted Σ.(sorts) V0 ->
          ⟦ t_i : σ_i ⟧(Σ, A, V0) ⇓ w1 -> ⟦ t_i : σ_i ⟧(Σ, A, V0) ⇓ w2 -> w1 = w2) ->
    ⟦ TApp f (Some σ) ts : σ ⟧(Σ, A, V) ⇓ v1 ->
    ⟦ TApp f (Some σ) ts : σ ⟧(Σ, A, V) ⇓ v2 ->
    v1 = v2.
Proof.
  intros Σ A V f ts σs σ v1 v2 HV Hrank Hlen Hws Hvd Hev1 Hev2.
  apply eval_TApp_inv in Hev1, Hev2.
  destruct Hev1 as (σs1 & vs1 & Hargs1 & _ & _ & HF1).
  destruct Hev2 as (σs2 & vs2 & Hargs2 & _ & _ & HF2).
  assert (Hσseq : forall σsX vsX, ⟦ ts : σsX ⟧*(Σ, A, V) ⇓ vsX -> σsX = σs).
  { intros σsX vsX HX.
    eapply evals_sorts_eq; [exact HV | exact Hlen | | exact HX].
    intros i t_i σ_i Hti Hsi σ' w V' HV' Hw.
    exact (eval_sort_of_well_sorted _ _ _ _ _ _ _ (Hws i t_i σ_i Hti Hsi) HV' Hw). }
  pose proof (Hσseq _ _ Hargs1) as Hs1. pose proof (Hσseq _ _ Hargs2) as Hs2.
  subst σs1 σs2. rewrite <- HF1, <- HF2. f_equal.
  apply (evals_vals_eq Σ A V ts σs vs1 vs2 Hlen); [|exact Hargs1|exact Hargs2].
  intros i t_i σ_i Hti Hσi w1 w2. exact (Hvd i t_i σ_i Hti Hσi V w1 w2 HV).
Qed.

(** The [TLet] case.  Both evaluations bind argument hlists at [σs], since
    [eval_sort_of_well_sorted] pins both bound-sort lists; one fresh distinct
    binder list instantiates the cofinite body premise of both, and the body
    hypothesis closes the goal once the bound hlists agree. *)
Lemma eval_deterministic_TLet_arm :
  forall Σ A (V : valuation A) (L : gset var) σs ts t σ (v1 v2 : A.(domain) σ),
    valuation_well_sorted Σ.(sorts) V ->
    length σs = length ts ->
    (forall i t_i σ_i, ts !! i = Some t_i -> σs !! i = Some σ_i ->
        Σ ⊢ t_i : σ_i) ->
    (forall i t_i σ_i, ts !! i = Some t_i -> σs !! i = Some σ_i ->
        forall (V0 : valuation A) (w1 w2 : A.(domain) σ_i),
          valuation_well_sorted Σ.(sorts) V0 ->
          ⟦ t_i : σ_i ⟧(Σ, A, V0) ⇓ w1 -> ⟦ t_i : σ_i ⟧(Σ, A, V0) ⇓ w2 -> w1 = w2) ->
    (forall xs : list var, NoDup xs -> length xs = length ts ->
        list_to_set xs ## L ->
        forall (V0 : valuation A) (w1 w2 : A.(domain) σ),
          valuation_well_sorted (list_to_map (zip xs σs) ∪ Σ.(sorts)) V0 ->
          ⟦ term_open 0 (map TFVar xs) t : σ ⟧(Σ, A, V0) ⇓ w1 ->
          ⟦ term_open 0 (map TFVar xs) t : σ ⟧(Σ, A, V0) ⇓ w2 -> w1 = w2) ->
    ⟦ TLet ts t : σ ⟧(Σ, A, V) ⇓ v1 ->
    ⟦ TLet ts t : σ ⟧(Σ, A, V) ⇓ v2 ->
    v1 = v2.
Proof.
  intros Σ A V L σs ts t σ v1 v2 HV Hlen Hws Hvd Hbodydet Hev1 Hev2.
  apply eval_TLet_inv in Hev1, Hev2.
  destruct Hev1 as (L0 & σs0 & vs0 & Hargs1 & Hbody1).
  destruct Hev2 as (L1 & σs1 & vs1 & Hargs2 & Hbody2).
  assert (Hσseq : forall σsX vsX, ⟦ ts : σsX ⟧*(Σ, A, V) ⇓ vsX -> σsX = σs).
  { intros σsX vsX HX.
    eapply evals_sorts_eq; [exact HV | exact Hlen | | exact HX].
    intros i t_i σ_i Hti Hsi σ' w V' HV' Hw.
    exact (eval_sort_of_well_sorted _ _ _ _ _ _ _ (Hws i t_i σ_i Hti Hsi) HV' Hw). }
  pose proof (Hσseq _ _ Hargs1) as Hs1. pose proof (Hσseq _ _ Hargs2) as Hs2.
  subst σs0 σs1.
  (* the two bound hlists agree by [evals_vals_eq] *)
  assert (Hvseq : vs0 = vs1).
  { apply (evals_vals_eq Σ A V ts σs vs0 vs1 Hlen); [|exact Hargs1|exact Hargs2].
    intros i t_i σ_i Hti Hσi w1 w2. exact (Hvd i t_i σ_i Hti Hσi V w1 w2 HV). }
  subst vs1.
  (* pick one fresh NoDup binder list and instantiate both bodies *)
  pose (xs := fresh_strings_of_set "" (length ts) (L ∪ L0 ∪ L1)).
  assert (Hndxs : NoDup xs) by (apply NoDup_fresh_strings_of_set).
  assert (Hlenxs : length xs = length ts) by (apply length_fresh_strings_of_set).
  assert (Hdisj : list_to_set xs ## (L ∪ L0 ∪ L1))
    by (apply fresh_strings_of_set_fresh; set_solver).
  apply disjoint_union_r in Hdisj as [Hdisj HdisjL1].
  apply disjoint_union_r in Hdisj as [HdisjL HdisjL0].
  specialize (Hbody1 xs Hndxs Hlenxs HdisjL0).
  specialize (Hbody2 xs Hndxs Hlenxs HdisjL1).
  apply (Hbodydet xs Hndxs Hlenxs HdisjL _ _ _
           (valuation_well_sorted_union_lookup_list_to_map _ _ _ _ _ vs0 HV)
           Hbody1 Hbody2).
Qed.

(** [E_TExists_true] and [E_TExists_false] cannot both apply: instantiating
    the false rule at the true rule's witness makes one body evaluate to both
    booleans.  This is the [TExists] case of [eval_deterministic], stated as a
    contradiction because that is the shape it takes. *)
Lemma eval_deterministic_TExists_arm :
  forall Σ A S (V : valuation A) (Ld Lt Lf : gset var) σ' t wt,
    valuation_well_sorted S V ->
    (forall x, x ∉ Lt ->
        ⟦ term_open 0 [TFVar x] t : σ_bool ⟧(Σ, A, <[x := existT σ' wt]> V)
          ⇓ cast_sym A.(domain_σ_bool) true) ->
    (forall x, x ∉ Lf -> forall (v' : A.(domain) σ'),
        ⟦ term_open 0 [TFVar x] t : σ_bool ⟧(Σ, A, <[x := existT σ' v']> V)
          ⇓ cast_sym A.(domain_σ_bool) false) ->
    (forall x, x ∉ Ld ->
        forall (V0 : valuation A) (w1 w2 : A.(domain) σ_bool),
          valuation_well_sorted (<[x:=σ']> S) V0 ->
          ⟦ term_open 0 [TFVar x] t : σ_bool ⟧(Σ, A, V0) ⇓ w1 ->
          ⟦ term_open 0 [TFVar x] t : σ_bool ⟧(Σ, A, V0) ⇓ w2 -> w1 = w2) ->
    False.
Proof.
  intros Σ A S V Ld Lt Lf σ' t wt HV Htrue Hfalse Hdet.
  pose (x := fresh_string_of_set "" (Ld ∪ Lt ∪ Lf)).
  assert (Hxf : x ∉ (Ld ∪ Lt ∪ Lf))
    by (apply fresh_string_of_set_fresh).
  apply not_elem_of_union in Hxf as [Hxf HxLf].
  apply not_elem_of_union in Hxf as [HxLd HxLt].
  specialize (Htrue x HxLt).
  specialize (Hfalse x HxLf wt).
  pose proof (Hdet x HxLd _ _ _ (valuation_well_sorted_insert _ _ _ _ _ _ HV)
                Htrue Hfalse) as Hbad.
  apply (cast_sym_true_neq_false A.(domain_σ_bool)). exact Hbad.
Qed.

(** The [TMatch] case.  Two derivations over the same scrutinee take the same
    arm, since [E_TMatch_PApp_true]'s [exists vs, F @@ vs = v'] and
    [E_TMatch_PApp_false]'s [forall vs, F @@ vs <> v'] cannot both hold. *)
Lemma eval_deterministic_TMatch :
  forall Σ A S (V : valuation A) (L : gset var) pts t δ σ
         (v1 v2 : A.(domain) σ),
    adt Σ δ ->
    valuation_well_sorted S V ->
    (forall (V0 : valuation A) (w1 w2 : A.(domain) δ),
        valuation_well_sorted S V0 ->
        ⟦ t : δ ⟧(Σ, A, V0) ⇓ w1 -> ⟦ t : δ ⟧(Σ, A, V0) ⇓ w2 -> w1 = w2) ->
    (forall (V0 : valuation A) (σ' : sort) (v0 : A.(domain) σ'),
        valuation_well_sorted S V0 ->
        ⟦ t : σ' ⟧(Σ, A, V0) ⇓ v0 -> σ' = δ) ->
    (forall c n t0, (PApp c n, t0) ∈ pts -> c ∈ Σ.(constructors)) ->
    (forall c n t0, (PApp c n, t0) ∈ pts ->
        exists σs, monomorphic_rank Σ c σs δ /\ length σs = n) ->
    (forall c n t0 σs xs, (PApp c n, t0) ∈ pts ->
        monomorphic_rank Σ c σs δ -> NoDup xs -> length xs = n ->
        list_to_set xs ## L ->
        forall (V0 : valuation A) (w1 w2 : A.(domain) σ),
          valuation_well_sorted (list_to_map (zip xs σs) ∪ S) V0 ->
          ⟦ term_open 0 (map TFVar xs) t0 : σ ⟧(Σ, A, V0) ⇓ w1 ->
          ⟦ term_open 0 (map TFVar xs) t0 : σ ⟧(Σ, A, V0) ⇓ w2 -> w1 = w2) ->
    (forall x t', x ∉ L -> (PVar, t') ∈ pts ->
        forall (V0 : valuation A) (w1 w2 : A.(domain) σ),
          valuation_well_sorted (<[x:=δ]> S) V0 ->
          ⟦ term_open 0 [TFVar x] t' : σ ⟧(Σ, A, V0) ⇓ w1 ->
          ⟦ term_open 0 [TFVar x] t' : σ ⟧(Σ, A, V0) ⇓ w2 -> w1 = w2) ->
    ⟦ TMatch t pts : σ ⟧(Σ, A, V) ⇓ v1 ->
    ⟦ TMatch t pts : σ ⟧(Σ, A, V) ⇓ v2 ->
    v1 = v2.
Proof.
  intros Σ A S V L pts t δ σ v1 v2 Hadt HV Hscrutdet Hscrutsort.
  revert v1 v2.
  induction pts as [|[p t'] pts' IH];
    intros v1 v2 Hcon Hex HbodyP HbodyV Hev1 Hev2.
  - apply eval_TMatch_nil_inv in Hev1. destruct Hev1.
  - (* Both evals are on [TMatch t ((p,t') :: pts')]; show same branch. *)
    destruct p as [|c n].
    + (* PVar: both use E_TMatch_PVar, body [TLet [t] t'] *)
      apply eval_TMatch_PVar_inv, eval_TLet_inv in Hev1.
      apply eval_TMatch_PVar_inv, eval_TLet_inv in Hev2.
      destruct Hev1 as (L0 & σsa & vsa & Hargsa & Hbodya).
      destruct Hev2 as (L1 & σsb & vsb & Hargsb & Hbodyb).
      (* scrutinee evals at sorts σsa = [δ], σsb = [δ]; concretize hlists *)
      apply evals_cons_sigT in Hargsa.
      destruct Hargsa as (σa & σsa' & va & vsa' & Heva & Htla & Hidxa).
      apply evals_nil_sorts in Htla. subst σsa'.
      apply evals_cons_sigT in Hargsb.
      destruct Hargsb as (σb & σsb' & vb & vsb' & Hevb & Htlb & Hidxb).
      apply evals_nil_sorts in Htlb. subst σsb'.
      pose proof Hidxa as Hshapea. pose proof Hidxb as Hshapeb.
      apply (f_equal (@projT1 _ _)) in Hshapea. simpl in Hshapea. subst σsa.
      apply (f_equal (@projT1 _ _)) in Hshapeb. simpl in Hshapeb. subst σsb.
      apply (Eqdep_dec.inj_pair2_eq_dec _ (fun x y => decide (x = y)))
        in Hidxa, Hidxb.
      subst vsa vsb. hlist_nil vsa'. hlist_nil vsb'.
      assert (Hδa : σa = δ) by (apply (Hscrutsort V σa va HV); exact Heva).
      assert (Hδb : σb = δ) by (apply (Hscrutsort V σb vb HV); exact Hevb).
      subst σa σb.
      assert (Hvsc : va = vb) by (apply (Hscrutdet V va vb HV); assumption).
      subst vb.
      (* now both bodies live at [<[x := existT δ va]> V] after a single
         fresh binder *)
      pose (x := fresh_string_of_set "" (L ∪ L0 ∪ L1)).
      assert (Hxf : x ∉ (L ∪ L0 ∪ L1))
        by (apply fresh_string_of_set_fresh).
      apply not_elem_of_union in Hxf as [Hxf HxLb].
      apply not_elem_of_union in Hxf as [HxL HxLa].
      assert (HdisjA : list_to_set [x] ## L0)
        by (rewrite list_to_set_singleton; by apply disjoint_singleton_l).
      assert (HdisjB : list_to_set [x] ## L1)
        by (rewrite list_to_set_singleton; by apply disjoint_singleton_l).
      specialize (Hbodya [x] (NoDup_singleton x) eq_refl HdisjA).
      specialize (Hbodyb [x] (NoDup_singleton x) eq_refl HdisjB).
      cbv zeta in Hbodya, Hbodyb. cbn [hlist_to_list map] in Hbodya, Hbodyb.
      rewrite list_to_map_zip_singleton_union in Hbodya, Hbodyb.
      exact (HbodyV x t' HxL (list_elem_of_here _ _) _ _ _
               (valuation_well_sorted_insert _ _ _ _ _ _ HV) Hbodya Hbodyb).
    + (* PApp c n: branch agreement via scrutinee + mutual exclusion *)
      assert (Hcon_c : c ∈ Σ.(constructors)) by (apply (Hcon c n t'); left).
      apply eval_TMatch_PApp_inv in Hev1, Hev2.
      destruct Hev1 as (δ0 & σs & v' & Hranka & Hscra & Harma).
      destruct Hev2 as (δ1 & σs0 & v'0 & Hrankb & Hscrb & Harmb).
      assert (Hδ1 : δ0 = δ) by (apply (Hscrutsort V δ0 v' HV); exact Hscra).
      assert (Hδ2 : δ1 = δ) by (apply (Hscrutsort V δ1 v'0 HV); exact Hscrb).
      subst δ0 δ1.
      assert (Hvsc : v' = v'0) by (apply (Hscrutdet V v' v'0 HV); assumption).
      subst v'0.
      (* σs1 = σs2 by constructor rank arg-functionality *)
      assert (Hσseq : σs = σs0)
        by (eapply monomorphic_rank_constructor_args_eq; eauto).
      subst σs0.
      destruct Harma as [[Hrangea Hleta] | [Hnorangea Hresta]];
        destruct Harmb as [[Hrangeb Hletb] | [Hnorangeb Hrestb]].
      * (* both PApp_true *)
        assert (Hgslen : length (Σ.(selectors_for_constructor) c) = length σs)
          by (eapply monomorphic_rank_selector_length; eauto).
        (* invert both body TLets *)
        apply eval_TLet_inv in Hleta, Hletb.
        destruct Hleta as (L0 & σs0 & vs & Hargsa & HbodyA).
        destruct Hletb as (L1 & σs1 & vs0 & Hargsb & HbodyB).
        (* both bound-sort lists are pinned to σs1 *)
        assert (HσsA : σs0 = σs)
          by (eapply evals_selector_sorts; [exact Hgslen | exact Hargsa]).
        assert (HσsB : σs1 = σs)
          by (eapply evals_selector_sorts; [exact Hgslen | exact Hargsb]).
        subst σs0 σs1.
        (* the two bound value-hlists agree (selector apps are deterministic) *)
        pose proof (evals_length _ _ _ _ _ _ Hargsa) as Hltsa.
        assert (Hvseq : vs = vs0).
        { eapply (evals_vals_eq Σ A V _ σs vs vs0 Hltsa);
            [|exact Hargsa|exact Hargsb].
          intros i t_i σ_i Hti Hσi w1 w2 Hw1 Hw2.
          (* t_i = TApp (gs!!i) (Some σ_i) [t] *)
          rewrite list_lookup_fmap in Hti.
          apply fmap_Some in Hti as (pr & Hzi & Hti_eq).
          apply lookup_zip_with_Some in Hzi
            as (g0 & σ0 & Hpair & Hg0 & Hσ0).
          subst pr.
          rewrite Hσi in Hσ0. injection Hσ0 as <-.
          simpl in Hti_eq. subst t_i.
          eapply (eval_deterministic_selector_app_arm Σ A V g0 σ_i t δ);
            [| |exact Hw1|exact Hw2].
          - intros u1 u2. apply (Hscrutdet V u1 u2 HV).
          - intros σ' u Heu. apply (Hscrutsort V σ' u HV). exact Heu. }
        subst vs0.
        (* run the body-determinism hypothesis at a fresh binder list *)
        pose (xs := fresh_strings_of_set "" (length σs) (L ∪ L0 ∪ L1)).
        assert (Hndxs : NoDup xs) by (apply NoDup_fresh_strings_of_set).
        assert (Hlenxs : length xs = length σs)
          by (apply length_fresh_strings_of_set).
        assert (Hdisj : list_to_set xs ## (L ∪ L0 ∪ L1))
          by (apply fresh_strings_of_set_fresh; set_solver).
        apply disjoint_union_r in Hdisj as [Hdisj HdisjLb].
        apply disjoint_union_r in Hdisj as [HdisjL HdisjLa].
        rewrite <- Hlenxs in Hltsa.
        specialize (HbodyA xs Hndxs Hltsa HdisjLa).
        specialize (HbodyB xs Hndxs Hltsa HdisjLb).
        destruct (Hex c n t') as (σs_ex & Hrank_ex & Hlen_ex); [left|].
        assert (Hlen_xs_n : length xs = n).
        { rewrite Hlenxs, <- Hlen_ex.
          eapply monomorphic_rank_constructor_length; eauto. }
        exact (HbodyP c n t' σs xs (list_elem_of_here _ _) Hranka Hndxs
                 Hlen_xs_n HdisjL _ _ _
                 (valuation_well_sorted_union_lookup_list_to_map _ _ _ _ _ vs HV)
                 HbodyA HbodyB).
      * (* PApp_true (1) vs PApp_false (2): contradiction *)
        exfalso. destruct Hrangea as [vs Hvs]. exact (Hnorangeb vs Hvs).
      * (* PApp_false (1) vs PApp_true (2): contradiction *)
        exfalso. destruct Hrangeb as [vs Hvs]. exact (Hnorangea vs Hvs).
      * (* both PApp_false: recurse *)
        apply (IH v1 v2).
        -- intros c1 n1 t1 Hin0. apply (Hcon c1 n1 t1). right. exact Hin0.
        -- intros c1 n1 t1 Hin0. apply (Hex c1 n1 t1). right. exact Hin0.
        -- intros c1 n1 t1 σs_tail xs0 Hin0.
           apply (HbodyP c1 n1 t1 σs_tail xs0). right. exact Hin0.
        -- intros x1 t1 Hx1 Hin0.
           apply (HbodyV x1 t1 Hx1). right. exact Hin0.
        -- exact Hresta.
        -- exact Hrestb.
Qed.

(** Evaluation of a well-sorted term under a valuation for its signature's
    variables is deterministic.  A binder case moves both of the body's
    evaluations to the extended signature its body is sorted under
    ([eval_cong_signature]). *)
Theorem eval_deterministic : forall Σ (A : structure) (V : valuation A) σ t
    (v1 v2 : A.(domain) σ),
    Σ ⊢ t : σ ->
    valuation_well_sorted Σ.(sorts) V ->
    ⟦ t : σ ⟧(Σ, A, V) ⇓ v1 ->
    ⟦ t : σ ⟧(Σ, A, V) ⇓ v2 ->
    v1 = v2.
Proof.
  intros Σ A V σ t v1 v2 Hsort. revert V v1 v2.
  induction Hsort; intros V v1 v2 HV Hev1 Hev2.
  - (* S_TFVar *)
    apply eval_TFVar_inv in Hev1, Hev2.
    rewrite Hev2 in Hev1. injection Hev1 as Hv.
    apply (Eqdep_dec.inj_pair2_eq_dec _ (fun x y => decide (x = y))) in Hv.
    symmetry. exact Hv.
  - (* S_TApp *)
    eapply eval_deterministic_TApp_arm;
      [ exact HV | exact H | exact H0 | exact H1
      | exact H2
      | exact H3 | exact Hev1 | exact Hev2 ].
  - (* S_TApp_annotated *)
    eapply eval_deterministic_TApp_arm_typed;
      [ exact HV | exact H | exact H0
      | exact H1
      | exact H2 | exact Hev1 | exact Hev2 ].
  - (* S_TLambda *)
    apply eval_TLambda_inv in Hev1, Hev2.
    destruct Hev1 as (L0 & σ2a & g1 & Hval1 & Hb1).
    destruct Hev2 as (L1 & σ2b & g2 & Hval2 & Hb2).
    pose proof Hval1 as Hsa. pose proof Hval2 as Hsb.
    apply (f_equal (@projT1 _ _)) in Hsa, Hsb. simpl in Hsa, Hsb.
    assert (σ2a = σ2) by (unfold τ_map in Hsa; congruence).
    assert (σ2b = σ2) by (unfold τ_map in Hsb; congruence).
    subst σ2a σ2b.
    apply (Eqdep_dec.inj_pair2_eq_dec _ (fun x y => decide (x = y)))
      in Hval1, Hval2. subst g1 g2.
    assert (Hcast : cast (A.(domain_σ_map) σ1 σ2) v1
                  = cast (A.(domain_σ_map) σ1 σ2) v2).
    { apply functional_extensionality. intros w.
      pose (x := fresh_string_of_set "" (L ∪ L0 ∪ L1)).
      assert (Hxf : x ∉ (L ∪ L0 ∪ L1))
        by (apply fresh_string_of_set_fresh).
      apply not_elem_of_union in Hxf as [Hxf HxL2].
      apply not_elem_of_union in Hxf as [HxL HxL1].
      specialize (Hb1 x HxL1 w). simpl in Hb1.
      specialize (Hb2 x HxL2 w). simpl in Hb2.
      apply (eval_cong_signature (<[x := σ1]> Σ)) in Hb1, Hb2;
        [| apply signatures_agree_except_sorts_insert ..].
      apply (H2 x HxL _ _ _ (valuation_well_sorted_insert _ _ _ _ _ _ HV) Hb1 Hb2). }
    rewrite <- (cast_sym_cast (A.(domain_σ_map) σ1 σ2) v1).
    rewrite <- (cast_sym_cast (A.(domain_σ_map) σ1 σ2) v2).
    rewrite Hcast. reflexivity.
  - (* S_TExists *)
    apply eval_TExists_inv in Hev1, Hev2.
    destruct Hev1 as (L0 & [(w1 & Hval1 & Hb1) | (Hval1 & Hb1)]);
      destruct Hev2 as (L1 & [(w2 & Hval2 & Hb2) | (Hval2 & Hb2)]);
      apply (Eqdep_dec.inj_pair2_eq_dec _ (fun x y => decide (x = y)))
        in Hval1, Hval2; subst v1 v2.
    + reflexivity.
    + exfalso.
      eapply (eval_deterministic_TExists_arm Σ A Σ.(sorts) V L L0 L1 σ t w1);
        [exact HV | exact Hb1 | exact Hb2 |].
      intros x Hx V0 w1' w2' HV0 Hw1 Hw2.
      apply (eval_cong_signature (<[x := σ]> Σ)) in Hw1, Hw2;
        [| apply signatures_agree_except_sorts_insert ..].
      exact (H2 x Hx V0 w1' w2' HV0 Hw1 Hw2).
    + exfalso.
      eapply (eval_deterministic_TExists_arm Σ A Σ.(sorts) V L L1 L0 σ t w2);
        [exact HV | exact Hb2 | exact Hb1 |].
      intros x Hx V0 w1' w2' HV0 Hw1 Hw2.
      apply (eval_cong_signature (<[x := σ]> Σ)) in Hw1, Hw2;
        [| apply signatures_agree_except_sorts_insert ..].
      exact (H2 x Hx V0 w1' w2' HV0 Hw1 Hw2).
    + reflexivity.
  - (* S_TForall *)
    apply eval_TForall_inv in Hev1, Hev2.
    destruct Hev1 as (L0 & [(Hval1 & Hb1) | (w1 & Hval1 & Hb1)]);
      destruct Hev2 as (L1 & [(Hval2 & Hb2) | (w2 & Hval2 & Hb2)]);
      apply (Eqdep_dec.inj_pair2_eq_dec _ (fun x y => decide (x = y)))
        in Hval1, Hval2; subst v1 v2.
    + reflexivity.
    + exfalso.
      pose (x := fresh_string_of_set "" (L ∪ L0 ∪ L1)).
      assert (Hxf : x ∉ (L ∪ L0 ∪ L1))
        by (apply fresh_string_of_set_fresh).
      apply not_elem_of_union in Hxf as [Hxf HxL1].
      apply not_elem_of_union in Hxf as [HxL HxL0].
      specialize (Hb1 x HxL0 w2). simpl in Hb1.
      specialize (Hb2 x HxL1). simpl in Hb2.
      apply (eval_cong_signature (<[x := σ]> Σ)) in Hb1, Hb2;
        [| apply signatures_agree_except_sorts_insert ..].
      pose proof (H2 x HxL _ _ _ (valuation_well_sorted_insert _ _ _ _ _ _ HV)
                    Hb1 Hb2) as Hbad.
      exact (cast_sym_true_neq_false A.(domain_σ_bool) Hbad).
    + exfalso.
      pose (x := fresh_string_of_set "" (L ∪ L0 ∪ L1)).
      assert (Hxf : x ∉ (L ∪ L0 ∪ L1))
        by (apply fresh_string_of_set_fresh).
      apply not_elem_of_union in Hxf as [Hxf HxL1].
      apply not_elem_of_union in Hxf as [HxL HxL0].
      specialize (Hb1 x HxL0). simpl in Hb1.
      specialize (Hb2 x HxL1 w1). simpl in Hb2.
      apply (eval_cong_signature (<[x := σ]> Σ)) in Hb1, Hb2;
        [| apply signatures_agree_except_sorts_insert ..].
      pose proof (H2 x HxL _ _ _ (valuation_well_sorted_insert _ _ _ _ _ _ HV)
                    Hb1 Hb2) as Hbad.
      symmetry in Hbad. exact (cast_sym_true_neq_false A.(domain_σ_bool) Hbad).
    + reflexivity.
  - (* S_TLet *)
    eapply eval_deterministic_TLet_arm;
      [ exact HV | exact H
      | exact H0
      | exact H1 | | exact Hev1 | exact Hev2 ].
    intros xs Hnd Hlen Hdisj V0 w1 w2 HV0 Hw1 Hw2.
    apply (eval_cong_signature (list_to_map (zip xs σs) ⊍ Σ)) in Hw1, Hw2;
      [| apply signatures_agree_except_sorts_add_sorts ..].
    exact (H3 xs Hnd Hlen Hdisj V0 w1 w2 HV0 Hw1 Hw2).
  - (* S_TMatch_PApp *)
    assert (HnoPVar : forall t', (PVar, t') ∉ pts).
    { intros t' Hin.
      apply (exact_coverage_no_PVar ps); [unfold cs in H2; exact H2|].
      apply list_elem_of_fmap. exists (PVar, t'). split; [reflexivity| exact Hin]. }
    assert (Hcon : forall c n t0, (PApp c n, t0) ∈ pts -> c ∈ Σ.(constructors)).
    { intros c n t0 Hin.
      eapply (match_pattern_constructor_in_constructors Σ pts δ s c n t0);
        eauto. rewrite <- H1. done. }
    eapply (eval_deterministic_TMatch Σ A Σ.(sorts) V L pts t δ σ v1 v2);
      [ exact H | exact HV | exact IHHsort
      | intros V0 σ' v0 HV0 Hev0;
          exact (eval_sort_of_well_sorted _ _ _ _ _ _ _ Hsort HV0 Hev0)
      | exact Hcon | exact H5 |
      | intros x t' Hx Hin; exfalso; apply (HnoPVar t' Hin)
      | exact Hev1 | exact Hev2 ].
    intros c n t0 σs xs Hin Hrank Hnd Hlen Hdisj V0 w1 w2 HV0 Hw1 Hw2.
    apply (eval_cong_signature (list_to_map (zip xs σs) ⊍ Σ)) in Hw1, Hw2;
      [| apply signatures_agree_except_sorts_add_sorts ..].
    exact (H4 c n t0 σs xs Hin Hrank Hnd Hlen Hdisj V0 w1 w2 HV0 Hw1 Hw2).
  - (* S_TMatch_PVar *)
    assert (Hcon : forall c n t0, (PApp c n, t0) ∈ pts -> c ∈ Σ.(constructors)).
    { intros c n t0 Hin.
      eapply (match_pattern_constructor_in_constructors Σ pts δ s c n t0);
        eauto. }
    eapply (eval_deterministic_TMatch Σ A Σ.(sorts) V L pts t δ σ v1 v2);
      [ exact H | exact HV | exact IHHsort
      | intros V0 σ' v0 HV0 Hev0;
          exact (eval_sort_of_well_sorted _ _ _ _ _ _ _ Hsort HV0 Hev0)
      | exact Hcon | exact H7 | | | exact Hev1 | exact Hev2 ].
    + intros c n t0 σs xs Hin Hrank Hnd Hlen Hdisj V0 w1 w2 HV0 Hw1 Hw2.
      apply (eval_cong_signature (list_to_map (zip xs σs) ⊍ Σ)) in Hw1, Hw2;
        [| apply signatures_agree_except_sorts_add_sorts ..].
      exact (H4 c n t0 σs xs Hin Hrank Hnd Hlen Hdisj V0 w1 w2 HV0 Hw1 Hw2).
    + intros x t' Hx Hin V0 w1 w2 HV0 Hw1 Hw2.
      apply (eval_cong_signature (<[x := δ]> Σ)) in Hw1, Hw2;
        [| apply signatures_agree_except_sorts_insert ..].
      exact (H6 x t' Hx Hin V0 w1 w2 HV0 Hw1 Hw2).
Qed.

(** The argument-list form: two evaluations of one term list agree on both the
    sort list and the value hlist, so the values agree only heterogeneously. *)
Lemma evals_deterministic :
  forall Σ A (V : valuation A),
    forall ts σs1 σs2 (vs1 : hlist A.(domain) σs1)
           (vs2 : hlist A.(domain) σs2),
      valuation_well_sorted Σ.(sorts) V ->
      (forall i t_i σ_i, ts !! i = Some t_i -> σs1 !! i = Some σ_i ->
          Σ ⊢ t_i : σ_i) ->
      ⟦ ts : σs1 ⟧*(Σ, A, V) ⇓ vs1 ->
      ⟦ ts : σs2 ⟧*(Σ, A, V) ⇓ vs2 ->
      σs1 = σs2 /\ vs1 ≅ vs2.
Proof.
  intros Σ A V ts.
  induction ts as [|t ts' IH]; intros σs1 σs2 vs1 vs2 HV Hws He1 He2.
  - apply evals_nil_sorts in He1, He2. subst σs1 σs2.
    hlist_nil vs1. hlist_nil vs2. split; reflexivity.
  - apply evals_cons_sigT in He1, He2.
    destruct He1 as (σa1 & σsa1 & va1 & vsa1 & Hva1 & Htl1 & Hidx1).
    destruct He2 as (σa2 & σsa2 & va2 & vsa2 & Hva2 & Htl2 & Hidx2).
    pose proof Hidx1 as Hshape1. pose proof Hidx2 as Hshape2.
    apply (f_equal (@projT1 _ _)) in Hshape1, Hshape2.
    simpl in Hshape1, Hshape2. subst σs1 σs2.
    apply (Eqdep_dec.inj_pair2_eq_dec _ (fun x y => decide (x = y)))
      in Hidx1, Hidx2. subst vs1 vs2.
    assert (Hσa : σa2 = σa1)
      by (eapply eval_sort_of_well_sorted;
          [ exact (Hws 0 t σa1 eq_refl eq_refl) | exact HV | exact Hva2 ]).
    symmetry in Hσa.
    subst σa2.
    assert (Hva : va1 = va2)
      by (eapply eval_deterministic;
          [ exact (Hws 0 t σa1 eq_refl eq_refl) | exact HV
          | exact Hva1 | exact Hva2 ]).
    subst va2.
    destruct (IH σsa1 σsa2 vsa1 vsa2 HV
                (fun i t_i σ_i Ht_i Hσ_i =>
                   Hws (Datatypes.S i) t_i σ_i Ht_i Hσ_i)
                Htl1 Htl2) as [Hσs Hvs].
    subst σsa2.
    apply eq_of_heq in Hvs. subst vsa2.
    split; [reflexivity | reflexivity].
Qed.

(** An application's value is its arguments' values under the symbol's
    interpretation, so the same symbol applied to terms with the same values
    has the same value, under any valuation. *)
Lemma eval_TApp_args_value :
  forall Σ A (V V' : valuation A)
         g σopt ts ts' σs (ws : hlist A.(domain) σs) σ (v : A.(domain) σ),
    valuation_well_sorted Σ.(sorts) V ->
    Forall2 (fun t σ => Σ ⊢ t : σ) ts σs ->
    ⟦ TApp g σopt ts : σ ⟧(Σ, A, V) ⇓ v ->
    ⟦ ts : σs ⟧*(Σ, A, V) ⇓ ws ->
    ⟦ ts' : σs ⟧*(Σ, A, V') ⇓ ws ->
    ⟦ TApp g σopt ts' : σ ⟧(Σ, A, V') ⇓ v.
Proof.
  intros Σ A V V' g σopt ts ts' σs ws σ v HV Hsorts Happ Hargs Hargs'.
  apply eval_TApp_inv in Happ as (σs0 & vs0 & Hargs0 & Hσopt & Hrank & Hv).
  destruct (evals_deterministic Σ A V ts σs σs0 ws vs0 HV
              ltac:(intros i t_i σ_i Ht Hσ; eapply Forall2_lookup_lr; eauto)
              Hargs Hargs0) as [<- Hvs].
  apply eq_of_heq in Hvs. subst vs0.
  econstructor; [exact Hargs' | exact Hσopt | exact Hrank | exact Hv].
Qed.

(** * Renaming and Substitution *)

(** Replacing variables in a term that already evaluates: renaming one free
    variable, alpha-renaming a single binder, substituting a binder list, and
    alpha-renaming a binder list. *)

(** ** Renaming a Free Variable *)

(** The mutual induction behind [eval_rename]: substituting [TFVar a'] for
    [a] preserves evaluation when [a'] is distinct from [a] and the valuation
    gives it the same sort and value. *)
Local Lemma eval_rename_mut_aux :
  forall Σ A,
  (forall (V : valuation A) σ t v
     (_ : ⟦ t : σ ⟧(Σ, A, V) ⇓ v),
   forall (a a' : var),
     a' <> a ->
     V !! a' = V !! a ->
     ⟦ term_subst {[ a := TFVar a' ]} t : σ ⟧(Σ, A, V) ⇓ v)
  /\
  (forall (V : valuation A) σs ts vs
     (_ : ⟦ ts : σs ⟧*(Σ, A, V) ⇓ vs),
   forall (a a' : var),
     a' <> a ->
     V !! a' = V !! a ->
     ⟦ map (term_subst {[ a := TFVar a' ]}) ts : σs ⟧*(Σ, A, V) ⇓ vs).
Proof.
  intros Σ A.
  apply eval_combined_ind.
  - (* E_TFVar *)
    intros V x σ v Hv a a' Hne Hjm.
    simpl. destruct (decide (a = x)) as [->|Hne_x].
    + rewrite lookup_singleton_eq. apply E_TFVar. rewrite Hjm. exact Hv.
    + rewrite lookup_singleton_ne; [|auto]. apply E_TFVar. exact Hv.
  - (* E_TApp *)
    intros V f σopt ts σs σ vs v Hts IHts Hσopt Hrank F Hv a a' Hne Hjm.
    eapply E_TApp;
      [apply IHts; auto | exact Hσopt | exact Hrank | exact Hv].
  - (* E_TExists_true *)
    intros L V σ' t v' Hbody IHbody a a' Hne Hjm.
    simpl. apply E_TExists_true with (L := L ∪ {[a; a']}) (v' := v').
    intros y Hy. simpl.
    assert (Hy_a : y <> a) by set_solver.
    assert (Hy_a' : y <> a') by set_solver.
    rewrite <- term_subst_singleton_open_TFVar1_comm by auto.
    apply IHbody; [set_solver | exact Hne |].
    rewrite !lookup_insert_ne by auto. exact Hjm.
  - (* E_TExists_false *)
    intros L V σ' t Hbody IHbody a a' Hne Hjm.
    simpl. apply E_TExists_false with (L := L ∪ {[a; a']}).
    intros y Hy. simpl. intros w.
    assert (Hy_a : y <> a) by set_solver.
    assert (Hy_a' : y <> a') by set_solver.
    rewrite <- term_subst_singleton_open_TFVar1_comm by auto.
    apply IHbody; [set_solver | exact Hne |].
    rewrite !lookup_insert_ne by auto. exact Hjm.
  - (* E_TForall_true *)
    intros L V σ' t Hbody IHbody a a' Hne Hjm.
    simpl. apply E_TForall_true with (L := L ∪ {[a; a']}).
    intros y Hy. simpl. intros w.
    assert (Hy_a : y <> a) by set_solver.
    assert (Hy_a' : y <> a') by set_solver.
    rewrite <- term_subst_singleton_open_TFVar1_comm by auto.
    apply IHbody; [set_solver | exact Hne |].
    rewrite !lookup_insert_ne by auto. exact Hjm.
  - (* E_TForall_false *)
    intros L V σ' t v' Hbody IHbody a a' Hne Hjm.
    simpl. apply E_TForall_false with (L := L ∪ {[a; a']}) (v' := v').
    intros y Hy. simpl.
    assert (Hy_a : y <> a) by set_solver.
    assert (Hy_a' : y <> a') by set_solver.
    rewrite <- term_subst_singleton_open_TFVar1_comm by auto.
    apply IHbody; [set_solver | exact Hne |].
    rewrite !lookup_insert_ne by auto. exact Hjm.
  - (* E_TLambda *)
    intros L V σ1 t σ2 fv_ Hbody IHbody a a' Hne Hjm.
    simpl. apply E_TLambda with (L := L ∪ {[a; a']}).
    intros y Hy. simpl. intros w.
    assert (Hy_a : y <> a) by set_solver.
    assert (Hy_a' : y <> a') by set_solver.
    rewrite <- term_subst_singleton_open_TFVar1_comm by auto.
    apply IHbody; [set_solver | exact Hne |].
    rewrite !lookup_insert_ne by auto. exact Hjm.
  - (* E_TLet *)
    intros L V σs ts σ t vs v Hts IHts Hbody IHbody a a' Hne Hjm.
    simpl. apply E_TLet with (L := L ∪ {[a; a']}) (vs := vs).
    + apply IHts; auto.
    + intros xs Hndxs Hlen Hxs. simpl.
      rewrite length_map in Hlen.
      assert (Hxs_a : a ∉ xs).
      { intros Hin. apply (Hxs a); set_solver. }
      assert (Hxs_a' : a' ∉ xs).
      { intros Hin. apply (Hxs a'); set_solver. }
      rewrite <- term_subst_singleton_open_TFVar_comm by auto.
      apply IHbody; [exact Hndxs | exact Hlen | set_solver | exact Hne |].
      rewrite !lookup_union_r by (apply lookup_list_to_map_zip_None; assumption).
      exact Hjm.
  - (* E_TMatch_PVar *)
    intros V σ t t' pts v Hlet IHlet a a' Hne Hjm.
    simpl. apply E_TMatch_PVar.
    specialize (IHlet a a' Hne Hjm). simpl in IHlet. exact IHlet.
  - (* E_TMatch_PApp_true *)
    intros V σ δ t c n t' pts v' v σs Hrank Hscrut IHscrut Hrange gs
           Hbody IHbody a a' Hne Hjm.
    simpl. eapply E_TMatch_PApp_true.
    + exact Hrank.
    + apply IHscrut; auto.
    + destruct Hrange as [ws Hws]. simpl in Hws.
      exists ws. simpl. exact Hws.
    + specialize (IHbody a a' Hne Hjm). simpl in IHbody.
      rewrite map_map in IHbody.
      erewrite map_ext in IHbody;
        [ exact IHbody | intros [g σ_i]; reflexivity ].
  - (* E_TMatch_PApp_false *)
    intros V σ δ t c n t' pts v' v σs Hrank Hscrut IHscrut Hrange
           Htail IHtail a a' Hne Hjm.
    simpl. eapply E_TMatch_PApp_false.
    + exact Hrank.
    + apply IHscrut; auto.
    + exact Hrange.
    + specialize (IHtail a a' Hne Hjm). simpl in IHtail. exact IHtail.
  - (* ES_nil *)
    intros V a a' Hne Hjm.
    simpl. constructor.
  - (* ES_cons *)
    intros V σ σs t ts v vs Hev IHev Hts IHts a a' Hne Hjm.
    simpl. constructor.
    + apply IHev; auto.
    + apply IHts; auto.
Qed.

(** Renaming a free variable to a distinct variable of the same sort and value
    preserves evaluation.

    This is the locally-nameless alpha-equivalence statement a client needs
    when it has already chosen a fresh variable and has to meet the cofinite
    variable an [E_TLambda] or [E_TExists] premise quantifies over. *)
Corollary eval_rename :
  forall Σ A (V : valuation A) σ t v (a a' : var),
    a' <> a ->
    V !! a' = V !! a ->
    ⟦ t : σ ⟧(Σ, A, V) ⇓ v ->
    ⟦ term_subst {[ a := TFVar a' ]} t : σ ⟧(Σ, A, V) ⇓ v.
Proof.
  intros Σ A V σ t v a a' Hne Hjm Heval.
  destruct (eval_rename_mut_aux Σ A) as [Hev _].
  eapply Hev; eauto.
Qed.

(** ** Alpha-Renaming One Binder *)

(** The binder of a one-variable body may be renamed to any other variable
    fresh for the body, keeping the same value.  Proved by weakening the
    context by the new binder, renaming, and strengthening the old binder
    away. *)
Lemma eval_term_open_alpha1 :
  forall Σ A (V : valuation A) σ c v x y σ' (w : A.(domain) σ'),
    x <> y ->
    x ∉ fv c ->
    y ∉ fv c ->
    ⟦ term_open 0 [TFVar x] c : σ ⟧(Σ, A, <[x := existT σ' w]> V) ⇓ v ->
    ⟦ term_open 0 [TFVar y] c : σ ⟧(Σ, A, <[y := existT σ' w]> V) ⇓ v.
Proof.
  intros Σ A V σ c v x y σ' w Hxy Hx Hyy Hev.
  assert (Hy_open : y ∉ fv (term_open 0 [TFVar x] c)).
  { intros Hy.
    pose proof (fv_term_open_TFVar1_subseteq c 0 x) as Hsub.
    apply Hsub in Hy. rewrite elem_of_union in Hy.
    destruct Hy as [Hy|Hy]; [exact (Hyy Hy)|].
    rewrite elem_of_singleton in Hy. apply Hxy. symmetry. exact Hy. }
  pose proof (eval_weaken1 Σ A (<[x := existT σ' w]> V) σ
    (term_open 0 [TFVar x] c) v y σ' w Hy_open Hev) as Hweaken.
  rewrite (insert_insert_ne V y x _ _ (not_eq_sym Hxy)) in Hweaken.
  assert (Hval_yx :
    <[x := existT σ' w]> (<[y := existT σ' w]> V) !! y =
    <[x := existT σ' w]> (<[y := existT σ' w]> V) !! x).
  { rewrite lookup_insert_ne by exact Hxy. rewrite !lookup_insert_eq. reflexivity. }
  pose proof (eval_rename Σ A (<[x := existT σ' w]> (<[y := existT σ' w]> V)) σ
    (term_open 0 [TFVar x] c) v x y (not_eq_sym Hxy) Hval_yx Hweaken)
    as Hren.
  change ({[x := TFVar y]} : stringmap term)
    with (list_to_map (zip [x] (map TFVar [y])) : stringmap term) in Hren.
  change [TFVar x] with (map TFVar [x]) in Hren.
  rewrite (term_subst_open_TFVar_rename [x] [y] c 0) in Hren.
  2:{ reflexivity. }
  2:{ apply NoDup_singleton. }
  2:{ rewrite list_to_set_singleton. apply elem_of_disjoint.
      intros z Hz Hfv. rewrite elem_of_singleton in Hz. subst z. exact (Hx Hfv). }
  assert (Hx_open : x ∉ fv (term_open 0 [TFVar y] c)).
  { intros Hx'.
    pose proof (fv_term_open_TFVar1_subseteq c 0 y) as Hsub.
    apply Hsub in Hx'. rewrite elem_of_union in Hx'.
    destruct Hx' as [Hx'|Hx']; [exact (Hx Hx')|].
    rewrite elem_of_singleton in Hx'. exact (Hxy Hx'). }
  eapply eval_strengthen1.
  - exact Hx_open.
  - exact Hren.
Qed.

(** ** Substitution *)

(** The mutual induction behind [eval_term_subst_singleton_insert]:
    substituting a locally closed [elem] for [x] undoes the insertion of
    [elem]'s value at [x].  [elem] must be locally closed because it is pushed
    under the term's binders. *)
Local Lemma eval_term_subst_singleton_insert_mut_aux :
  forall Σ A,
  (forall (V : valuation A) σ t v
     (_ : ⟦ t : σ ⟧(Σ, A, V) ⇓ v),
   forall (V0 : valuation A) x σx elem (w : A.(domain) σx),
     V = <[ x := existT σx w ]> V0 ->
     lc_at [] elem ->
     ⟦ elem : σx ⟧(Σ, A, V0) ⇓ w ->
     ⟦ term_subst {[ x := elem ]} t : σ ⟧(Σ, A, V0) ⇓ v)
  /\
  (forall (V : valuation A) σs ts vs
     (_ : ⟦ ts : σs ⟧*(Σ, A, V) ⇓ vs),
   forall (V0 : valuation A) x σx elem (w : A.(domain) σx),
     V = <[ x := existT σx w ]> V0 ->
     lc_at [] elem ->
     ⟦ elem : σx ⟧(Σ, A, V0) ⇓ w ->
     ⟦ map (term_subst {[ x := elem ]}) ts : σs ⟧*(Σ, A, V0) ⇓ vs).
Proof.
  intros Σ A.
  apply eval_combined_ind.
  - (* E_TFVar *)
    intros V x σ v Hv V0 z σ_z elem w_z HV Hlc Hev.
    subst V. simpl.
    destruct (decide (z = x)) as [->|Hne].
    + rewrite lookup_singleton_eq.
      rewrite lookup_insert_eq in Hv. apply (inj Some) in Hv.
      assert (σ_z = σ) as -> by exact (f_equal (@projT1 _ _) Hv).
      apply eq_of_existT in Hv. subst v. exact Hev.
    + rewrite lookup_singleton_ne by auto.
      apply E_TFVar. rewrite lookup_insert_ne in Hv by auto. exact Hv.
  - (* E_TApp *)
    intros V f σopt ts σs σ vs v Hts IHts Hσopt Hrank F Hv
           V0 z σ_z elem w_z HV Hlc Hev.
    simpl. eapply E_TApp; [eapply IHts; eauto|exact Hσopt|exact Hrank|exact Hv].
  - (* E_TExists_true *)
    intros L V σ_binder t v' Hbody IHbody V0 z σ_z elem w_z HV Hlc Hev.
    simpl.
    apply E_TExists_true with (L := L ∪ {[z]} ∪ fv elem) (v' := v').
    intros y Hy. simpl.
    assert (Hyz : y <> z) by set_solver.
    assert (Hy_L : y ∉ L) by set_solver.
    assert (Hyfv : y ∉ fv elem) by set_solver.
    rewrite <- (term_subst_open_TFVar_comm {[z := elem]} t 0 [y]).
    2:{ intros k u Hu. rewrite lookup_singleton_Some in Hu.
        destruct Hu as [_ <-]. apply lc_lc_at. exact Hlc. }
    2:{ intros k Hk. apply list_elem_of_singleton in Hk. subst k.
        apply lookup_singleton_ne. auto. }
    eapply (IHbody y Hy_L (<[y := existT σ_binder v']> V0) z σ_z elem w_z).
    + rewrite HV. apply insert_insert_ne. exact Hyz.
    + exact Hlc.
    + apply eval_weaken1; auto.
  - (* E_TExists_false *)
    intros L V σ_binder t Hbody IHbody V0 z σ_z elem w_z HV Hlc Hev.
    simpl.
    apply E_TExists_false with (L := L ∪ {[z]} ∪ fv elem).
    intros y Hy. simpl. intros w'.
    assert (Hyz : y <> z) by set_solver.
    assert (Hy_L : y ∉ L) by set_solver.
    assert (Hyfv : y ∉ fv elem) by set_solver.
    rewrite <- (term_subst_open_TFVar_comm {[z := elem]} t 0 [y]).
    2:{ intros k u Hu. rewrite lookup_singleton_Some in Hu.
        destruct Hu as [_ <-]. apply lc_lc_at. exact Hlc. }
    2:{ intros k Hk. apply list_elem_of_singleton in Hk. subst k.
        apply lookup_singleton_ne. auto. }
    eapply (IHbody y Hy_L w' (<[y := existT σ_binder w']> V0) z σ_z elem w_z).
    + rewrite HV. apply insert_insert_ne. exact Hyz.
    + exact Hlc.
    + apply eval_weaken1; auto.
  - (* E_TForall_true *)
    intros L V σ_binder t Hbody IHbody V0 z σ_z elem w_z HV Hlc Hev.
    simpl.
    apply E_TForall_true with (L := L ∪ {[z]} ∪ fv elem).
    intros y Hy. simpl. intros w'.
    assert (Hyz : y <> z) by set_solver.
    assert (Hy_L : y ∉ L) by set_solver.
    assert (Hyfv : y ∉ fv elem) by set_solver.
    rewrite <- (term_subst_open_TFVar_comm {[z := elem]} t 0 [y]).
    2:{ intros k u Hu. rewrite lookup_singleton_Some in Hu.
        destruct Hu as [_ <-]. apply lc_lc_at. exact Hlc. }
    2:{ intros k Hk. apply list_elem_of_singleton in Hk. subst k.
        apply lookup_singleton_ne. auto. }
    eapply (IHbody y Hy_L w' (<[y := existT σ_binder w']> V0) z σ_z elem w_z).
    + rewrite HV. apply insert_insert_ne. exact Hyz.
    + exact Hlc.
    + apply eval_weaken1; auto.
  - (* E_TForall_false *)
    intros L V σ_binder t v' Hbody IHbody V0 z σ_z elem w_z HV Hlc Hev.
    simpl.
    apply E_TForall_false with (L := L ∪ {[z]} ∪ fv elem) (v' := v').
    intros y Hy. simpl.
    assert (Hyz : y <> z) by set_solver.
    assert (Hy_L : y ∉ L) by set_solver.
    assert (Hyfv : y ∉ fv elem) by set_solver.
    rewrite <- (term_subst_open_TFVar_comm {[z := elem]} t 0 [y]).
    2:{ intros k u Hu. rewrite lookup_singleton_Some in Hu.
        destruct Hu as [_ <-]. apply lc_lc_at. exact Hlc. }
    2:{ intros k Hk. apply list_elem_of_singleton in Hk. subst k.
        apply lookup_singleton_ne. auto. }
    eapply (IHbody y Hy_L (<[y := existT σ_binder v']> V0) z σ_z elem w_z).
    + rewrite HV. apply insert_insert_ne. exact Hyz.
    + exact Hlc.
    + apply eval_weaken1; auto.
  - (* E_TLambda *)
    intros L V σ1 t σ2 f Hbody IHbody V0 z σ_z elem w_z HV Hlc Hev.
    simpl.
    apply E_TLambda with (L := L ∪ {[z]} ∪ fv elem).
    intros y Hy. simpl. intros w'.
    assert (Hyz : y <> z) by set_solver.
    assert (Hy_L : y ∉ L) by set_solver.
    assert (Hyfv : y ∉ fv elem) by set_solver.
    rewrite <- (term_subst_open_TFVar_comm {[z := elem]} t 0 [y]).
    2:{ intros k u Hu. rewrite lookup_singleton_Some in Hu.
        destruct Hu as [_ <-]. apply lc_lc_at. exact Hlc. }
    2:{ intros k Hk. apply list_elem_of_singleton in Hk. subst k.
        apply lookup_singleton_ne. auto. }
    eapply (IHbody y Hy_L w' (<[y := existT σ1 w']> V0) z σ_z elem w_z).
    + rewrite HV. apply insert_insert_ne. exact Hyz.
    + exact Hlc.
    + apply eval_weaken1; auto.
  - (* E_TLet *)
    intros L V σs ts σ t vs v Hts IHts Hbody IHbody V0 z σ_z elem w_z
           HV Hlc Hev.
    simpl.
    apply E_TLet with (L := L ∪ {[z]} ∪ fv elem) (vs := vs).
    + eapply IHts; eauto.
    + intros xs Hndxs Hlen Hxs. simpl.
      rewrite length_map in Hlen.
      assert (Hxsz : z ∉ xs).
      { intros Hin. apply (Hxs z); set_solver. }
      assert (Hxs_L : list_to_set xs ## L) by set_solver.
      assert (Hxs_elem : (list_to_set xs : gset var) ## fv elem).
      { intros u Hu Hfv. apply (Hxs u); set_solver. }
      rewrite <- (term_subst_open_TFVar_comm {[z := elem]} t 0 xs).
      2:{ intros k u Hu. rewrite lookup_singleton_Some in Hu.
          destruct Hu as [_ <-]. apply lc_lc_at. exact Hlc. }
      2:{ intros k Hk. apply lookup_singleton_ne. set_solver. }
      eapply (IHbody xs Hndxs Hlen Hxs_L
                (list_to_map (zip xs (hlist_to_list vs)) ∪ V0) z σ_z elem w_z).
      * rewrite HV. symmetry. apply insert_union_r.
        apply lookup_list_to_map_zip_None. exact Hxsz.
      * exact Hlc.
      * apply eval_weaken; [exact Hxs_elem|exact Hev].
  - (* E_TMatch_PVar *)
    intros V σ t t' pts v Hlet IHlet V0 z σ_z elem w_z HV Hlc Hev.
    simpl. apply E_TMatch_PVar. eapply IHlet; eauto.
  - (* E_TMatch_PApp_true *)
    intros V σ δ t c n t' pts v' v σs Hrank Hscrut IHscrut Hrange gs
           Hbody IHbody V0 z σ_z elem w_z HV Hlc Hev.
    simpl. eapply E_TMatch_PApp_true.
    + exact Hrank.
    + eapply IHscrut; eauto.
    + destruct Hrange as [ws Hws]. exists ws. exact Hws.
    + specialize (IHbody V0 z σ_z elem w_z HV Hlc Hev).
      simpl in IHbody. rewrite map_map in IHbody.
      erewrite map_ext in IHbody; [exact IHbody|].
      intros [g σ_i]. reflexivity.
  - (* E_TMatch_PApp_false *)
    intros V σ δ t c n t' pts v' v σs Hrank Hscrut IHscrut Hrange
           Htail IHtail V0 z σ_z elem w_z HV Hlc Hev.
    simpl. eapply E_TMatch_PApp_false.
    + exact Hrank.
    + eapply IHscrut; eauto.
    + exact Hrange.
    + eapply IHtail; eauto.
  - (* ES_nil *)
    intros V V0 z σ_z elem w_z HV Hlc Hev.
    simpl. constructor.
  - (* ES_cons *)
    intros V σ σs t ts v vs Hev' IHev Hts IHts V0 z σ_z elem w_z
           HV Hlc Hev.
    simpl. constructor; [eapply IHev; eauto|eapply IHts; eauto].
Qed.

(** Substituting a locally closed term for a variable has the same effect on
    evaluation as inserting that term's value at the variable. *)
Corollary eval_term_subst_singleton_insert :
  forall Σ A (V : valuation A) x σx elem
         (w : A.(domain) σx) σ t v,
    lc_at [] elem ->
    ⟦ elem : σx ⟧(Σ, A, V) ⇓ w ->
    ⟦ t : σ ⟧(Σ, A, <[x := existT σx w]> V) ⇓ v ->
    ⟦ term_subst {[x := elem]} t : σ ⟧(Σ, A, V) ⇓ v.
Proof.
  intros Σ A V x σx elem w σ t v Hlc Helem Hev.
  destruct (eval_term_subst_singleton_insert_mut_aux Σ A) as [Hev_sub _].
  eapply Hev_sub; [exact Hev | reflexivity | exact Hlc | exact Helem].
Qed.

(** ** Alpha-Renaming the Variable a Context Was Extended At *)

(** Renaming the variable a context was extended at: substituting [TFVar y]
    for [x] moves the evaluation from the [x]-extended context to the
    [y]-extended one, provided [y] is not already free in the term.  Unlike
    [eval_term_open_alpha1] this says nothing about a binder, so it asks
    nothing about local closure — the term is renamed where it stands. *)
Lemma eval_term_subst_TFVar1_alpha :
  forall Σ A (V : valuation A) x y σx (w : A.(domain) σx) σ t v,
    y <> x ->
    y ∉ fv t ->
    ⟦ t : σ ⟧(Σ, A, <[x := existT σx w]> V) ⇓ v ->
    ⟦ term_subst {[x := TFVar y]} t : σ ⟧(Σ, A, <[y := existT σx w]> V) ⇓ v.
Proof.
  intros Σ A V x y σx w σ t v Hyx Hy_t Heval.
  pose proof (eval_weaken1 Σ A (<[x := existT σx w]> V)
    σ t v y σx w Hy_t Heval) as Hweak.
  rewrite (insert_insert_ne V y x _ _ Hyx) in Hweak.
  eapply (eval_term_subst_singleton_insert Σ A
    (<[y := existT σx w]> V) x σx (TFVar y) w σ t v).
  - constructor.
  - apply eval_inserted_TFVar.
  - exact Hweak.
Qed.

(** And back: the substituted term evaluates in the [y]-extended context
    exactly when the original does in the [x]-extended one. *)
Lemma eval_term_subst_TFVar1_alpha_inv :
  forall Σ A (V : valuation A) x y σx (w : A.(domain) σx) σ t v,
    y <> x ->
    y ∉ fv t ->
    ⟦ term_subst {[x := TFVar y]} t : σ ⟧(Σ, A, <[y := existT σx w]> V) ⇓ v ->
    ⟦ t : σ ⟧(Σ, A, <[x := existT σx w]> V) ⇓ v.
Proof.
  intros Σ A V x y σx w σ t v Hyx Hy_t Heval.
  assert (Hx_subst : x ∉ fv (term_subst {[x := TFVar y]} t)).
  { intros Hxfv.
    pose proof (fv_term_subst_singleton_TFVar_subseteq x y t x Hxfv) as Hcases.
    rewrite elem_of_union in Hcases.
    destruct Hcases as [Hcases|Hcases].
    - rewrite elem_of_difference, elem_of_singleton in Hcases. tauto.
    - rewrite elem_of_singleton in Hcases. exact (Hyx (eq_sym Hcases)). }
  pose proof (eval_term_subst_TFVar1_alpha Σ A V y x σx w σ
    (term_subst {[x := TFVar y]} t) v
    (not_eq_sym Hyx) Hx_subst Heval) as Halpha.
  rewrite (term_subst_subst_fresh_singleton x y (TFVar x) t)
    in Halpha by exact Hy_t.
  rewrite term_subst_id_singleton in Halpha.
  exact Halpha.
Qed.

(** The list form: renaming a distinct binder list [xs] to a distinct,
    disjoint binder list [ys] by substitution moves the evaluation from the
    [xs]-extended context to the [ys]-extended one. *)
Lemma eval_term_subst_TFVar_alpha :
  forall Σ A xs ys σs (V : valuation A) σ t v
         (ws : hlist A.(domain) σs),
    length xs = length ys ->
    length xs = length σs ->
    NoDup xs ->
    NoDup ys ->
    (list_to_set xs : gset var) ## (list_to_set ys : gset var) ->
    (list_to_set ys : gset var) ## fv t ->
    lc_at [] t ->
    ⟦ t : σ ⟧(Σ, A, list_to_map (zip xs (hlist_to_list ws)) ∪ V) ⇓ v ->
    ⟦ term_subst (list_to_map (zip xs (map TFVar ys)) : gmap var term) t
      : σ ⟧(Σ, A, list_to_map (zip ys (hlist_to_list ws)) ∪ V) ⇓ v.
Proof.
  intros Σ A xs.
  induction xs as [|x xs IH]; intros ys σs V σ t v ws
    Hlenxy Hlenxσ Hndx Hndy Hdisj Hfresh Hlc Hev.
  - destruct ys as [|y ys]; [|discriminate].
    destruct σs as [|σ0 σs']; [|discriminate].
    hlist_nil ws.
    rewrite term_subst_id_zip. exact Hev.
  - destruct ys as [|y ys]; [discriminate|].
    destruct σs as [|σx σs']; [discriminate|].
    hlist_cons ws.
    simpl in Hlenxy, Hlenxσ.
    apply NoDup_cons in Hndx as [Hxnot Hndx'].
    apply NoDup_cons in Hndy as [Hynot Hndy'].
    assert (Hdisj_tail :
      (list_to_set xs : gset var) ## (list_to_set ys : gset var)) by set_solver.
    assert (Hfresh_tail : (list_to_set ys : gset var) ## fv t) by set_solver.
    assert (Hlenxy' : length xs = length ys) by lia.
    assert (Hlenxσ' : length xs = length σs') by lia.
    assert (Hxys : x ∉ ys) by set_solver.
    assert (Hxnone : (list_to_map (zip xs (hlist_to_list ws)) : valuation A) !! x = None)
      by (apply lookup_list_to_map_zip_None; exact Hxnot).
    assert (Hxnone' : (list_to_map (zip ys (hlist_to_list ws)) : valuation A) !! x = None)
      by (apply lookup_list_to_map_zip_None; exact Hxys).
    (* move the head binder onto the base valuation, and run the tail *)
    cbn [hlist_to_list zip zip_with] in Hev.
    rewrite list_to_map_cons, <- insert_union_l,
      (insert_union_r _ _ _ _ Hxnone) in Hev.
    pose proof (IH ys σs' (<[x := existT σx d]> V)
      σ t v ws Hlenxy' Hlenxσ' Hndx' Hndy' Hdisj_tail
      Hfresh_tail Hlc Hev) as Htail.
    rewrite <- (insert_union_r _ _ _ _ Hxnone') in Htail.
    set (t_tail := term_subst (list_to_map (zip xs (map TFVar ys)) : gmap var term) t) in *.
    assert (Htail_lc : lc_at [] t_tail).
    { subst t_tail. eapply lc_at_term_subst_TFVar; [|exact Hlc].
      intros z u Hu.
      apply elem_of_list_to_map_2 in Hu.
      apply elem_of_lookup_zip_with in Hu as (i & a & b & Heq & _ & Hu).
      injection Heq as -> ->.
      rewrite list_lookup_fmap in Hu.
      destruct (ys !! i) as [yi|] eqn:Hyi; simpl in Hu; [|discriminate].
      injection Hu as <-. eexists. reflexivity. }
    assert (Hx_c : x ∉ fv (term_close [x] 0 t_tail)).
    { rewrite fv_term_close. set_solver. }
    assert (Hy_ttail : y ∉ fv t_tail).
    { subst t_tail. intro Hyfv.
      pose proof (fv_term_subst_subseteq
        (list_to_map (zip xs (map TFVar ys)) : gmap var term)
        (list_to_set ys : gset var) t) as Hsub.
      assert (Hmapfv :
        forall z u,
          (list_to_map (zip xs (map TFVar ys)) : gmap var term) !! z = Some u ->
          fv u ⊆ (list_to_set ys : gset var)).
      { intros z u Hu q Hq.
        apply elem_of_list_to_map_2 in Hu.
        apply elem_of_lookup_zip_with in Hu as (i & a & b & Heq & _ & Hu).
        injection Heq as -> ->.
        rewrite list_lookup_fmap in Hu.
        destruct (ys !! i) as [yi|] eqn:Hyi; simpl in Hu; [|discriminate].
        injection Hu as <-. simpl in Hq. rewrite elem_of_singleton in Hq. subst q.
        rewrite elem_of_list_to_set. apply list_elem_of_lookup. eauto. }
      specialize (Hsub Hmapfv y Hyfv). set_solver. }
    assert (Hy_c : y ∉ fv (term_close [x] 0 t_tail)).
    { rewrite fv_term_close. set_solver. }
    assert (Hxy_ne : x <> y) by set_solver.
    pose proof (eval_term_open_alpha1 Σ A
      (list_to_map (zip ys (hlist_to_list ws)) ∪ V) σ
      (term_close [x] 0 t_tail) v x y σx d
      Hxy_ne Hx_c Hy_c) as Halpha.
    assert (Hopen_x : ⟦ term_open 0 [TFVar x] (term_close [x] 0 t_tail)
                        : σ ⟧(Σ, A,
                          <[x := existT σx d]> (list_to_map (zip ys (hlist_to_list ws)) ∪ V))
                        ⇓ v).
    { rewrite (term_open_close_subst1_nil t_tail x x Htail_lc).
      rewrite term_subst_id_singleton. exact Htail. }
    specialize (Halpha Hopen_x).
    rewrite (term_open_close_subst1_nil t_tail x y Htail_lc) in Halpha.
    cbn [hlist_to_list zip zip_with map].
    rewrite !list_to_map_cons.
    rewrite term_subst_insert_zip_TFVar by auto.
    rewrite <- insert_union_l. exact Halpha.
Qed.

(** ** Alpha-Renaming a Binder List *)

(** Closing over [xs] and reopening at [ys] moves an evaluation from the
    [xs]-extended context to the [ys]-extended one, when the two lists are
    disjoint. *)
Corollary eval_term_open_close_inserts :
  forall Σ A (V : valuation A) σ t v xs ys σs
         (ws : hlist A.(domain) σs),
    length xs = length ys ->
    length xs = length σs ->
    NoDup xs ->
    NoDup ys ->
    (list_to_set xs : gset var) ## (list_to_set ys : gset var) ->
    (list_to_set ys : gset var) ## fv (term_close xs 0 t) ->
    lc_at [] t ->
    ⟦ t : σ ⟧(Σ, A, list_to_map (zip xs (hlist_to_list ws)) ∪ V) ⇓ v ->
    ⟦ term_open 0 (map TFVar ys) (term_close xs 0 t)
      : σ ⟧(Σ, A, list_to_map (zip ys (hlist_to_list ws)) ∪ V) ⇓ v.
Proof.
  intros Σ A V σ t v xs ys σs ws Hlenxy Hlenxσ Hndx Hndy
    Hdisj Hfresh_close Hlc Hev.
  assert (Hlen_map : length xs = length (map TFVar ys))
    by (rewrite length_map; exact Hlenxy).
  rewrite (term_open_close_subst_nil t xs (map TFVar ys) Hlen_map Hlc).
  eapply eval_term_subst_TFVar_alpha; eauto.
  rewrite fv_term_close in Hfresh_close. set_solver.
Qed.

(** Alpha-renaming the binder list of an opened body, when the old and new
    lists are disjoint.  The renaming runs through a substitution, which is
    where the disjointness is needed; [eval_term_open_alpha] lifts it. *)
Lemma eval_term_open_alpha_disjoint :
  forall Σ A (V : valuation A) σ c v xs ys σs (ws : hlist A.(domain) σs),
    length xs = length ys ->
    length xs = length σs ->
    NoDup xs ->
    NoDup ys ->
    (list_to_set xs : gset var) ## (list_to_set ys : gset var) ->
    (list_to_set xs : gset var) ## fv c ->
    (list_to_set ys : gset var) ## fv c ->
    lc_at [length xs] c ->
    ⟦ term_open 0 (map TFVar xs) c
      : σ ⟧(Σ, A, list_to_map (zip xs (hlist_to_list ws)) ∪ V) ⇓ v ->
    ⟦ term_open 0 (map TFVar ys) c
      : σ ⟧(Σ, A, list_to_map (zip ys (hlist_to_list ws)) ∪ V) ⇓ v.
Proof.
  intros Σ A V σ c v xs ys σs ws Hlenxy Hlenxσ Hndx Hndy Hdisj Hx Hy Hlc Hev.
  rewrite <- (term_subst_open_TFVar_rename xs ys c 0 Hlenxy Hndx Hx).
  eapply eval_term_subst_TFVar_alpha; eauto.
  - pose proof (fv_term_open_TFVar_subseteq c 0 xs) as Hsub. set_solver.
  - apply lc_at_term_open_nil.
    + apply Forall_forall. intros u Hu.
      apply list_elem_of_fmap in Hu as (x & -> & _). constructor.
    + rewrite length_map. exact Hlc.
Qed.

(** Alpha-renaming the binder list of an opened body.  The binders of a
    [TLet], and of a [TMatch] arm, may be renamed to any distinct list of the
    same length fresh for the body; the two lists need not be disjoint. *)
Lemma eval_term_open_alpha :
  forall Σ A (V : valuation A) σ c v xs ys σs (ws : hlist A.(domain) σs),
    length xs = length ys ->
    length xs = length σs ->
    NoDup xs ->
    NoDup ys ->
    (list_to_set xs : gset var) ## fv c ->
    (list_to_set ys : gset var) ## fv c ->
    lc_at [length xs] c ->
    ⟦ term_open 0 (map TFVar xs) c
      : σ ⟧(Σ, A, list_to_map (zip xs (hlist_to_list ws)) ∪ V) ⇓ v ->
    ⟦ term_open 0 (map TFVar ys) c
      : σ ⟧(Σ, A, list_to_map (zip ys (hlist_to_list ws)) ∪ V) ⇓ v.
Proof.
  intros Σ A V σ c v xs ys σs ws Hlenxy Hlenxσ Hndx Hndy Hx Hy Hlc Hev.
  (* route the renaming through a list fresh for both, so each hop meets
     [eval_term_open_alpha_disjoint]'s disjointness condition *)
  pose (zs := fresh_strings_of_set "" (length xs)
                (list_to_set xs ∪ list_to_set ys ∪ fv c)).
  assert (Hndz : NoDup zs) by apply NoDup_fresh_strings_of_set.
  assert (Hlenz : length zs = length xs) by apply length_fresh_strings_of_set.
  assert (Hzx : (list_to_set zs : gset var) ## (list_to_set xs : gset var))
    by (apply fresh_strings_of_set_fresh; set_solver).
  assert (Hzy : (list_to_set zs : gset var) ## (list_to_set ys : gset var))
    by (apply fresh_strings_of_set_fresh; set_solver).
  assert (Hzc : (list_to_set zs : gset var) ## fv c)
    by (apply fresh_strings_of_set_fresh; set_solver).
  eapply eval_term_open_alpha_disjoint with (xs := zs) (ys := ys);
    try eassumption; try lia.
  - rewrite Hlenz. exact Hlc.
  - eapply eval_term_open_alpha_disjoint with (xs := xs) (ys := zs);
      try eassumption; try lia.
    symmetry. exact Hzx.
Qed.

(** * Totality *)

(** Walking the arms of a [TMatch] whose scrutinee value was built by [c0].

    Serves both sorting rules for [TMatch]: the arms that fire and the arms
    that are skipped are the same either way, and the two rules differ only in
    what guarantees that some arm fires at all — coverage of the sort's
    constructors for [S_TMatch_PApp], a default arm for
    [S_TMatch_PVar].  That guarantee is the last premise. *)
Lemma eval_TMatch_total :
  forall Σ A (V : valuation A) (L : gset var) pts t δ σ s c0 σs0
         (v' : A.(domain) δ) (vs0 : hlist A.(domain) σs0),
    adt_constructed Σ A ->
    valuation_well_sorted Σ.(sorts) V ->
    s ∈ Σ.(sort_symbols) ->
    sort_top_symbol δ = Some s ->
    c0 ∈ Σ.(constructors_for_sort) s ->
    monomorphic_rank Σ c0 σs0 δ ->
    sort_wf Σ δ ->
    interp_apply A.(domain) (A.(interp) c0 σs0 δ) vs0 = v' ->
    ⟦ t : δ ⟧(Σ, A, V) ⇓ v' ->
    (forall c n t_c, (PApp c n, t_c) ∈ pts -> c ∈ Σ.(constructors_for_sort) s) ->
    (forall c n t_c, (PApp c n, t_c) ∈ pts ->
        exists σs, monomorphic_rank Σ c σs δ /\ length σs = n) ->
    (forall c n t_c σs xs, (PApp c n, t_c) ∈ pts ->
        monomorphic_rank Σ c σs δ -> NoDup xs -> length xs = n ->
        list_to_set xs ## L ->
        list_to_map (zip xs σs) ⊍ Σ ⊢ term_open 0 (map TFVar xs) t_c : σ) ->
    (forall c n t_c σs xs, (PApp c n, t_c) ∈ pts ->
        monomorphic_rank Σ c σs δ -> NoDup xs -> length xs = n ->
        list_to_set xs ## L ->
        forall V0 : valuation A,
          valuation_well_sorted (list_to_map (zip xs σs) ∪ Σ.(sorts)) V0 ->
          exists v, ⟦ term_open 0 (map TFVar xs) t_c : σ ⟧(Σ, A, V0) ⇓ v) ->
    (forall x t_c, x ∉ L -> (PVar, t_c) ∈ pts ->
        <[x := δ]> Σ ⊢ term_open 0 [TFVar x] t_c : σ) ->
    (forall x t_c, x ∉ L -> (PVar, t_c) ∈ pts ->
        forall V0 : valuation A,
          valuation_well_sorted (<[x := δ]> Σ.(sorts)) V0 ->
          exists v, ⟦ term_open 0 [TFVar x] t_c : σ ⟧(Σ, A, V0) ⇓ v) ->
    (exists p t_c, (p, t_c) ∈ pts /\ (p = PVar \/ exists n, p = PApp c0 n)) ->
    exists v, ⟦ TMatch t pts : σ ⟧(Σ, A, V) ⇓ v.
Proof.
  intros Σ A V L pts t δ σ s c0 σs0 v' vs0
    Hadt HV Hs Hhead Hc0 Hrank0 Hwfδ Hbuilt Hscrut
    Harmc Harmrank Hbodyσ Hbody HPVarσ HPVar Hfire.
  revert Harmc Harmrank Hbodyσ Hbody HPVarσ HPVar Hfire.
  induction pts as [|[p t_c] pts' IH];
    intros Harmc Harmrank Hbodyσ Hbody HPVarσ HPVar Hfire.
  - (* no arms left, so nothing fired after all *)
    exfalso. destruct Hfire as (p & tc & Hin & _).
    apply elem_of_nil in Hin. exact Hin.
  - destruct p as [|c n].
    + (* a default arm always fires *)
      pose (x0 := fresh_string_of_set "" (L ∪ fv t_c)).
      assert (Hx0 : x0 ∉ (L ∪ fv t_c)) by apply fresh_string_of_set_fresh.
      assert (Hin0 : (PVar, t_c) ∈ (PVar, t_c) :: pts') by apply list_elem_of_here.
      assert (Hx0_L : x0 ∉ L) by set_solver.
      assert (Hlc : lc_at [length [x0]] t_c).
      { apply lc_at_of_lc_term_open_TFVar.
        eapply term_has_sort_lc.
        apply (HPVarσ x0 t_c Hx0_L Hin0). }
      destruct (HPVar x0 t_c Hx0_L Hin0 (<[x0 := existT δ v']> V)
                  (valuation_well_sorted_insert _ _ _ _ _ _ HV)) as (v & Hv).
      exists v.
      apply E_TMatch_PVar.
      eapply E_TLet with (L := L ∪ fv t_c) (σs := [δ])
        (vs := HCons δ [] v' HNil).
      * constructor; [exact Hscrut | constructor].
      * intros xs Hnd Hlen Hdisj t' V'.
        eapply eval_term_open_alpha with (xs := [x0]) (ws := HCons δ [] v' HNil);
          try assumption.
        -- simpl. simpl in Hlen. lia.
        -- reflexivity.
        -- apply NoDup_singleton.
        -- set_solver.
        -- set_solver.
        -- cbn [hlist_to_list]. rewrite list_to_map_zip_singleton_union. exact Hv.
    + assert (Hhere : (PApp c n, t_c) ∈ (PApp c n, t_c) :: pts')
        by apply list_elem_of_here.
      destruct (decide (c = c0)) as [->|Hne]; cycle 1.
      * (* another constructor built the scrutinee: skip this arm *)
        destruct (Harmrank c n t_c Hhere) as (σsc & Hrankc & _).
        assert (Hrec : exists v, ⟦ TMatch t pts' : σ ⟧(Σ, A, V) ⇓ v).
        { apply IH.
          - intros c1 n1 t1 Hin1. apply (Harmc c1 n1 t1). right. exact Hin1.
          - intros c1 n1 t1 Hin1. apply (Harmrank c1 n1 t1). right. exact Hin1.
          - intros c1 n1 t1 σs1 xs1 Hin1.
            apply (Hbodyσ c1 n1 t1 σs1 xs1). right. exact Hin1.
          - intros c1 n1 t1 σs1 xs1 Hin1.
            apply (Hbody c1 n1 t1 σs1 xs1). right. exact Hin1.
          - intros x1 t1 Hx1 Hin1. apply (HPVarσ x1 t1 Hx1). right. exact Hin1.
          - intros x1 t1 Hx1 Hin1. apply (HPVar x1 t1 Hx1). right. exact Hin1.
          - (* what fires is not this arm, so it is still ahead *)
            destruct Hfire as (p1 & t1 & Hin1 & Hp1).
            exists p1, t1. split; [|exact Hp1].
            apply elem_of_cons in Hin1 as [Heq1|Hin1]; [|exact Hin1].
            exfalso. injection Heq1 as Heq1 _.
            destruct Hp1 as [Hp1|(n1 & Hp1)]; rewrite Hp1 in Heq1;
              [discriminate|].
            injection Heq1 as Heq1 _. apply Hne. symmetry. exact Heq1. }
        destruct Hrec as (v & Hv).
        exists v.
        apply (E_TMatch_PApp_false Σ A V σ δ t c n t_c pts' v' v σsc);
          [exact Hrankc | exact Hscrut | | exact Hv].
        intros vs F Hcontra. subst F.
        apply Hne.
        eapply (adt_constructed_disjoint Hadt c c0 σsc σs0 δ s);
          try eassumption.
        -- apply (Harmc c n t_c Hhere).
        -- rewrite Hcontra. symmetry. exact Hbuilt.
      * (* this arm's constructor built the scrutinee: it fires *)
        assert (Hc0con : c0 ∈ Σ.(constructors))
          by (eapply Σ.(constructors_for_sort_wf); eassumption).
        destruct (Harmrank c0 n t_c Hhere) as (σsc & Hrankc & Hlenc).
        assert (Hσeq : σsc = σs0)
          by (eapply monomorphic_rank_constructor_args_eq; eassumption).
        subst σsc.
        (* each selector application evaluates, so the arm's [TLet] has an
           argument hlist *)
        assert (Hgslen : length (Σ.(selectors_for_constructor) c0) = length σs0)
          by (eapply monomorphic_rank_selector_length; eassumption).
        assert (Hsellen : length σs0
                  = length (map (fun '(g, σ_i) => TApp g (Some σ_i) [t])
                              (zip (Σ.(selectors_for_constructor) c0) σs0))).
        { rewrite length_map, length_zip_with. lia. }
        assert (Hselpt : forall i t_i σ_i,
                   map (fun '(g, σ_i) => TApp g (Some σ_i) [t])
                     (zip (Σ.(selectors_for_constructor) c0) σs0) !! i = Some t_i ->
                   σs0 !! i = Some σ_i ->
                   exists w, ⟦ t_i : σ_i ⟧(Σ, A, V) ⇓ w).
        { intros i t_i σ_i Hti Hσi.
          rewrite list_lookup_fmap in Hti.
          destruct (zip (Σ.(selectors_for_constructor) c0) σs0 !! i)
            as [[g σ_j]|] eqn:Hz; simpl in Hti; [|discriminate].
          injection Hti as <-.
          rewrite lookup_zip_with in Hz.
          destruct (Σ.(selectors_for_constructor) c0 !! i) as [g'|] eqn:Hg;
            simpl in Hz; [|discriminate].
          rewrite Hσi in Hz. simpl in Hz. injection Hz as <- <-.
          exists (interp_apply A.(domain) (A.(interp) g' [δ] σ_i)
                    (HCons δ [] v' HNil)).
          eapply E_TApp with (σs := [δ]).
          - constructor; [exact Hscrut|constructor].
          - apply option_Forall_Some. reflexivity.
          - eapply monomorphic_rank_selector; eassumption.
          - reflexivity. }
        destruct (evals_intro Σ A V σs0 _ Hsellen Hselpt)
          as (selvals & Hselvals).
        (* the arm's body evaluates at one run of binders, and alpha-renaming
           carries that to every other *)
        pose (xs0 := fresh_strings_of_set "" (length σs0) (L ∪ fv t_c)).
        assert (Hnd0 : NoDup xs0) by apply NoDup_fresh_strings_of_set.
        assert (Hlen0 : length xs0 = length σs0)
          by apply length_fresh_strings_of_set.
        assert (Hfr0 : (list_to_set xs0 : gset var) ## (L ∪ fv t_c))
          by (apply fresh_strings_of_set_fresh; set_solver).
        assert (Hlen0n : length xs0 = n) by lia.
        assert (Hdisj0 : list_to_set xs0 ## L) by set_solver.
        assert (Hlc : lc_at [length xs0] t_c).
        { apply lc_at_of_lc_term_open_TFVar.
          eapply term_has_sort_lc.
          apply (Hbodyσ c0 n t_c σs0 xs0 Hhere Hrank0 Hnd0 Hlen0n Hdisj0). }
        pose proof (Hbody c0 n t_c σs0 xs0 Hhere Hrank0 Hnd0 Hlen0n Hdisj0)
          as Hb.
        destruct (Hb (list_to_map (zip xs0 (hlist_to_list selvals)) ∪ V)
                    (valuation_well_sorted_union_lookup_list_to_map
                       _ _ _ _ _ selvals HV)) as (v & Hv).
        exists v.
        apply (E_TMatch_PApp_true Σ A V σ δ t c0 n t_c pts' v' v σs0);
          [exact Hrank0 | exact Hscrut | exists vs0; exact Hbuilt | ].
        eapply E_TLet with (L := L ∪ fv t_c) (σs := σs0) (vs := selvals);
          [exact Hselvals |].
        intros xs Hnd Hlen Hdisj t' V'.
        eapply eval_term_open_alpha with (xs := xs0); try assumption.
        -- rewrite Hlen0, Hsellen. symmetry. exact Hlen.
        -- set_solver.
        -- set_solver.
Qed.

(** Totality at a signature carries to every signature agreeing with it except
    on sorts, for the valuations the first one's sorts admit. *)
Local Lemma eval_total_signatures_agree_except_sorts :
  forall Σ Σ' (A : structure) t σ,
    signatures_agree_except_sorts Σ' Σ ->
    adt_constructed Σ A ->
    (forall V : valuation A,
        adt_constructed Σ' A ->
        valuation_well_sorted Σ'.(sorts) V ->
        exists v : A.(domain) σ, ⟦ t : σ ⟧(Σ', A, V) ⇓ v) ->
    forall V : valuation A,
      valuation_well_sorted Σ'.(sorts) V ->
      exists v : A.(domain) σ, ⟦ t : σ ⟧(Σ, A, V) ⇓ v.
Proof.
  intros Σ Σ' A t σ Hsym Hadt Htot V HV.
  destruct (Htot V
              (adt_constructed_signatures_agree_except_sorts _ _ _
                 (signatures_agree_except_sorts_sym _ _ Hsym) Hadt)
              HV) as (v & Hv).
  exists v. exact (proj1 (eval_cong_signature _ _ _ _ _ _ _ Hsym) Hv).
Qed.

(** Evaluation is total on well-sorted terms, under a valuation for their
    signature's variables.

    The premise is the condition SMT-LIB puts on a model of a signature that
    declares datatypes, in the form that survives signature composition: every
    value of an ADT sort is built by exactly one of that sort's constructors.
    A [match] with no variable pattern carries no default arm, so nothing
    weaker says that one of its arms fires.  It asks nothing of a signature
    declaring no datatype, where no [TMatch] is well-sorted anyway.
    [adt_constructed_of_adt_axioms] is what a model of an ADT theory
    discharges it with. *)
Theorem eval_total :
  forall Σ (A : structure) (V : valuation A) t σ,
    adt_constructed Σ A ->
    Σ ⊢ t : σ ->
    valuation_well_sorted Σ.(sorts) V ->
    exists v : A.(domain) σ, ⟦ t : σ ⟧(Σ, A, V) ⇓ v.
Proof.
  intros Σ A V t σ Hadt Hsort HV. revert V Hadt HV.
  induction Hsort; intros V Hadt HV.
  - (* S_TFVar *)
    destruct (valuation_well_sorted_lookup _ _ _ _ _ HV H) as [v Hv].
    exists v. apply E_TFVar. exact Hv.
  - (* S_TApp *)
    destruct (evals_intro Σ A V σs ts H1
                (fun i t_i σ_i Hts Hσs => H3 i t_i σ_i Hts Hσs V Hadt HV)) as (vs & Hvs).
    exists (interp_apply A.(domain) (A.(interp) f σs σ) vs).
    eapply E_TApp; [exact Hvs | apply option_Forall_None | exact H | reflexivity].
  - (* S_TApp_annotated *)
    destruct (evals_intro Σ A V σs ts H0
                (fun i t_i σ_i Hts Hσs => H2 i t_i σ_i Hts Hσs V Hadt HV)) as (vs & Hvs).
    exists (interp_apply A.(domain) (A.(interp) f σs σ) vs).
    eapply E_TApp;
      [exact Hvs | apply option_Forall_Some; reflexivity | exact H | reflexivity].
  - (* S_TLambda *)
    pose (x0 := fresh_string_of_set "" (L ∪ fv t)).
    assert (Hx0 : x0 ∉ (L ∪ fv t)) by apply fresh_string_of_set_fresh.
    assert (Hx0_L : x0 ∉ L) by set_solver.
    (* pick a body value for every argument *)
    assert (Hchoice : forall w : A.(domain) σ1,
               { u : A.(domain) σ2
               | ⟦ term_open 0 [TFVar x0] t
                   : σ2 ⟧(Σ, A, <[x0 := existT σ1 w]> V) ⇓ u }).
    { intros w. apply constructive_indefinite_description.
      apply (eval_total_signatures_agree_except_sorts Σ _ A _ _
             (signatures_agree_except_sorts_insert Σ x0 σ1) Hadt
             (H2 x0 Hx0_L) (<[x0 := existT σ1 w]> V)
             (valuation_well_sorted_insert _ _ _ _ _ _ HV)). }
    exists (cast_sym (A.(domain_σ_map) σ1 σ2) (fun w => proj1_sig (Hchoice w))).
    eapply E_TLambda with (L := L ∪ fv t ∪ {[x0]}).
    intros x Hx t' w.
    rewrite cast_cast_sym.
    eapply eval_term_open_alpha1 with (x := x0);
      [ set_solver | set_solver | set_solver | ].
    exact (proj2_sig (Hchoice w)).
  - (* S_TExists *)
    pose (x0 := fresh_string_of_set "" (L ∪ fv t)).
    assert (Hx0 : x0 ∉ (L ∪ fv t)) by apply fresh_string_of_set_fresh.
    assert (Hx0_L : x0 ∉ L) by set_solver.
    destruct (classic (exists w : A.(domain) σ,
                  ⟦ term_open 0 [TFVar x0] t
                    : σ_bool ⟧(Σ, A, <[x0 := existT σ w]> V)
                    ⇓ cast_sym A.(domain_σ_bool) true))
      as [(w & Hw)|Hno].
    + exists (cast_sym A.(domain_σ_bool) true).
      eapply E_TExists_true with (L := L ∪ fv t ∪ {[x0]}) (v' := w).
      intros x Hx t'.
      eapply eval_term_open_alpha1 with (x := x0);
        [set_solver|set_solver|set_solver|exact Hw].
    + exists (cast_sym A.(domain_σ_bool) false).
      eapply E_TExists_false with (L := L ∪ fv t ∪ {[x0]}).
      intros x Hx w t'.
      destruct (eval_total_signatures_agree_except_sorts Σ _ A _ _
                (signatures_agree_except_sorts_insert Σ x0 σ) Hadt
                (H2 x0 Hx0_L) (<[x0 := existT σ w]> V)
                (valuation_well_sorted_insert _ _ _ _ _ _ HV)) as (u & Hu).
      destruct (cast_sym_true_or_false A.(domain_σ_bool) u) as [ -> | -> ].
      * exfalso. apply Hno. exists w. exact Hu.
      * eapply eval_term_open_alpha1 with (x := x0);
          [set_solver|set_solver|set_solver|exact Hu].
  - (* S_TForall *)
    pose (x0 := fresh_string_of_set "" (L ∪ fv t)).
    assert (Hx0 : x0 ∉ (L ∪ fv t)) by apply fresh_string_of_set_fresh.
    assert (Hx0_L : x0 ∉ L) by set_solver.
    destruct (classic (exists w : A.(domain) σ,
                  ⟦ term_open 0 [TFVar x0] t
                    : σ_bool ⟧(Σ, A, <[x0 := existT σ w]> V)
                    ⇓ cast_sym A.(domain_σ_bool) false))
      as [(w & Hw)|Hno].
    + exists (cast_sym A.(domain_σ_bool) false).
      eapply E_TForall_false with (L := L ∪ fv t ∪ {[x0]}) (v' := w).
      intros x Hx t'.
      eapply eval_term_open_alpha1 with (x := x0);
        [set_solver|set_solver|set_solver|exact Hw].
    + exists (cast_sym A.(domain_σ_bool) true).
      eapply E_TForall_true with (L := L ∪ fv t ∪ {[x0]}).
      intros x Hx w t'.
      destruct (eval_total_signatures_agree_except_sorts Σ _ A _ _
                (signatures_agree_except_sorts_insert Σ x0 σ) Hadt
                (H2 x0 Hx0_L) (<[x0 := existT σ w]> V)
                (valuation_well_sorted_insert _ _ _ _ _ _ HV)) as (u & Hu).
      destruct (cast_sym_true_or_false A.(domain_σ_bool) u) as [ -> | -> ].
      * eapply eval_term_open_alpha1 with (x := x0);
          [set_solver|set_solver|set_solver|exact Hu].
      * exfalso. apply Hno. exists w. exact Hu.
  - (* S_TLet *)
    destruct (evals_intro Σ A V σs ts H
                (fun i t_i σ_i Hts Hσs => H1 i t_i σ_i Hts Hσs V Hadt HV)) as (vs & Hvs).
    pose (xs0 := fresh_strings_of_set "" (length ts) (L ∪ fv t)).
    assert (Hnd0 : NoDup xs0) by apply NoDup_fresh_strings_of_set.
    assert (Hlen0 : length xs0 = length ts) by apply length_fresh_strings_of_set.
    assert (Hfresh0 : (list_to_set xs0 : gset var) ## (L ∪ fv t))
      by (apply fresh_strings_of_set_fresh; set_solver).
    assert (Hlen0σ : length xs0 = length σs) by (rewrite Hlen0; symmetry; exact H).
    assert (Hdisj0 : list_to_set xs0 ## L) by set_solver.
    assert (Hlc : lc_at [length xs0] t).
    { apply lc_at_of_lc_term_open_TFVar.
      eapply term_has_sort_lc.
      apply (H2 xs0 Hnd0 Hlen0 Hdisj0). }
    pose proof (eval_total_signatures_agree_except_sorts Σ _ A _ _
                (signatures_agree_except_sorts_add_sorts Σ _) Hadt
                (H3 xs0 Hnd0 Hlen0 Hdisj0)) as Hbody.
    destruct (Hbody (list_to_map (zip xs0 (hlist_to_list vs)) ∪ V)
                (valuation_well_sorted_union_lookup_list_to_map _ _ _ _ _ vs HV))
      as (v0 & Hv0).
    exists v0.
    eapply E_TLet with (L := L ∪ fv t) (vs := vs); [exact Hvs|].
    intros xs Hnd Hlen Hdisj t' V'.
    eapply eval_term_open_alpha with (xs := xs0);
      try eassumption; try (rewrite Hlen0; symmetry; exact Hlen);
      set_solver.
  - (* S_TMatch_PApp *)
    destruct (IHHsort V Hadt HV) as (v' & Hv').
    destruct (adt_constructed_domain Hadt δ v' H)
      as (c0 & σs0 & s0 & vs0 & Hs0 & Hhead0 & Hc0 & Hrank0 & Hbuilt).
    assert (Hss : s0 = s) by congruence. subst s0.
    (* [ps] and [cs] are local definitions of the rule; restate the two
       coverage premises in unfolded form, which conversion gives for free *)
    assert (H1' : (list_to_set (omap pattern_constructor (map fst pts)) : gset func)
                  = Σ.(constructors_for_sort) s) by exact H1.
    assert (H2' : size (list_to_set (omap pattern_constructor (map fst pts))
                        : gset func)
                  = length (map fst pts)) by exact H2.
    assert (HnoPVar : forall t_c, (PVar, t_c) ∉ pts).
    { intros t_c Hin.
      apply (exact_coverage_no_PVar (map fst pts)); [exact H2'|].
      apply list_elem_of_fmap. exists (PVar, t_c). split; [reflexivity|exact Hin]. }
    assert (Harmc : forall c n t_c, (PApp c n, t_c) ∈ pts ->
                      c ∈ Σ.(constructors_for_sort) s).
    { intros c n t_c Hin. rewrite <- H1'.
      apply elem_of_list_to_set. apply list_elem_of_omap.
      exists (PApp c n). split; [|reflexivity].
      apply list_elem_of_fmap. exists (PApp c n, t_c).
      split; [reflexivity|exact Hin]. }
    (* coverage is what says the scrutinee's constructor has an arm *)
    assert (Hfire : exists p t_c, (p, t_c) ∈ pts
                      /\ (p = PVar \/ exists n, p = PApp c0 n)).
    { assert (Hc0cs : c0 ∈ (list_to_set (omap pattern_constructor (map fst pts))
                            : gset func)) by (rewrite H1'; exact Hc0).
      apply elem_of_list_to_set, list_elem_of_omap in Hc0cs as (p & Hp & Hpc).
      destruct p as [|c n]; simpl in Hpc; [discriminate|].
      injection Hpc as ->.
      apply list_elem_of_fmap in Hp as ((p1 & t_c) & Heq & Hin).
      simpl in Heq. subst p1.
      exists (PApp c0 n), t_c. split; [exact Hin|]. right. exists n. reflexivity. }
    pose proof (proj1 (adt_spec_of_adt _ _ H)) as Hwfδ.
    eapply (eval_TMatch_total Σ A V L pts t δ σ s c0 σs0 v' vs0 Hadt HV);
      try eassumption.
    + intros c n t_c σs xs Hin Hrank Hnd Hlen Hdisj.
      exact (eval_total_signatures_agree_except_sorts Σ _ A _ _
             (signatures_agree_except_sorts_add_sorts Σ _) Hadt
             (H4 c n t_c σs xs Hin Hrank Hnd Hlen Hdisj)).
    + intros x t_c Hx Hin. destruct (HnoPVar t_c Hin).
    + intros x t_c Hx Hin. destruct (HnoPVar t_c Hin).
  - (* S_TMatch_PVar *)
    destruct (IHHsort V Hadt HV) as (v' & Hv').
    destruct (adt_constructed_domain Hadt δ v' H)
      as (c0 & σs0 & s0 & vs0 & Hs0 & Hhead0 & Hc0 & Hrank0 & Hbuilt).
    assert (Hss : s0 = s) by congruence. subst s0.
    assert (H1' : (list_to_set (omap pattern_constructor (map fst pts)) : gset func)
                  ⊆ Σ.(constructors_for_sort) s) by exact H1.
    assert (Harmc : forall c n t_c, (PApp c n, t_c) ∈ pts ->
                      c ∈ Σ.(constructors_for_sort) s).
    { intros c n t_c Hin. apply H1'.
      apply elem_of_list_to_set. apply list_elem_of_omap.
      exists (PApp c n). split; [|reflexivity].
      apply list_elem_of_fmap. exists (PApp c n, t_c).
      split; [reflexivity|exact Hin]. }
    (* here it is the default arm that fires, if no [PApp] arm does first *)
    assert (Hfire : exists p t_c, (p, t_c) ∈ pts
                      /\ (p = PVar \/ exists n, p = PApp c0 n)).
    { assert (HPV : PVar ∈ map fst pts) by exact H2.
      apply list_elem_of_fmap in HPV as ((p1 & t_c) & Heq & Hin).
      simpl in Heq. subst p1.
      exists PVar, t_c. split; [exact Hin|]. left. reflexivity. }
    pose proof (proj1 (adt_spec_of_adt _ _ H)) as Hwfδ.
    eapply (eval_TMatch_total Σ A V L pts t δ σ s c0 σs0 v' vs0 Hadt HV);
      try eassumption.
    + intros c n t_c σs xs Hin Hrank Hnd Hlen Hdisj.
      exact (eval_total_signatures_agree_except_sorts Σ _ A _ _
             (signatures_agree_except_sorts_add_sorts Σ _) Hadt
             (H4 c n t_c σs xs Hin Hrank Hnd Hlen Hdisj)).
    + intros x t_c Hx Hin.
      exact (eval_total_signatures_agree_except_sorts Σ _ A _ _
             (signatures_agree_except_sorts_insert Σ x δ) Hadt
             (H6 x t_c Hx Hin)).
Qed.



(** * Satisfaction *)

(** A formula holds in a model under a valuation when every instance of it
    evaluates to true.  This is Definition 11's first rule, which gives a
    formula writing sort parameters its meaning: the parameters are schematic,
    standing for every monomorphic sort the signature has, so what a formula
    says can depend on which sorts those are.  A parameter-free formula is its
    own only instance, so for it this is evaluation to true
    ([holds_iff_eval]).

    The standard also asks [ϕ] itself to be well sorted at [Bool], under a
    reading of the sorting rules at polymorphic sorts.  The sorting judgment
    here is monomorphic, and an instance that is not well sorted has no value,
    so a formula holds only if every instance is well sorted
    ([polymorphic_term_has_sort]).  That is how the
    examples of §3.6 read a polymorphic assertion, and it does not rely on the
    claim after Definition 3 that every instance of a well-sorted term is well
    sorted, which overloading falsifies. *)
Definition holds (T : theory) (A : structure) (V : valuation A) (ϕ : term)
  : Prop :=
  forall θ, monomorphic_sort_subst T.(Σ) ϕ θ ->
    ⟦ term_sort_subst θ ϕ : σ_bool ⟧(T.(Σ), A, V)
      ⇓ cast_sym A.(domain_σ_bool) true.

Theorem holds_iff_eval : forall T A V ϕ,
    pars ϕ = ∅ ->
    holds T A V ϕ <->
    ⟦ ϕ : σ_bool ⟧(T.(Σ), A, V) ⇓ cast_sym A.(domain_σ_bool) true.
Proof.
  intros T A V ϕ Hpars. split.
  - intros Hholds. rewrite <- (term_sort_subst_empty ϕ).
    apply Hholds. split; [by rewrite dom_empty_L, Hpars | apply map_Forall_empty].
  - intros Heval θ [Hdom _]. rewrite Hpars in Hdom.
    apply dom_empty_inv_L in Hdom as ->. by rewrite term_sort_subst_empty.
Qed.

(** A set of formulae is satisfiable in the theory [T] when one model of [T]
    and one valuation for the signature's variables make every one of them
    hold.  This is the satisfiability half of Definition 14, generalised from
    the standard's single sentence to a finite set.

    The signature's variable sorts [T.(Σ).(sorts)] enter only here, through
    [valuation_well_sorted]: [Φ] is read against the sorts the signature
    declares for its variables. *)
Definition sat (T : theory) (Φ : gset term) : Prop :=
  exists A (V : valuation A),
    T.(models) A /\ valuation_well_sorted T.(Σ).(sorts) V /\
    forall ϕ, ϕ ∈ Φ -> holds T A V ϕ.

(** The entailment half of Definition 14: [Γ] T-entails [ϕ] when every model
    of [T] satisfying all of [Γ] satisfies [ϕ] as well, written [Γ ⊨T ϕ] in
    the standard.  Valuations are paired with models as they are in [sat],
    since terms here may have free variables where the standard's are
    sentences, and they range over valuations for the signature's variables:
    a valuation that leaves one of [ϕ]'s variables undefined would evaluate
    [ϕ] to nothing.

    Validity is the [Γ = ∅] case.  The standard does not name it separately
    and neither does this.

    [Γ ⊨[ T ] ϕ] and [~ sat T ({[not_ ϕ]} ∪ Γ)] are not interchangeable:
    the first implies the second by [eval_not] and [eval_deterministic], but
    the converse needs [ϕ] to evaluate to something, which is [eval_total] and
    so classical.  At a [ϕ] writing sort parameters the converse fails
    outright, since [not_ ϕ] holds only if every instance of [ϕ] is false
    ([SMTLIB.tests.UnitTests.not_sat_not_at_most_two]).  They are stated here
    as separate facts for that reason. *)
Definition entails (T : theory) (Γ : gset term) (ϕ : term) : Prop :=
  forall A (V : valuation A),
    T.(models) A ->
    valuation_well_sorted T.(Σ).(sorts) V ->
    (forall ψ, ψ ∈ Γ -> holds T A V ψ) ->
    holds T A V ϕ.

(** [Γ ⊨[ T ] ϕ] is Definition 14's [Γ ⊨_T ϕ]; [⊨] is [\models]. *)
Notation "Γ ⊨[ T ] ϕ" := (entails T Γ ϕ)
  (at level 70, T at level 200, no associativity) : smt_scope.

(** Satisfaction as it reads on monomorphic formulae: one model and one
    valuation under which every formula evaluates to true, with no instances
    to range over.  On parameter-free formulae, and so on well-sorted ones
    ([term_has_sort_pars_empty]), it is [sat] ([sat_iff_monomorphic_sat]),
    which makes it the form to work in for a consumer that only builds
    well-sorted formulae. *)
Definition monomorphic_sat (T : theory) (Φ : gset term) : Prop :=
  exists A (V : valuation A),
    T.(models) A /\ valuation_well_sorted T.(Σ).(sorts) V /\
    forall ϕ, ϕ ∈ Φ ->
      ⟦ ϕ : σ_bool ⟧(T.(Σ), A, V) ⇓ cast_sym A.(domain_σ_bool) true.

Corollary sat_iff_monomorphic_sat : forall T Φ,
    (forall ϕ, ϕ ∈ Φ -> pars ϕ = ∅) ->
    sat T Φ <-> monomorphic_sat T Φ.
Proof.
  intros T Φ Hpars. split.
  - intros (A & V & HA & HV & HΦ). exists A, V. split_and!; [exact HA | exact HV |].
    intros ϕ Hϕ. apply (holds_iff_eval T A V ϕ (Hpars ϕ Hϕ)), HΦ, Hϕ.
  - intros (A & V & HA & HV & HΦ). exists A, V. split_and!; [exact HA | exact HV |].
    intros ϕ Hϕ. apply (holds_iff_eval T A V ϕ (Hpars ϕ Hϕ)), HΦ, Hϕ.
Qed.

(** Entailment as it reads on monomorphic formulae, and its agreement with
    [entails] on parameter-free premises and conclusion. *)
Definition monomorphic_entails (T : theory) (Γ : gset term) (ϕ : term) : Prop :=
  forall A (V : valuation A),
    T.(models) A ->
    valuation_well_sorted T.(Σ).(sorts) V ->
    (forall ψ, ψ ∈ Γ ->
       ⟦ ψ : σ_bool ⟧(T.(Σ), A, V) ⇓ cast_sym A.(domain_σ_bool) true) ->
    ⟦ ϕ : σ_bool ⟧(T.(Σ), A, V) ⇓ cast_sym A.(domain_σ_bool) true.

Corollary entails_iff_monomorphic_entails : forall T Γ ϕ,
    (forall ψ, ψ ∈ Γ -> pars ψ = ∅) ->
    pars ϕ = ∅ ->
    Γ ⊨[ T ] ϕ <-> monomorphic_entails T Γ ϕ.
Proof.
  intros T Γ ϕ HΓ Hϕ. split.
  - intros Hentails A V HA HV HΓ_eval.
    apply (holds_iff_eval T A V ϕ Hϕ), Hentails; [exact HA | exact HV |].
    intros ψ Hψ. apply (holds_iff_eval T A V ψ (HΓ ψ Hψ)), HΓ_eval, Hψ.
  - intros Heval A V HA HV HΓ_holds.
    apply (holds_iff_eval T A V ϕ Hϕ), Heval; [exact HA | exact HV |].
    intros ψ Hψ. apply (holds_iff_eval T A V ψ (HΓ ψ Hψ)), HΓ_holds, Hψ.
Qed.

(** Both facts below are relative to [Γ] being satisfiable at all: entailment
    from an unsatisfiable [Γ] says nothing, and [sat T ∅] is the special case
    saying [T] has a model.  Stating them once is what keeps a consumer from
    restating the consistency premise per formula. *)
Theorem entails_sat : forall T Γ ϕ,
    sat T Γ -> Γ ⊨[ T ] ϕ -> sat T ({[ ϕ ]} ∪ Γ).
Proof.
  intros T Γ ϕ (A & V & Hmodels & HV & HΓ) Hentails.
  exists A, V. split; [exact Hmodels |]. split; [exact HV |].
  intros ψ Hψ. apply elem_of_union in Hψ as [Hψ | Hψ].
  - apply elem_of_singleton in Hψ as ->. by apply Hentails.
  - by apply HΓ.
Qed.

Corollary not_sat_not_entails : forall T Γ ϕ,
    sat T Γ -> ~ sat T ({[ ϕ ]} ∪ Γ) -> ~ Γ ⊨[ T ] ϕ.
Proof.
  intros T Γ ϕ HΓ Hunsat Hentails. apply Hunsat. by apply entails_sat.
Qed.

(** The three cases a formula can fall into, relative to premises [Γ] that
    are satisfiable at all: [ϕ] follows from [Γ], [ϕ] is inconsistent with
    [Γ], or neither.  Each case pins both coordinates, so the three are
    visibly exclusive — the pairs are (true, true), (false, false) and
    (false, true) — and no axiom is needed for that: the first case's second
    component is [entails_sat], the second case's first is
    [not_sat_not_entails].

    That the three are *exhaustive* is excluded middle on two propositions,
    and is the only classical step in the proof.  Note what it does not need:
    [eval_total], and so nothing about whether [ϕ] evaluates at all.  That
    makes this cheaper than the [entails]/[~ sat] duality across a negated
    formula, which does need it. *)
Theorem entails_trichotomy : forall T Γ ϕ,
    sat T Γ ->
    (Γ ⊨[ T ] ϕ /\ sat T ({[ ϕ ]} ∪ Γ))
    \/ (~ Γ ⊨[ T ] ϕ /\ ~ sat T ({[ ϕ ]} ∪ Γ))
    \/ (~ Γ ⊨[ T ] ϕ /\ sat T ({[ ϕ ]} ∪ Γ)).
Proof.
  intros T Γ ϕ HΓ.
  destruct (classic (Γ ⊨[ T ] ϕ)) as [Hentails | Hentails].
  - left. split; [exact Hentails | by apply entails_sat].
  - destruct (classic (sat T ({[ ϕ ]} ∪ Γ))) as [Hsat | Hsat].
    + right; right. split; assumption.
    + right; left. split; assumption.
Qed.
