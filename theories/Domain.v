(** * SMTLIB.Domain : Building a Model's Domain *)

(** A [structure] fixes one [domain : sort -> Type] that every theory component
    constrains at once.  [Theory.v] explains why that cannot be built
    componentwise: [pretheory_compose] conjoins the two model predicates at a
    single structure, and [SMTLIB.Theory.Seq] alone asks for
    [domain (τ_seq σ) = list (domain σ)] at sorts it has never heard of.  So
    the domain is chosen first, and only the interpretation composes.  This
    file is that choice, for any signature whose stack closes with
    [theory_init_seq].

    What a domain does at the *nullary* sort symbols is the caller's business.
    Which of them a signature declares is up to the signature, and which types
    they must denote is up to the theory components it is built from: a stack
    without [SMTLIB.Theory.Strings] pins nothing at [σ_string], and one with a
    component this library has never heard of pins something here unknown.  So
    the construction takes that assignment as a parameter, [base], and extends
    it through the three sort constructors any stack reaching
    [SMTLIB.Theory.Seq] constrains.  It meets, simultaneously:

    - [domain (SApp s []) = base s], away from the datatypes;
    - [domain (τ_map σ1 σ2) = domain σ1 -> domain σ2] ([structure] itself);
    - [domain (τ_seq σ) = list (domain σ)] ([SMTLIB.Theory.Seq]);
    - [domain δ = seq_ground_term Σ (fun σ _ => domain σ) δ] at every datatype
      sort ([seq_adt_axioms]).

    The last is not a fixpoint equation to be solved up to isomorphism: it asks
    the domain to *be* that inductive, on the nose.

    A caller combining several theories supplies as [base] the domains its
    theories pin, and reads the equations those theories owe off
    [sort_domain_base]. *)

From Stdlib Require Import FunctionalExtensionality.
From SMTLIB Require Import Utils Symbols Term Signature Theory.
From SMTLIB.Theory Require Import Seq.

(** ** The Two Passes

    The obstruction is that the datatype equation defines the domain at [δ]
    from the domain at the generator sorts, which is not a subterm relation —
    the generators of [δ]'s free algebra are sorts unrelated to [δ].  The way
    round is to notice that the algebra consults its generator parameter *only*
    at generator sorts, so a first pass that is correct there suffices to build
    it, and the second pass can then agree with the first exactly where the
    difference would show.

    - [adt_free_domain] is the domain a signature with no datatypes would
      have, which is the correct one at every [adt_free] sort and a lie
      elsewhere;
    - [sort_domain] is the real thing: the free algebra over
      [adt_free_domain] at a datatype sort, and [adt_free_domain]'s own
      clauses elsewhere.

    [sort_domain_adt_free] is the step the whole construction rests on: the
    two agree at every [adt_free] sort, hence at every [generator_sort].  It is
    provable only because [SMTLIB.Theory.Seq]'s generators are the
    *datatype-free* sorts rather than Definition 9(3)'s "every sort that is not
    a datatype".  Under the latter [τ_map δ δ] is a generator sort, where the
    first pass gives [unit -> unit] and the second gives
    [sort_domain δ -> sort_domain δ]; the two passes would have no sound step
    there.  See [domain_gen] in [Theory.v] for that argument in full. *)

Section DomainConstruction.

  (** [base] is total in the sort symbol rather than restricted to [Σ]'s own,
      because a sort is a symbol applied to arguments and nothing here knows
      which symbols are declared.  At a symbol the caller does not care about,
      any inhabited type will do. *)
  Context (Σ : signature) (base : sortsymb -> Type).

  (** Pass one.  Structural in the sort, and blind to the signature: the point
      is that it can be defined before any datatype's domain is.  A datatype
      sort is nullary here like any other, so it lands on [base], which is the
      deliberate lie [sort_domain] overrides. *)
  Fixpoint adt_free_domain (σ : sort) : Type :=
    match σ with
    | SParam _ => unit
    | SApp s [] => base s
    | SApp s [σ1] =>
        if decide (s = s_seq) then list (adt_free_domain σ1) else unit
    | SApp s [σ1; σ2] =>
        if decide (s = s_map)
        then (adt_free_domain σ1 -> adt_free_domain σ2)
        else unit
    | SApp _ _ => unit
    end.

  (** Pass two.  The datatype test comes first, so the equation it owes holds
      by [decide_True] alone; every other equation owes a proof that its sort
      is not a datatype, which is a condition on [Σ] and the caller's to
      discharge. *)
  Fixpoint sort_domain (σ : sort) : Type :=
    if decide (adt Σ σ)
    then seq_ground_term Σ (fun τ _ => adt_free_domain τ) σ
    else
      match σ with
      | SParam _ => unit
      | SApp s [] => base s
      | SApp s [σ1] =>
          if decide (s = s_seq) then list (sort_domain σ1) else unit
      | SApp s [σ1; σ2] =>
          if decide (s = s_map)
          then (sort_domain σ1 -> sort_domain σ2)
          else unit
      | SApp _ _ => unit
      end.

  (** ** The Agreement

      Where no datatype is mentioned the two passes are the same function.
      The induction is over the sort rather than over the [adt_free]
      derivation, since [adt_free_app] holds its premises in a [Forall] and the
      generated scheme offers no hypothesis about them. *)
  Lemma sort_domain_adt_free : forall σ,
      adt_free Σ σ -> sort_domain σ = adt_free_domain σ.
  Proof.
    induction σ as [u | s τs IH]; intros Hf.
    - cbn [sort_domain adt_free_domain].
      rewrite decide_False by (by apply adt_free_not_adt). reflexivity.
    - apply adt_free_app_inv in Hf as [Hnadt Hτs].
      cbn [sort_domain adt_free_domain].
      rewrite decide_False by (unfold adt; congruence).
      destruct τs as [| σ1 [| σ2 τs']]; try reflexivity.
      + case_decide; [| reflexivity]. f_equal.
        apply IH; [set_solver | by inversion Hτs].
      + case_decide; [| reflexivity].
        inversion Hτs as [| ? ? Hσ1 Hτs']; subst.
        inversion Hτs' as [| ? ? Hσ2 _]; subst.
        rewrite (IH σ1) by (first [set_solver | exact Hσ1]).
        rewrite (IH σ2) by (first [set_solver | exact Hσ2]).
        reflexivity.
  Qed.

  (** ** The Equations

      Each of the three non-datatype equations holds as soon as its sort is not
      a datatype.  That is a real condition — a signature is free to declare a
      constructor at [σ_int] — and it is why these are stated with the premise
      rather than proved outright. *)

  Lemma sort_domain_base : forall s,
      ~ adt Σ (SApp s []) -> sort_domain (SApp s []) = base s.
  Proof.
    intros s H. cbn [sort_domain]. by rewrite decide_False.
  Qed.

  Lemma sort_domain_τ_map : forall σ1 σ2,
      ~ adt Σ (τ_map σ1 σ2) ->
      sort_domain (τ_map σ1 σ2) = (sort_domain σ1 -> sort_domain σ2).
  Proof.
    intros σ1 σ2 H. unfold τ_map in *. cbn [sort_domain].
    rewrite decide_False by exact H. by rewrite decide_True.
  Qed.

  Lemma sort_domain_τ_seq : forall σ,
      ~ adt Σ (τ_seq σ) -> sort_domain (τ_seq σ) = list (sort_domain σ).
  Proof.
    intros σ H. unfold τ_seq in *. cbn [sort_domain].
    rewrite decide_False by exact H. by rewrite decide_True.
  Qed.

  (** The datatype equation.  [sort_domain] is the free algebra over
      [adt_free_domain] by definition; what has to be shown is that reading it
      as the algebra over [sort_domain] gives the *same type*, and that is an
      equality of the two generator parameters, by functional extensionality
      twice — once for the sort, once for the [generator_sort] proof the
      parameter is indexed by.  [sort_domain_adt_free] is what makes the bodies
      equal, and it applies because the index is exactly a proof that the sort
      is datatype-free. *)
  Lemma sort_domain_adt : forall δ,
      adt Σ δ -> sort_domain δ = seq_ground_term Σ (fun σ _ => sort_domain σ) δ.
  Proof.
    intros δ H. destruct δ; cbn [sort_domain]; rewrite decide_True by exact H;
      f_equal; apply functional_extensionality_dep; intros σ;
      apply functional_extensionality_dep; intros [Hfree _];
      symmetry; by apply sort_domain_adt_free.
  Qed.

  (** ** Inhabitation

      [interp] is total: a structure gives a value at every rank, declared or
      not, so [interp f [] σ] is an element of the domain at every [σ] and no
      structure exists over a domain that is empty anywhere.  Away from the
      datatype sorts that follows from [base] being inhabited, which is
      therefore what the caller owes here. *)

  Context (base_witness : forall s, base s).

  Definition adt_free_domain_witness : forall σ, adt_free_domain σ.
  Proof.
    induction σ as [u | s τs IH] using sort_rect.
    - exact tt.
    - destruct τs as [| σ1 [| σ2 [| σ3 τs']]]; cbn [adt_free_domain].
      + exact (base_witness s).
      + case_decide; [exact [] | exact tt].
      + case_decide; [intros _; apply IH; set_solver | exact tt].
      + exact tt.
  Defined.

  (** At a datatype sort it is not free, and the obligation does not reduce
      further: the free algebra at [δ] is empty unless some constructor of [δ]
      has every field sort inhabited, which is a well-foundedness condition on
      the datatype declarations rather than anything this construction can
      supply.  It is taken as a parameter and owed by whoever builds [Σ]. *)
  Definition sort_domain_witness
    (w : forall δ, adt Σ δ ->
                   seq_ground_term Σ (fun τ _ => adt_free_domain τ) δ)
    : forall σ, sort_domain σ.
  Proof.
    induction σ as [u | s τs IH] using sort_rect; cbn [sort_domain].
    - destruct (decide (adt Σ (SParam u))) as [Ha | Ha];
        [exact (w _ Ha) | exact tt].
    - destruct (decide (adt Σ (SApp s τs))) as [Ha | Ha]; [exact (w _ Ha) |].
      destruct τs as [| σ1 [| σ2 [| σ3 τs']]]; cbn [sort_domain].
      + exact (base_witness s).
      + case_decide; [exact [] | exact tt].
      + case_decide; [intros _; apply IH; set_solver | exact tt].
      + exact tt.
  Defined.

End DomainConstruction.
