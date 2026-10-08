(** * SMTLIB.Signature : Signatures, their Construction and Composition *)

(** This file largely corresponds to Sec. 5.2.1, _signatures_.
    A [signature] (Definition 2) fixes what an SMT-LIB query may talk about: which sort
    symbols exist and at which arity, which function symbols exist and at which
    ranks, which of those are datatype constructors, selectors and testers, and
    what sort each variable carries.

    The file runs in seven parts.

    - [Signatures] — the record itself, with [monomorphic_rank_base], which
      one of its conditions is stated with, and [sort_wf], the well-formed
      sorts it admits.
    - [Monomorphic Ranks] — the monomorphic instances of a symbol's rank.
    - [Algebraic Datatypes] — which sorts have constructors.
    - [Signature Expansion] — Definition 4.
    - [Rank Extension] — the preorder "declares at least as much, at the same
      ranks", which is what both constructions below produce.
    - [Signature Composition] — the union of two signatures that agree
      wherever they overlap, Sec. 5.4.1's [Σ1 + Σ2].
    - [Adding Sorts to a Signature] — overriding finitely many variable sorts
      and changing nothing else, Sec. 5.2.2's [Σ[x1:τ1, …, xn:τn]], written
      [m ⊍ Σ], and the [Lookup] and [Insert] instances that read and extend a
      signature at one variable as [Σ !! x] and [<[x := σ]> Σ].

    A [sorting] is a finite map from variables to sorts, so it sorts only the
    variables a signature declares, as Definition 2's partial mapping does.
    Extending a context is stdpp's [<[x := σ]>] for one variable and [m ∪ S]
    for several, the left operand winning where both are defined. *)

From SMTLIB Require Import Symbols Term.
From stdpp Require Import base gmap.

Declare Scope smt_scope.
Delimit Scope smt_scope with smt.
Open Scope smt_scope.

(** * Signatures *)

(** The sorts of the declared variables.  A signature declares finitely many,
    as every SMT-LIB script does.  A [Notation] rather than a [Definition], so
    that stdpp's map instances and lemmas apply to it without unfolding. *)
Notation sorting := (gmap var sort).

(** A monomorphic instance of a rank [R] gives [f]: some rank [τs -> τ] of [f]
    together with a single substitution [θ] carrying it to [σs -> σ]. One
    substitution for the whole rank rather than one per argument — that is what
    makes the argument sorts constrain each other. Stated over a bare ranking
    relation so that [signature] can use it for its own [rank];
    [monomorphic_rank] is this at a signature. A [Notation] rather than a
    [Definition], so that a statement using it is the same term as one
    writing the existential out, and proofs about either serve both. *)
Notation monomorphic_rank_base R f σs σ :=
  (exists θ τs τ,
    R f τs τ
    /\ monomorphic_instance_of θ τ σ
    /\ Forall2 (monomorphic_instance_of θ) τs σs).

(** The declared vocabulary of a problem, carrying the well-formedness
    conditions the rest of the development assumes. Each data field is
    followed immediately by its [_wf] conditions, so a field and everything
    assumed about it read together. *)
Record signature :=
  {
    (** The sort symbols a sort may be built from. Always contains [s_bool] and
        [s_map]: the term language needs both whatever theory is in play. *)
    sort_symbols : gset sortsymb;
    sort_symbols_wf : {[ s_bool ; s_map ]} ⊆ sort_symbols;

    (** The function symbols. A predicate rather than a [gset] so that a
        signature may declare infinitely many — the numeric literals are the
        motivating case, and are why nothing here may enumerate [funcs].
        Membership is nonetheless decidable, which is weaker than being
        enumerable and is what a composition needs to know which component
        interprets a symbol. *)
    funcs : func -> Prop;
    funcs_dec : forall f, Decision (funcs f);

    (** The datatype apparatus. [constructors], [selectors] and [testers] are
        three pairwise-disjoint finite sets of declared symbols; the
        disjointness is what lets a term be classified by its head symbol
        alone. *)
    constructors : gset func;
    constructors_wf : forall c, c ∈ constructors -> funcs c;

    selectors : gset func;
    selectors_wf : forall g, g ∈ selectors -> funcs g;
    selectors_disj : selectors ## constructors;

    testers : gset func;
    testers_wf : forall p, p ∈ testers -> funcs p;
    testers_disj : testers ## constructors /\ testers ## selectors;

    (** Which constructors belong to a sort symbol. Total, but constrained only
        on [sort_symbols]. A symbol with no constructors is not a datatype;
        [adt] below is the predicate that says which are. *)
    constructors_for_sort : sortsymb -> gset func;
    constructors_for_sort_wf :
      forall s, s ∈ sort_symbols -> constructors_for_sort s ⊆ constructors;

    (** How many sort arguments a symbol takes. Total for the same reason: a
        partial arity would put a side condition into every sort. *)
    arity : sortsymb -> nat;
    arity_s_bool : arity s_bool = 0;
    arity_s_map : arity s_map = 2;

    (** A constructor's selectors, in argument order — hence a [list] and not a
        [gset]. [rank_selectors] below is what ties position [i] of this list
        to argument sort [i]. *)
    selectors_for_constructor : func -> list func;
    selectors_for_constructor_wf :
      forall c,
        c ∈ constructors ->
        list_to_set (selectors_for_constructor c) ⊆ selectors;

    (** A constructor has exactly one tester and a tester exactly one
        constructor, so this pair is a bijection where the selectors need a
        list. The two [_bijection] fields state its two directions. *)
    tester_for_constructor : func -> func;
    tester_for_constructor_wf :
      forall c, c ∈ constructors -> tester_for_constructor c ∈ testers;
    constructor_for_tester : func -> func;
    constructor_for_tester_wf :
      forall p, p ∈ testers -> constructor_for_tester p ∈ constructors;
    constructor_tester_bijection :
      forall c,
        c ∈ constructors -> constructor_for_tester (tester_for_constructor c) = c;
    tester_constructor_bijection :
      forall p,
        p ∈ testers -> tester_for_constructor (constructor_for_tester p) = p;

    (** The sorts of the declared variables. Nothing here asks them to be
        well formed or monomorphic: the sorting judgment checks both of every
        variable a term reads ([S_TFVar]), and a variable no term reads has no
        effect. *)
    sorts : sorting;

    (** [rank f τs τ] says [f] may be applied to arguments of sorts [τs] to give
        [τ]. A relation and not a function, because an overloaded symbol has one
        rank per instantiation.

        The seven conditions say, in order: every sort in a rank is
        well-formed; a symbol with a rank is declared; a declared symbol has a
        rank; a constructor's result has a symbol that lists it; a
        constructor's result sort determines its argument sorts; a
        constructor's selectors take its result to its arguments; and its
        tester takes its result to [σ_bool].

        The fifth replaces Definition 2's item 4, which says no constructor
        has two ranks with the same result sort and different argument sorts.
        Note 59 gives the reason for item 4: a constructor's result sort then
        determines its argument sorts. Item 4 does not achieve this once ranks
        are polymorphic, because it compares ranks, not their monomorphic
        instances: [c : u D] is a single rank, so it satisfies item 4, yet
        gives [c] both [Int D] and [Bool D]. The fifth condition states Note
        59's property directly, on monomorphic instances, since those are
        what a term is sorted at. A declared datatype satisfies it: §4.1 gives
        each constructor one rank, and §4.2.3 makes every argument parameter
        occur in the result, which is enough by
        [rank_constructor_args_determined_intro] below. *)
    rank : func -> list sort -> sort -> Prop;
    rank_wf :
      forall f τs τ,
        rank f τs τ ->
        sort_wf_base sort_symbols arity τ
        /\ Forall (sort_wf_base sort_symbols arity) τs;
    rank_domain : forall f τs τ, rank f τs τ -> funcs f;
    rank_left_total : forall f, funcs f -> exists τs τ, rank f τs τ;
    rank_constructor :
      forall c τs τ,
        c ∈ constructors ->
        rank c τs τ ->
        exists s, sort_top_symbol τ = Some s /\ c ∈ constructors_for_sort s;
    rank_constructor_args_determined :
      forall c σs σs' σ,
        c ∈ constructors ->
        monomorphic_rank_base rank c σs σ ->
        monomorphic_rank_base rank c σs' σ ->
        σs = σs';
    rank_selectors :
      forall c gs τs τ,
        c ∈ constructors ->
        gs = selectors_for_constructor c ->
        rank c τs τ ->
        length τs = length gs
        /\ Forall (fun '(g, τ') => rank g [τ] τ') (zip gs τs);
    rank_tester :
      forall c p τs τ,
        c ∈ constructors ->
        p = tester_for_constructor c ->
        rank c τs τ ->
        rank p [τ] σ_bool;
  }.

(** The sorts [Σ] admits: [sort_wf_base] at this signature's symbols and arities.  *)
Definition sort_wf (Σ : signature) : sort -> Prop :=
  sort_wf_base Σ.(sort_symbols) Σ.(arity).

(** [sort_symbols_wf] forces [s_bool] into every signature and [arity_s_bool]
    fixes its arity, so this needs no hypothesis at all. *)
Theorem sort_wf_σ_bool : forall Σ, sort_wf Σ σ_bool.
Proof.
  intro Σ.
  constructor; auto.
  - apply Σ.(sort_symbols_wf). set_solver.
  - rewrite Σ.(arity_s_bool). reflexivity.
Qed.

(** * Monomorphic Ranks *)

(** A symbol's [rank] is a relation and a term's sorting needs one monomorphic
    instance of it. [monomorphic_rank] is that instance. The results here say
    how much of it is pinned down: for a constructor, the result sort
    determines the argument sorts outright, which is what makes a constructor
    application unambiguous. *)

(** A monomorphic instance of a rank [Σ] gives [f]: [monomorphic_rank_base]
    at this signature's ranks. *)
Definition monomorphic_rank (Σ : signature) (f : func) (σs : list sort)
    (σ : sort) : Prop :=
  monomorphic_rank_base Σ.(rank) f σs σ.

Theorem rank_monomorphic :
  forall Σ f σs σ,
    Σ.(rank) f σs σ ->
    Forall monomorphic σs ->
    monomorphic σ ->
    monomorphic_rank Σ f σs σ.
Proof.
  intros Σ f σs σ Hrank Hσs Hσ.
  exists ∅, σs, σ. split_and!; auto.
  - apply monomorphic_instance_of_refl. assumption.
  - apply Forall_Forall2_diag.
    eapply Forall_impl; eauto.
    apply monomorphic_instance_of_refl.
Qed.

(** The monomorphic reading of the signature's [rank_selectors] field: sorting a
    selector application needs one monomorphic instance of the selector's
    rank, and the constructor's own instance supplies it, position by
    position. *)
Theorem monomorphic_rank_selector :
  forall Σ c σs δ i g σ,
    c ∈ Σ.(constructors) ->
    monomorphic_rank Σ c σs δ ->
    Σ.(selectors_for_constructor) c !! i = Some g ->
    σs !! i = Some σ ->
    monomorphic_rank Σ g [δ] σ.
Proof.
  intros Σ c σs δ i g σ Hcon (θ & τs & τ & Hrank & Hτ & Hσs) Hg Hσ.
  (* the polymorphic rank of the selector standing in position [i] *)
  eapply Σ.(rank_selectors) in Hrank as [_ Hsel]; auto.
  apply (Forall2_lookup_r _ _ _ i σ) in Hσs as (τ_i & Hτi & Hinst); [|exact Hσ].
  assert (Hzip : zip (Σ.(selectors_for_constructor) c) τs !! i = Some (g, τ_i))
    by (rewrite lookup_zip_with, Hg, Hτi; reflexivity).
  eapply Forall_lookup_1 in Hsel; [|exact Hzip].
  (* the constructor's substitution makes that rank monomorphic: its output
     sort at [δ], its argument sort at [σ] *)
  exists θ, [τ], τ_i.
  split_and!; [exact Hsel|exact Hinst|].
  constructor; [exact Hτ|constructor].
Qed.

(** A constructor's selector list has the same length as its (monomorphic)
    argument-sort list. *)
Lemma monomorphic_rank_selector_length :
  forall Σ c σs δ,
    c ∈ Σ.(constructors) ->
    monomorphic_rank Σ c σs δ ->
    length (Σ.(selectors_for_constructor) c) = length σs.
Proof.
  intros Σ c σs δ Hcon (θ & τs & τ & Hrank & _ & Hf).
  (* the selector list has the length of the polymorphic argument list *)
  eapply Σ.(rank_selectors) in Hrank as [Hlen _]; auto.
  (* and the substitution relates that list to the monomorphic one *)
  apply Forall2_length in Hf.
  rewrite <- Hlen, Hf. reflexivity.
Qed.

(** Two monomorphic ranks of one constructor have equal-length argument lists:
    both have the length of its selector list. *)
Corollary monomorphic_rank_constructor_length :
  forall Σ c σs σs' δ δ',
    c ∈ Σ.(constructors) ->
    monomorphic_rank Σ c σs δ ->
    monomorphic_rank Σ c σs' δ' ->
    length σs = length σs'.
Proof.
  intros Σ c σs σs' δ δ' Hcon Hr1 Hr2.
  apply monomorphic_rank_selector_length in Hr1, Hr2; auto.
  rewrite <- Hr1, <- Hr2. reflexivity.
Qed.

(** Constructors with one rank each, whose argument parameters all occur in
    its result, satisfy [rank_constructor_args_determined]: two monomorphic
    instances then share that rank, and their substitutions agree on the
    parameters of its arguments because they agree on its result. *)
Theorem rank_constructor_args_determined_intro :
  forall (C : gset func) (R : func -> list sort -> sort -> Prop),
    (forall c τs τ τs' τ', c ∈ C -> R c τs τ -> R c τs' τ' -> τ = τ' /\ τs = τs') ->
    (forall c τs τ, c ∈ C -> R c τs τ -> ⋃ (map sort_params τs) ⊆ sort_params τ) ->
    forall c σs σs' σ,
      c ∈ C ->
      monomorphic_rank_base R c σs σ ->
      monomorphic_rank_base R c σs' σ ->
      σs = σs'.
Proof.
  intros C R Hfunctional Hparams c σs σs' σ Hc
    (θ & τs & τ & Hr & [Hi _] & Hσs) (θ' & τs' & τ' & Hr' & [Hi' _] & Hσs').
  destruct (Hfunctional _ _ _ _ _ Hc Hr Hr') as [Hτeq Hτseq].
  subst τ' τs'.
  assert (Hout : sort_subst θ τ = sort_subst θ' τ)
    by (unfold instance_of in Hi, Hi'; rewrite Hi, Hi'; reflexivity).
  specialize (Hparams _ _ _ Hc Hr).
  apply list_eq. intros i.
  assert (Hl1 : length τs = length σs) by (by eapply Forall2_length).
  assert (Hl2 : length τs = length σs') by (by eapply Forall2_length).
  destruct (σs !! i) as [a|] eqn:Ha; destruct (σs' !! i) as [b|] eqn:Hb.
  - f_equal.
    destruct (τs !! i) as [τ0|] eqn:Hτ0; cycle 1.
    { apply lookup_ge_None in Hτ0. apply lookup_lt_Some in Ha. lia. }
    eapply Forall2_lookup_lr in Hσs as [Hia _]; eauto.
    eapply Forall2_lookup_lr in Hσs' as [Hib _]; eauto.
    unfold instance_of in Hia, Hib.
    assert (Hsub : sort_params τ0 ⊆ sort_params τ).
    { etrans; [|exact Hparams].
      intros p Hp. apply elem_of_union_list. exists (sort_params τ0).
      split; [|exact Hp].
      apply list_elem_of_fmap. exists τ0.
      split; [reflexivity| apply list_elem_of_lookup_2 with i; exact Hτ0]. }
    rewrite <- Hia, <- Hib. eapply sort_subst_eq_subset; eauto.
  - apply lookup_lt_Some in Ha. apply lookup_ge_None in Hb.
    rewrite <- Hl1, Hl2 in Ha. lia.
  - apply lookup_lt_Some in Hb. apply lookup_ge_None in Ha.
    rewrite <- Hl2, Hl1 in Hb. lia.
  - reflexivity.
Qed.

(** A constructor's monomorphic argument sorts are determined by its result
    sort — which is what makes a constructor application's arguments unambiguous. *)
Theorem monomorphic_rank_constructor_args_eq :
  forall Σ c σs σs' δ,
    c ∈ Σ.(constructors) ->
    monomorphic_rank Σ c σs δ ->
    monomorphic_rank Σ c σs' δ ->
    σs = σs'.
Proof. intros Σ. apply Σ.(rank_constructor_args_determined). Qed.

(** * Algebraic Datatypes *)

(** Which sorts have constructors. [Theory.v] needs this to know when a model's
    domain is forced to be the ground constructor terms. *)

(** [τ] is a datatype under [Σ]: a well-formed sort whose head is a declared
    symbol carrying at least one constructor. *)
Definition adt_spec (Σ : signature) (τ : sort) : Prop :=
  sort_wf Σ τ
  /\ exists s c,
      s ∈ Σ.(sort_symbols)
      /\ sort_top_symbol τ = Some s
      /\ c ∈ Σ.(constructors_for_sort) s.

Global Instance adt_spec_dec (Σ : signature) (τ : sort) :
  Decision (adt_spec Σ τ).
Proof.
  unfold adt_spec.
  destruct (decide (sort_wf_base Σ.(sort_symbols) Σ.(arity) τ)) as [Hwf|Hwf];
    last first.
  { right. intros [Hwf' _]. contradiction. }
  destruct (sort_top_symbol τ) as [s|] eqn:Hhead; last first.
  { right. intros [_ (s' & c & _ & Hhead' & _)]. congruence. }
  destruct (decide (s ∈ Σ.(sort_symbols))) as [Hs|Hs]; last first.
  { right. intros [_ (s' & c & Hs' & Hhead' & _)].
    assert (s' = s) as -> by congruence. contradiction. }
  destruct (decide (Σ.(constructors_for_sort) s ≡ ∅)) as [Hempty|Hempty].
  - right. intros [_ (s' & c & _ & Hhead' & Hc)].
    assert (s' = s) as -> by congruence.
    apply Hempty in Hc. set_solver.
  - left. split; [exact Hwf |].
    apply set_choose in Hempty as [c Hc].
    exists s, c. split_and!; [exact Hs | reflexivity | exact Hc].
Qed.

(** A sort is a datatype when its decision says so.  Recording the decision
    rather than the witness makes any two proofs equal, which the embedding of
    a datatype's domain into the ground terms needs: that embedding is indexed
    by such a proof, and two indexings must agree. *)
Definition adt (Σ : signature) (τ : sort) : Prop :=
  bool_decide (adt_spec Σ τ) = true.

Theorem adt_spec_of_adt : forall Σ τ, adt Σ τ -> adt_spec Σ τ.
Proof. intros Σ τ H. by apply (bool_decide_eq_true_1 (adt_spec Σ τ)). Qed.

Theorem adt_of_adt_spec : forall Σ τ, adt_spec Σ τ -> adt Σ τ.
Proof. intros Σ τ H. by apply (bool_decide_eq_true_2 (adt_spec Σ τ)). Qed.

Theorem adt_irrelevant : forall Σ τ (H1 H2 : adt Σ τ), H1 = H2.
Proof. intros Σ τ H1 H2. apply (Eqdep_dec.UIP_dec Bool.bool_dec). Qed.

Global Instance adt_dec (Σ : signature) (τ : sort) : Decision (adt Σ τ).
Proof. unfold adt. apply _. Defined.

Theorem adt_intro :
  forall Σ δ s c,
    s ∈ Σ.(sort_symbols) ->
    sort_top_symbol δ = Some s ->
    c ∈ Σ.(constructors_for_sort) s ->
    sort_wf Σ δ ->
    adt Σ δ.
Proof. intros Σ δ s c Hs Hhead Hc Hwf. apply adt_of_adt_spec. hauto lq:on. Qed.

(** [τ] mentions no datatype anywhere.

    This is the mechanisation's generator guard: [SMTLIB.Theory]'s
    [domain_gen] takes the generators of a datatype's free algebra to be the
    domains of the [adt_free] sorts, rather than Definition 9(3)'s "every sort
    that is not a datatype".  The argument for the departure is at
    [domain_gen], which is where 9(3) is transcribed. *)
(** The test for datatype-freedom.  The inner fix walks the argument sorts;
    [sort] recurses through [list sort], so they are structurally smaller. *)
Fixpoint adt_freeb (Σ : signature) (τ : sort) : bool :=
  match τ with
  | SParam u => negb (bool_decide (adt_spec Σ (SParam u)))
  | SApp s τs =>
      negb (bool_decide (adt_spec Σ (SApp s τs)))
      && (fix args (l : list sort) : bool :=
            match l with
            | [] => true
            | τ' :: l' => adt_freeb Σ τ' && args l'
            end) τs
  end.

(** The arguments clause, named so the facts below can speak about it. *)
Fixpoint adt_freeb_args (Σ : signature) (l : list sort) : bool :=
  match l with
  | [] => true
  | τ :: l' => adt_freeb Σ τ && adt_freeb_args Σ l'
  end.

Lemma adt_freeb_args_unfold : forall Σ s τs,
    adt_freeb Σ (SApp s τs)
    = negb (bool_decide (adt_spec Σ (SApp s τs))) && adt_freeb_args Σ τs.
Proof.
  intros Σ s τs. simpl. f_equal.
  induction τs as [|τ τs' IH]; simpl; [reflexivity|].
  by rewrite IH.
Qed.

(** [τ] mentions no datatype anywhere.  Like [adt] it is recorded by its
    decision, so the generator case of a ground term, which is indexed by
    such a proof, is indexed by something irrelevant. *)
Definition adt_free (Σ : signature) (τ : sort) : Prop := adt_freeb Σ τ = true.

Theorem adt_free_irrelevant : forall Σ τ (H1 H2 : adt_free Σ τ), H1 = H2.
Proof. intros Σ τ H1 H2. apply (Eqdep_dec.UIP_dec Bool.bool_dec). Qed.

Global Instance adt_free_dec (Σ : signature) (τ : sort) : Decision (adt_free Σ τ).
Proof. unfold adt_free. apply _. Defined.

Lemma adt_freeb_args_true : forall Σ τs,
    adt_freeb_args Σ τs = true <-> Forall (adt_free Σ) τs.
Proof.
  intros Σ τs. induction τs as [|τ τs' IH]; simpl.
  - split; [constructor | reflexivity].
  - rewrite andb_true_iff, IH. split.
    + intros [H1 H2]. by constructor.
    + intros H. by inversion H.
Qed.

(** Introduction and elimination, in place of the constructors. *)
Theorem adt_free_param : forall Σ u,
    bool_decide (adt_spec Σ (SParam u)) = false -> adt_free Σ (SParam u).
Proof. intros Σ u Hb. unfold adt_free. cbn [adt_freeb]. by rewrite Hb. Qed.

Theorem adt_free_app : forall Σ s τs,
    bool_decide (adt_spec Σ (SApp s τs)) = false ->
    Forall (adt_free Σ) τs ->
    adt_free Σ (SApp s τs).
Proof.
  intros Σ s τs Hb HF. unfold adt_free.
  rewrite adt_freeb_args_unfold, Hb. simpl.
  by apply adt_freeb_args_true.
Qed.

Theorem adt_free_app_inv : forall Σ s τs,
    adt_free Σ (SApp s τs) ->
    bool_decide (adt_spec Σ (SApp s τs)) = false /\ Forall (adt_free Σ) τs.
Proof.
  intros Σ s τs H. unfold adt_free in H.
  rewrite adt_freeb_args_unfold, andb_true_iff, negb_true_iff,
    adt_freeb_args_true in H.
  exact H.
Qed.

Theorem adt_free_param_inv : forall Σ u,
    adt_free Σ (SParam u) -> bool_decide (adt_spec Σ (SParam u)) = false.
Proof.
  intros Σ u H. unfold adt_free in H. cbn [adt_freeb] in H.
  by rewrite negb_true_iff in H.
Qed.

Theorem adt_free_not_adt : forall Σ τ, adt_free Σ τ -> ~ adt Σ τ.
Proof.
  intros Σ τ H Hadt. unfold adt in Hadt. destruct τ as [u | s τs].
  - apply adt_free_param_inv in H. congruence.
  - apply adt_free_app_inv in H as [Hb _]. congruence.
Qed.

(** The introduction rules as the rest of the development states them. *)
Theorem adt_free_param_intro : forall Σ u,
    ~ adt Σ (SParam u) -> adt_free Σ (SParam u).
Proof.
  intros Σ u H. apply adt_free_param.
  destruct (bool_decide (adt_spec Σ (SParam u))) eqn:Hb; [| reflexivity].
  by destruct (H Hb).
Qed.

Theorem adt_free_app_intro : forall Σ s τs,
    ~ adt Σ (SApp s τs) ->
    Forall (adt_free Σ) τs ->
    adt_free Σ (SApp s τs).
Proof.
  intros Σ s τs Hn HF. apply adt_free_app; [| exact HF].
  destruct (bool_decide (adt_spec Σ (SApp s τs))) eqn:Hb; [| reflexivity].
  by destruct (Hn Hb).
Qed.

(** The sorts at which a domain element crosses into the term algebra: a
    datatype sort, whose elements are ground terms already, or a datatype-free
    sort, whose elements are generators.  A datatype buried under another sort
    constructor is neither.  [SMTLIB.Theory]'s [ground_term_embed] is that
    crossing, and this is exactly where it is defined. *)
Definition embeddable_sort (Σ : signature) (τ : sort) : Prop :=
  adt Σ τ \/ adt_free Σ τ.

Theorem adt_free_of_embeddable : forall Σ τ,
    embeddable_sort Σ τ -> ~ adt Σ τ -> adt_free Σ τ.
Proof. intros Σ τ [Ha | Hf] Hn; [contradiction | exact Hf]. Qed.

Theorem embeddable_sort_adt : forall Σ τ, adt Σ τ -> embeddable_sort Σ τ.
Proof. intros Σ τ H. by left. Qed.

Theorem embeddable_sort_adt_free : forall Σ τ,
    adt_free Σ τ -> embeddable_sort Σ τ.
Proof. intros Σ τ H. by right. Qed.

(** Both disjuncts are decided, so the crossing is too.  Kept opaque for the
    same reason the datatype decision is: nothing needs it to reduce, and a
    transparent one would sit inside every proof that mentions it. *)
Global Instance embeddable_sort_dec (Σ : signature) (τ : sort) :
  Decision (embeddable_sort Σ τ).
Proof. unfold embeddable_sort. apply _. Qed.

(** A nullary sort application is embeddable at every signature: it either
    is a datatype or, having no arguments to bury one in, mentions none. *)
Theorem embeddable_sort_app_nil : forall Σ s,
    embeddable_sort Σ (SApp s []).
Proof.
  intros Σ s. destruct (decide (adt Σ (SApp s []))) as [H | H];
    [by left | right; apply adt_free_app_intro; [exact H | constructor]].
Qed.

(** A strengthening of SMT-LIB §4.2.3(iv), read as a condition on Σ: every
    rank the signature gives a constructor has argument sorts the crossing is
    defined at.  (iv) forbids a field burying a datatype only within that
    datatype's declaration group; this forbids it everywhere.  It is what
    the no-confusion clause of [SMTLIB.Theory]'s [adt_constructed] needs and
    cannot derive, since the two constructor applications it compares are
    given at the domain and carry no ground term to read their sorts off.
    It is not a field of
    [signature]: [adt_free] shrinks as a signature gains datatypes, so a
    signature satisfying it need not do so after composition. *)
Definition constructor_args_embeddable (Σ : signature) : Prop :=
  forall c σs δ s,
    s ∈ Σ.(sort_symbols) ->
    sort_top_symbol δ = Some s ->
    c ∈ Σ.(constructors_for_sort) s ->
    monomorphic_rank Σ c σs δ ->
    Forall (embeddable_sort Σ) σs.

(** A constructor named by a covered match pattern is a constructor of the
    signature: it is in [constructors_for_sort s] for the scrutinee's sort
    head, and [constructors_for_sort_wf] puts that inside [constructors]. *)
Lemma match_pattern_constructor_in_constructors :
  forall Σ (pts : list (pattern * term)) δ s c n t0,
    adt Σ δ ->
    Some s = sort_top_symbol δ ->
    list_to_set (omap pattern_constructor (map fst pts))
      ⊆ Σ.(constructors_for_sort) s ->
    (PApp c n, t0) ∈ pts ->
    c ∈ Σ.(constructors).
Proof.
  intros Σ pts δ s c n t0 Hadt Htops Hsub Hin.
  apply adt_spec_of_adt in Hadt as (_ & s' & c' & Hsym & Htop & _).
  rewrite Htop in Htops. injection Htops as <-.
  assert (Hccs : c ∈ (list_to_set (omap pattern_constructor (map fst pts))
                  : gset func)).
  { apply elem_of_list_to_set. apply list_elem_of_omap.
    exists (PApp c n). split; [|reflexivity].
    apply list_elem_of_fmap. exists (PApp c n, t0). split; [reflexivity|exact Hin]. }
  pose proof (elem_of_weaken _ _ _ Hccs Hsub) as Hcs.
  pose proof (Σ.(constructors_for_sort_wf) s Hsym) as Hwf.
  exact (elem_of_weaken _ _ _ Hcs Hwf).
Qed.

(** * Signature Expansion *)

(** Definition 4: [Ω] keeps everything [Σ] declares. The arities of [Σ]'s sort
    symbols, the constructors of its sorts, and the selectors and tester of its
    constructors are unchanged, and so is every variable at a sort of [Σ]. [Ω]
    may add sort symbols, function symbols and ranks, including new ranks for
    [Σ]'s own symbols.

    [signature_expansion_constructors] is not among Definition 4's clauses, but its
    clause on selectors and testers presupposes it: only a constructor of [Ω]
    has a selector list and a tester in [Ω]. *)
Record signature_expansion (Σ Ω : signature) : Prop :=
  {
    signature_expansion_sort_symbols : Σ.(sort_symbols) ⊆ Ω.(sort_symbols);
    signature_expansion_funcs : forall f, Σ.(funcs) f -> Ω.(funcs) f;
    signature_expansion_arity : forall s,
      s ∈ Σ.(sort_symbols) -> Ω.(arity) s = Σ.(arity) s;
    signature_expansion_constructors_for_sort : forall s,
      s ∈ Σ.(sort_symbols) ->
      Ω.(constructors_for_sort) s = Σ.(constructors_for_sort) s;
    signature_expansion_constructors : Σ.(constructors) ⊆ Ω.(constructors);
    signature_expansion_selectors_for_constructor : forall c,
      c ∈ Σ.(constructors) ->
      Ω.(selectors_for_constructor) c = Σ.(selectors_for_constructor) c;
    signature_expansion_tester_for_constructor : forall c,
      c ∈ Σ.(constructors) ->
      Ω.(tester_for_constructor) c = Σ.(tester_for_constructor) c;
    signature_expansion_sorts : forall x σ,
      sort_wf Σ σ -> Σ.(sorts) !! x = Some σ <-> Ω.(sorts) !! x = Some σ;
    signature_expansion_rank : forall f τs τ, Σ.(rank) f τs τ -> Ω.(rank) f τs τ;
  }.

Theorem sort_wf_signature_expansion : forall Σ Ω σ,
    signature_expansion Σ Ω ->
    sort_wf Σ σ ->
    sort_wf Ω σ.
Proof.
  intros Σ Ω σ Hexp.
  induction σ as [u | s τs IH]; intros Hwf; inversion Hwf as [|? ? Hs Harity Hτs]; subst.
  - constructor.
  - constructor.
    + exact (Hexp.(signature_expansion_sort_symbols _ _) _ Hs).
    + rewrite Hexp.(signature_expansion_arity _ _) by exact Hs. exact Harity.
    + rewrite Forall_forall in Hτs |- *.
      intros τ Hτ. apply IH; [exact Hτ|]. apply Hτs. exact Hτ.
Qed.

(** * Rank Extension *)

(** [extends_rank Σ1 Σ2] is the preorder "[Σ2] declares everything [Σ1] does, at
    the same ranks, and no new rank for a symbol [Σ1] already declares". Both
    constructions in the two sections below produce extensions in this sense,
    and that is what lets a derivation over the smaller signature be reused
    over the larger one.

    It is not Definition 4. The last field, conservativity, is stronger than
    anything Definition 4 asks: a consumer evaluating one of [Σ1]'s symbols in
    [Σ2] needs to know the symbol has no ranks there that [Σ1]'s
    interpretation does not cover. And it forgets Definition 4's datatype and
    variable clauses, which no consumer needs. [extends_rank_of_signature_expansion]
    says it is a conservative expansion with those clauses dropped.

    It is stated over what it reads of each signature, its well-formed sorts,
    function symbols and ranks, through [rank_extension].  So it does not see
    variable sorts: [extends_rank Σ1 (signature_with_sorts Σ2 m)] is
    [extends_rank Σ1 Σ2] by conversion, and a fact about [Σ2] serves every
    signature that extends [Σ2] by variables. *)

Record rank_extension (sw1 sw2 : sort -> Prop) (f1 f2 : func -> Prop)
    (r1 r2 : func -> list sort -> sort -> Prop) : Prop :=
  {
    sort_wf_extends : forall σ, sw1 σ -> sw2 σ;
    funcs_extends : forall f, f1 f -> f2 f;
    rank_extends : forall f τs τ, r1 f τs τ -> r2 f τs τ;
    rank_conservative : forall f τs τ, f1 f -> r2 f τs τ -> r1 f τs τ
  }.

Definition extends_rank (Σ1 Σ2 : signature) : Prop :=
  rank_extension (sort_wf Σ1) (sort_wf Σ2) Σ1.(funcs) Σ2.(funcs)
    Σ1.(rank) Σ2.(rank).

Arguments sort_wf_extends {_ _ _ _ _ _}.
Arguments funcs_extends {_ _ _ _ _ _}.
Arguments rank_extends {_ _ _ _ _ _}.
Arguments rank_conservative {_ _ _ _ _ _}.

(** [⊑] is [\sqsubseteq].  It shadows stdpp's [⊑] where [smt_scope] is open. *)
Notation "Σ1 ⊑ Σ2" := (extends_rank Σ1 Σ2) (at level 70) : smt_scope.

Global Instance extends_rank_refl : Reflexive extends_rank.
Proof. firstorder. Qed.

Global Instance extends_rank_trans : Transitive extends_rank.
Proof. firstorder. Qed.

Theorem extends_rank_of_signature_expansion : forall Σ1 Σ2,
    signature_expansion Σ1 Σ2 ->
    (forall f τs τ, Σ1.(funcs) f -> Σ2.(rank) f τs τ -> Σ1.(rank) f τs τ) ->
    Σ1 ⊑ Σ2.
Proof.
  intros Σ1 Σ2 Hexp Hconservative. split.
  - intros σ. apply sort_wf_signature_expansion. exact Hexp.
  - exact Hexp.(signature_expansion_funcs _ _).
  - exact Hexp.(signature_expansion_rank _ _).
  - exact Hconservative.
Qed.

(** Ground ranks transport backwards along an extension: a symbol already
    declared in [Σ1] gains no monomorphic rank by moving to [Σ2]. This is
    [rank_conservative] lifted through the instantiating substitution. *)
Theorem monomorphic_rank_conservative : forall Σ1 Σ2 f σs σ,
    monomorphic_rank Σ2 f σs σ ->
    Σ1 ⊑ Σ2 ->
    Σ1.(funcs) f ->
    monomorphic_rank Σ1 f σs σ.
Proof. sauto. Qed.

(** The forward direction, and the monomorphic-rank counterpart of the
    [rank_extends] field: a monomorphic rank survives the extension.  With
    [monomorphic_rank_conservative] it says an extension changes nothing about
    the monomorphic ranks of a symbol the smaller signature already declares. *)
Theorem monomorphic_rank_extends : forall Σ1 Σ2 f σs σ,
    monomorphic_rank Σ1 f σs σ ->
    Σ1 ⊑ Σ2 ->
    monomorphic_rank Σ2 f σs σ.
Proof. sauto. Qed.

(** * Signature Composition *)

(** [signature_compose] takes the union of two signatures, which is Sec.
    5.4.1's [Σ1 + Σ2]: its ranks are exactly those of [Σ1] and of [Σ2], and it
    is an expansion of both ([signature_compose_signature_expansion_left] and
    [_right]). The work is entirely in the side conditions: a union of two
    records is only a record again if the two agree wherever both have
    something to say. *)

(** ** Composability *)

(** What two signatures must satisfy for [signature_compose] to build a
    signature from them: they agree on every sort symbol, constructor,
    selector, tester and map they share, they declare the same variables, and
    neither's selectors or testers collide with the other's constructors.

    This generalises Sec. 5.4.1's compatibility, which asks for the same sort
    symbols, constructors, selectors and testers, where this asks only for
    agreement on the ones both have. The standard gets that sameness by
    instantiating every component theory at one common signature (Sec. 5.5).
    Here each component is built over its own sort symbols, and composition
    takes their union. *)
(** So that [decide] sees the field. *)
Global Existing Instance funcs_dec.

Record signatures_composable (Σ1 Σ2 : signature) : Prop :=
  {
    arities_consistent : forall s,
      s ∈ Σ1.(sort_symbols) ->
      s ∈ Σ2.(sort_symbols) ->
      Σ1.(arity) s = Σ2.(arity) s;

    selectors_mutually_disj :
      Σ1.(selectors) ## Σ2.(constructors)
      /\ Σ2.(selectors) ## Σ1.(constructors);

    testers_mutually_disj :
      Σ1.(testers) ## Σ2.(constructors)
      /\ Σ2.(testers) ## Σ1.(constructors)
      /\ Σ1.(testers) ## Σ2.(selectors)
      /\ Σ2.(testers) ## Σ1.(selectors);

    constructors_for_sort_consistent : forall s,
        s ∈ Σ1.(sort_symbols) ->
        s ∈ Σ2.(sort_symbols) ->
        Σ1.(constructors_for_sort) s = Σ2.(constructors_for_sort) s;

    selectors_for_constructor_consistent : forall c,
        c ∈ Σ1.(constructors) ->
        c ∈ Σ2.(constructors) ->
        Σ1.(selectors_for_constructor) c = Σ2.(selectors_for_constructor) c;

    tester_for_constructor_consistent : forall c,
        c ∈ Σ1.(constructors) ->
        c ∈ Σ2.(constructors) ->
        Σ1.(tester_for_constructor) c = Σ2.(tester_for_constructor) c;

    constructor_for_tester_consistent : forall t,
        t ∈ Σ1.(testers) ->
        t ∈ Σ2.(testers) ->
        Σ1.(constructor_for_tester) t = Σ2.(constructor_for_tester) t;

    constructors_consistent_left : forall c,
        c ∈ Σ1.(constructors) ->
        Σ2.(funcs) c <-> c ∈ Σ2.(constructors);

    constructors_consistent_right : forall c,
        c ∈ Σ2.(constructors) ->
        Σ1.(funcs) c <-> c ∈ Σ1.(constructors);

    rank_constructor_consistent : forall c τs τ,
        c ∈ Σ1.(constructors) ->
        c ∈ Σ2.(constructors) ->
        Σ1.(rank) c τs τ <-> Σ2.(rank) c τs τ;

    sorts_consistent : Σ1.(sorts) = Σ2.(sorts);
  }.

(** ** The Composed Signature *)

Local Lemma sort_wf_inherit_left : forall σ Σ1 Σ2,
  sort_wf Σ1 σ ->
  sort_wf_base
    (sort_symbols Σ1 ∪ sort_symbols Σ2)
    (λ s : sortsymb,
       if decide (s ∈ sort_symbols Σ1)
       then arity Σ1 s
       else arity Σ2 s) σ.
Proof.
  induction σ; intros * Hσ; inversion Hσ; constructor.
  - set_solver.
  - unfold arity. rewrite decide_True; assumption.
  - rewrite Forall_forall in *. intros σ' Hσ'.
    pose proof Hσ' as Hσ''.
    specialize H4 with σ'. apply H4 in Hσ'.
    eapply H in Hσ'; eauto.
Qed.

Local Lemma sort_wf_inherit_right : forall σ Σ1 Σ2 (C : signatures_composable Σ1 Σ2),
  sort_wf Σ2 σ ->
  sort_wf_base
    (sort_symbols Σ1 ∪ sort_symbols Σ2)
    (λ s : sortsymb,
       if decide (s ∈ sort_symbols Σ1)
       then arity Σ1 s
       else arity Σ2 s) σ.
Proof.
  induction σ; intros * C Hσ; inversion Hσ; constructor.
  - set_solver.
  - unfold arity. destruct (decide (s ∈ Σ1.(sort_symbols))); auto.
    rewrite C.(arities_consistent Σ1 Σ2); assumption.
  - rewrite Forall_forall in *. intros σ' Hσ'.
    pose proof Hσ' as Hσ''.
    specialize H4 with σ'. apply H4 in Hσ'.
    eapply H in Hσ'; eauto.
Qed.

(** Sec. 5.5's [T1 + T2], for signatures and for pretheories alike: [a ⊕[ C ] b]
    composes [a] and [b], which [C] shows composable.  [⊕] is [\oplus]. *)
Class Compose (A : Type) (R : A -> A -> Prop) :=
  smt_compose : forall a b, R a b -> A.
Global Arguments smt_compose {_ _ _} _ _ _.
Notation "a ⊕[ C ] b" := (smt_compose a b C)
  (at level 50, C at level 200, left associativity).

(** The union of two composable signatures. Every set-valued field is a union;
    every function-valued field asks whether its argument belongs to [Σ1] and
    defers to [Σ2] otherwise, which is well defined exactly because
    [signatures_composable] makes the two agree wherever both apply. [sorts] is
    taken from [Σ1] alone — variable sortings are not composed.

    The obligations discharge the record's well-formedness fields in
    declaration order. *)
Program Definition signature_compose
  (Σ1 : signature) (Σ2 : signature)
  (C : signatures_composable Σ1 Σ2) : signature :=
  {|
    sort_symbols := Σ1.(sort_symbols) ∪ Σ2.(sort_symbols);

    funcs f := Σ1.(funcs) f \/ Σ2.(funcs) f;
    funcs_dec f := or_dec (Σ1.(funcs_dec) f) (Σ2.(funcs_dec) f);

    constructors := Σ1.(constructors) ∪ Σ2.(constructors);
    selectors := Σ1.(selectors) ∪ Σ2.(selectors);
    testers := Σ1.(testers) ∪ Σ2.(testers);

    constructors_for_sort (s : sortsymb) :=
      if decide (s ∈ Σ1.(sort_symbols))
      then Σ1.(constructors_for_sort) s
      else Σ2.(constructors_for_sort) s;

    arity s :=
      if decide (s ∈ Σ1.(sort_symbols))
      then Σ1.(arity) s
      else Σ2.(arity) s;

    selectors_for_constructor (c : func) :=
      if decide (c ∈ Σ1.(constructors))
      then Σ1.(selectors_for_constructor) c
      else Σ2.(selectors_for_constructor) c;

    tester_for_constructor (c : func) :=
      if decide (c ∈ Σ1.(constructors))
      then Σ1.(tester_for_constructor) c
      else Σ2.(tester_for_constructor) c;

    constructor_for_tester (p : func) :=
      if decide (p ∈ Σ1.(testers))
      then Σ1.(constructor_for_tester) p
      else Σ2.(constructor_for_tester) p;

    sorts := Σ1.(sorts);
    rank f τs τ :=
       Σ1.(rank) f τs τ \/ Σ2.(rank) f τs τ;
  |}.

Next Obligation.
Proof.
  intros Σ1 Σ2 C.
  intros s Hs. unfold sort_symbols.
  rewrite elem_of_union. left.
  apply Σ1.(sort_symbols_wf). assumption.
Qed.

Next Obligation.
Proof.
  intros Σ1 Σ2 C.
  unfold constructors, funcs. intros c Hc.
  rewrite elem_of_union in Hc.
  destruct Hc as [Hc | Hc].
  - left. apply Σ1.(constructors_wf). assumption.
  - right. apply Σ2.(constructors_wf). assumption.
Qed.

Next Obligation.
Proof.
  intros Σ1 Σ2 C.
  unfold selectors, funcs. intros g Hg.
  rewrite elem_of_union in Hg.
  destruct Hg as [Hg | Hg].
  - left. apply Σ1.(selectors_wf). assumption.
  - right. apply Σ2.(selectors_wf). assumption.
Qed.

Next Obligation.
Proof.
  intros Σ1 Σ2 C.
  unfold selectors, constructors. intros g Hg Hg'.
  rewrite elem_of_union in *.
  destruct Hg as [Hg | Hg]; destruct Hg' as [Hg' | Hg'].
  - apply Σ1.(selectors_disj) in Hg. apply Hg. assumption.
  - apply C.(selectors_mutually_disj Σ1 Σ2) in Hg. apply Hg. assumption.
  - apply C.(selectors_mutually_disj Σ1 Σ2) in Hg. apply Hg. assumption.
  - apply Σ2.(selectors_disj) in Hg. apply Hg. assumption.
Qed.

Next Obligation.
Proof.
  intros Σ1 Σ2 C.
  unfold testers, funcs. intros p Hp.
  rewrite elem_of_union in Hp.
  destruct Hp as [Hp | Hp].
  - left. apply Σ1.(testers_wf). assumption.
  - right. apply Σ2.(testers_wf). assumption.
Qed.

Next Obligation.
Proof.
  intros Σ1 Σ2 C.
  unfold testers, constructors, selectors. split.
  - intros p Hp Hp'. rewrite elem_of_union in *.
    destruct Σ1.(testers_disj) as [testers_disj1 _].
    destruct Σ2.(testers_disj) as [testers_disj2 _].
    destruct C.(testers_mutually_disj Σ1 Σ2) as (testers_disj3&testers_disj4&_).
    naive_solver.
  - intros p Hp Hp'. rewrite elem_of_union in *.
    destruct Σ1.(testers_disj) as [_ testers_disj1].
    destruct Σ2.(testers_disj) as [_ testers_disj2].
    destruct C.(testers_mutually_disj Σ1 Σ2) as (_&_&testers_disj3&testers_disj4).
    naive_solver.
Qed.

Next Obligation.
Proof.
  intros Σ1 Σ2 C.
  intros s Hs c Hc.
  unfold constructors_for_sort in Hc.
  unfold constructors. rewrite elem_of_union.
  unfold sort_symbols in Hs.
  destruct (decide (s ∈ Σ1.(sort_symbols))).
  - left. eapply Σ1.(constructors_for_sort_wf); eauto.
  - right. eapply Σ2.(constructors_for_sort_wf); eauto.
    set_solver.
Qed.

Next Obligation.
Proof.
  intros Σ1 Σ2 C.
  unfold arity.
  assert (s_bool ∈ Σ1.(sort_symbols)).
  { apply Σ1.(sort_symbols_wf). set_solver. }
  rewrite decide_True; auto. apply Σ1.(arity_s_bool).
Qed.

Next Obligation.
Proof.
  intros Σ1 Σ2 C.
  unfold arity.
  assert (s_map ∈ Σ1.(sort_symbols)).
  { apply Σ1.(sort_symbols_wf). set_solver. }
  rewrite decide_True; auto. apply Σ1.(arity_s_map).
Qed.

Next Obligation.
Proof.
  intros Σ1 Σ2 C.
  intros c Hc g Hg.
  unfold selectors_for_constructor in Hg.
  unfold selectors. rewrite elem_of_union.
  unfold constructors in Hc.
  destruct (decide (c ∈ Σ1.(constructors))).
  - left. eapply Σ1.(selectors_for_constructor_wf); eauto.
  - right. eapply Σ2.(selectors_for_constructor_wf); eauto.
    set_solver.
Qed.

Next Obligation.
Proof.
  intros Σ1 Σ2 C.
  intros c Hc.
  rewrite elem_of_union in Hc. rewrite elem_of_union.
  destruct (decide (c ∈ Σ1.(constructors))); destruct Hc as [Hc | Hc].
  - left. apply Σ1.(tester_for_constructor_wf). assumption.
  - left. apply Σ1.(tester_for_constructor_wf). assumption.
  - contradiction.
  - right. apply Σ2.(tester_for_constructor_wf). assumption.
Qed.

Next Obligation.
Proof.
  intros Σ1 Σ2 C.
  intros p Hp.
  rewrite elem_of_union in Hp. rewrite elem_of_union.
  destruct (decide (p ∈ Σ1.(testers))); destruct Hp as [Hp | Hp].
  - left. apply Σ1.(constructor_for_tester_wf). assumption.
  - left. apply Σ1.(constructor_for_tester_wf). assumption.
  - contradiction.
  - right. apply Σ2.(constructor_for_tester_wf). assumption.
Qed.

Next Obligation.
Proof.
  intros Σ1 Σ2 C.
  intros c Hc.
  destruct (decide (c ∈ Σ1.(constructors))).
  - destruct (decide (Σ1.(tester_for_constructor) c ∈ Σ1.(testers))).
    + rewrite decide_True; [| rewrite decide_True]; auto.
      rewrite decide_True; auto.
      apply Σ1.(constructor_tester_bijection). assumption.
    + apply Σ1.(tester_for_constructor_wf) in e. contradiction.
  - unfold constructors in Hc. rewrite elem_of_union in Hc.
    destruct Hc as [Hc | Hc]; try contradiction.
    destruct (decide (Σ2.(tester_for_constructor) c ∈ Σ1.(testers))).
    + pose proof Hc as Hc'.
      apply Σ2.(tester_for_constructor_wf) in Hc.
      rewrite C.(constructor_for_tester_consistent Σ1 Σ2);
        [| rewrite decide_False | rewrite decide_False]; auto.
      rewrite decide_True; [| rewrite decide_False]; auto.
      rewrite decide_False; auto.
      apply Σ2.(constructor_tester_bijection). assumption.
    + rewrite decide_False; [| rewrite decide_False]; auto.
      rewrite decide_False; auto.
      apply Σ2.(constructor_tester_bijection). assumption.
Qed.

Next Obligation.
Proof.
  intros Σ1 Σ2 C.
  intros p Hp.
  destruct (decide (p ∈ Σ1.(testers))) as [Hp1 | Hp1].
  - rewrite !(decide_True _ _ Hp1).
    rewrite decide_True by (apply Σ1.(constructor_for_tester_wf); assumption).
    apply Σ1.(tester_constructor_bijection). assumption.
  - rewrite !(decide_False _ _ Hp1).
    unfold testers in Hp. rewrite elem_of_union in Hp.
    destruct Hp as [Hp | Hp]; try contradiction.
    pose proof (Σ2.(constructor_for_tester_wf) p Hp) as Hc2.
    destruct (decide (Σ2.(constructor_for_tester) p ∈ Σ1.(constructors))).
    (* A constructor shared with [Σ1] has the same tester in both. *)
    + rewrite C.(tester_for_constructor_consistent Σ1 Σ2) by assumption.
      apply Σ2.(tester_constructor_bijection). assumption.
    + apply Σ2.(tester_constructor_bijection). assumption.
Qed.

Next Obligation.
Proof.
  intros Σ1 Σ2 C.
  intros f τs τ Hf. destruct Hf as [Hf | Hf].
  - apply Σ1.(rank_wf) in Hf. destruct Hf as [Hτ Hτs]. split.
    + apply sort_wf_inherit_left. assumption.
    + eapply Forall_impl in Hτs.
      apply Hτs. hauto l: on use: sort_wf_inherit_left.
  - apply Σ2.(rank_wf) in Hf. destruct Hf as [Hτ Hτs]. split.
    + apply sort_wf_inherit_right; assumption.
    + eapply Forall_impl in Hτs.
      apply Hτs. hauto l: on use: sort_wf_inherit_right.
Qed.

Next Obligation.
Proof.
  intros Σ1 Σ2 C f τs τ Hrank. simpl in *.
  destruct Hrank.
  - left. eapply Σ1.(rank_domain). eauto.
  - right. eapply Σ2.(rank_domain). eauto.
Qed.

Next Obligation.
Proof.
  intros Σ1 Σ2 C.
  unfold funcs. intros f Hf.
  destruct Hf as [Hf | Hf]; pose proof Hf as Hf'.
  - apply Σ1.(rank_left_total) in Hf. destruct Hf as (τs & τ & Hf).
    exists τs, τ. left. tauto.
  - apply Σ2.(rank_left_total) in Hf. destruct Hf as (τs & τ & Hf).
    exists τs, τ. right. tauto.
Qed.

Next Obligation.
Proof.
  intros Σ1 Σ2 C.
  intros c τs τ Hc Hc'.
  unfold constructors in Hc. rewrite elem_of_union in Hc.
  unfold rank in Hc'.
  destruct Hc as [Hc | Hc]; destruct Hc' as [Hc' | Hc'].
  - destruct (Σ1.(rank_wf) _ _ _ Hc') as [Hτ _].
    apply Σ1.(rank_constructor) in Hc'; auto.
    destruct Hc' as [s [Hs Hc']].
    exists s. split.
    + assumption.
    + unfold sort_top_symbol in Hs.
      destruct τ as [u | s' τs']; try congruence.
      inversion Hs. subst s'.
      inversion Hτ.
      unfold constructors_for_sort.
      rewrite decide_True; assumption.
  - apply rank_domain in Hc' as Hc''.
    apply C.(constructors_consistent_left Σ1 Σ2) in Hc''; auto.
    destruct (Σ2.(rank_wf) _ _ _ Hc') as [Hτ _].
    apply Σ2.(rank_constructor) in Hc'; auto.
    destruct Hc' as [s [Hs Hc']].
    exists s. split.
    + assumption.
    + unfold sort_top_symbol in Hs.
      destruct τ as [u | s' τs']; try congruence.
      inversion Hs. subst s'.
      inversion Hτ.
      unfold constructors_for_sort.
      destruct (decide (s ∈ Σ1.(sort_symbols))); auto.
      rewrite C.(constructors_for_sort_consistent Σ1 Σ2); assumption.
  - apply rank_domain in Hc' as Hc''.
    apply C.(constructors_consistent_right Σ1 Σ2) in Hc''; auto.
    destruct (Σ1.(rank_wf) _ _ _ Hc') as [Hτ _].
    apply Σ1.(rank_constructor) in Hc'; auto.
    destruct Hc' as [s [Hs Hc']].
    exists s. split.
    + assumption.
    + unfold sort_top_symbol in Hs.
      destruct τ as [u | s' τs']; try congruence.
      inversion Hs. subst s'.
      inversion Hτ.
      unfold constructors_for_sort.
      rewrite decide_True; assumption.
  - destruct (Σ2.(rank_wf) _ _ _ Hc') as [Hτ _].
    apply Σ2.(rank_constructor) in Hc'; auto.
    destruct Hc' as [s [Hs Hc']].
    exists s. split.
    + assumption.
    + unfold sort_top_symbol in Hs.
      destruct τ as [u | s' τs']; try congruence.
      inversion Hs. subst s'.
      inversion Hτ.
      unfold constructors_for_sort.
      destruct (decide (s ∈ Σ1.(sort_symbols))); auto.
      rewrite C.(constructors_for_sort_consistent Σ1 Σ2); assumption.
Qed.

Next Obligation.
Proof.
  intros Σ1 Σ2 C c σs σs' σ Hcon
    (θ & τs & τ & Hr & Hi & Hσs) (θ' & τs' & τ' & Hr' & Hi' & Hσs').
  destruct (decide (c ∈ constructors Σ1)) as [Hc1|Hc1].
  - (* a rank [Σ2] gives a constructor of [Σ1] is one [Σ1] gives it *)
    assert (Hto1 : forall τs0 τ0,
               rank Σ1 c τs0 τ0 \/ rank Σ2 c τs0 τ0 -> rank Σ1 c τs0 τ0).
    { intros τs0 τ0 [Hrank|Hrank]; [assumption|].
      apply Σ2.(rank_domain) in Hrank as Hf.
      apply C.(constructors_consistent_left Σ1 Σ2) in Hf; auto.
      rewrite <- (C.(rank_constructor_consistent Σ1 Σ2) c τs0 τ0) in Hrank; auto. }
    apply (Σ1.(rank_constructor_args_determined) c σs σs' σ Hc1).
    + exists θ, τs, τ. auto.
    + exists θ', τs', τ'. auto.
  - (* a constructor of [Σ2] only, which [Σ1] gives no rank *)
    apply elem_of_union in Hcon. destruct Hcon as [Hc2|Hc2]; [contradiction|].
    assert (Hto2 : forall τs0 τ0,
               rank Σ1 c τs0 τ0 \/ rank Σ2 c τs0 τ0 -> rank Σ2 c τs0 τ0).
    { intros τs0 τ0 [Hrank|Hrank]; [|assumption].
      apply Σ1.(rank_domain) in Hrank as Hf.
      apply C.(constructors_consistent_right Σ1 Σ2) in Hf; auto.
      contradiction. }
    apply (Σ2.(rank_constructor_args_determined) c σs σs' σ Hc2).
    + exists θ, τs, τ. auto.
    + exists θ', τs', τ'. auto.
Qed.

Next Obligation.
Proof.
  intros Σ1 Σ2 C c gs τs τ Hcon Hgs Hrank.
  subst gs.
  destruct (decide (c ∈ constructors Σ1)) as [Hc1|Hc1].
  - assert (Hr1 : rank Σ1 c τs τ).
    { destruct Hrank as [Hrank|Hrank]; [assumption|].
      apply Σ2.(rank_domain) in Hrank as Hf.
      apply C.(constructors_consistent_left Σ1 Σ2) in Hf; auto.
      rewrite <- (C.(rank_constructor_consistent Σ1 Σ2) c τs τ) in Hrank; auto. }
    eapply Σ1.(rank_selectors) in Hr1 as [Hlen Hforall]; auto.
    split; [assumption|].
    eapply Forall_impl; [eassumption|].
    intros [g τ'] Hg. left. exact Hg.
  - apply elem_of_union in Hcon. destruct Hcon as [Hc2|Hc2]; [contradiction|].
    assert (Hr2 : rank Σ2 c τs τ).
    { destruct Hrank as [Hrank|Hrank]; [|assumption].
      apply Σ1.(rank_domain) in Hrank as Hf.
      apply C.(constructors_consistent_right Σ1 Σ2) in Hf; auto.
      contradiction. }
    eapply Σ2.(rank_selectors) in Hr2 as [Hlen Hforall]; auto.
    split; [assumption|].
    eapply Forall_impl; [eassumption|].
    intros [g τ'] Hg. right. exact Hg.
Qed.

Next Obligation.
Proof.
  intros Σ1 Σ2 C c p τs τ Hcon Hp Hrank.
  subst p.
  destruct (decide (c ∈ constructors Σ1)) as [Hc1|Hc1].
  - assert (Hr1 : rank Σ1 c τs τ).
    { destruct Hrank as [Hrank|Hrank]; [assumption|].
      apply Σ2.(rank_domain) in Hrank as Hf.
      apply C.(constructors_consistent_left Σ1 Σ2) in Hf; auto.
      rewrite <- (C.(rank_constructor_consistent Σ1 Σ2) c τs τ) in Hrank; auto. }
    left. eapply Σ1.(rank_tester); eauto.
  - apply elem_of_union in Hcon. destruct Hcon as [Hc2|Hc2]; [contradiction|].
    assert (Hr2 : rank Σ2 c τs τ).
    { destruct Hrank as [Hrank|Hrank]; [|assumption].
      apply Σ1.(rank_domain) in Hrank as Hf.
      apply C.(constructors_consistent_right Σ1 Σ2) in Hf; auto.
      contradiction. }
    right. eapply Σ2.(rank_tester); eauto.
Qed.

#[global] Instance signature_compose_compose :
  Compose signature signatures_composable := signature_compose.

(** ** What Composition Preserves *)

(** Composition only adds sort symbols and only agrees about arities, so a sort
    well-formed under either part is well-formed under the composite. *)
Theorem signature_compose_sort_wf_left : forall Σ1 Σ2 C τ,
    let Σ := Σ1 ⊕[ C ] Σ2 in
    sort_wf Σ1 τ ->
    sort_wf Σ τ.
Proof.
  induction τ.
  - sauto lq: on.
  - intros * Hwf. inversion Hwf. simplify_eq.
    constructor.
    + set_solver.
    + hauto lq: on rew: off.
    + qauto l:on use:Forall_forall.
Qed.

Theorem signature_compose_sort_wf_right : forall Σ1 Σ2 C τ,
    let Σ := Σ1 ⊕[ C ] Σ2 in
    sort_wf Σ2 τ ->
    sort_wf Σ τ.
Proof.
  induction τ.
  - sauto lq: on.
  - intros * Hwf. inversion Hwf. simplify_eq.
    constructor.
    + set_solver.
    + sauto.
    + qauto l:on use:Forall_forall.
Qed.

Theorem signature_compose_signature_expansion_left : forall Σ1 Σ2 C,
    signature_expansion Σ1 (Σ1 ⊕[ C ] Σ2).
Proof.
  intros Σ1 Σ2 C. split; simpl.
  - set_solver.
  - intros f Hf. left. exact Hf.
  - intros s Hs. rewrite decide_True by exact Hs. reflexivity.
  - intros s Hs. rewrite decide_True by exact Hs. reflexivity.
  - set_solver.
  - intros c Hc. rewrite decide_True by exact Hc. reflexivity.
  - intros c Hc. rewrite decide_True by exact Hc. reflexivity.
  - intros x σ _. reflexivity.
  - intros f τs τ Hrank. left. exact Hrank.
Qed.

(** The composite takes each shared symbol's arity, constructors, selectors
    and tester from [Σ1], so this direction is where [C]'s agreement is used. *)
Theorem signature_compose_signature_expansion_right : forall Σ1 Σ2 C,
    signature_expansion Σ2 (Σ1 ⊕[ C ] Σ2).
Proof.
  intros Σ1 Σ2 C. split; simpl.
  - set_solver.
  - intros f Hf. right. exact Hf.
  - intros s Hs. case_decide as Hs1; [|reflexivity].
    apply C.(arities_consistent Σ1 Σ2); assumption.
  - intros s Hs. case_decide as Hs1; [|reflexivity].
    apply C.(constructors_for_sort_consistent Σ1 Σ2); assumption.
  - set_solver.
  - intros c Hc. case_decide as Hc1; [|reflexivity].
    apply C.(selectors_for_constructor_consistent Σ1 Σ2); assumption.
  - intros c Hc. case_decide as Hc1; [|reflexivity].
    apply C.(tester_for_constructor_consistent Σ1 Σ2); assumption.
  - intros x σ _. rewrite C.(sorts_consistent Σ1 Σ2). reflexivity.
  - intros f τs τ Hrank. right. exact Hrank.
Qed.

(** Rank consistency states that the two signatures assign the same ranks to the symbols
    they both declare. Weaker than [signatures_composable], and separate from it because
    it is not needed to *build* the composite, nor for the composite to be an
    expansion of each part. It is needed only for the composite to be a
    conservative one, a rank extension, which Definition 4 does not ask for. *)
Definition rank_consistent (Σ1 Σ2 : signature) := forall f τs τ,
    Σ1.(funcs) f ->
    Σ2.(funcs) f ->
    Σ1.(rank) f τs τ <-> Σ2.(rank) f τs τ.

(** With ranks consistent, the composite is a *conservative* extension of each
    part: it proves no rank for an already-declared symbol that the part did not
    already prove. *)
Theorem signature_compose_extends_rank_left : forall Σ1 Σ2 C,
    let Σ := Σ1 ⊕[ C ] Σ2 in
    rank_consistent Σ1 Σ2 ->
    Σ1 ⊑ Σ.
Proof.
  intros * Hconsistent.
  apply extends_rank_of_signature_expansion; [apply signature_compose_signature_expansion_left|].
  intros f τs τ Hfunc1 [Hrank | Hrank].
  - assumption.
  - apply Σ2.(rank_domain) in Hrank as Hfunc2.
    rewrite (Hconsistent f τs τ Hfunc1 Hfunc2). assumption.
Qed.

Theorem signature_compose_extends_rank_right : forall Σ1 Σ2 C,
    let Σ := Σ1 ⊕[ C ] Σ2 in
    rank_consistent Σ1 Σ2 ->
    Σ2 ⊑ Σ.
Proof.
  intros * Hconsistent.
  apply extends_rank_of_signature_expansion; [apply signature_compose_signature_expansion_right|].
  intros f τs τ Hfunc2 [Hrank | Hrank].
  - apply Σ1.(rank_domain) in Hrank as Hfunc1.
    rewrite <- (Hconsistent f τs τ Hfunc1 Hfunc2). assumption.
  - assumption.
Qed.

(** * Adding Sorts to a Signature *)

(** The other construction: change the variable sorting and nothing else.
    This is Sec. 5.2.2's [Σ[x1:τ1, …, xn:τn]], which maps each [xi] to [τi] and
    agrees with [Σ] elsewhere. It is not an expansion in general, since
    Definition 4 keeps every variable at a sort of [Σ].

    The standard uses [Σ[…]] only in the binder rules, and a script never
    declares a variable: [declare-const x σ] declares a nullary function
    symbol, and an asserted formula is closed (Constraint 3). Here a query's
    free symbols are variables instead, declared with this construction, and
    [sat] chooses their values through the valuation. The standard notes after
    Constraint 3 that the two readings agree for satisfiability, and the
    backend prints each such variable as a [declare-const]. *)

(** [Σ] with its variable sorts replaced by [m]. No other field mentions
    [sorts], so every data field is [Σ]'s and every obligation is the
    corresponding proof field of [Σ]. The obligations stay opaque: two
    signatures then differ at their first proof field unless they are the
    same construction, so comparing a replacement with the signature it
    replaces fails at once instead of unfolding both. *)
Program Definition signature_with_sorts (Σ : signature) (m : sorting) : signature :=
  {|
    sort_symbols := Σ.(sort_symbols);
    funcs := Σ.(funcs);
    funcs_dec := Σ.(funcs_dec);
    constructors := Σ.(constructors);
    selectors := Σ.(selectors);
    testers := Σ.(testers);
    constructors_for_sort := Σ.(constructors_for_sort);
    arity := Σ.(arity);
    selectors_for_constructor := Σ.(selectors_for_constructor);
    tester_for_constructor := Σ.(tester_for_constructor);
    constructor_for_tester := Σ.(constructor_for_tester);
    sorts := m;
    rank := Σ.(rank);
  |}.
Next Obligation. intros Σ m. sauto lq:on. Qed.
Next Obligation. intros Σ m. sauto lq:on. Qed.
Next Obligation. intros Σ m. sauto lq:on. Qed.
Next Obligation. intros Σ m. sauto lq:on. Qed.
Next Obligation. intros Σ m. sauto lq:on. Qed.
Next Obligation. intros Σ m. sauto lq:on. Qed.
Next Obligation. intros Σ m. sauto lq:on. Qed.
Next Obligation. intros Σ m. sauto lq:on. Qed.
Next Obligation. intros Σ m. sauto lq:on. Qed.
Next Obligation. intros Σ m. sauto lq:on. Qed.
Next Obligation. intros Σ m. sauto lq:on. Qed.
Next Obligation. intros Σ m. sauto lq:on. Qed.
Next Obligation. intros Σ m. sauto lq:on. Qed.
Next Obligation. intros Σ m. apply Σ.(tester_constructor_bijection). Qed.
Next Obligation. intros Σ m. sauto lq:on. Qed.
Next Obligation. intros Σ m. sauto lq:on rew:off. Qed.
Next Obligation. intros Σ m. sauto lq:on. Qed.
Next Obligation. intros Σ m. sauto lq: on dep: on. Qed.
Next Obligation. intros Σ m. apply Σ.(rank_constructor_args_determined). Qed.
Next Obligation. intros Σ m. sauto lq:on rew:off. Qed.
Next Obligation. intros Σ m. sauto lq:on rew:off. Qed.

(** [m ⊍ Σ] declares the variables of [m] at [m]'s sorts and is [Σ]
    elsewhere: Sec. 5.2.2's [Σ[x1:τ1, …, xn:τn]] for [m] the map from each
    [xi] to [τi]. *)
Definition signature_add_sorts (Σ : signature) (m : sorting) : signature :=
  signature_with_sorts Σ (m ∪ Σ.(sorts)).

(** [⊍] is U+228D.  In a Coq buffer with company-coq it completes from
    [\cupdot]; anywhere in Emacs, [C-x 8 RET 228D] inserts it. *)
Notation "m ⊍ Σ" := (signature_add_sorts Σ m) (at level 50, left associativity).

(** A signature is read and extended at one variable through its sorting:
    [Σ !! x] is the sort [Σ] declares [x] at, and [<[x := σ]> Σ] is
    [Σ[x:σ]]. *)
#[global] Instance signature_lookup : Lookup var sort signature :=
  fun x Σ => Σ.(sorts) !! x.

#[global] Instance signature_insert : Insert var sort signature :=
  fun x σ Σ => signature_with_sorts Σ (<[x := σ]> Σ.(sorts)).

Theorem signature_lookup_insert_eq : forall (Σ : signature) x σ,
    <[x := σ]> Σ !! x = Some σ.
Proof. intros Σ x σ. apply (lookup_insert_eq Σ.(sorts)). Qed.

Theorem signature_lookup_insert_ne : forall (Σ : signature) x y σ,
    x <> y -> <[x := σ]> Σ !! y = Σ !! y.
Proof. intros Σ x y σ Hne. apply (lookup_insert_ne Σ.(sorts)). exact Hne. Qed.

Theorem signature_insert_sorts : forall (Σ : signature) x σ,
    (<[x := σ]> Σ).(sorts) = <[x := σ]> Σ.(sorts).
Proof. reflexivity. Qed.

Theorem signature_add_sorts_sorts : forall (Σ : signature) (m : sorting),
    (m ⊍ Σ).(sorts) = m ∪ Σ.(sorts).
Proof. reflexivity. Qed.

Theorem signature_lookup_with_sorts : forall (Σ : signature) (m : sorting) x,
    signature_with_sorts Σ m !! x = m !! x.
Proof. reflexivity. Qed.

Theorem signature_lookup_add_sorts : forall (Σ : signature) (m : sorting) x,
    (m ⊍ Σ) !! x = (m ∪ Σ.(sorts)) !! x.
Proof. reflexivity. Qed.

(** [Σ1] and [Σ2] agree on every field but their variable sorts, leaving
    aside the proof fields and [funcs_dec], whose type depends on [funcs].  A
    signature with its sorts replaced agrees with the one it replaces, so a
    fact about terms carries between the two wherever it does not look at a
    variable. *)
Record signatures_agree_except_sorts (Σ1 Σ2 : signature) : Prop :=
  {
    signatures_agree_except_sorts_sort_symbols :
      Σ1.(sort_symbols) = Σ2.(sort_symbols);
    signatures_agree_except_sorts_funcs : Σ1.(funcs) = Σ2.(funcs);
    signatures_agree_except_sorts_constructors :
      Σ1.(constructors) = Σ2.(constructors);
    signatures_agree_except_sorts_selectors : Σ1.(selectors) = Σ2.(selectors);
    signatures_agree_except_sorts_testers : Σ1.(testers) = Σ2.(testers);
    signatures_agree_except_sorts_constructors_for_sort :
      Σ1.(constructors_for_sort) = Σ2.(constructors_for_sort);
    signatures_agree_except_sorts_arity : Σ1.(arity) = Σ2.(arity);
    signatures_agree_except_sorts_selectors_for_constructor :
      Σ1.(selectors_for_constructor) = Σ2.(selectors_for_constructor);
    signatures_agree_except_sorts_tester_for_constructor :
      Σ1.(tester_for_constructor) = Σ2.(tester_for_constructor);
    signatures_agree_except_sorts_constructor_for_tester :
      Σ1.(constructor_for_tester) = Σ2.(constructor_for_tester);
    signatures_agree_except_sorts_rank : Σ1.(rank) = Σ2.(rank);
  }.

Theorem signatures_agree_except_sorts_refl : forall Σ,
    signatures_agree_except_sorts Σ Σ.
Proof. intros Σ. split; reflexivity. Qed.

Theorem signatures_agree_except_sorts_sym : forall Σ1 Σ2,
    signatures_agree_except_sorts Σ1 Σ2 ->
    signatures_agree_except_sorts Σ2 Σ1.
Proof. intros Σ1 Σ2 []. split; symmetry; assumption. Qed.

Theorem signatures_agree_except_sorts_trans : forall Σ1 Σ2 Σ3,
    signatures_agree_except_sorts Σ1 Σ2 ->
    signatures_agree_except_sorts Σ2 Σ3 ->
    signatures_agree_except_sorts Σ1 Σ3.
Proof. intros Σ1 Σ2 Σ3 [] []. split; etransitivity; eassumption. Qed.

Theorem signatures_agree_except_sorts_with_sorts : forall Σ m,
    signatures_agree_except_sorts (signature_with_sorts Σ m) Σ.
Proof. intros Σ m. split; reflexivity. Qed.

Corollary signatures_agree_except_sorts_insert : forall (Σ : signature) x σ,
    signatures_agree_except_sorts (<[x := σ]> Σ) Σ.
Proof. intros Σ x σ. apply signatures_agree_except_sorts_with_sorts. Qed.

Corollary signatures_agree_except_sorts_add_sorts : forall Σ m,
    signatures_agree_except_sorts (m ⊍ Σ) Σ.
Proof. intros Σ m. apply signatures_agree_except_sorts_with_sorts. Qed.

Theorem signatures_agree_except_sorts_insert_mono :
  forall (Σ1 Σ2 : signature) x σ,
    signatures_agree_except_sorts Σ1 Σ2 ->
    signatures_agree_except_sorts (<[x := σ]> Σ1) (<[x := σ]> Σ2).
Proof.
  intros Σ1 Σ2 x σ Hsym.
  eapply signatures_agree_except_sorts_trans;
    [apply signatures_agree_except_sorts_insert |].
  eapply signatures_agree_except_sorts_trans; [exact Hsym |].
  apply signatures_agree_except_sorts_sym, signatures_agree_except_sorts_insert.
Qed.

Theorem signatures_agree_except_sorts_add_sorts_mono : forall Σ1 Σ2 m,
    signatures_agree_except_sorts Σ1 Σ2 ->
    signatures_agree_except_sorts (m ⊍ Σ1) (m ⊍ Σ2).
Proof.
  intros Σ1 Σ2 m Hsym.
  eapply signatures_agree_except_sorts_trans;
    [apply signatures_agree_except_sorts_add_sorts |].
  eapply signatures_agree_except_sorts_trans; [exact Hsym |].
  apply signatures_agree_except_sorts_sym,
    signatures_agree_except_sorts_add_sorts.
Qed.

Theorem sort_wf_signatures_agree_except_sorts : forall Σ1 Σ2 τ,
    signatures_agree_except_sorts Σ1 Σ2 -> sort_wf Σ1 τ -> sort_wf Σ2 τ.
Proof.
  intros Σ1 Σ2 τ Hsym Hτ. unfold sort_wf.
  rewrite <- (signatures_agree_except_sorts_sort_symbols _ _ Hsym),
    <- (signatures_agree_except_sorts_arity _ _ Hsym).
  exact Hτ.
Qed.

Theorem monomorphic_rank_signatures_agree_except_sorts : forall Σ1 Σ2 f σs σ,
    signatures_agree_except_sorts Σ1 Σ2 ->
    monomorphic_rank Σ1 f σs σ -> monomorphic_rank Σ2 f σs σ.
Proof.
  intros Σ1 Σ2 f σs σ Hsym Hrank. unfold monomorphic_rank.
  rewrite <- (signatures_agree_except_sorts_rank _ _ Hsym). exact Hrank.
Qed.

Theorem adt_signatures_agree_except_sorts : forall Σ1 Σ2 τ,
    signatures_agree_except_sorts Σ1 Σ2 -> adt Σ1 τ -> adt Σ2 τ.
Proof.
  intros Σ1 Σ2 τ Hsym Hadt.
  apply adt_spec_of_adt in Hadt as (Hwf & s & c & Hs & Hhead & Hc).
  apply adt_of_adt_spec.
  split; [exact (sort_wf_signatures_agree_except_sorts _ _ _ Hsym Hwf) |].
  exists s, c.
  rewrite <- (signatures_agree_except_sorts_sort_symbols _ _ Hsym),
    <- (signatures_agree_except_sorts_constructors_for_sort _ _ Hsym).
  done.
Qed.

(** Adding sorts touches no symbol, arity or rank, so both of the properties a
    consumer carries across a construction survive it. *)
Theorem sort_wf_add_sorts : forall Σ m τ,
    sort_wf Σ τ ->
    sort_wf (m ⊍ Σ) τ.
Proof. intros Σ m τ Hτ. exact Hτ. Qed.

Theorem extends_rank_add_sorts : forall Σ m,
    Σ ⊑ (m ⊍ Σ).
Proof. intros Σ m. exact (extends_rank_refl Σ). Qed.

(** Replacing sorts likewise preserves both.  Each holds by conversion, but
    for a concrete [Σ] whose own sorts resemble [m] the conversion compares the
    two sortings at length; applying these instead matches syntactically. *)
Theorem sort_wf_with_sorts : forall Σ m τ,
    sort_wf Σ τ ->
    sort_wf (signature_with_sorts Σ m) τ.
Proof. intros Σ m τ Hτ. exact Hτ. Qed.

Theorem extends_rank_with_sorts : forall Σ1 Σ2 m,
    Σ1 ⊑ Σ2 ->
    Σ1 ⊑ (signature_with_sorts Σ2 m).
Proof. intros Σ1 Σ2 m Hext. exact Hext. Qed.

(** ** Datatype Sorts Across the Two Constructions *)

(** [adt] survives both signature constructions, so a datatype fact proved of
    a component carries to the signature the whole stack ends at.  The
    composite declares the same constructors for a sort as whichever component
    declares that sort, and [constructors_for_sort_consistent] settles the
    overlap; adding variable sortings touches neither the symbols nor the
    constructors. *)

(** A sort declared by a component keeps that component's constructors in the
    composite, [constructors_for_sort_consistent] settling the overlap. *)

Lemma signature_compose_constructors_for_sort_left :
  forall Σ1 Σ2 (C : signatures_composable Σ1 Σ2) s,
    s ∈ Σ1.(sort_symbols) ->
    (Σ1 ⊕[ C ] Σ2).(constructors_for_sort) s
    = Σ1.(constructors_for_sort) s.
Proof. intros Σ1 Σ2 C s Hs. simpl. now rewrite decide_True. Qed.

Lemma signature_compose_constructors_for_sort_right :
  forall Σ1 Σ2 (C : signatures_composable Σ1 Σ2) s,
    s ∈ Σ2.(sort_symbols) ->
    (Σ1 ⊕[ C ] Σ2).(constructors_for_sort) s
    = Σ2.(constructors_for_sort) s.
Proof.
  intros Σ1 Σ2 C s Hs. simpl.
  destruct (decide (s ∈ Σ1.(sort_symbols))) as [Hs1 | Hs1]; [| reflexivity].
  now apply (C.(constructors_for_sort_consistent Σ1 Σ2)).
Qed.

(** The same for a constructor's selectors and tester, which the composite
    takes from whichever component declares the constructor. *)

Lemma signature_compose_selectors_for_constructor_right :
  forall Σ1 Σ2 (C : signatures_composable Σ1 Σ2) c,
    c ∈ Σ2.(constructors) ->
    (Σ1 ⊕[ C ] Σ2).(selectors_for_constructor) c
    = Σ2.(selectors_for_constructor) c.
Proof.
  intros Σ1 Σ2 C c Hc. simpl.
  destruct (decide (c ∈ Σ1.(constructors))) as [Hc1 | Hc1]; [| reflexivity].
  now apply (C.(selectors_for_constructor_consistent Σ1 Σ2)).
Qed.

Lemma signature_compose_tester_for_constructor_right :
  forall Σ1 Σ2 (C : signatures_composable Σ1 Σ2) c,
    c ∈ Σ2.(constructors) ->
    (Σ1 ⊕[ C ] Σ2).(tester_for_constructor) c
    = Σ2.(tester_for_constructor) c.
Proof.
  intros Σ1 Σ2 C c Hc. simpl.
  destruct (decide (c ∈ Σ1.(constructors))) as [Hc1 | Hc1]; [| reflexivity].
  now apply (C.(tester_for_constructor_consistent Σ1 Σ2)).
Qed.

Lemma signature_compose_adt_left :
  forall Σ1 Σ2 (C : signatures_composable Σ1 Σ2) δ,
    adt Σ1 δ -> adt (Σ1 ⊕[ C ] Σ2) δ.
Proof.
  intros Σ1 Σ2 C δ Hadt.
  apply adt_spec_of_adt in Hadt as (Hwf & s & c & Hs & Hhead & Hc).
  apply adt_of_adt_spec.
  split; [by apply signature_compose_sort_wf_left |].
  exists s, c. split_and!; [set_solver | exact Hhead |].
  now rewrite signature_compose_constructors_for_sort_left.
Qed.

Lemma signature_compose_adt_right :
  forall Σ1 Σ2 (C : signatures_composable Σ1 Σ2) δ,
    adt Σ2 δ -> adt (Σ1 ⊕[ C ] Σ2) δ.
Proof.
  intros Σ1 Σ2 C δ Hadt.
  apply adt_spec_of_adt in Hadt as (Hwf & s & c & Hs & Hhead & Hc).
  apply adt_of_adt_spec.
  split; [by apply signature_compose_sort_wf_right |].
  exists s, c. split_and!; [set_solver | exact Hhead |].
  now rewrite signature_compose_constructors_for_sort_right.
Qed.

Lemma signature_add_sorts_adt :
  forall Σ m δ, adt Σ δ -> adt (m ⊍ Σ) δ.
Proof.
  intros Σ m δ Hadt.
  apply adt_spec_of_adt in Hadt as (Hwf' & s & c & Hs & Hhead & Hc).
  apply adt_of_adt_spec.
  split; [by apply sort_wf_add_sorts |]. exists s, c. done.
Qed.

(** The other direction, where a sort has no constructors at all. *)
Lemma not_adt_of_no_constructors :
  forall Σ δ s,
    sort_top_symbol δ = Some s ->
    Σ.(constructors_for_sort) s ≡ ∅ ->
    ~ adt Σ δ.
Proof.
  intros Σ δ s Hhead Hempty Hadt.
  apply adt_spec_of_adt in Hadt as (_ & s' & c & _ & Hhead' & Hc).
  assert (s' = s) as -> by congruence. set_solver.
Qed.
