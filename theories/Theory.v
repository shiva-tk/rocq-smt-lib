(** * SMTLIB.Theory : Structures & Theories *)

(** Corresponds to Sec. 5.3, _structures and satisfiability_, and Sec. 5.4,
    _theories_.

    A [structure] is Definition 7's Σ-structure. Its [domain] field is
    indexed by [sort] rather than being a single untyped universe, so a term
    of sort σ evaluates to something of type [domain σ].

    [interp] gives a value to every function symbol at every rank, including
    ranks the signature does not declare; the model conditions constrain only
    the declared ones. A rank carries a list of argument sorts, so an
    interpretation is a curried function rather than a value: [interpretation]
    is its type, [hlist] is a list of argument values sorted pointwise by the
    rank, and [interp_apply] applies the one to the other.

    [adt_axioms] holds the conditions a structure owes where the signature
    declares datatypes — Definition 8's absolutely free structure for the
    domain and for the constructor interpretations, and Definition 9's
    selector and tester conditions. It is deliberately not a field of
    [structure] for ergonomic theory composition.

    A [theory] is Definition 12 — a signature together with the class of
    structures that model it. It is reached from a [pretheory], which is the
    same pair without the datatype condition: [pretheory_compose] combines two
    whose signatures compose, and a model of the result is a structure
    modelling both, while [theory_init] closes the result off by conjoining
    the datatype condition at the signature reached. *)

From Equations Require Import Equations.
From SMTLIB Require Import Signature Symbols Utils.

Open Scope smt_scope.


(** * Interpretations and Heterogeneous Lists *)

(** The type of an interpretation of one rank, the arguments it is applied to,
    and the application itself. *)

Section Interpretation.

  Variable (domain : sort -> Type).

  Fixpoint interpretation (σs : list sort) (σ : sort) : Type :=
    match σs with
    | [] => domain σ
    | σ' :: σs' => domain σ' -> interpretation σs' σ
    end.

  Inductive hlist : list sort -> Type :=
  | HNil : hlist []
  | HCons : forall σ σs, domain σ -> hlist σs -> hlist (σ :: σs).

  (** Case analysis on an [hlist] whose index is a known list shape.
      [dependent destruction] reaches these too, but by a route that needs
      [eq_rect_eq]; a dependent match on the index does not. *)
  Lemma hlist_nil_eq : forall (vs : hlist []), vs = HNil.
  Proof.
    intros vs.
    refine (match vs as vs0 in hlist l
                  return match l return hlist l -> Prop with
                         | [] => fun vs1 => vs1 = HNil
                         | _ :: _ => fun _ => True
                         end vs0
            with
            | HNil => eq_refl
            | HCons _ _ _ _ => I
            end).
  Qed.

  Lemma hlist_cons_eq : forall σ σs (vs : hlist (σ :: σs)),
      exists v vs', vs = HCons σ σs v vs'.
  Proof.
    intros σ σs vs.
    refine (match vs as vs0 in hlist l
                  return match l return hlist l -> Prop with
                         | [] => fun _ => True
                         | σ0 :: σs0 =>
                             fun vs1 => exists v vs', vs1 = HCons σ0 σs0 v vs'
                         end vs0
            with
            | HNil => I
            | HCons σ0 σs0 v vs' => _
            end).
    now exists v, vs'.
  Qed.

  Equations interp_apply {σs σ}
    (F : interpretation σs σ)
    (vs : hlist σs) : domain σ :=
    interp_apply F HNil := F;
    interp_apply F (HCons _ _ v vs') := interp_apply (F v) vs'.

  (** The inverse of [interp_apply]: the interpretation of a rank read off a
      function on its argument lists. *)
  Fixpoint interp_curry {σs σ} : (hlist σs -> domain σ) -> interpretation σs σ :=
    match σs return (hlist σs -> domain σ) -> interpretation σs σ with
    | [] => fun F => F HNil
    | σ' :: σs' => fun F v => interp_curry (fun vs => F (HCons σ' σs' v vs))
    end.

  Lemma interp_apply_curry : forall σs σ (F : hlist σs -> domain σ) vs,
      interp_apply (interp_curry F) vs = F vs.
  Proof.
    intros σs σ F vs. revert F.
    induction vs as [| σ' σs' v vs IH]; intros F; simp interp_apply.
    - reflexivity.
    - apply (IH (fun vs => F (HCons σ' σs' v vs))).
  Qed.

  (** ** Operations on [hlist] *)

  Fixpoint hlist_lookup {σs} (vs : hlist σs)
    (i : nat) : option { σ : sort & domain σ } :=
    match vs with
    | HNil => None
    | HCons σ0 σs0 v0 vs0 =>
        match i with
        | 0 => Some (existT σ0 v0)
        | S i' => hlist_lookup vs0 i'
        end
    end.

  Theorem hlist_lookup_Some : forall σs (vs : hlist σs) i σ,
      σs !! i = Some σ <-> exists v, hlist_lookup vs i = Some (existT σ v).
  Proof. induction vs; sauto q:on. Qed.

  Corollary hlist_lookup_Some_1 : forall σs (vs : hlist σs) i σ v,
      hlist_lookup vs i = Some (existT σ v) -> σs !! i = Some σ.
  Proof. hauto lq:on use:hlist_lookup_Some. Qed.

  Corollary hlist_lookup_is_Some : forall σs (vs : hlist σs) i,
      is_Some (σs !! i) <-> is_Some (hlist_lookup vs i).
  Proof.
    split; intros.
    - destruct H as [σ Hσ].
      rewrite hlist_lookup_Some with (vs := vs) in Hσ.
      destruct Hσ as [v Hσ_v]. exists (existT σ v). assumption.
    - destruct H as [[σ v] Hσ_v].
      exists σ. eapply hlist_lookup_Some_1. eauto.
  Qed.

  (** The values of an [hlist], each tagged with its sort: the form a finite
      map from variables stores them in. *)
  Fixpoint hlist_to_list {σs} (vs : hlist σs) : list (sigT domain) :=
    match vs with
    | HNil => []
    | HCons σ0 σs0 v0 vs0 => existT σ0 v0 :: hlist_to_list vs0
    end.

  Lemma list_lookup_hlist_to_list : forall σs (vs : hlist σs) i,
      hlist_to_list vs !! i = hlist_lookup vs i.
  Proof. induction vs as [| σ σs v vs IH]; intros [|i]; simpl; auto. Qed.

  Lemma fmap_projT1_hlist_to_list : forall σs (vs : hlist σs),
      projT1 <$> hlist_to_list vs = σs.
  Proof. induction vs as [| σ σs v vs IH]; simpl; [done | by f_equal]. Qed.

  Lemma length_hlist_to_list : forall σs (vs : hlist σs),
      length (hlist_to_list vs) = length σs.
  Proof. induction vs as [| σ σs v vs IH]; simpl; congruence. Qed.

  (** Type-valued "every element satisfies [P]". *)
  Fixpoint hlist_ForallT {σs}
    (P : forall σ, domain σ -> Type) (vs : hlist σs) : Type :=
    match vs with
    | HNil => unit
    | HCons σ σs' v vs' => (P σ v * hlist_ForallT P vs')%type
    end.

  (** The [hlist_ForallT] payload is a nested tuple, which is what a Type-level
      definition wants.  A proof wants it indexed, to match the [hlist_lookup]
      lemmas above. *)
  Theorem hlist_ForallT_lookup :
    forall (P : forall σ, dom σ -> Prop) σs (vs : hlist σs),
      hlist_ForallT P vs ->
      forall i p, hlist_lookup vs i = Some p -> P (projT1 p) (projT2 p).
  Proof.
    intros P σs vs. induction vs as [|σ σs' v vs' IH]; simpl.
    - intros _ i p Hlk. destruct i; simpl in Hlk; discriminate.
    - intros [Hv Hall] i p Hlk. destruct i; simpl in Hlk.
      + injection Hlk as <-. exact Hv.
      + eapply IH; eassumption.
  Qed.

End Interpretation.

Arguments HNil {_}.
Arguments HCons {_}.
Arguments hlist_to_list {_ _} _.

(** Replacements for [dependent destruction] on an [hlist] at a known index
    shape, so that the lemmas above carry the case analysis rather than
    [eq_rect_eq].  [hlist_cons] keeps the tail under the name the head
    variable had, as [dependent destruction] does. *)
Ltac hlist_nil vs :=
  let H := fresh in
  pose proof (hlist_nil_eq _ vs) as H; subst vs.

Ltac hlist_cons vs :=
  let v := fresh "d" in
  let tl := fresh in
  destruct (hlist_cons_eq _ _ _ vs) as (v & tl & ->); rename tl into vs.

Fixpoint hlist_map
  {domain1 domain2 : sort -> Type}
  (g : forall σ, domain1 σ -> domain2 σ)
  {σs : list sort}
  (vs : hlist domain1 σs) : hlist domain2 σs :=
  match vs with
  | HNil => HNil
  | HCons σ σs v vs' => HCons σ σs (g σ v) (hlist_map g vs')
  end.

Theorem hlist_map_map :
  forall {d1 d2 d3} (f : forall σ, d1 σ -> d2 σ) (g : forall σ, d2 σ -> d3 σ)
    σs (vs : hlist d1 σs),
    hlist_map g (hlist_map f vs) = hlist_map (fun σ v => g σ (f σ v)) vs.
Proof. intros d1 d2 d3 f g σs vs. induction vs; simpl; congruence. Qed.

(** [hlist_map] commutes with lookup: the [i]th element of the mapped list is
    the image of the [i]th element. *)
Theorem hlist_lookup_map :
  forall {d1 d2} (f : forall σ, d1 σ -> d2 σ) σs (vs : hlist d1 σs) i σ v,
    hlist_lookup d1 vs i = Some (existT σ v) ->
    hlist_lookup d2 (hlist_map f vs) i = Some (existT σ (f σ v)).
Proof.
  intros d1 d2 f σs vs.
  induction vs as [| σ0 σs0 v0 vs0 IH]; intros i σ v Hlk.
  - destruct i; discriminate.
  - destruct i as [| i]; cbn in *.
    + injection Hlk as Hσ Hv. subst σ0.
      apply (Eqdep_dec.inj_pair2_eq_dec _ (fun x y => decide (x = y)))
        in Hv. by subst v0.
    + apply IH, Hlk.
Qed.

Theorem hlist_map_id :
  forall {d} (f : forall σ, d σ -> d σ) σs (vs : hlist d σs),
    (forall σ v, f σ v = v) -> hlist_map f vs = vs.
Proof. intros d f σs vs Hf. induction vs; simpl; congruence. Qed.

(** * Ground Terms *)

(** The free term algebra over a signature's constructors: the domain that
    Definition 8 requires a datatype sort to have.  A [ground_term] is either a
    generator — an element of a datatype-free domain — or a constructor
    applied to further ground terms.

    [gen] is quantified over generator sorts, taking the guard as an argument,
    rather than being a plain [sort -> Type].  This is not decoration, and is necessary
    to ensure that [structure]s (introduced below) remain constructable.
    Proof irrelevance makes the extra argument invisible in use.

    The guard is [adt_free] and not Definition 9(3)'s "not a datatype"; the
    argument is at [domain_gen] below, which is where 9(3) is transcribed. *)

Section GroundTerm.

  Variables (Σ : signature) (gen : forall σ, adt_free Σ σ -> Type).

  Unset Elimination Schemes.

  Inductive ground_term : sort -> Type :=
  | GGen :
    forall σ (H : adt_free Σ σ),
      gen σ H ->
      ground_term σ
  | GConstr :
    forall c σs δ s,
      s ∈ Σ.(sort_symbols) ->
      sort_top_symbol δ = Some s ->
      c ∈ Σ.(constructors_for_sort) s ->
      monomorphic_rank Σ c σs δ ->
      sort_wf Σ δ ->
      hlist ground_term σs ->
      ground_term δ.

  Set Elimination Schemes.

End GroundTerm.

Arguments GGen {_} {_}.
Arguments GConstr {_} {_}.

Definition ground_term_constructor {Σ gen δ} (g : ground_term Σ gen δ)
  : option func :=
  match g with
  | GGen _ _ _ => None
  | GConstr c _ _ _ _ _ _ _ _ _ => Some c
  end.

(** ** Elimination *)

(** [ground_term] nests through [hlist], so Rocq's generated eliminator gives no
    induction hypothesis for a constructor's arguments.  These are the usable
    ones. *)

Section GroundTermRect.

  Context (Σ : signature) (gen : forall σ, adt_free Σ σ -> Type).
  Context (P : forall σ, ground_term Σ gen σ -> Type).
  Context (Hgen : forall σ H (x : gen σ H), P σ (GGen σ H x)).
  Context (Hconstr :
            forall c σs δ s Hs Hδ Hc Hrank Hwf (vs : hlist (ground_term Σ gen) σs),
              hlist_ForallT (ground_term Σ gen) P vs ->
              P δ (GConstr c σs δ s Hs Hδ Hc Hrank Hwf vs)).

  (** The recursion over the argument list has to be an inner [fix].  Written as
      a mutual [Fixpoint] the guard checker rejects it: [hlist] is not in the
      same inductive block as [ground_term], so it cannot see an element of the
      list as a subterm of the term.  Inlined, the subterm information
      propagates, because [ws] is passed [vs] and [vs] is a subterm of [g]. *)
  Fixpoint ground_term_rect σ (g : ground_term Σ gen σ) {struct g} : P σ g :=
    match g with
    | GGen σ H x => Hgen σ H x
    | GConstr c σs δ s Hs Hδ Hc Hrank Hwf vs =>
        Hconstr c σs δ s Hs Hδ Hc Hrank Hwf vs
          ((fix go σs' (ws : hlist (ground_term Σ gen) σs') {struct ws}
              : hlist_ForallT (ground_term Σ gen) P ws :=
              match ws with
              | HNil => tt
              | HCons σ' σs'' w ws' => (ground_term_rect σ' w, go σs'' ws')
              end) σs vs)
    end.

End GroundTermRect.

Lemma ground_term_ind :
  forall (Σ : signature) (gen : forall σ, adt_free Σ σ -> Type)
    (P : forall σ, ground_term Σ gen σ -> Prop),
    (forall σ H (x : gen σ H), P σ (GGen σ H x)) ->
    (forall c σs δ s Hs Hδ Hc Hrank Hwf (vs : hlist (ground_term Σ gen) σs),
        (forall i p, hlist_lookup (ground_term Σ gen) vs i = Some p ->
                     P (projT1 p) (projT2 p)) ->
        P δ (GConstr c σs δ s Hs Hδ Hc Hrank Hwf vs)) ->
    forall σ g, P σ g.
Proof.
  intros Σ gen P Hgen Hconstr.
  apply (ground_term_rect Σ gen P Hgen).
  intros c σs δ s Hs Hδ Hc Hrank Hwf vs Hall.
  apply Hconstr. now apply hlist_ForallT_lookup.
Qed.

(** ** Reading a Sort Off a Term *)

(** A ground term at σ witnesses that σ is one of the sorts a datatype's fields
    can be read back at: a leaf sits at a datatype-free sort, a constructor
    application at a datatype sort, and there is no third case.  This is where
    the [embeddable_sort] premises below come from when the argument sorts
    are read off a term rather than off the signature. *)
Definition embeddable_sort_of_ground_term
  (Σ : signature) (gen : forall σ, adt_free Σ σ -> Type)
  (σ : sort) (g : ground_term Σ gen σ) : embeddable_sort Σ σ :=
  match g in ground_term _ _ σ0 return embeddable_sort Σ σ0 with
  | GGen σ0 H _ => embeddable_sort_adt_free Σ σ0 H
  | GConstr c σs δ s Hs Hδ Hc Hrank Hwf _ =>
      embeddable_sort_adt Σ δ (adt_intro Σ δ s c Hs Hδ Hc Hwf)
  end.

Corollary Forall_embeddable_sort_of_hlist :
  forall Σ gen σs,
    hlist (ground_term Σ gen) σs -> Forall (embeddable_sort Σ) σs.
Proof.
  intros Σ gen σs vs. induction vs as [| σ σs' v vs' IH]; constructor;
    eauto using embeddable_sort_of_ground_term.
Qed.

(** * Structures *)

Section Structure.

  Record structure :=
    {
      domain : sort -> Type;
      domain_σ_bool : domain σ_bool = bool;
      domain_σ_map : forall σ1 σ2, domain (τ_map σ1 σ2) = (domain σ1 -> domain σ2);
      interp : func -> forall (σs : list sort) (σ : sort), interpretation domain σs σ;
    }.

  Variable (Σ : signature).

  (** ** Moving Between the Domain and the Term Algebra *)

  (** Definition 9(3)'s generators, restricted.  The standard takes them to be
      the domains of every sort that is not a datatype, and that is circular
      wherever such a sort has its domain fixed in terms of a datatype's.
      [τ_seq δ] is not a datatype, so 9(3) makes its domain a generator of the
      algebra that defines δ's domain, while [SMTLIB.Theory.Seq] fixes that
      same domain to be the lists over δ's; neither is prior to the other.
      Arrows do the same inside Definition 9 itself, 9(2) fixing the domain of
      [σ → δ] as a function space over δ's.

      Restricting the generators to the [adt_free] sorts breaks the circle.  A
      generator at a sort mentioning a datatype could only reach a term as a
      constructor field at that sort, so the two readings build the same ground
      terms exactly when no constructor field buries a datatype
      ([constructor_args_embeddable]).  §4.2.3(iv) forbids that only within a
      declaration group: a field [Int → List] of a datatype declared after
      [List] keeps to (iv), and builds a ground term under 9(3) but none here.
      At such a rank [adt_interp_constructor] and the selector condition below
      say nothing; see there. *)
  Definition domain_gen (A : structure) : forall σ, adt_free Σ σ -> Type :=
    fun σ _ => A.(domain) σ.

  Section EmbedProject.

    Context (A : structure).
    Context (Hdom : forall δ, adt Σ δ ->
                              A.(domain) δ = ground_term Σ (domain_gen A) δ).

    (** [adt_axioms]' constructor condition has to equate a domain-level
        application with a term-level one, so it needs to send a constructor's
        arguments across.  A datatype-sorted argument transports by the domain
        equation; a datatype-free one is a generator leaf.  The choice between
        the two builds a term, so it cannot be made classically — [adt_dec] is
        what makes this a function.

        An argument sort that is neither — a datatype buried under another sort
        constructor — has no ground terms at all, so there is nothing to send
        it to.  The crossing therefore takes an [embeddable_sort] proof, and
        the constructor condition below is stated only at the ranks that have
        one. *)
    Definition ground_term_embed (σ : sort) (Hi : embeddable_sort Σ σ)
      (v : A.(domain) σ) : ground_term Σ (domain_gen A) σ :=
      match decide (adt Σ σ) with
      | left  H => cast (Hdom σ H) v
      | right H => GGen σ (adt_free_of_embeddable Σ σ Hi H) v
      end.

    (** The left inverse.  A leaf gives its generator back; a constructor
        application is a datatype element, so the domain equation transports it
        back.  This is what takes a destructured [GConstr]'s argument list back
        to domain elements. *)
    Definition ground_term_project (σ : sort)
      (g : ground_term Σ (domain_gen A) σ) : A.(domain) σ :=
      match g in ground_term _ _ σ0 return A.(domain) σ0 with
      | GGen σ H x => x
      | GConstr c σs δ s Hs Hδ Hc Hrank Hwf vs =>
          cast_sym (Hdom δ (adt_intro Σ δ s c Hs Hδ Hc Hwf))
            (GConstr c σs δ s Hs Hδ Hc Hrank Hwf vs)
      end.

    Lemma ground_term_embed_adt : forall σ Hi (H : adt Σ σ) v,
        ground_term_embed σ Hi v = cast (Hdom σ H) v.
    Proof.
      intros σ Hi H v. unfold ground_term_embed.
      destruct (decide (adt Σ σ)) as [H'|H']; [| contradiction].
      now rewrite (adt_irrelevant _ _ H' H).
    Qed.

    Lemma ground_term_embed_gen : forall σ Hi (H : adt_free Σ σ) v,
        ground_term_embed σ Hi v = GGen σ H v.
    Proof.
      intros σ Hi H v. unfold ground_term_embed.
      destruct (decide (adt Σ σ)) as [H'|H'];
        [destruct (adt_free_not_adt Σ σ H H') |].
      now rewrite (adt_free_irrelevant _ _ (adt_free_of_embeddable Σ σ Hi H') H).
    Qed.

    Lemma ground_term_project_adt : forall σ (H : adt Σ σ) g,
        ground_term_project σ g = cast_sym (Hdom σ H) g.
    Proof.
      intros σ Hadt g. revert Hadt.
      destruct g as [σ0 Hn x | c σs δ s Hs Hδ Hc Hrank Hwf vs]; intros Hadt.
      - destruct (adt_free_not_adt Σ σ0 Hn Hadt).
      - simpl. now rewrite (adt_irrelevant _ _ (adt_intro _ _ _ _ Hs Hδ Hc Hwf) Hadt).
    Qed.

    (** The two round trips.  [ground_term_project] is a genuine inverse, not merely a
        retraction, which is what lets a destructured [GConstr] be put back
        together after its arguments have been read off. *)

    Lemma ground_term_project_embed : forall σ Hi v,
        ground_term_project σ (ground_term_embed σ Hi v) = v.
    Proof.
      intros σ Hi v. unfold ground_term_embed.
      destruct (decide (adt Σ σ)) as [H|H].
      - rewrite (ground_term_project_adt σ H). now rewrite cast_sym_cast.
      - reflexivity.
    Qed.

    Lemma ground_term_embed_project : forall σ Hi g,
        ground_term_embed σ Hi (ground_term_project σ g) = g.
    Proof.
      intros σ Hi g. destruct (decide (adt Σ σ)) as [Hd|Hd].
      - rewrite (ground_term_project_adt σ Hd), (ground_term_embed_adt σ Hi Hd).
        now rewrite cast_cast_sym.
      - rewrite (ground_term_embed_gen σ Hi (adt_free_of_embeddable Σ σ Hi Hd)).
        revert Hd.
        destruct g as [σ0 Hn x | c σs δ s Hs Hδ Hc Hrank Hwf vs]; intros Hd.
        + simpl. now rewrite (adt_free_irrelevant _ _
                                (adt_free_of_embeddable Σ σ0 Hi Hd) Hn).
        + exfalso. apply Hd. exact (adt_intro _ _ _ _ Hs Hδ Hc Hwf).
    Qed.

    Lemma ground_term_embed_inj : forall σ Hi v1 v2,
        ground_term_embed σ Hi v1 = ground_term_embed σ Hi v2 -> v1 = v2.
    Proof.
      intros σ Hi v1 v2 Heq.
      rewrite <- (ground_term_project_embed σ Hi v1),
              <- (ground_term_project_embed σ Hi v2).
      now f_equal.
    Qed.

    (** ** Crossing a Constructor's Argument List *)

    (** [ground_term_embed] takes a proof, so the map over an argument list
        threads one per element.  The [Forall] cannot be taken apart ahead of
        the recursion — it lives in [Prop] and the result in [Type] — so it is
        passed along as an argument and destructed one cons at a time, as the
        [hlist] is consumed. *)
    Fixpoint hlist_map_embed {σs} (vs : hlist A.(domain) σs)
      : Forall (embeddable_sort Σ) σs ->
        hlist (ground_term Σ (domain_gen A)) σs :=
      match vs in hlist _ σs0
            return Forall (embeddable_sort Σ) σs0 ->
                   hlist (ground_term Σ (domain_gen A)) σs0 with
      | HNil => fun _ => HNil
      | HCons σ σs' v vs' =>
          fun H =>
            HCons σ σs' (ground_term_embed σ (Forall_cons_head H) v)
              (hlist_map_embed vs' (Forall_cons_tail H))
      end.

    (** The round trip on a whole argument list: what a destructured [GConstr]
        needs in order to be put back together after its arguments have been
        read off the domain. *)
    Lemma hlist_map_embed_project :
      forall σs (vs : hlist (ground_term Σ (domain_gen A)) σs) H,
        hlist_map_embed (hlist_map ground_term_project vs) H = vs.
    Proof.
      intros σs vs. induction vs as [| σ σs' v vs' IH]; intros H.
      - reflexivity.
      - cbn [hlist_map hlist_map_embed].
        f_equal; [apply ground_term_embed_project | apply IH].
    Qed.

  End EmbedProject.

  (** ** The Selector and Tester Conditions *)

  (** Definition 9's requirements on selectors and testers.  They constrain
      the interpretation alone — no domain equation, no term algebra — so
      they are stated apart from [adt_axioms] and reused by a theory that
      reads the domain condition differently; [Theory.Seq] is one.  The
      consequences below are proved against them for the same reason. *)

  (** A selector applied to a value built by its own constructor returns the
      corresponding argument.  Selectors stay unconstrained off the range of
      that constructor.

      The condition is restricted to constructors for the same reason as the
      tester condition below: [selectors_for_constructor] is total on [func],
      and nothing constrains it off [constructors].

      It is also restricted to the ranks whose argument sorts satisfy [E], the
      sorts at which the reading of the domain condition in force builds ground
      terms: [embeddable_sort] for [adt_axioms], [seq_embeddable_sort] for
      [Theory.Seq]'s.  At any other rank the constructor contributes no ground
      term, so its datatype's domain has no room for its values, and asking its
      selectors to invert it would ask it to be injective into that domain.
      Where its argument domains are larger, as [Seq List]'s is than [List]'s
      under [List ::= nil | wrap (Seq List)], no interpretation would exist. *)
  Definition adt_selector_condition (E : sort -> Prop) (A : structure) : Prop :=
    forall c σs δ i g σi vi,
      c ∈ Σ.(constructors) ->
      monomorphic_rank Σ c σs δ ->
      Forall E σs ->
      Σ.(selectors_for_constructor) c !! i = Some g ->
      let G := A.(interp) g [δ] σi in
      forall vs,
        hlist_lookup A.(domain) vs i = Some (existT σi vi) ->
        let C := A.(interp) c σs δ in
        G (interp_apply A.(domain) C vs) = vi.

  (** A tester holds exactly on the range of its constructor, at each sort
      the constructor builds.  At any other sort the condition says nothing,
      as Definition 9(5) says nothing, so a tester the signature overloads at
      such a sort is left free there.

      The condition is about constructors and says nothing about any other
      symbol.  It has to be restricted explicitly, because
      [tester_for_constructor] is a total function on [func] that a signature
      is free to define as the identity off [constructors] — as [Σ_core] and
      [Σ_reals_ints] both do.  Read at such a symbol the condition would ask
      the symbol's own interpretation to recognise the symbol's own range,
      which no interpretation of a surjection can do: at [f_not] it asks
      [negb] to be true exactly on the range of [negb]. *)
  Definition adt_tester_condition (A : structure) : Prop :=
    forall c σs δ,
      c ∈ Σ.(constructors) ->
      monomorphic_rank Σ c σs δ ->
      let P := A.(interp) (Σ.(tester_for_constructor) c) [δ] σ_bool in
      let C := A.(interp) c σs δ in
      forall v,
        cast A.(domain_σ_bool) (P v) = true
        <-> exists vs, interp_apply A.(domain) C vs = v.

  (** ** The Constructor Condition *)

  (** Definition 8, second bullet, and the constructor half of Definition 9's
      ADT requirement, relative to a domain equation [Hdom]: a constructor is
      interpreted as the term former it names, so applying its interpretation
      to arguments builds exactly the ground term built from them.  Unlike the
      selector and tester conditions it is about [ground_term], so a theory
      reading the domain condition differently states its own.

      [Hσs] is §4.2.3(iv), asked of one rank: the argument sorts are ones the
      crossing is defined at.  A constructor whose argument sort buries a
      datatype under another sort constructor has no such rank, and this
      condition then says nothing about it — it is left uninterpreted rather
      than making the theory modelless.

      The premises are bound by name rather than as implications because the
      conclusion mentions their proofs: [adt_intro] and [GConstr] carry them. *)
  Definition adt_constructor_condition (A : structure)
      (Hdom : forall δ, adt Σ δ -> A.(domain) δ = ground_term Σ (domain_gen A) δ)
      : Prop :=
    forall c σs δ s
      (Hs : s ∈ Σ.(sort_symbols))
      (Hδ : sort_top_symbol δ = Some s)
      (Hc : c ∈ Σ.(constructors_for_sort) s)
      (Hrank : monomorphic_rank Σ c σs δ)
      (Hwf : sort_wf Σ δ)
      (Hσs : Forall (embeddable_sort Σ) σs),
      let C := A.(interp) c σs δ in
      forall vs, cast (Hdom δ (adt_intro Σ δ s c Hs Hδ Hc Hwf))
                   (interp_apply A.(domain) C vs) =
                 GConstr c σs δ s Hs Hδ Hc Hrank Hwf
                   (hlist_map_embed A Hdom vs Hσs).

  Record adt_axioms (A : structure) : Prop :=
    {
      (** Definition 8, first bullet, and the domain half of Definition 9's
          ADT requirement: the domain of a datatype sort is the free term
          algebra over the signature's constructors. *)
      adt_domain : forall δ, adt Σ δ -> A.(domain) δ = ground_term Σ (domain_gen A) δ;

      (** The constructor condition reads the domain through [adt_domain];
          the selector and tester conditions do not mention [ground_term], and
          are shared with the variants of the domain condition that other
          theories introduce. *)
      adt_interp_constructor : adt_constructor_condition A adt_domain;
      adt_interp_selector : adt_selector_condition (embeddable_sort Σ) A;
      adt_interp_tester : adt_tester_condition A;
    }.

End Structure.

Arguments adt_axioms {_}.
Arguments adt_domain {_} {_}.
Arguments adt_interp_constructor {_} {_}.
Arguments adt_interp_selector {_} {_}.
Arguments adt_interp_tester {_} {_}.

(** ** Consequences of the Structure Axioms *)

(** What a client can conclude about a model without unfolding [structure] or
    [adt_axioms]. *)

(** An inhabitant of every domain, obtained by interpreting the nullary
    application of the symbol [IdSimple ""] at result sort [σ].  Every [structure]
    interprets every symbol at every rank, so this always exists — a caller
    needing an element of [A.(domain) σ] never has to carry a non-emptiness
    side-condition to get one. *)
Definition domain_witness (A : structure) (σ : sort) : A.(domain) σ :=
  A.(interp) (IdSimple "") [] σ.

(** The tester condition with its [let]s reduced, in the form a caller
    applies. *)
Corollary adt_interp_tester_at_rank :
  forall Σ (A : structure) (Ht : adt_tester_condition Σ A) c σs δ,
    c ∈ Σ.(constructors) ->
    monomorphic_rank Σ c σs δ ->
    forall v,
      cast A.(domain_σ_bool)
        (A.(interp) (Σ.(tester_for_constructor) c) [δ] σ_bool v) = true
      <-> exists vs, interp_apply A.(domain) (A.(interp) c σs δ) vs = v.
Proof.
  intros Σ A Ht c σs δ Hcon Hrank v. exact (Ht c σs δ Hcon Hrank v).
Qed.

Arguments adt_interp_tester_at_rank {_} {_}.

Theorem adt_interp_constructor_disjoint :
  forall Σ (A : structure) (Hadt : adt_axioms (Σ := Σ) A)
    c1 c2 σs1 σs2 δ s
    (Hs : s ∈ Σ.(sort_symbols)) (Hδ : sort_top_symbol δ = Some s)
    (Hc1 : c1 ∈ Σ.(constructors_for_sort) s)
    (Hc2 : c2 ∈ Σ.(constructors_for_sort) s)
    (Hrank1 : monomorphic_rank Σ c1 σs1 δ)
    (Hrank2 : monomorphic_rank Σ c2 σs2 δ)
    (Hwf : sort_wf Σ δ)
    (Hσs1 : Forall (embeddable_sort Σ) σs1)
    (Hσs2 : Forall (embeddable_sort Σ) σs2)
    vs1 vs2,
    interp_apply A.(domain) (A.(interp) c1 σs1 δ) vs1
      = interp_apply A.(domain) (A.(interp) c2 σs2 δ) vs2 ->
    c1 = c2.
Proof.
  intros Σ A Hadt c1 c2 σs1 σs2 δ s Hs Hδ Hc1 Hc2 Hrank1 Hrank2 Hwf Hσs1 Hσs2
    vs1 vs2 Heq.
  pose proof (adt_interp_constructor Hadt c1 σs1 δ s Hs Hδ Hc1 Hrank1 Hwf Hσs1 vs1)
    as H1.
  pose proof (adt_interp_constructor Hadt c2 σs2 δ s Hs Hδ Hc2 Hrank2 Hwf Hσs2 vs2)
    as H2.
  simpl in H1, H2.
  set (P1 := adt_domain Hadt δ (adt_intro Σ δ s c1 Hs Hδ Hc1 Hwf)) in *.
  set (P2 := adt_domain Hadt δ (adt_intro Σ δ s c2 Hs Hδ Hc2 Hwf)) in *.
  (* Cast both sides of Heq through P1; reconcile P2 with P1 by
     proof irrelevance, then rewrite by the constructor axioms. *)
  assert (Hcast : cast P1 (interp_apply A.(domain) (A.(interp) c1 σs1 δ) vs1)
               = cast P1 (interp_apply A.(domain) (A.(interp) c2 σs2 δ) vs2)).
  { f_equal. exact Heq. }
  rewrite H1 in Hcast.
  assert (HP : P1 = P2) by (unfold P1, P2; f_equal; apply adt_irrelevant).
  rewrite HP in Hcast.
  rewrite H2 in Hcast.
  pose proof (f_equal ground_term_constructor Hcast) as Hcc. simpl in Hcc.
  now injection Hcc.
Qed.

Arguments adt_interp_constructor_disjoint {_} {_}.

(** ** What a Consumer of the Datatype Condition Needs *)

(** [adt_axioms] states the datatype condition as an equation on the domain,
    which pins it down exactly but names a particular inductive: [ground_term]
    is the standard's reading of Definition 8, in which a datatype may not
    appear below another sort constructor.  A theory that extends the standard
    past that restriction states its own variant over its own inductive —
    [Theory.Seq]'s [seq_adt_axioms] is one — and there is no reason to expect
    it to be the last.

    [adt_constructed] is what all such variants have in common, stated over the
    interpretation alone: no junk and no confusion.  It is strictly weaker —
    it does not rule out a domain with infinite descent, which the equation
    does — but it is what a consumer reasoning about a [match] needs,
    and it is what such a consumer can *name*.  [Eval.v] is below every
    variant, so [eval_total] cannot ask for [adt_axioms] without foreclosing
    the extended ones; it asks for this instead, and each variant supplies its
    own way in ([adt_constructed_of_adt_axioms] here). *)
Record adt_constructed (Σ : signature) (A : structure) : Prop :=
  {
    (** No junk: every value of a datatype sort is built by one of that
        sort's constructors.  A [match] with no variable pattern rests on
        this: it is what says one of the arms fires. *)
    adt_constructed_domain :
    forall δ (v : A.(domain) δ),
      adt Σ δ ->
      exists c σs s (vs : hlist A.(domain) σs),
        s ∈ Σ.(sort_symbols)
        /\ sort_top_symbol δ = Some s
        /\ c ∈ Σ.(constructors_for_sort) s
        /\ monomorphic_rank Σ c σs δ
        /\ interp_apply A.(domain) (A.(interp) c σs δ) vs = v;

    (** No confusion: two constructors of one sort that build a common value
        are the same constructor.  Restates
        [adt_interp_constructor_disjoint] without naming [adt_axioms]. *)
    adt_constructed_disjoint :
    forall c1 c2 σs1 σs2 δ s,
      s ∈ Σ.(sort_symbols) ->
      sort_top_symbol δ = Some s ->
      c1 ∈ Σ.(constructors_for_sort) s ->
      c2 ∈ Σ.(constructors_for_sort) s ->
      monomorphic_rank Σ c1 σs1 δ ->
      monomorphic_rank Σ c2 σs2 δ ->
      sort_wf Σ δ ->
      forall vs1 vs2,
        interp_apply A.(domain) (A.(interp) c1 σs1 δ) vs1
          = interp_apply A.(domain) (A.(interp) c2 σs2 δ) vs2 ->
        c1 = c2;
  }.

Arguments adt_constructed_domain {_} {_}.
Arguments adt_constructed_disjoint {_} {_}.

(** [adt_constructed] does not read a signature's variable sorts, so it carries
    to any signature agreeing with it except on sorts. *)
Theorem adt_constructed_signatures_agree_except_sorts : forall Σ1 Σ2 A,
    signatures_agree_except_sorts Σ1 Σ2 ->
    adt_constructed Σ1 A -> adt_constructed Σ2 A.
Proof.
  intros Σ1 Σ2 A Hsym Hadt. split.
  - intros δ v Hδ.
    apply (adt_signatures_agree_except_sorts _ _ _
      (signatures_agree_except_sorts_sym _ _ Hsym)) in Hδ.
    destruct (adt_constructed_domain Hadt δ v Hδ)
      as (c & σs & s & vs & Hs & Hhead & Hc & Hrank & Hv).
    exists c, σs, s, vs.
    rewrite <- (signatures_agree_except_sorts_sort_symbols _ _ Hsym),
      <- (signatures_agree_except_sorts_constructors_for_sort _ _ Hsym).
    split_and!; [exact Hs | exact Hhead | exact Hc | | exact Hv].
    exact (monomorphic_rank_signatures_agree_except_sorts _ _ _ _ _ Hsym Hrank).
  - intros c1 c2 σs1 σs2 δ s Hs Hhead Hc1 Hc2 Hrank1 Hrank2 Hwf.
    pose proof (signatures_agree_except_sorts_sym _ _ Hsym) as Hsym'.
    apply (adt_constructed_disjoint Hadt c1 c2 σs1 σs2 δ s).
    + rewrite (signatures_agree_except_sorts_sort_symbols _ _ Hsym). exact Hs.
    + exact Hhead.
    + rewrite
      (signatures_agree_except_sorts_constructors_for_sort _ _ Hsym). exact Hc1.
    + rewrite
      (signatures_agree_except_sorts_constructors_for_sort _ _ Hsym). exact Hc2.
    + exact (monomorphic_rank_signatures_agree_except_sorts _ _ _ _ _
               Hsym' Hrank1).
    + exact (monomorphic_rank_signatures_agree_except_sorts _ _ _ _ _
               Hsym' Hrank2).
    + exact (sort_wf_signatures_agree_except_sorts _ _ _ Hsym' Hwf).
Qed.

Theorem adt_constructed_of_adt_axioms :
  forall Σ (A : structure),
    constructor_args_embeddable Σ ->
    adt_axioms (Σ := Σ) A -> adt_constructed Σ A.
Proof.
  intros Σ A Hiv Hadt. constructor.
  - intros δ v Hδ.
    (* a datatype domain is the ground terms at that sort, and it holds no
       generator leaves, so the element is a constructor application *)
    destruct (cast (adt_domain Hadt δ Hδ) v)
      as [σ0 Hn x | c σs δ' s Hs Hhead Hc Hrank Hwf vs] eqn:Hg;
      [destruct (adt_free_not_adt Σ σ0 Hn Hδ) |].
    (* the arguments are themselves ground terms, so their sorts are ones the
       crossing is defined at — no appeal to the signature is needed here *)
    pose proof (Forall_embeddable_sort_of_hlist Σ _ σs vs) as Hσs.
    (* the arguments come back as ground terms; project them to the domain *)
    exists c, σs, s, (hlist_map (ground_term_project Σ A (adt_domain Hadt)) vs).
    split_and!; try assumption.
    (* [c]'s interpretation builds that same ground term, so the two agree
       underneath the domain equality *)
    pose proof (adt_interp_constructor Hadt c σs δ' s Hs Hhead Hc Hrank Hwf Hσs
                  (hlist_map (ground_term_project Σ A (adt_domain Hadt)) vs)) as Hconstr.
    simpl in Hconstr.
    rewrite hlist_map_embed_project in Hconstr.
    rewrite (adt_irrelevant _ _ (adt_intro Σ δ' s c Hs Hhead Hc Hwf) Hδ) in Hconstr.
    rewrite <- Hg in Hconstr.
    apply (f_equal (cast_sym (adt_domain Hadt δ' Hδ))) in Hconstr.
    rewrite !cast_sym_cast in Hconstr.
    exact Hconstr.
  - intros c1 c2 σs1 σs2 δ s Hs Hδ Hc1 Hc2 Hrank1 Hrank2 Hwf vs1 vs2 Heq.
    eapply (adt_interp_constructor_disjoint Hadt c1 c2 σs1 σs2 δ s
              Hs Hδ Hc1 Hc2 Hrank1 Hrank2 Hwf
              (Hiv c1 σs1 δ s Hs Hδ Hc1 Hrank1)
              (Hiv c2 σs2 δ s Hs Hδ Hc2 Hrank2)).
    exact Heq.
Qed.

(** No-confusion in the form a client of a tester wants: outside the range of
    its own constructor a tester is false.  Stated against [adt_constructed]
    rather than [adt_axioms], so it serves every reading of the domain
    condition. *)
Theorem adt_interp_tester_false_off_constructor :
  forall Σ (A : structure)
    (Ht : adt_tester_condition Σ A) (Hcon : adt_constructed Σ A)
    c1 c2 σs1 σs2 δ s
    (Hs : s ∈ Σ.(sort_symbols)) (Hδ : sort_top_symbol δ = Some s)
    (Hc1 : c1 ∈ Σ.(constructors_for_sort) s)
    (Hc2 : c2 ∈ Σ.(constructors_for_sort) s)
    (Hrank1 : monomorphic_rank Σ c1 σs1 δ)
    (Hrank2 : monomorphic_rank Σ c2 σs2 δ)
    (Hwf : sort_wf Σ δ)
    vs2,
    c1 <> c2 ->
    cast A.(domain_σ_bool)
      (A.(interp) (Σ.(tester_for_constructor) c1) [δ] σ_bool
        (interp_apply A.(domain) (A.(interp) c2 σs2 δ) vs2)) = false.
Proof.
  intros Σ A Ht Hcon c1 c2 σs1 σs2 δ s Hs Hδ Hc1 Hc2 Hrank1 Hrank2 Hwf vs2 Hne.
  assert (Hc1' : c1 ∈ Σ.(constructors))
    by (eapply Σ.(constructors_for_sort_wf); eassumption).
  pose proof (Ht c1 σs1 δ Hc1' Hrank1) as Htest.
  simpl in Htest.
  set (v := interp_apply A.(domain) (A.(interp) c2 σs2 δ) vs2) in *.
  destruct (cast A.(domain_σ_bool)
              (A.(interp) (Σ.(tester_for_constructor) c1) [δ] σ_bool v))
    eqn:Hb.
  - exfalso.
    apply Htest in Hb.
    destruct Hb as [vs1 Hvs1].
    eapply (adt_constructed_disjoint Hcon) in Hvs1; eauto.
  - reflexivity.
Qed.

Arguments adt_interp_tester_false_off_constructor {_} {_}.

(** * Theories *)

(** Definition 12. A theory names a signature Σ together with a class of
    Σ-structures obeying some axioms; the members of that class are the
    theory's models.

    The datatype condition is not among those axioms until the signature is
    finished.  [adt_axioms] is an equation about [A.(domain) δ] at every
    datatype sort of Σ, and [ground_term Σ] is indexed by Σ, so asserting it
    at a component's own signature says something about a different type from
    the condition Definition 9 places on the *combined* structure, with no
    transport between the two.  A component therefore owes no datatype
    condition at all: the finished structure owes it once, at the signature
    its models are really about.

    [pretheory] is what a component is — a signature and a model predicate,
    composable and extensible by variable sortings.  [theory_init] closes a
    pretheory into a [theory] by conjoining the datatype condition at the
    signature reached, and [theory] is what [sat] consumes.  Composing past an
    [init] is then not merely discouraged but unrepresentable.  A theory
    wanting the extended reading of the datatype condition closes with its own
    operation instead — see [Theory.Seq]'s [theory_init_seq]. *)

Record pretheory :=
  {
    pΣ : signature;
    pmodels : structure -> Prop;
  }.

Record pretheories_composable (pT1 : pretheory) (pT2 : pretheory) : Prop :=
  {
    ptc_signatures_composable : signatures_composable pT1.(pΣ) pT2.(pΣ);
  }.

Arguments ptc_signatures_composable {_} {_}.

Definition pretheory_compose
  (pT1 : pretheory) (pT2 : pretheory)
  (C : pretheories_composable pT1 pT2) : pretheory :=
  {|
    pΣ := pT1.(pΣ) ⊕[ C.(ptc_signatures_composable) ] pT2.(pΣ);
    pmodels A :=
      pT1.(pmodels) A /\ pT2.(pmodels) A;
  |}.

#[global] Instance pretheory_compose_compose :
  Compose pretheory pretheories_composable := pretheory_compose.

Definition pretheory_add_sorts (pT : pretheory) (sorts' : sorting) : pretheory :=
  {|
    pΣ := sorts' ⊍ pT.(pΣ);
    pmodels A := pT.(pmodels) A;
  |}.

Record theory :=
  {
    Σ : signature;
    models : structure -> Prop;
  }.

(** Closing with the standard's reading of Definition 8: a datatype domain is
    the well-sorted ground terms, in which a datatype sort occurs as a
    constructor's argument sort and never below another sort constructor. *)
Definition theory_init (pT : pretheory) : theory :=
  {|
    Σ := pT.(pΣ);
    models A := pT.(pmodels) A /\ adt_axioms (Σ := pT.(pΣ)) A;
  |}.

(** * Model Construction *)

(** Exhibiting a model means producing one [structure]: a domain, and an
    interpretation of every symbol at every rank.  For a theory assembled by
    [pretheory_compose] the interpretation can be built one component at a
    time, but the domain cannot.  The domain is a single object that all the
    components constrain together, and some of those constraints reach beyond
    the component that makes them: [Theory.Seq] asks for
    [domain (τ_seq σ) = list (domain σ)] at every sort, including the sorts
    other components introduce.

    The domain is therefore chosen first, and everything below varies the
    interpretation over a domain held fixed.  A component supplies two facts
    about itself, [pretheory_local] and [pretheory_interpretable], and the
    theorems here assemble them.

    To build a model of a composed theory:

    - construct a domain meeting every component's requirements;
    - take each component's [pretheory_interpretable] at that domain and
      combine them with [pretheory_compose_interpretable];
    - discharge the datatype condition at the finished signature, which no
      component owes — see [theory_init]. *)

(** The structure with domain [D] and interpretation [ι]. *)
Definition structure_of (D : sort -> Type)
  (Hbool : D σ_bool = bool)
  (Hmap : forall σ1 σ2, D (τ_map σ1 σ2) = (D σ1 -> D σ2))
  (ι : forall f (σs : list sort) (σ : sort), interpretation D σs σ)
  : structure :=
  {|
    domain := D;
    domain_σ_bool := Hbool;
    domain_σ_map := Hmap;
    interp := ι;
  |}.

(** [ι1] and [ι2] give the same value at every rank of every symbol in
    [fs]. *)
Definition interp_agree_on (D : sort -> Type) (fs : func -> Prop)
  (ι1 ι2 : forall f (σs : list sort) (σ : sort), interpretation D σs σ) : Prop :=
  forall f, fs f -> forall σs σ, ι1 f σs σ = ι2 f σs σ.

(** ** Building an Interpretation *)

(** [interp] is total: a structure gives a value at every rank, whether or not
    the signature declares it.  So an interpretation that pins a handful of
    ranks needs somewhere to send the rest, and building a structure at all
    needs the domain inhabited at every sort.  Three combinators cover that:
    a base to fall through to, an override at one rank, and an override at one
    symbol — the last for a symbol like [f_eq], whose ranks are not a finite
    list. *)
Section BuildInterp.

  Context (D : sort -> Type).

  (** Ignore the arguments and return the domain's witness. *)
  Fixpoint interp_const (witness : forall σ, D σ) (σs : list sort) (σ : sort)
    : interpretation D σs σ :=
    match σs with
    | [] => witness σ
    | _ :: σs' => fun _ => interp_const witness σs' σ
    end.

  (** Override [base] at one rank, in the shape of stdpp's [fn_insert]: key,
      value, function. *)
  Definition interp_insert_rank (σs : list sort) (σ : sort)
    (v : interpretation D σs σ)
    (base : forall σs σ, interpretation D σs σ)
    : forall σs' σ', interpretation D σs' σ' :=
    fun σs' σ' =>
      match decide ((σs', σ') = (σs, σ)) with
      | left H =>
          @eq_rect_r (list sort * sort) (σs, σ)
            (fun p : list sort * sort => interpretation D (fst p) (snd p))
            v (σs', σ') H
      | right _ => base σs' σ'
      end.

  Lemma interp_insert_rank_eq : forall σs σ v base,
      interp_insert_rank σs σ v base σs σ = v.
  Proof.
    intros σs σ v base. unfold interp_insert_rank.
    destruct (decide ((σs, σ) = (σs, σ))) as [Heq | Hne];
      [| exfalso; by apply Hne].
    by rewrite (Eqdep_dec.UIP_dec (fun x y => decide (x = y)) Heq eq_refl).
  Qed.

  Lemma interp_insert_rank_ne : forall σs σ v base σs' σ',
      (σs', σ') <> (σs, σ) ->
      interp_insert_rank σs σ v base σs' σ' = base σs' σ'.
  Proof.
    intros σs σ v base σs' σ' Hne. unfold interp_insert_rank.
    by destruct (decide ((σs', σ') = (σs, σ))).
  Qed.

  (** Override [base] at one function symbol, at every rank. *)
  Definition interp_insert_func (f : func)
    (v : forall σs σ, interpretation D σs σ)
    (base : forall f σs σ, interpretation D σs σ)
    : forall f' σs σ, interpretation D σs σ :=
    fun f' σs σ => if decide (f' = f) then v σs σ else base f' σs σ.

  Lemma interp_insert_func_eq : forall f v base σs σ,
      interp_insert_func f v base f σs σ = v σs σ.
  Proof.
    intros f v base σs σ. unfold interp_insert_func.
    by rewrite decide_True by reflexivity.
  Qed.

  Lemma interp_insert_func_ne : forall f v base f' σs σ,
      f' <> f -> interp_insert_func f v base f' σs σ = base f' σs σ.
  Proof.
    intros f v base f' σs σ Hne. unfold interp_insert_func.
    by rewrite decide_False.
  Qed.

End BuildInterp.

(** [pT]'s model conditions depend on the domain and on the symbols [pT]
    declares, and on nothing else — so interpreting another component's
    symbols leaves them standing.  A component proves this of its own
    conditions; it is immediate when each condition names a single symbol. *)
Definition pretheory_local (pT : pretheory) : Prop :=
  forall D Hbool Hmap ι1 ι2,
    interp_agree_on D pT.(pΣ).(funcs) ι1 ι2 ->
    pT.(pmodels) (structure_of D Hbool Hmap ι1) ->
    pT.(pmodels) (structure_of D Hbool Hmap ι2).

(** [pT]'s symbols can be interpreted over the domain [D].  Whatever [pT]
    requires of [D] is a premise of the component's own theorem rather than
    part of this predicate, so that a composition can be stated over one
    domain. *)
Definition pretheory_interpretable (pT : pretheory) (D : sort -> Type)
  (Hbool : D σ_bool = bool)
  (Hmap : forall σ1 σ2, D (τ_map σ1 σ2) = (D σ1 -> D σ2)) : Prop :=
  exists ι, pT.(pmodels) (structure_of D Hbool Hmap ι).

(** The composite declares the union of the two symbol sets, so agreeing on
    them is agreeing on each. *)
Theorem pretheory_compose_local :
  forall pT1 pT2 (C : pretheories_composable pT1 pT2),
    pretheory_local pT1 ->
    pretheory_local pT2 ->
    pretheory_local (pT1 ⊕[ C ] pT2).
Proof.
  intros pT1 pT2 C Hloc1 Hloc2 D Hbool Hmap ι1 ι2 Hagree [Hm1 Hm2].
  split.
  - eapply Hloc1; [| exact Hm1].
    intros f Hf. apply Hagree. left. exact Hf.
  - eapply Hloc2; [| exact Hm2].
    intros f Hf. apply Hagree. right. exact Hf.
Qed.

(** Interpret each symbol by the component that declares it.

    The two components must declare disjoint symbols.
    [signatures_composable] makes the signatures agree where they overlap — on
    arities, on [constructors_for_sort], and on the ranks of shared
    constructors — but it still admits a shared function symbol, which the two
    model predicates may pin to different values.  Where components do share a
    symbol, this needs a different argument: that their conditions on it
    agree. *)
Theorem pretheory_compose_interpretable :
  forall pT1 pT2 (C : pretheories_composable pT1 pT2) D Hbool Hmap,
    pretheory_local pT1 ->
    pretheory_local pT2 ->
    (forall f, pT1.(pΣ).(funcs) f -> pT2.(pΣ).(funcs) f -> False) ->
    pretheory_interpretable pT1 D Hbool Hmap ->
    pretheory_interpretable pT2 D Hbool Hmap ->
    pretheory_interpretable (pT1 ⊕[ C ] pT2) D Hbool Hmap.
Proof.
  intros pT1 pT2 C D Hbool Hmap Hloc1 Hloc2 Hdisj [ι1 Hm1] [ι2 Hm2].
  (* [funcs] is a bare [Prop], but a signature carries its decision, so the
     split between the two components is by [decide]. *)
  exists (fun f σs σ =>
    match decide (pT1.(pΣ).(funcs) f) with
    | left _ => ι1 f σs σ
    | right _ => ι2 f σs σ
    end).
  split.
  - eapply Hloc1; [| exact Hm1].
    intros f Hf σs σ. destruct (decide _); [reflexivity |].
    contradiction.
  - eapply Hloc2; [| exact Hm2].
    intros f Hf σs σ. destruct (decide _) as [Hf1 |];
      [| reflexivity].
    exfalso. eapply Hdisj; eassumption.
Qed.

(** [pretheory_add_sorts] changes neither the declared symbols nor the model
    predicate, so both properties survive it. *)
Theorem pretheory_add_sorts_local :
  forall pT sorts',
    pretheory_local pT ->
    pretheory_local (pretheory_add_sorts pT sorts').
Proof.
  intros pT sorts' Hloc D Hbool Hmap ι1 ι2 Hagree Hm. eapply Hloc; eauto.
Qed.

Theorem pretheory_add_sorts_interpretable :
  forall pT sorts' D Hbool Hmap,
    pretheory_interpretable pT D Hbool Hmap ->
    pretheory_interpretable (pretheory_add_sorts pT sorts') D Hbool Hmap.
Proof.
  intros pT sorts' D Hbool Hmap [ι Hm]. exists ι. exact Hm.
Qed.
