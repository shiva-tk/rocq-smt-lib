(** * SMTLIB.Symbols : Symbols, Identifiers and Sorts *)

(** Three layers, in order: the symbol and identifier vocabulary shared by every
    other file in the package; the [sort] datatype
    (corresponding with Sec. 5.1, _the language of sorts_), with the induction
    principles its nested list argument makes necessary; and sort substitution,
    by which a polymorphic rank is instantiated at a monomorphic sort.

    Throughout, [σ] names a sort required to be monomorphic and [τ] one that is
    arbitrary. *)

From Hammer Require Export Tactics.
From stdpp Require Export list gmap countable strings.
From SMTLIB Require Import Utils.

(** * Symbols *)

Notation symbol := string.

Notation var := symbol.

(** * Identifiers & Indices *)

(** Identifiers can be indexed: see Sec. 3.3, _identifiers_. *)

Inductive index : Type :=
| IdxNum (n : nat)
| IdxSym (s : symbol).

Global Instance index_eq_decision : EqDecision index.
Proof. solve_decision. Qed.

Global Instance index_countable : Countable index :=
 inj_countable
  (λ i,
    match i with
    | IdxNum n => inl n
    | IdxSym s => inr s
    end)
  (λ code,
    match code with
    | inl n => Some (IdxNum n)
    | inr s => Some (IdxSym s)
    end)
  (λ i,
    match i with
    | IdxNum n => eq_refl
    | IdxSym s => eq_refl
    end).

Inductive identifier : Type :=
| IdSimple (s : symbol)
| IdIndexed (s : symbol) (idx : list index).

(** A function symbol, in the head position of an application. *)
Notation func := identifier.

(** The head of an applied sort. *)
Notation sortsymb := identifier.

(** A sort variable, bound by the parameter list of a polymorphic rank. *)
Notation sortparam := identifier.

Global Instance identifier_eq_decision : EqDecision identifier.
Proof. solve_decision. Qed.

Global Instance identifier_countable : Countable identifier :=
 inj_countable
  (λ i,
    match i with
    | IdSimple s => inl s
    | IdIndexed s idx => inr (s, idx)
    end)
  (λ code,
    match code with
    | inl s => Some (IdSimple s)
    | inr (s, idx) => Some (IdIndexed s idx)
    end)
  (λ i,
    match i with
    | IdSimple s => eq_refl
    | IdIndexed s idx => eq_refl
    end).

Global Instance identifier_infinite : Infinite identifier :=
 inj_infinite
  IdSimple
  (fun i => match i with
         | IdSimple s => Some s
         | IdIndexed _ _ => None
         end)
  (λ _, eq_refl).

Definition identifier_add_prefix (prefix : string) (id : identifier) :=
 match id with
 | IdSimple s => IdSimple (prefix ++ s)
 | IdIndexed s idx => IdIndexed (prefix ++ s) idx
 end.

(** With this in scope a bare string literal may be written wherever an
    identifier is expected, which is how the constants further down are
    defined. *)
Coercion IdSimple : symbol >-> identifier.

(** ** Boolean Equality *)

(** The [EqDecision] instances above already decide equality, but they return a
    [sumbool] carrying a proof.  These return a plain [bool], which is what the
    hammer tactics and any [if] inside a definition want instead. *)

Definition index_eqb (i1 i2 : index) : bool :=
 match i1, i2 with
 | IdxNum n1, IdxNum n2 => Nat.eqb n1 n2
 | IdxSym s1, IdxSym s2 => String.eqb s1 s2
 | _, _ => false
 end.

Lemma index_eqb_iff : forall i1 i2, index_eqb i1 i2 = true <-> i1 = i2.
Proof.
 intros [ n1 | s1 ] [ n2 | s2 ]; simpl; split; intros Heq; try discriminate.
 - f_equal. by apply Nat.eqb_eq.
 - injection Heq as ->. by apply Nat.eqb_eq.
 - f_equal. by apply String.eqb_eq.
 - injection Heq as ->. by apply String.eqb_eq.
Qed.

Definition identifier_eqb (id1 id2 : identifier) : bool :=
 match id1, id2 with
 | IdSimple s1, IdSimple s2 => String.eqb s1 s2
 | IdIndexed s1 idx1, IdIndexed s2 idx2 =>
     String.eqb s1 s2 && list_eqb index_eqb idx1 idx2
 | _, _ => false
 end.

Theorem identifier_eqb_iff : forall id1 id2,
 identifier_eqb id1 id2 = true <-> id1 = id2.
Proof.
 intros [ s1 | s1 i1 ] [ s2 | s2 i2 ]; simpl; split; intros Heq; try discriminate.
 - f_equal. by apply String.eqb_eq.
 - injection Heq as ->. by apply String.eqb_eq.
 - apply andb_true_iff in Heq as [ Hs Hi ].
   apply String.eqb_eq in Hs.
   apply list_eqb_iff in Hi; [| apply index_eqb_iff ].
   congruence.
 - injection Heq as -> ->. apply andb_true_iff. split.
   + by apply String.eqb_eq.
   + apply list_eqb_iff; [ apply index_eqb_iff | reflexivity ].
Qed.

(** * Sorts *)

(** A sort is a parameter or a sort symbol applied to a list of argument sorts.
    Nullary application is how a sort symbol of arity 0, such as [Bool], is
    written as a sort. *)

Unset Elimination Schemes.

Inductive sort : Type :=
| SParam (u : sortparam)
| SApp (s : sortsymb) (τs : list sort).

Set Elimination Schemes.

(** ** Induction and Recursion Principles *)

(** [SApp] holds a [list sort], so the scheme Rocq generates by default offers
    no hypothesis about the elements of that list and is useless for every proof
    in this file.  Generation is switched off around the declaration above and
    the principles are supplied here instead.

    [sort_ind] is written directly, with the element hypothesis
    [∀ τ, τ ∈ τs -> P τ].  Since no automatic [sort_ind] exists, it is also what
    every later [induction τ] on a sort resolves to by name — a dependency that
    no `.glob` records and that no reordering may break.

    [sort_rect] is the [Type] analogue.  It is derived rather than written out,
    from the well-founded subterm order [sub_sort], and [sort_rec] is its [Set]
    instance. *)

(* Defined, not Qed, down the whole chain: a function built by [sort_rect]
   reduces only if [wf_sub_sort] does, and that only if [sort_ind] does. *)

Section sort_ind.

  Variables (P : sort -> Prop)
    (HP_SParam : ∀ u, P (SParam u))
    (HP_SApp : ∀ s τs, (forall τ, τ ∈ τs -> P τ) -> P (SApp s τs)).

  Fixpoint sort_ind τ : P τ.
  Proof.
    destruct τ.
    - apply HP_SParam.
    - apply HP_SApp. induction τs; intros * Helem.
      + inversion Helem.
      + rewrite elem_of_cons in Helem. destruct Helem as [->|Helem].
        ++ apply sort_ind.
        ++ apply IHτs. apply Helem.
  Defined.

End sort_ind.

(** [sub_sort τ1 τ2] holds when [τ1] is an immediate argument of [τ2]. *)
Definition sub_sort τ1 τ2 : Prop :=
  match τ2 with
  | SApp s τs => τ1 ∈ τs
  | _ => False
  end.

Theorem wf_sub_sort : well_founded sub_sort.
Proof.
  intros τ. induction τ; sauto lq:on rew:off.
Defined.

Section sort_rect.

  Variables (P : sort -> Type)
    (HP_SParam : ∀ u, P (SParam u))
    (HP_SApp : ∀ s τs, (forall τ, τ ∈ τs -> P τ) -> P (SApp s τs)).

  Definition sort_rect τ : P τ.
  Proof.
    induction τ
      as [ ? IH ]
      using (well_founded_induction_type wf_sub_sort).
    destruct τ; hauto l:on.
  Defined.

End sort_rect.

Definition sort_rec (P : _ -> Set) := sort_rect P.

(** ** Decidable Equality and Countability *)

Global Instance sort_eq_decision : EqDecision sort.
Proof.
  unfold EqDecision, Decision; intros; decide equality;
  simplify_eq; try solve_trivial_decision.
  apply list_eq_dec_elem_of. naive_solver.
Qed.

(** Countability goes through [gen_tree identifier]: a parameter becomes a leaf,
    and an application becomes a node holding its top symbol as a leaf followed
    by the encodings of its arguments. *)
Fixpoint sort_to_gen_tree (s : sort) : gen_tree identifier :=
  match s with
  | SParam u => GenLeaf u
  | SApp sym τs => GenNode 0 (GenLeaf sym :: map sort_to_gen_tree τs)
  end.

Fixpoint gen_tree_to_sort (t : gen_tree identifier) : option sort :=
  match t with
  | GenLeaf u => Some (SParam u)
  | GenNode 0 (GenLeaf sym :: ts) =>
      τs ← mapM gen_tree_to_sort ts;
      Some (SApp sym τs)
  | _ => None
  end.

Lemma sort_gen_tree_cancel : ∀ s, gen_tree_to_sort (sort_to_gen_tree s) = Some s.
Proof.
  induction s using sort_ind; simpl.
  - reflexivity.
  - enough (mapM gen_tree_to_sort (map sort_to_gen_tree τs) = Some τs) as ->;
      [reflexivity|].
    induction τs as [|τ τs' IH]; simpl in *; [reflexivity|].
    rewrite (H τ) by set_solver.
    rewrite IH by (intros; apply H; set_solver).
    reflexivity.
Qed.

Global Instance sort_countable : Countable sort :=
  inj_countable sort_to_gen_tree gen_tree_to_sort sort_gen_tree_cancel.

(** ** Operations on Sorts *)

(** The parameters occurring anywhere in a sort.  Empty exactly when the sort is
    monomorphic — see [monomorphic_iff_sort_params_empty], which needs
    [monomorphic] and so is stated below it. *)
Fixpoint sort_params (τ : sort) : gset sortparam :=
  match τ with
  | SParam u => {[ u ]}
  | SApp _ τs => ⋃ (map sort_params τs)
  end.

(** The top symbol of a sort, absent for a bare parameter. *)
Definition sort_top_symbol (τ : sort) : option sortsymb :=
  match τ with
  | SParam _ => None
  | SApp s _ => Some s
  end.

(** ** Well-Formedness *)

(** A sort is well formed against a set [S] of declared sort symbols and an
    arity for each: every applied symbol is declared, and is applied to exactly
    as many arguments as its arity gives.  A parameter is well formed
    unconditionally — nothing here constrains which parameters may appear.

    Well-formedness is conceptually a property of a sort against a *signature*,
    and that is how a client states it: [sort_wf] is this predicate at a
    signature's own sort symbols and arities.  It is the base form because a
    signature is defined partly in terms of it — the well-formedness of a
    signature's sorts and of its ranks are both fields of the record — so
    nothing signature-shaped can be said until it exists. *)
Inductive sort_wf_base (S : gset sortsymb) (arity : sortsymb -> nat) : sort -> Prop :=
| WF_SParam : forall u, sort_wf_base S arity (SParam u)
| WF_SApp : forall s τs,
    s ∈ S ->
    arity s = length τs ->
    Forall (sort_wf_base S arity) τs ->
    sort_wf_base S arity (SApp s τs).

Global Instance sort_wf_base_dec (S : gset sortsymb) (arity : sortsymb -> nat)
  (τ : sort) : Decision (sort_wf_base S arity τ).
Proof.
  induction τ as [u | s τs IH] using sort_rect.
  - left. constructor.
  - destruct (decide (s ∈ S)) as [Hs | Hs];
      [| right; intros Hwf; inversion Hwf; contradiction].
    destruct (decide (arity s = length τs)) as [Ha | Ha];
      [| right; intros Hwf; inversion Hwf; contradiction].
    destruct (Forall_dec_elem (sort_wf_base S arity) τs IH) as [Hall | Hall].
    + left. by constructor.
    + right. intros Hwf. inversion Hwf. contradiction.
Defined.

(** * Elementary Sorts *)

(** The sorts and sort symbols every signature carries, whatever theories it is
    built from: the boolean sort that every formula has, and the map sort
    constructor [->] of §3.9, whose sorts denote maps.  A map is a value, and
    so has a sort; a function symbol has ranks instead, and is not one. *)

Definition s_bool : sortsymb := "Bool".
Definition s_map : sortsymb := "->".
Definition σ_bool : sort := SApp s_bool [].
Definition τ_map (τ : sort) (τ' : sort) : sort :=
  SApp s_map [τ ; τ'].

(** * Sort Parameters *)

(** A fixed supply of parameter names, used to state the polymorphic ranks in
    the theory files.  Unlike the sorts above these are an arbitrary choice
    rather than anything the standard fixes: any two distinct parameters would
    do, and the names are short only so the ranks read well. *)

Definition u_A : sortparam := "A".
Definition u_B : sortparam := "B".
Definition τ_A : sort := SParam u_A.
Definition τ_B : sort := SParam u_B.

(** * Monomorphic Sorts *)

(* TODO: Don't make this a prop,
   separate out into its own inductive datatype. *)
Inductive monomorphic : sort -> Prop :=
| M_SApp : forall s τs, Forall monomorphic τs -> monomorphic (SApp s τs).

Theorem monomorphic_SApp_const : forall s, monomorphic (SApp s []).
Proof. constructor. constructor. Qed.

Corollary monomorphic_σ_bool : monomorphic σ_bool.
Proof. apply monomorphic_SApp_const. Qed.

Theorem monomorphic_iff_sort_params_empty : forall τ,
    monomorphic τ <-> sort_params τ = ∅.
Proof.
  induction τ using sort_ind; simpl.
  - (* SParam *) split; intros Hm; [inversion Hm | set_solver].
  - (* SApp *) split; intros Hm.
    + inversion Hm as [ ? ? Hall ]; subst.
      apply set_eq. intros u. rewrite elem_of_union_list.
      split; [| set_solver]. intros (X & HX & Hu).
      apply list_elem_of_fmap in HX as (τ & -> & Hτ).
      rewrite Forall_forall in Hall.
      pose proof (proj1 (H τ Hτ) (Hall τ Hτ)) as Hempty.
      rewrite Hempty in Hu. set_solver.
    + constructor. rewrite Forall_forall. intros τ Hτ.
      apply (H τ Hτ). apply set_eq. intros u.
      split; [| set_solver]. intros Hu.
      assert (Hin : u ∈ ⋃ (map sort_params τs)).
      { apply elem_of_union_list. exists (sort_params τ).
        split; [apply list_elem_of_fmap; eauto | done]. }
      set_solver.
Qed.

(** * Sort Substitution *)

(** A [sort_subst_map] assigns sorts to sort parameters, and [sort_subst]
    applies one throughout a sort, leaving any parameter the map does not
    mention.  This is how a polymorphic rank is brought to a particular sort:
    the two lemmas below say when two assignments cannot be told apart by doing
    so. *)

Notation sort_subst_map := (gmap sortparam sort).

Definition sort_subst_map_monomorphic (θ : sort_subst_map) : Prop :=
  forall u σ, θ !! u = Some σ -> monomorphic σ.

Fixpoint sort_subst (θ : sort_subst_map) (τ : sort) : sort :=
  match τ with
  | SParam u =>
      match θ !! u with
      | None => SParam u
      | Some τ' => τ'
      end
  | SApp s τs =>
      SApp s (map (sort_subst θ) τs)
  end.

Theorem sort_subst_empty : forall τ, sort_subst ∅ τ = τ.
Proof.
  induction τ using sort_ind; simpl; [reflexivity |].
  f_equal. rewrite <- (list_fmap_id τs) at 2.
  apply list_fmap_ext. intros i τ Hi. apply H.
  apply list_elem_of_lookup_2 with i. exact Hi.
Qed.

(** [sort_subst θ1] and [sort_subst θ2] agreeing on a sort [τ] forces them to
    agree on every parameter occurring in [τ]. *)
Lemma sort_subst_eq_param_agree :
  forall θ1 θ2 τ,
    sort_subst θ1 τ = sort_subst θ2 τ ->
    forall u, u ∈ sort_params τ ->
      sort_subst θ1 (SParam u) = sort_subst θ2 (SParam u).
Proof.
  intros θ1 θ2 τ. induction τ using sort_ind; intros Heq w Hw.
  - (* SParam *) simpl in Hw. apply elem_of_singleton in Hw. subst w.
    exact Heq.
  - (* SApp *) simpl in Heq. injection Heq as Hmap.
    simpl in Hw. apply elem_of_union_list in Hw as (X & HX & Hw).
    apply list_elem_of_fmap in HX as (τ0 & -> & Hτ0).
    apply list_elem_of_lookup in Hτ0 as (i & Hi).
    assert (Hsub_i : sort_subst θ1 τ0 = sort_subst θ2 τ0).
    { pose proof (f_equal (fun l => l !! i) Hmap) as Hmi.
      rewrite !list_lookup_fmap, Hi in Hmi. simpl in Hmi.
      injection Hmi as Hmi. exact Hmi. }
    apply (H τ0 (list_elem_of_lookup_2 _ _ _ Hi) Hsub_i w Hw).
Qed.

(** If [sort_subst θ1] and [sort_subst θ2] agree on [τ] and [τ']'s parameters
    are all among [τ]'s, then they agree on [τ'] too. *)
Lemma sort_subst_eq_subset :
  forall θ1 θ2 τ τ',
    sort_subst θ1 τ = sort_subst θ2 τ ->
    sort_params τ' ⊆ sort_params τ ->
    sort_subst θ1 τ' = sort_subst θ2 τ'.
Proof.
  intros θ1 θ2 τ τ' Heq Hsub.
  induction τ' using sort_ind.
  - (* SParam *) apply (sort_subst_eq_param_agree θ1 θ2 τ Heq).
    apply Hsub. simpl. apply elem_of_singleton. reflexivity.
  - (* SApp *) simpl. f_equal. apply list_eq. intros i.
    rewrite !list_lookup_fmap.
    destruct (τs !! i) as [τ0|] eqn:Hi; simpl; [|reflexivity].
    f_equal. apply H; [apply list_elem_of_lookup_2 with i; exact Hi|].
    etrans; [|exact Hsub]. simpl.
    intros p Hp. apply elem_of_union_list. exists (sort_params τ0).
    split; [|exact Hp]. apply list_elem_of_fmap. exists τ0.
    split; [reflexivity|apply list_elem_of_lookup_2 with i; exact Hi].
Qed.

(** * Instantiation *)

(** [instance_of θ τ τ'] says [τ'] is what the polymorphic sort [τ] becomes
    under the parameter assignment [θ].  The monomorphic variant additionally
    demands that the result carry no parameters at all, which is what a rank
    must reach before a term can be given that sort. *)

Definition instance_of (θ : sort_subst_map) (τ τ' : sort) : Prop :=
  sort_subst θ τ = τ'.

Theorem instance_of_functional : forall θ τ τ1 τ2,
    instance_of θ τ τ1 ->
    instance_of θ τ τ2 ->
    τ1 = τ2.
Proof. hauto l:on. Qed.

Theorem instance_of_refl : forall θ σ, monomorphic σ -> instance_of θ σ σ.
Proof.
  intros θ σ Hmono.
  induction σ; unfold instance_of; simpl.
  - inversion Hmono.
  - apply f_equal. apply list_eq_Forall2.
    apply Forall2_fmap_l.
    apply Forall_Forall2_diag.
    apply Forall_forall.
    intros τ Hσ. apply H; auto.
    inversion Hmono. rewrite Forall_forall in H1.
    apply H1. apply Hσ.
Qed.

Definition monomorphic_instance_of (θ : sort_subst_map) (τ σ : sort)
  : Prop :=
  instance_of θ τ σ /\ monomorphic σ.

Corollary monomorphic_instance_of_functional : forall θ τ σ1 σ2,
    monomorphic_instance_of θ τ σ1 ->
    monomorphic_instance_of θ τ σ2 ->
    σ1 = σ2.
Proof. hauto lq:on rew:off use:instance_of_functional. Qed.

Corollary monomorphic_instance_of_refl :
  forall θ σ, monomorphic σ -> monomorphic_instance_of θ σ σ.
Proof.
  intros θ σ Hmono. split; auto.
  apply instance_of_refl; auto.
Qed.

Corollary monomorphic_instance_of_SApp_const :
  forall θ s, monomorphic_instance_of θ (SApp s []) (SApp s []).
Proof.
  intros θ s.
  apply monomorphic_instance_of_refl.
  apply monomorphic_SApp_const.
Qed.

Corollary monomorphic_instance_of_σ_bool :
  forall θ, monomorphic_instance_of θ σ_bool σ_bool.
Proof. intros. apply monomorphic_instance_of_SApp_const. Qed.

(** A monomorphic sort is its own only instance: [instance_of] substitutes for
    sort parameters, and a monomorphic sort has none.  This is how a proof
    reads a monomorphic rank off a declaration whose argument sorts are already
    concrete. *)
Corollary monomorphic_instance_of_mono : forall θ τ σ,
    monomorphic τ -> monomorphic_instance_of θ τ σ -> σ = τ.
Proof.
  intros θ τ σ Hmono H. symmetry.
  eapply monomorphic_instance_of_functional;
    [apply monomorphic_instance_of_refl, Hmono | exact H].
Qed.

Corollary Forall2_monomorphic_instance_of_mono : forall θ τs σs,
    Forall monomorphic τs ->
    Forall2 (monomorphic_instance_of θ) τs σs ->
    σs = τs.
Proof.
  intros θ τs σs Hmono H. revert Hmono.
  induction H as [| τ σ τs' σs' Hτ _ IH]; intros Hmono; [reflexivity |].
  inversion Hmono as [| ? ? Hτm Hτsm]; subst.
  f_equal; [eapply monomorphic_instance_of_mono; eassumption | exact (IH Hτsm)].
Qed.
