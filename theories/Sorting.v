(** * SMTLIB.Sorting : Well-Sortedness of SMT-LIB Terms *)

(** The sorting judgment [Σ ⊢ t : σ] and its structural metatheory:
    extensionality with weakening and strengthening as its cases, renaming,
    substitution, and the exchange of [term_close] for [term_open].
    Corresponds to Sec. 5.2.1, _well sorted terms_.*)

From SMTLIB Require Import Signature Term Symbols Utils.
From stdpp Require Import base gmap stringmap functions.
From Stdlib Require Import Setoid Morphisms.

(** * The Sorting Judgment *)

Open Scope smt_scope.

Reserved Notation "Σ ⊢ t : σ" (at level 70, t at level 99, no associativity).
Reserved Notation "Σ ⊢p t : τ" (at level 70, t at level 99, no associativity).

(** [term_has_sort Σ t σ], written [Σ ⊢ t : σ], says that under the
    signature [Σ] the term [t] has sort [σ].  This corresponds to Definition 5,
    and is indexed by the signature alone, as the standard's judgment is: a
    binder rule sorts its body under [Σ] extended with what it binds, the
    standard's [Σ[x:τ]], written [<[x := τ]> Σ] for one binder and
    [list_to_map (zip xs τs) ⊍ Σ] for several.  [S_TFVar] requires the
    variable to be declared in [Σ], as the standard's rule requires [x:τ ∈ Σ],
    at a well-formed monomorphic sort.  The rules constrain only the variables
    [t] mentions ([term_has_sort_fv_lookup]), so a well-sorted term reads no
    variable at a sort [Σ] cannot form or at a polymorphic one, whatever [Σ]
    declares for the variables [t] does not mention.

    One constructor per term former, named [S_T<Former>].  Application has two
    rules, according to whether the symbol is annotated with a result sort:
    [S_TApp] covers [TApp f None ts] and [S_TApp_annotated] covers
    [TApp f (Some σ) ts].  The annotation is not the only difference — [S_TApp]
    also requires the rank to be *unique*, since with no annotation to
    disambiguate it there would otherwise be nothing to pin down which sort a
    polymorphic symbol returns.
    Matching likewise has two rules, according to whether some pattern is a
    variable, as in the standard's Remark 20.  Both are exhaustive:
    [S_TMatch_PApp] has only constructor patterns, and they name every
    constructor of the scrutinee's sort; [S_TMatch_PVar] has a variable
    pattern, which catches whatever constructor the others leave out.

    The binder rules ([S_TExists], [S_TForall], [S_TLet], and the two match
    rules) sort their bodies after [term_open]ing them with fresh variables, and
    carry the [NoDup] and length side conditions that opening needs.

    Where a rule relates a list of terms to a list of sorts, it does so with a
    length equation plus a premise indexed by position, rather than with
    [Forall2].  The two are equivalent, but [Forall2] is a nested inductive and
    Rocq's generated induction principle does not descend through it, leaving
    no usable hypothesis for the sub-terms; the indexed form does. *)
Inductive term_has_sort : signature -> term -> sort -> Prop :=
| S_TFVar:
  forall Σ x σ,
    Σ !! x = Some σ ->
    sort_wf Σ σ ->
    monomorphic σ ->
    Σ ⊢ TFVar x : σ

| S_TApp:
  forall Σ f ts σs σ,
    monomorphic_rank Σ f σs σ ->
    (forall σ', monomorphic_rank Σ f σs σ' -> σ = σ') ->
    length σs = length ts ->
    (forall i t_i σ_i,
        ts !! i = Some t_i ->
        σs !! i = Some σ_i ->
        Σ ⊢ t_i : σ_i) ->
    Σ ⊢ TApp f None ts : σ

| S_TApp_annotated:
  forall Σ f ts σs σ,
    monomorphic_rank Σ f σs σ ->
    length σs = length ts ->
    (forall i t_i σ_i,
        ts !! i = Some t_i ->
        σs !! i = Some σ_i ->
        Σ ⊢ t_i : σ_i) ->
    Σ ⊢ TApp f (Some σ) ts : σ

| S_TLambda:
  forall Σ (L : gset var) σ1 σ2 t,
    sort_wf Σ σ1 ->
    monomorphic σ1 ->
    (forall x,
        x ∉ L ->
        let t' := term_open 0 [ TFVar x ] t in
        <[ x := σ1 ]> Σ ⊢ t' : σ2) ->
    Σ ⊢ TLambda σ1 t : τ_map σ1 σ2

| S_TExists:
  forall Σ (L : gset var) σ t,
    sort_wf Σ σ ->
    monomorphic σ ->
    (forall x,
        x ∉ L ->
        let t' := term_open 0 [ TFVar x ] t in
        <[ x := σ ]> Σ ⊢ t' : σ_bool) ->
    Σ ⊢ TExists σ t : σ_bool

| S_TForall:
  forall Σ (L : gset var) σ t,
    sort_wf Σ σ ->
    monomorphic σ ->
    (forall x,
        x ∉ L ->
        let t' := term_open 0 [ TFVar x ] t in
        <[ x := σ ]> Σ ⊢ t' : σ_bool) ->
    Σ ⊢ TForall σ t : σ_bool

| S_TLet:
  forall Σ (L : gset var) σs ts t σ,
    length σs = length ts ->
    (forall i t_i σ_i,
        ts !! i = Some t_i ->
        σs !! i = Some σ_i ->
        Σ ⊢ t_i : σ_i) ->
    (forall xs : list var,
        NoDup xs ->
        length xs = length ts ->
        list_to_set xs ## L ->
        let t' := term_open 0 (map TFVar xs) t in
        let Σ' := list_to_map (zip xs σs) ⊍ Σ in
        Σ' ⊢ t' : σ) ->
    Σ ⊢ TLet ts t : σ

| S_TMatch_PApp :
  forall Σ (L : gset var) pts t δ s σ,

    (* Scrutinee has sort δ which is an ADT *)
    Σ ⊢ t : δ ->
    adt Σ δ ->

    (* Patterns completely cover constructors for δ *)
    let ps := map fst pts in
    let cs : gset func := list_to_set (omap pattern_constructor ps) in
    Some s = sort_top_symbol δ ->
    cs = Σ.(constructors_for_sort) s ->
    size cs = length ps ->

    (* Each case of the match statement is well-sorted *)
    (forall c n t_c σs xs,
        (PApp c n, t_c) ∈ pts ->
        (* Constructor c has rank σs -> δ *)
        monomorphic_rank Σ c σs δ ->
        (* Open the case's body *)
        NoDup xs ->
        length xs = n ->
        list_to_set xs ## L ->
        let t' := term_open 0 (map TFVar xs) t_c in
        (* Change the sorting environment *)
        let Σ' := list_to_map (zip xs σs) ⊍ Σ in
        (* Check the sort of the body against the new environment *)
        Σ' ⊢ t' : σ) ->

    (* Every covered constructor genuinely has a monomorphic rank into δ.
       The coverage premise above cannot supply this: [constructors_for_sort]
       is indexed by the top *symbol* s, so membership only says c builds some
       sort whose top symbol is s, not δ itself.  The case premise cannot
       either, being conditioned on a rank that may not exist.  So the
       derivation records it. *)
    (forall c n t_c,
        (PApp c n, t_c) ∈ pts ->
        exists σs, monomorphic_rank Σ c σs δ /\ length σs = n) ->

    Σ ⊢ TMatch t pts : σ

| S_TMatch_PVar :
  forall Σ (L : gset var) pts t δ s σ,

    (* Scrutinee has sort δ which is an ADT *)
    Σ ⊢ t : δ ->
    adt Σ δ ->

    (* Patterns partially cover constructors for δ *)
    let ps := map fst pts in
    let cs : gset func := list_to_set (omap pattern_constructor ps) in
    Some s = sort_top_symbol δ ->
    cs ⊆ Σ.(constructors_for_sort) s ->
    PVar ∈ ps ->

    (* Each PApp case of the match statement is well-sorted *)
    (forall c n t_c σs xs,
        (PApp c n, t_c) ∈ pts ->
        (* Constructor c has rank σs -> δ *)
        monomorphic_rank Σ c σs δ ->
        (* Open the case's body *)
        NoDup xs ->
        length xs = n ->
        list_to_set xs ## L ->
        let t' := term_open 0 (map TFVar xs) t_c in
        (* Change the sorting environment *)
        let Σ' := list_to_map (zip xs σs) ⊍ Σ in
        (* Check the sort of the body against the new environment *)
        Σ' ⊢ t' : σ) ->

    (* Each PVar case of the match statement is well-sorted *)
    (forall x t_c,
        x ∉ L ->
        (PVar, t_c) ∈ pts ->
        let t' := term_open 0 [ TFVar x ] t_c in
        <[ x := δ ]> Σ ⊢ t' : σ) ->

    (* Every covered constructor genuinely has a monomorphic rank into δ. *)
    (forall c n t_c,
        (PApp c n, t_c) ∈ pts ->
        exists σs, monomorphic_rank Σ c σs δ /\ length σs = n) ->

    Σ ⊢ TMatch t pts : σ

where "Σ ⊢ t : σ" := (term_has_sort Σ t σ) : smt_scope.

(** * Extensionality *)

(** Two sortings agreeing on the free variables of [t'] still agree after both
    are extended along the same binder list.  Any free variable of
    [term_open 0 (map TFVar xs) t'] is either free in [t'], where the
    hypothesis applies, or one of the [xs], where the two extensions coincide
    because they add the same [list_to_map (zip xs σs)].  Auxiliary to the
    binder cases of [term_has_sort_cong]. *)
Local Lemma union_lookup_list_to_map_agree :
  forall (S1 S2 : sorting) (xs : list var) (σs : list sort) (t' : term),
    length xs = length σs ->
    (forall y, y ∈ fv t' -> S1 !! y = S2 !! y) ->
    forall y, y ∈ fv (term_open 0 (map TFVar xs) t') ->
      (list_to_map (zip xs σs) ∪ S1) !! y
      = (list_to_map (zip xs σs) ∪ S2) !! y.
Proof.
  intros S1 S2 xs σs t' Hlen Hag y Hy.
  destruct ((list_to_map (zip xs σs) : sorting) !! y) as [σy|] eqn:Hlu.
  - rewrite !(lookup_union_Some_l _ _ _ _ Hlu). reflexivity.
  - rewrite !(lookup_union_r _ _ _ Hlu). apply Hag.
    apply (elem_of_fv_term_open_TFVar t' 0 xs) in Hy as [Hl|Hr]; [exact Hl|].
    (* y ∈ xs would put it in the map's domain, contradicting Hlu *)
    exfalso.
    apply not_elem_of_list_to_map_2 in Hlu. apply Hlu.
    rewrite fst_zip by lia. exact Hr.
Qed.

(** Sorting reads a signature's variable sorts only at the free variables of
    the term: a signature agreeing with it except on sorts, and declaring those
    variables alike, sorts [t] alike. *)
Theorem term_has_sort_cong : forall Σ1 t σ,
    Σ1 ⊢ t : σ ->
    forall Σ2,
      signatures_agree_except_sorts Σ1 Σ2 ->
      (forall y, y ∈ fv t -> Σ1 !! y = Σ2 !! y) ->
      Σ2 ⊢ t : σ.
Proof.
  intros Σ1 t σ Hsort. induction Hsort; intros Σ2 Hsym Hag.
  - (* S_TFVar *)
    simpl in Hag.
    apply S_TFVar; [| exact
      (sort_wf_signatures_agree_except_sorts _ _ _ Hsym H0) | exact H1].
    rewrite <- (Hag x); [exact H | set_solver].
  - (* S_TApp *)
    simpl in Hag.
    apply S_TApp with (σs := σs).
    + exact (monomorphic_rank_signatures_agree_except_sorts _ _ _ _ _ Hsym H).
    + intros σ' Hσ'. apply H0.
      exact (monomorphic_rank_signatures_agree_except_sorts _ _ _ _ _
        (signatures_agree_except_sorts_sym _ _ Hsym) Hσ').
    + exact H1.
    + intros i t_i σ_i Hts Hσs.
      apply (H3 i t_i σ_i Hts Hσs _ Hsym).
      intros y Hy. apply Hag.
      rewrite elem_of_union_list. exists (fv t_i). split; [|exact Hy].
      apply list_elem_of_fmap. exists t_i. split; [reflexivity|].
      apply list_elem_of_lookup_2 with i. exact Hts.
  - (* S_TApp_annotated *)
    simpl in Hag.
    apply S_TApp_annotated with (σs := σs).
    + exact (monomorphic_rank_signatures_agree_except_sorts _ _ _ _ _ Hsym H).
    + exact H0.
    + intros i t_i σ_i Hts Hσs.
      apply (H2 i t_i σ_i Hts Hσs _ Hsym).
      intros y Hy. apply Hag.
      rewrite elem_of_union_list. exists (fv t_i). split; [|exact Hy].
      apply list_elem_of_fmap. exists t_i. split; [reflexivity|].
      apply list_elem_of_lookup_2 with i. exact Hts.
  - (* S_TLambda *)
    simpl in Hag.
    apply S_TLambda with (L := L);
      [exact (sort_wf_signatures_agree_except_sorts _ _ _ Hsym H) | exact H0 |].
    intros x0 Hx0. simpl.
    apply (H2 x0 Hx0);
      [exact (signatures_agree_except_sorts_insert_mono _ _ _ _ Hsym) |].
    intros y Hy.
    destruct (decide (y = x0)) as [->|Hne].
    + rewrite !signature_lookup_insert_eq. reflexivity.
    + rewrite !signature_lookup_insert_ne by auto.
      apply Hag.
      apply (elem_of_fv_term_open_TFVar1 t 0 x0) in Hy as [Hl|Hr]; [exact Hl|].
      contradiction.
  - (* S_TExists *)
    simpl in Hag.
    apply S_TExists with (L := L);
      [exact (sort_wf_signatures_agree_except_sorts _ _ _ Hsym H) | exact H0 |].
    intros x0 Hx0. simpl.
    apply (H2 x0 Hx0);
      [exact (signatures_agree_except_sorts_insert_mono _ _ _ _ Hsym) |].
    intros y Hy.
    destruct (decide (y = x0)) as [->|Hne].
    + rewrite !signature_lookup_insert_eq. reflexivity.
    + rewrite !signature_lookup_insert_ne by auto.
      apply Hag.
      apply (elem_of_fv_term_open_TFVar1 t 0 x0) in Hy as [Hl|Hr]; [exact Hl|].
      contradiction.
  - (* S_TForall *)
    simpl in Hag.
    apply S_TForall with (L := L);
      [exact (sort_wf_signatures_agree_except_sorts _ _ _ Hsym H) | exact H0 |].
    intros x0 Hx0. simpl.
    apply (H2 x0 Hx0);
      [exact (signatures_agree_except_sorts_insert_mono _ _ _ _ Hsym) |].
    intros y Hy.
    destruct (decide (y = x0)) as [->|Hne].
    + rewrite !signature_lookup_insert_eq. reflexivity.
    + rewrite !signature_lookup_insert_ne by auto.
      apply Hag.
      apply (elem_of_fv_term_open_TFVar1 t 0 x0) in Hy as [Hl|Hr]; [exact Hl|].
      contradiction.
  - (* S_TLet *)
    simpl in Hag.
    apply S_TLet with (L := L) (σs := σs); [exact H | |].
    + intros i t_i σ_i Hts Hσs.
      apply (H1 i t_i σ_i Hts Hσs _ Hsym).
      intros y Hy. apply Hag. apply elem_of_union_r.
      rewrite elem_of_union_list. exists (fv t_i). split; [|exact Hy].
      apply list_elem_of_fmap. exists t_i. split; [reflexivity|].
      apply list_elem_of_lookup_2 with i. exact Hts.
    + intros xs Hnodup Hlenxs Hdisj. simpl.
      apply (H3 xs Hnodup Hlenxs Hdisj);
        [exact (signatures_agree_except_sorts_add_sorts_mono _ _ _ Hsym) |].
      intros y Hy. rewrite !signature_lookup_add_sorts.
      apply (union_lookup_list_to_map_agree Σ.(sorts) Σ2.(sorts) xs σs t);
        [lia| |exact Hy].
      intros z Hz. apply Hag. apply elem_of_union_l. exact Hz.
  - (* S_TMatch_PApp *)
    simpl in Hag.
    apply S_TMatch_PApp with (L := L) (δ := δ) (s := s).
    + apply (IHHsort _ Hsym). intros y Hy. apply Hag. apply elem_of_union_l. exact Hy.
    + exact (adt_signatures_agree_except_sorts _ _ _ Hsym H).
    + exact H0.
    + rewrite <- (signatures_agree_except_sorts_constructors_for_sort _ _ Hsym).
      exact H1.
    + exact H2.
    + intros c n t0 σs xs Hpts Hrank Hnodup Hlenxs Hdisj. simpl.
      apply (monomorphic_rank_signatures_agree_except_sorts _ _ _ _ _
        (signatures_agree_except_sorts_sym _ _ Hsym)) in Hrank.
      destruct (H5 c n t0 Hpts) as (σs' & Hrank' & Hlenσs).
      assert (Hcon_c : c ∈ Σ.(constructors)).
      { eapply (match_pattern_constructor_in_constructors Σ pts δ s c n t0);
          eauto. rewrite <- H1. done. }
      assert (Hlxσ : length xs = length σs).
      { rewrite Hlenxs, <- Hlenσs.
        eapply monomorphic_rank_constructor_length; eauto. }
      apply (H4 c n t0 σs xs Hpts Hrank Hnodup Hlenxs Hdisj);
        [exact (signatures_agree_except_sorts_add_sorts_mono _ _ _ Hsym) |].
      intros y Hy. rewrite !signature_lookup_add_sorts.
      apply (union_lookup_list_to_map_agree Σ.(sorts) Σ2.(sorts) xs σs t0);
        [lia| |exact Hy].
      intros z Hz. apply Hag. apply elem_of_union_r.
      rewrite elem_of_union_list. exists (fv t0). split; [|exact Hz].
      apply list_elem_of_fmap. exists (PApp c n, t0).
      split; [reflexivity|exact Hpts].
    + intros c n t0 Hpts.
      destruct (H5 c n t0 Hpts) as (σs & Hrank & Hlenσs).
      exists σs. split; [| exact Hlenσs].
      exact (monomorphic_rank_signatures_agree_except_sorts _ _ _ _ _
               Hsym Hrank).
  - (* S_TMatch_PVar *)
    simpl in Hag.
    apply S_TMatch_PVar with (L := L) (δ := δ) (s := s).
    + apply (IHHsort _ Hsym). intros y Hy. apply Hag. apply elem_of_union_l. exact Hy.
    + exact (adt_signatures_agree_except_sorts _ _ _ Hsym H).
    + exact H0.
    + rewrite <- (signatures_agree_except_sorts_constructors_for_sort _ _ Hsym).
      exact H1.
    + exact H2.
    + intros c n t0 σs xs Hpts Hrank Hnodup Hlenxs Hdisj. simpl.
      apply (monomorphic_rank_signatures_agree_except_sorts _ _ _ _ _
        (signatures_agree_except_sorts_sym _ _ Hsym)) in Hrank.
      destruct (H7 c n t0 Hpts) as (σs' & Hrank' & Hlenσs).
      assert (Hcon_c : c ∈ Σ.(constructors)).
      { eapply (match_pattern_constructor_in_constructors Σ pts δ s c n t0);
          eauto. }
      assert (Hlxσ : length xs = length σs).
      { rewrite Hlenxs, <- Hlenσs.
        eapply monomorphic_rank_constructor_length; eauto. }
      apply (H4 c n t0 σs xs Hpts Hrank Hnodup Hlenxs Hdisj);
        [exact (signatures_agree_except_sorts_add_sorts_mono _ _ _ Hsym) |].
      intros y Hy. rewrite !signature_lookup_add_sorts.
      apply (union_lookup_list_to_map_agree Σ.(sorts) Σ2.(sorts) xs σs t0);
        [lia| |exact Hy].
      intros z Hz. apply Hag. apply elem_of_union_r.
      rewrite elem_of_union_list. exists (fv t0). split; [|exact Hz].
      apply list_elem_of_fmap. exists (PApp c n, t0).
      split; [reflexivity|exact Hpts].
    + intros x t0 Hx Hpts. simpl.
      apply (H6 x t0 Hx Hpts);
        [exact (signatures_agree_except_sorts_insert_mono _ _ _ _ Hsym) |].
      intros y Hy.
      destruct (decide (y = x)) as [->|Hne].
      * rewrite !signature_lookup_insert_eq. reflexivity.
      * rewrite !signature_lookup_insert_ne by auto.
        apply Hag.
        apply elem_of_union_r.
        apply (elem_of_fv_term_open_TFVar1 t0 0 x) in Hy as [Hl|Hr]; cycle 1.
        { contradiction. }
        rewrite elem_of_union_list. exists (fv t0). split; [|exact Hl].
        apply list_elem_of_fmap. exists (PVar, t0).
        split; [reflexivity|exact Hpts].
    + intros c n t0 Hpts.
      destruct (H7 c n t0 Hpts) as (σs & Hrank & Hlenσs).
      exists σs. split; [| exact Hlenσs].
      exact (monomorphic_rank_signatures_agree_except_sorts _ _ _ _ _
               Hsym Hrank).
Qed.

(** Signatures agreeing except on sorts, and on their sorts too, sort alike. *)
Corollary term_has_sort_sorts_eq : forall Σ1 Σ2 t σ,
    signatures_agree_except_sorts Σ1 Σ2 ->
    Σ1.(sorts) = Σ2.(sorts) ->
    Σ1 ⊢ t : σ ->
    Σ2 ⊢ t : σ.
Proof.
  intros Σ1 Σ2 t σ Hsym Hsorts Hsort.
  apply (term_has_sort_cong _ t σ Hsort _ Hsym).
  intros y _. change (Σ1.(sorts) !! y = Σ2.(sorts) !! y). by rewrite Hsorts.
Qed.

(** A signature with its sorts replaced and then extended at [x] sorts as the
    signature with the extended sorts.  The two agree on every field, but
    seeing that by conversion unfolds the signature, which is costly for a
    concrete one; this proves it once, for every [Σ]. *)
Theorem term_has_sort_insert_with_sorts : forall Σ m x σ t τ,
    <[x := σ]> (signature_with_sorts Σ m) ⊢ t : τ <->
    signature_with_sorts Σ (<[x := σ]> m) ⊢ t : τ.
Proof.
  intros Σ m x σ t τ.
  split; intros Hsort;
    (eapply term_has_sort_sorts_eq; [| | exact Hsort]; [split | ]; reflexivity).
Qed.

(** The same for a binder list, extending the replaced sorts by [m']. *)
Theorem term_has_sort_add_sorts_with_sorts : forall Σ m m' t τ,
    m' ⊍ signature_with_sorts Σ m ⊢ t : τ <->
    signature_with_sorts Σ (m' ∪ m) ⊢ t : τ.
Proof.
  intros Σ m m' t τ.
  split; intros Hsort;
    (eapply term_has_sort_sorts_eq; [| | exact Hsort]; [split | ]; reflexivity).
Qed.

(** * Weakening and Strengthening *)

(** Each is extensionality at a signature that differs from [Σ] only at
    variables [t] does not mention. *)
Corollary term_has_sort_weaken : forall Σ (m : sorting) t σ,
    (forall z, z ∈ dom m -> z ∉ fv t) ->
    Σ ⊢ t : σ ->
    m ⊍ Σ ⊢ t : σ.
Proof.
  intros Σ m t σ Hfresh Hsort.
  apply (term_has_sort_cong Σ t σ Hsort);
    [apply signatures_agree_except_sorts_sym,
      signatures_agree_except_sorts_add_sorts |].
  intros y Hy. rewrite signature_lookup_add_sorts, lookup_union_r; [reflexivity |].
  apply not_elem_of_dom. intros Hdom. exact (Hfresh y Hdom Hy).
Qed.

Corollary term_has_sort_weaken1 : forall Σ t σ x σ',
    x ∉ fv t ->
    Σ ⊢ t : σ ->
    <[x := σ']> Σ ⊢ t : σ.
Proof.
  intros Σ t σ x σ' Hfv Hsort.
  apply (term_has_sort_cong Σ t σ Hsort);
    [apply signatures_agree_except_sorts_sym,
      signatures_agree_except_sorts_insert |].
  intros y Hy. rewrite signature_lookup_insert_ne; [reflexivity | set_solver].
Qed.

Corollary term_has_sort_strengthen : forall Σ (m : sorting) t σ,
    (forall z, z ∈ dom m -> z ∉ fv t) ->
    m ⊍ Σ ⊢ t : σ ->
    Σ ⊢ t : σ.
Proof.
  intros Σ m t σ Hfresh Hsort.
  apply (term_has_sort_cong _ t σ Hsort);
    [apply signatures_agree_except_sorts_add_sorts |].
  intros y Hy. rewrite signature_lookup_add_sorts, lookup_union_r; [reflexivity |].
  apply not_elem_of_dom. intros Hdom. exact (Hfresh y Hdom Hy).
Qed.

Corollary term_has_sort_strengthen1 : forall Σ t σ x σ',
    x ∉ fv t ->
    <[x := σ']> Σ ⊢ t : σ ->
    Σ ⊢ t : σ.
Proof.
  intros Σ t σ x σ' Hfv Hsort.
  apply (term_has_sort_cong _ t σ Hsort);
    [apply signatures_agree_except_sorts_insert |].
  intros y Hy. rewrite signature_lookup_insert_ne; [reflexivity | set_solver].
Qed.

(** * Local Closure *)

(** Only locally closed terms are sortable.  The binder rules open their bodies
    with fresh variables, which is exactly what [lc] requires. *)
Theorem term_has_sort_lc : forall Σ t σ,
    Σ ⊢ t : σ ->
    lc t.
Proof.
  intros Σ t σ H. induction H.
  - apply LCT_TFVar.
  - apply (LCT_TApp f None ts). intros t0 Hin.
    apply list_elem_of_lookup in Hin as (i & Hi).
    assert (Hsi : is_Some (σs !! i)).
    { apply lookup_lt_is_Some_2. rewrite H1. apply lookup_lt_Some in Hi. exact Hi. }
    destruct Hsi as (σ_i & Hσi). apply (H3 i t0 σ_i Hi Hσi).
  - apply (LCT_TApp f (Some σ) ts). intros t0 Hin.
    apply list_elem_of_lookup in Hin as (i & Hi).
    assert (Hsi : is_Some (σs !! i)).
    { apply lookup_lt_is_Some_2. rewrite H0. apply lookup_lt_Some in Hi. exact Hi. }
    destruct Hsi as (σ_i & Hσi). apply (H2 i t0 σ_i Hi Hσi).
  - apply (LCT_TLambda σ1 t L). exact H2.
  - apply (LCT_TExists σ t L). exact H2.
  - apply (LCT_TForall σ t L). exact H2.
  - apply (LCT_TLet ts t L).
    + intros t0 Hin.
      apply list_elem_of_lookup in Hin as (i & Hi).
      assert (Hsi : is_Some (σs !! i)).
      { apply lookup_lt_is_Some_2. rewrite H. apply lookup_lt_Some in Hi. exact Hi. }
      destruct Hsi as (σ_i & Hσi). apply (H1 i t0 σ_i Hi Hσi).
    + intros xs Hlen Hdisj.
      (* [H3] needs a [NoDup] binder list; choose a fresh [NoDup] one of
         the same length, then transfer along [lc_term_open_rename]. *)
      set (xs0 := fresh_strings_of_set "" (length ts) L).
      assert (Hnd0 : NoDup xs0) by (subst xs0; apply NoDup_fresh_strings_of_set).
      assert (Hlen0 : length xs0 = length ts)
        by (subst xs0; apply length_fresh_strings_of_set).
      assert (Hdisj0 : list_to_set xs0 ## L)
        by (subst xs0; apply fresh_strings_of_set_fresh; set_solver).
      apply (lc_term_open_rename t 0 xs0 xs).
      { rewrite Hlen0, Hlen. reflexivity. }
      apply (H3 xs0 Hnd0 Hlen0 Hdisj0).
  - (* S_TMatch_PApp *)
    apply (LCT_TMatch t pts L).
    + exact IHterm_has_sort.
    + intros p t0 xs Hin Hlen Hdisj. destruct p as [|c n].
      * (* PVar: impossible by full coverage. *)
        exfalso.
        assert (HPVar : PVar ∈ ps).
        { apply list_elem_of_fmap. exists (PVar, t0). split; [reflexivity|]. exact Hin. }
        pose proof (length_omap_lt pattern_constructor ps PVar HPVar eq_refl) as Hlt.
        pose proof (size_list_to_set_le (omap pattern_constructor ps)) as Hle.
        unfold cs in H3. lia.
      * (* PApp: use rank witness + body IH. *)
        destruct (H6 c n t0 Hin) as (σs & Hrank & _).
        set (xs0 := fresh_strings_of_set "" n L).
        assert (Hnd0 : NoDup xs0) by (subst xs0; apply NoDup_fresh_strings_of_set).
        assert (Hlen0 : length xs0 = n)
          by (subst xs0; apply length_fresh_strings_of_set).
        assert (Hdisj0 : list_to_set xs0 ## L)
          by (subst xs0; apply fresh_strings_of_set_fresh; set_solver).
        apply (lc_term_open_rename t0 0 xs0 xs).
        { rewrite Hlen0, Hlen. reflexivity. }
        apply (H5 c n t0 σs xs0 Hin Hrank Hnd0 Hlen0 Hdisj0).
  - (* S_TMatch_PVar *)
    apply (LCT_TMatch t pts L).
    + exact IHterm_has_sort.
    + intros p t0 xs Hin Hlen Hdisj. destruct p as [|c n].
      * (* PVar: length xs = 1, so xs = [x]. *)
        simpl in Hlen.
        destruct xs as [|x [|y xs']]; simpl in Hlen; try discriminate.
        assert (Hx : x ∉ L) by set_solver.
        specialize (H7 x t0 Hx Hin). simpl in H7. exact H7.
      * (* PApp: use rank witness + body IH. *)
        destruct (H8 c n t0 Hin) as (σs & Hrank & _).
        set (xs0 := fresh_strings_of_set "" n L).
        assert (Hnd0 : NoDup xs0) by (subst xs0; apply NoDup_fresh_strings_of_set).
        assert (Hlen0 : length xs0 = n)
          by (subst xs0; apply length_fresh_strings_of_set).
        assert (Hdisj0 : list_to_set xs0 ## L)
          by (subst xs0; apply fresh_strings_of_set_fresh; set_solver).
        apply (lc_term_open_rename t0 0 xs0 xs).
        { rewrite Hlen0, Hlen. reflexivity. }
        apply (H5 c n t0 σs xs0 Hin Hrank Hnd0 Hlen0 Hdisj0).
Qed.

(** * Declared Variables *)

(** A well-sorted term mentions only variables declared at well-formed
    monomorphic sorts: [S_TFVar] requires exactly that of its variable, and
    every binder rule declares what it binds. *)
Theorem term_has_sort_fv_lookup : forall Σ t σ y,
    Σ ⊢ t : σ ->
    y ∈ fv t ->
    exists τ, Σ !! y = Some τ /\ sort_wf Σ τ /\ monomorphic τ.
Proof.
  intros Σ t σ y Hsort. revert y. induction Hsort; simpl; intros y Hy.
  - (* S_TFVar *)
    apply elem_of_singleton in Hy as ->. exists σ. done.
  - (* S_TApp *)
    apply elem_of_union_list in Hy as (X & HX & Hy).
    apply list_elem_of_fmap in HX as (t_i & -> & Hin).
    apply list_elem_of_lookup in Hin as (i & Hi).
    destruct (lookup_lt_is_Some_2 σs i) as (σ_i & Hσi).
    { rewrite H1. eapply lookup_lt_Some. exact Hi. }
    exact (H3 i t_i σ_i Hi Hσi y Hy).
  - (* S_TApp_annotated *)
    apply elem_of_union_list in Hy as (X & HX & Hy).
    apply list_elem_of_fmap in HX as (t_i & -> & Hin).
    apply list_elem_of_lookup in Hin as (i & Hi).
    destruct (lookup_lt_is_Some_2 σs i) as (σ_i & Hσi).
    { rewrite H0. eapply lookup_lt_Some. exact Hi. }
    exact (H2 i t_i σ_i Hi Hσi y Hy).
  - (* S_TLambda *)
    destruct (exist_fresh (L ∪ {[y]})) as [x Hx].
    apply not_elem_of_union in Hx as [HxL Hxy].
    destruct (H2 x HxL y (fv_subseteq_fv_term_open _ _ _ _ Hy)) as (τ & Hτ & Hwf).
    rewrite signature_lookup_insert_ne in Hτ by set_solver. eauto.
  - (* S_TExists *)
    destruct (exist_fresh (L ∪ {[y]})) as [x Hx].
    apply not_elem_of_union in Hx as [HxL Hxy].
    destruct (H2 x HxL y (fv_subseteq_fv_term_open _ _ _ _ Hy)) as (τ & Hτ & Hwf).
    rewrite signature_lookup_insert_ne in Hτ by set_solver. eauto.
  - (* S_TForall *)
    destruct (exist_fresh (L ∪ {[y]})) as [x Hx].
    apply not_elem_of_union in Hx as [HxL Hxy].
    destruct (H2 x HxL y (fv_subseteq_fv_term_open _ _ _ _ Hy)) as (τ & Hτ & Hwf).
    rewrite signature_lookup_insert_ne in Hτ by set_solver. eauto.
  - (* S_TLet *)
    apply elem_of_union in Hy as [Hy | Hy].
    + (* the body, opened at binders fresh for [y] *)
      set (xs := fresh_strings_of_set "" (length ts) (L ∪ {[y]})).
      assert (Hnd : NoDup xs) by (subst xs; apply NoDup_fresh_strings_of_set).
      assert (Hlen : length xs = length ts)
        by (subst xs; apply length_fresh_strings_of_set).
      assert (Hfresh : list_to_set xs ## L ∪ {[y]})
        by (subst xs; apply fresh_strings_of_set_fresh; set_solver).
      assert (HxsL : list_to_set xs ## L) by set_solver.
      destruct (H3 xs Hnd Hlen HxsL y (fv_subseteq_fv_term_open _ _ _ _ Hy))
        as (τ & Hτ & Hwf).
      rewrite signature_lookup_add_sorts, lookup_union_r in Hτ
        by (apply lookup_list_to_map_zip_None; set_solver).
      eauto.
    + (* a bound term *)
      apply elem_of_union_list in Hy as (X & HX & Hy).
      apply list_elem_of_fmap in HX as (t_i & -> & Hin).
      apply list_elem_of_lookup in Hin as (i & Hi).
      destruct (lookup_lt_is_Some_2 σs i) as (σ_i & Hσi).
      { rewrite H. eapply lookup_lt_Some. exact Hi. }
      exact (H1 i t_i σ_i Hi Hσi y Hy).
  - (* S_TMatch_PApp *)
    apply elem_of_union in Hy as [Hy | Hy]; [exact (IHHsort y Hy)|].
    apply elem_of_union_list in Hy as (X & HX & Hy).
    apply list_elem_of_fmap in HX as ([p t_c] & -> & Hin). simpl in Hy.
    destruct p as [|c n].
    + (* PVar: impossible by full coverage *)
      exfalso.
      assert (HPVar : PVar ∈ ps).
      { apply list_elem_of_fmap. exists (PVar, t_c). split; [reflexivity|]. exact Hin. }
      pose proof (length_omap_lt pattern_constructor ps PVar HPVar eq_refl) as Hlt.
      pose proof (size_list_to_set_le (omap pattern_constructor ps)) as Hle.
      unfold cs in H2. lia.
    + (* PApp *)
      destruct (H5 c n t_c Hin) as (σs & Hrank & Hlenσs).
      set (xs := fresh_strings_of_set "" n (L ∪ {[y]})).
      assert (Hnd : NoDup xs) by (subst xs; apply NoDup_fresh_strings_of_set).
      assert (Hlen : length xs = n) by (subst xs; apply length_fresh_strings_of_set).
      assert (Hfresh : list_to_set xs ## L ∪ {[y]})
        by (subst xs; apply fresh_strings_of_set_fresh; set_solver).
      assert (HxsL : list_to_set xs ## L) by set_solver.
      destruct (H4 c n t_c σs xs Hin Hrank Hnd Hlen HxsL y
                  (fv_subseteq_fv_term_open _ _ _ _ Hy)) as (τ & Hτ & Hwf).
      rewrite signature_lookup_add_sorts, lookup_union_r in Hτ
        by (apply lookup_list_to_map_zip_None; set_solver).
      eauto.
  - (* S_TMatch_PVar *)
    apply elem_of_union in Hy as [Hy | Hy]; [exact (IHHsort y Hy)|].
    apply elem_of_union_list in Hy as (X & HX & Hy).
    apply list_elem_of_fmap in HX as ([p t_c] & -> & Hin). simpl in Hy.
    destruct p as [|c n].
    + (* PVar *)
      destruct (exist_fresh (L ∪ {[y]})) as [x Hx].
      apply not_elem_of_union in Hx as [HxL Hxy].
      destruct (H6 x t_c HxL Hin y (fv_subseteq_fv_term_open _ _ _ _ Hy))
        as (τ & Hτ & Hwf).
      rewrite signature_lookup_insert_ne in Hτ by set_solver. eauto.
    + (* PApp *)
      destruct (H7 c n t_c Hin) as (σs & Hrank & Hlenσs).
      set (xs := fresh_strings_of_set "" n (L ∪ {[y]})).
      assert (Hnd : NoDup xs) by (subst xs; apply NoDup_fresh_strings_of_set).
      assert (Hlen : length xs = n) by (subst xs; apply length_fresh_strings_of_set).
      assert (Hfresh : list_to_set xs ## L ∪ {[y]})
        by (subst xs; apply fresh_strings_of_set_fresh; set_solver).
      assert (HxsL : list_to_set xs ## L) by set_solver.
      destruct (H4 c n t_c σs xs Hin Hrank Hnd Hlen HxsL y
                  (fv_subseteq_fv_term_open _ _ _ _ Hy)) as (τ & Hτ & Hwf).
      rewrite signature_lookup_add_sorts, lookup_union_r in Hτ
        by (apply lookup_list_to_map_zip_None; set_solver).
      eauto.
Qed.

Corollary term_has_sort_fv_subseteq_dom : forall Σ t σ,
    Σ ⊢ t : σ -> fv t ⊆ dom Σ.(sorts).
Proof.
  intros Σ t σ Hsort y Hy.
  destruct (term_has_sort_fv_lookup Σ t σ y Hsort Hy) as (τ & Hτ & _).
  apply elem_of_dom. eauto.
Qed.

(** In the binder-extended sorting, the [i]-th opened binder is well-sorted at
    the [i]-th bound sort, when the bound sorts are well-formed and
    monomorphic. *)
Lemma term_has_sort_map_TFVar_lookup :
  forall Σ (xs : list var) (σs : list sort) i t_i σ_i,
    NoDup xs ->
    length xs = length σs ->
    Forall (fun σ => sort_wf Σ σ /\ monomorphic σ) σs ->
    (map TFVar xs) !! i = Some t_i ->
    σs !! i = Some σ_i ->
    list_to_map (zip xs σs) ⊍ Σ ⊢ t_i : σ_i.
Proof.
  intros Σ xs σs i t_i σ_i Hnd Hlen Hσs Hti Hσi.
  rewrite list_lookup_fmap in Hti.
  destruct (xs !! i) as [x|] eqn:Hx; [|discriminate].
  simpl in Hti. injection Hti as <-.
  destruct (proj1 (Forall_lookup _ _) Hσs i σ_i Hσi) as [Hwf Hmono].
  apply S_TFVar; [| exact Hwf | exact Hmono].
  rewrite signature_lookup_add_sorts.
  apply lookup_union_Some_l, elem_of_list_to_map_1.
  - rewrite fst_zip by lia. exact Hnd.
  - apply elem_of_lookup_zip_with. exists i, x, σ_i. auto.
Qed.

(** * Sort Parameters *)

(** A well-sorted term writes no sort parameter: every binder rule asks for a
    monomorphic sort, and an annotation is the result of a monomorphic rank.
    So a well-sorted term is its own only instance, and Definition 11's rule
    for terms with sort parameters never applies to one. *)
Theorem term_has_sort_pars_empty : forall Σ t σ,
    Σ ⊢ t : σ -> pars t = ∅.
Proof.
  intros Σ t σ Hsort. induction Hsort; simpl.
  - (* S_TFVar *) reflexivity.
  - (* S_TApp *)
    rewrite (left_id_L ∅ union). apply empty_union_list_L, Forall_forall.
    intros X HX.
    apply list_elem_of_In, list_elem_of_fmap in HX as (t_i & -> & Hin).
    apply list_elem_of_lookup in Hin as (i & Hi).
    destruct (lookup_lt_is_Some_2 σs i) as (σ_i & Hσi).
    { rewrite H1. eapply lookup_lt_Some. exact Hi. }
    exact (H3 i t_i σ_i Hi Hσi).
  - (* S_TApp_annotated *)
    apply empty_union_L. split.
    + destruct H as (θ & τs & τ & _ & [_ Hmono] & _).
      by apply monomorphic_iff_sort_params_empty.
    + apply empty_union_list_L, Forall_forall.
      intros X HX.
      apply list_elem_of_In, list_elem_of_fmap in HX as (t_i & -> & Hin).
      apply list_elem_of_lookup in Hin as (i & Hi).
      destruct (lookup_lt_is_Some_2 σs i) as (σ_i & Hσi).
      { rewrite H0. eapply lookup_lt_Some. exact Hi. }
      exact (H2 i t_i σ_i Hi Hσi).
  - (* S_TLambda *)
    destruct (exist_fresh L) as [x Hx].
    apply empty_union_L. split; [by apply monomorphic_iff_sort_params_empty |].
    pose proof (pars_subseteq_pars_term_open t 0 [TFVar x]) as Hsub.
    specialize (H2 x Hx). simpl in H2. rewrite H2 in Hsub. set_solver.
  - (* S_TExists *)
    destruct (exist_fresh L) as [x Hx].
    apply empty_union_L. split; [by apply monomorphic_iff_sort_params_empty |].
    pose proof (pars_subseteq_pars_term_open t 0 [TFVar x]) as Hsub.
    specialize (H2 x Hx). simpl in H2. rewrite H2 in Hsub. set_solver.
  - (* S_TForall *)
    destruct (exist_fresh L) as [x Hx].
    apply empty_union_L. split; [by apply monomorphic_iff_sort_params_empty |].
    pose proof (pars_subseteq_pars_term_open t 0 [TFVar x]) as Hsub.
    specialize (H2 x Hx). simpl in H2. rewrite H2 in Hsub. set_solver.
  - (* S_TLet *)
    apply empty_union_L. split.
    + (* the body, opened at fresh binders *)
      set (xs := fresh_strings_of_set "" (length ts) L).
      assert (Hnd : NoDup xs) by (subst xs; apply NoDup_fresh_strings_of_set).
      assert (Hlen : length xs = length ts)
        by (subst xs; apply length_fresh_strings_of_set).
      assert (HxsL : list_to_set xs ## L)
        by (subst xs; apply fresh_strings_of_set_fresh; set_solver).
      pose proof (pars_subseteq_pars_term_open t 0 (map TFVar xs)) as Hsub.
      specialize (H3 xs Hnd Hlen HxsL). simpl in H3. rewrite H3 in Hsub.
      set_solver.
    + (* a bound term *)
      apply empty_union_list_L, Forall_forall.
      intros X HX.
      apply list_elem_of_In, list_elem_of_fmap in HX as (t_i & -> & Hin).
      apply list_elem_of_lookup in Hin as (i & Hi).
      destruct (lookup_lt_is_Some_2 σs i) as (σ_i & Hσi).
      { rewrite H. eapply lookup_lt_Some. exact Hi. }
      exact (H1 i t_i σ_i Hi Hσi).
  - (* S_TMatch_PApp *)
    rewrite IHHsort, (left_id_L ∅ union).
    apply empty_union_list_L, Forall_forall. intros X HX.
    apply list_elem_of_In, list_elem_of_fmap in HX as ([p t_c] & -> & Hin).
    simpl. destruct p as [|c n].
    + (* PVar: impossible by full coverage *)
      exfalso. apply (exact_coverage_no_PVar ps); [exact H2 |].
      apply list_elem_of_fmap. by exists (PVar, t_c).
    + (* PApp *)
      destruct (H5 c n t_c Hin) as (σs & Hrank & Hlenσs).
      set (xs := fresh_strings_of_set "" n L).
      assert (Hnd : NoDup xs) by (subst xs; apply NoDup_fresh_strings_of_set).
      assert (Hlen : length xs = n) by (subst xs; apply length_fresh_strings_of_set).
      assert (HxsL : list_to_set xs ## L)
        by (subst xs; apply fresh_strings_of_set_fresh; set_solver).
      pose proof (pars_subseteq_pars_term_open t_c 0 (map TFVar xs)) as Hsub.
      specialize (H4 c n t_c σs xs Hin Hrank Hnd Hlen HxsL). simpl in H4.
      rewrite H4 in Hsub. set_solver.
  - (* S_TMatch_PVar *)
    rewrite IHHsort, (left_id_L ∅ union).
    apply empty_union_list_L, Forall_forall. intros X HX.
    apply list_elem_of_In, list_elem_of_fmap in HX as ([p t_c] & -> & Hin).
    simpl. destruct p as [|c n].
    + (* PVar *)
      destruct (exist_fresh L) as [x Hx].
      pose proof (pars_subseteq_pars_term_open t_c 0 [TFVar x]) as Hsub.
      specialize (H6 x t_c Hx Hin). simpl in H6. rewrite H6 in Hsub. set_solver.
    + (* PApp *)
      destruct (H7 c n t_c Hin) as (σs & Hrank & Hlenσs).
      set (xs := fresh_strings_of_set "" n L).
      assert (Hnd : NoDup xs) by (subst xs; apply NoDup_fresh_strings_of_set).
      assert (Hlen : length xs = n) by (subst xs; apply length_fresh_strings_of_set).
      assert (HxsL : list_to_set xs ## L)
        by (subst xs; apply fresh_strings_of_set_fresh; set_solver).
      pose proof (pars_subseteq_pars_term_open t_c 0 (map TFVar xs)) as Hsub.
      specialize (H4 c n t_c σs xs Hin Hrank Hnd Hlen HxsL). simpl in H4.
      rewrite H4 in Hsub. set_solver.
Qed.

(** The sort substitutions Definition 11's first rule ranges over at [t]: one
    for each assignment of monomorphic sorts of [Σ] to the parameters [t]
    writes.  At a parameter-free [t] the only one is [∅]. *)
Definition monomorphic_sort_subst (Σ : signature) (t : term)
  (θ : sort_subst_map) : Prop :=
  dom θ = pars t /\ map_Forall (fun _ σ => sort_wf Σ σ /\ monomorphic σ) θ.

(** A term writing sort parameters is well sorted when every instance of it
    is: the reading of well-sortedness under which Definition 11's first rule
    is defined (see [SMTLIB.Eval.holds]).  An instance's sort is the instance
    of [τ], since it can depend on the parameters. *)
Definition polymorphic_term_has_sort (Σ : signature) (t : term) (τ : sort)
  : Prop :=
  forall θ, monomorphic_sort_subst Σ t θ ->
    Σ ⊢ term_sort_subst θ t : sort_subst θ τ.

Notation "Σ ⊢p t : τ" := (polymorphic_term_has_sort Σ t τ) : smt_scope.

Theorem polymorphic_term_has_sort_of_term_has_sort : forall Σ t σ,
    Σ ⊢ t : σ -> Σ ⊢p t : σ.
Proof.
  intros Σ t σ Hsort θ [Hdom _].
  rewrite (term_has_sort_pars_empty Σ t σ Hsort) in Hdom.
  apply dom_empty_inv_L in Hdom as ->.
  by rewrite term_sort_subst_empty, sort_subst_empty.
Qed.

(** * Renaming and Substitution *)

(** Substitution preserves sorting: if every term in [θ_t] has the sort [θ_σ]
    assigns to the same variable, then a term sorted under [θ_σ ⊍ Σ] stays
    sorted under [Σ] after [θ_t] is applied.  [dom θ_t = dom θ_σ]
    ties the two substitutions together. *)
Theorem term_has_sort_term_subst :
  forall Σ (θ_t : gmap var term) t σ (θ_σ : gmap var sort),
    dom θ_t = dom θ_σ ->
    ( forall x t' σ',
        θ_t !! x = Some t' ->
        θ_σ !! x = Some σ' ->
        Σ ⊢ t' : σ') ->
    θ_σ ⊍ Σ ⊢ t : σ ->
    Σ ⊢ term_subst θ_t t : σ.
Proof.
  intros Σ θ_t t σ θ_σ Hdom Hθ Hsort.
  (* the derivation's signature differs from [θ_σ ⊍ Σ] only in its sorts
     once a binder has extended it, so the induction tracks the two facts
     that survive extension rather than the equation itself *)
  remember (θ_σ ⊍ Σ) as Σctx eqn:HΣctx.
  assert (Hsym : signatures_agree_except_sorts Σctx Σ)
    by (subst Σctx; apply signatures_agree_except_sorts_add_sorts).
  assert (Hag : Σctx.(sorts) = θ_σ ∪ Σ.(sorts)) by (subst Σctx; reflexivity).
  clear HΣctx.
  revert Σ θ_t θ_σ Hdom Hθ Hsym Hag.
  induction Hsort; intros Σ0 θ_t θ_σ Hdom Hθ Hsym Hag.
  - (* S_TFVar *)
    simpl. change (Σ.(sorts) !! x = Some σ) in H. rewrite Hag in H.
    destruct (θ_t !! x) as [u|] eqn:Hxt.
    + assert (Hin : x ∈ dom θ_σ) by (rewrite <- Hdom; apply elem_of_dom; eauto).
      apply elem_of_dom in Hin. destruct Hin as [σ' Hxσ].
      rewrite (lookup_union_Some_l _ _ _ _ Hxσ) in H. injection H as <-.
      apply (Hθ x u σ' Hxt Hxσ).
    + assert (Hnone : θ_σ !! x = None).
      { apply not_elem_of_dom. rewrite <- Hdom. apply not_elem_of_dom. exact Hxt. }
      rewrite (lookup_union_r _ _ _ Hnone) in H.
      apply S_TFVar; [exact H | exact
        (sort_wf_signatures_agree_except_sorts _ _ _ Hsym H0) | exact H1].
  - (* S_TApp *)
    simpl.
    apply S_TApp with (σs := σs).
    { exact (monomorphic_rank_signatures_agree_except_sorts _ _ _ _ _ Hsym H). }
    { intros σ' Hσ'. apply H0.
      exact (monomorphic_rank_signatures_agree_except_sorts _ _ _ _ _
        (signatures_agree_except_sorts_sym _ _ Hsym) Hσ'). }
    { rewrite length_map. exact H1. }
    intros i t_i' σ_i Hts Hσs.
    rewrite list_lookup_fmap in Hts.
    destruct (ts !! i) as [t_i|] eqn:Hti; simpl in Hts; [|discriminate].
    injection Hts as <-.
    apply (H3 i t_i σ_i Hti Hσs Σ0 θ_t θ_σ Hdom Hθ Hsym Hag).
  - (* S_TApp_annotated *)
    simpl.
    apply S_TApp_annotated with (σs := σs).
    { exact (monomorphic_rank_signatures_agree_except_sorts _ _ _ _ _ Hsym H). }
    { rewrite length_map. exact H0. }
    intros i t_i' σ_i Hts Hσs.
    rewrite list_lookup_fmap in Hts.
    destruct (ts !! i) as [t_i|] eqn:Hti; simpl in Hts; [|discriminate].
    injection Hts as <-.
    apply (H2 i t_i σ_i Hti Hσs Σ0 θ_t θ_σ Hdom Hθ Hsym Hag).
  - (* S_TLambda *)
    simpl.
    pose (Lfv := ⋃ ((fun (p : var * term) => fv p.2) <$> map_to_list θ_t)
                 : gset var).
    pose (Ldom := dom θ_t : gset var).
    apply S_TLambda with (L := L ∪ Lfv ∪ Ldom);
      [exact (sort_wf_signatures_agree_except_sorts _ _ _ Hsym H) | exact H0 |].
    intros x0 Hx0. simpl.
    assert (Hx0dom : θ_t !! x0 = None).
    { apply not_elem_of_dom. intro Hin. apply Hx0.
      apply elem_of_union_r. exact Hin. }
    assert (Hweak : forall x t' σ', θ_t !! x = Some t' -> θ_σ !! x = Some σ' ->
                      <[x0:=σ1]> Σ0 ⊢ t' : σ').
    { intros x t' σ' Hxt Hxσ.
      apply term_has_sort_weaken1.
      - intro Hfvin. apply Hx0. apply elem_of_union_l. apply elem_of_union_r.
        apply elem_of_union_list. exists (fv t'). split; [|exact Hfvin].
        apply list_elem_of_fmap. exists (x, t'). split; [reflexivity|].
        apply elem_of_map_to_list. exact Hxt.
      - apply (Hθ x t' σ' Hxt Hxσ). }
    assert (Hlccod : forall x u, θ_t !! x = Some u -> lc u).
    { intros x u Hxt.
      assert (Hin : x ∈ dom θ_σ) by (rewrite <- Hdom; apply elem_of_dom; eauto).
      apply elem_of_dom in Hin. destruct Hin as [σ' Hxσ].
      apply (term_has_sort_lc Σ0 u σ'). apply (Hθ x u σ' Hxt Hxσ). }
    assert (Hfreshxs : forall x, x ∈ [x0] -> θ_t !! x = None).
    { intros x Hx. apply list_elem_of_singleton in Hx. subst x. exact Hx0dom. }
    change [TFVar x0] with (map TFVar [x0]).
    rewrite <- (term_subst_open_TFVar_comm θ_t t 0 [x0] Hlccod Hfreshxs).
    change (map TFVar [x0]) with [TFVar x0].
    assert (Hσnone : θ_σ !! x0 = None).
    { apply not_elem_of_dom. rewrite <- Hdom. apply not_elem_of_dom.
      exact Hx0dom. }
    eapply H2; eauto; [set_solver | exact
      (signatures_agree_except_sorts_insert_mono _ _ _ _ Hsym) |].
    change (<[x0:=σ1]> Σ.(sorts) = θ_σ ∪ <[x0:=σ1]> Σ0.(sorts)).
    rewrite Hag; apply (insert_union_r θ_σ Σ0.(sorts) x0 σ1 Hσnone).
  - (* S_TExists *)
    simpl.
    pose (Lfv := ⋃ ((fun (p : var * term) => fv p.2) <$> map_to_list θ_t)
                 : gset var).
    pose (Ldom := dom θ_t : gset var).
    apply S_TExists with (L := L ∪ Lfv ∪ Ldom);
      [exact (sort_wf_signatures_agree_except_sorts _ _ _ Hsym H) | exact H0 |].
    intros x0 Hx0. simpl.
    assert (Hx0dom : θ_t !! x0 = None).
    { apply not_elem_of_dom. intro Hin. apply Hx0.
      apply elem_of_union_r. exact Hin. }
    assert (Hweak : forall x t' σ', θ_t !! x = Some t' -> θ_σ !! x = Some σ' ->
                      <[x0:=σ]> Σ0 ⊢ t' : σ').
    { intros x t' σ' Hxt Hxσ.
      apply term_has_sort_weaken1.
      - intro Hfvin. apply Hx0. apply elem_of_union_l. apply elem_of_union_r.
        apply elem_of_union_list. exists (fv t'). split; [|exact Hfvin].
        apply list_elem_of_fmap. exists (x, t'). split; [reflexivity|].
        apply elem_of_map_to_list. exact Hxt.
      - apply (Hθ x t' σ' Hxt Hxσ). }
    assert (Hlccod : forall x u, θ_t !! x = Some u -> lc u).
    { intros x u Hxt.
      assert (Hin : x ∈ dom θ_σ) by (rewrite <- Hdom; apply elem_of_dom; eauto).
      apply elem_of_dom in Hin. destruct Hin as [σ' Hxσ].
      apply (term_has_sort_lc Σ0 u σ'). apply (Hθ x u σ' Hxt Hxσ). }
    assert (Hfreshxs : forall x, x ∈ [x0] -> θ_t !! x = None).
    { intros x Hx. apply list_elem_of_singleton in Hx. subst x. exact Hx0dom. }
    change [TFVar x0] with (map TFVar [x0]).
    rewrite <- (term_subst_open_TFVar_comm θ_t t 0 [x0] Hlccod Hfreshxs).
    change (map TFVar [x0]) with [TFVar x0].
    assert (Hσnone : θ_σ !! x0 = None).
    { apply not_elem_of_dom. rewrite <- Hdom. apply not_elem_of_dom.
      exact Hx0dom. }
    eapply H2; eauto; [set_solver | exact
      (signatures_agree_except_sorts_insert_mono _ _ _ _ Hsym) |].
    change (<[x0:=σ]> Σ.(sorts) = θ_σ ∪ <[x0:=σ]> Σ0.(sorts)).
    rewrite Hag; apply (insert_union_r θ_σ Σ0.(sorts) x0 σ Hσnone).
  - (* S_TForall *)
    simpl.
    pose (Lfv := ⋃ ((fun (p : var * term) => fv p.2) <$> map_to_list θ_t)
                 : gset var).
    pose (Ldom := dom θ_t : gset var).
    apply S_TForall with (L := L ∪ Lfv ∪ Ldom);
      [exact (sort_wf_signatures_agree_except_sorts _ _ _ Hsym H) | exact H0 |].
    intros x0 Hx0. simpl.
    assert (Hx0dom : θ_t !! x0 = None).
    { apply not_elem_of_dom. intro Hin. apply Hx0.
      apply elem_of_union_r. exact Hin. }
    assert (Hweak : forall x t' σ', θ_t !! x = Some t' -> θ_σ !! x = Some σ' ->
                      <[x0:=σ]> Σ0 ⊢ t' : σ').
    { intros x t' σ' Hxt Hxσ.
      apply term_has_sort_weaken1.
      - intro Hfvin. apply Hx0. apply elem_of_union_l. apply elem_of_union_r.
        apply elem_of_union_list. exists (fv t'). split; [|exact Hfvin].
        apply list_elem_of_fmap. exists (x, t'). split; [reflexivity|].
        apply elem_of_map_to_list. exact Hxt.
      - apply (Hθ x t' σ' Hxt Hxσ). }
    assert (Hlccod : forall x u, θ_t !! x = Some u -> lc u).
    { intros x u Hxt.
      assert (Hin : x ∈ dom θ_σ) by (rewrite <- Hdom; apply elem_of_dom; eauto).
      apply elem_of_dom in Hin. destruct Hin as [σ' Hxσ].
      apply (term_has_sort_lc Σ0 u σ'). apply (Hθ x u σ' Hxt Hxσ). }
    assert (Hfreshxs : forall x, x ∈ [x0] -> θ_t !! x = None).
    { intros x Hx. apply list_elem_of_singleton in Hx. subst x. exact Hx0dom. }
    change [TFVar x0] with (map TFVar [x0]).
    rewrite <- (term_subst_open_TFVar_comm θ_t t 0 [x0] Hlccod Hfreshxs).
    change (map TFVar [x0]) with [TFVar x0].
    assert (Hσnone : θ_σ !! x0 = None).
    { apply not_elem_of_dom. rewrite <- Hdom. apply not_elem_of_dom.
      exact Hx0dom. }
    eapply H2; eauto; [set_solver | exact
      (signatures_agree_except_sorts_insert_mono _ _ _ _ Hsym) |].
    change (<[x0:=σ]> Σ.(sorts) = θ_σ ∪ <[x0:=σ]> Σ0.(sorts)).
    rewrite Hag; apply (insert_union_r θ_σ Σ0.(sorts) x0 σ Hσnone).
  - (* S_TLet *)
    simpl.
    pose (Lfv := ⋃ ((fun (p : var * term) => fv p.2) <$> map_to_list θ_t)
                 : gset var).
    pose (Ldom := dom θ_t : gset var).
    apply S_TLet with (L := L ∪ Lfv ∪ Ldom) (σs := σs).
    { rewrite length_map. exact H. }
    { intros i t_i' σ_i Hts Hσs.
      rewrite list_lookup_fmap in Hts.
      destruct (ts !! i) as [t_i|] eqn:Hti; simpl in Hts; [|discriminate].
      injection Hts as <-.
      apply (H1 i t_i σ_i Hti Hσs Σ0 θ_t θ_σ Hdom Hθ Hsym Hag). }
    intros xs Hnodup Hlen Hdisj. simpl.
    rewrite length_map in Hlen.
    assert (Hxsθ : forall x, x ∈ xs -> θ_t !! x = None).
    { intros x Hx. apply not_elem_of_dom. intro Hin. apply (Hdisj x).
      - apply elem_of_list_to_set. exact Hx.
      - apply elem_of_union_r. exact Hin. }
    assert (Hlccod : forall x u, θ_t !! x = Some u -> lc u).
    { intros x u Hxt.
      assert (Hin : x ∈ dom θ_σ) by (rewrite <- Hdom; apply elem_of_dom; eauto).
      apply elem_of_dom in Hin. destruct Hin as [σ' Hxσ].
      apply (term_has_sort_lc Σ0 u σ'). apply (Hθ x u σ' Hxt Hxσ). }
    rewrite <- (term_subst_open_TFVar_comm θ_t t 0 xs Hlccod Hxsθ).
    assert (Hlenxsσs : length xs = length σs) by (rewrite Hlen; symmetry; exact H).
    assert (Hdomxs : dom (list_to_map (zip xs σs) : gmap var sort)
                       = list_to_set xs).
    { rewrite dom_list_to_map_L.
      rewrite fst_zip; [reflexivity| rewrite Hlenxsσs; reflexivity]. }
    assert (Hθ' : forall x t' σ', θ_t !! x = Some t' -> θ_σ !! x = Some σ' ->
       list_to_map (zip xs σs) ⊍ Σ0 ⊢ t' : σ').
    { intros x t' σ' Hxt Hxσ. apply term_has_sort_weaken.
      - intros z Hz Hzfv. rewrite Hdomxs in Hz.
        apply (Hdisj z); [exact Hz|].
        apply elem_of_union_l. apply elem_of_union_r.
        apply elem_of_union_list. exists (fv t'). split; [|exact Hzfv].
        apply list_elem_of_fmap. exists (x, t'). split; [reflexivity|].
        apply elem_of_map_to_list. exact Hxt.
      - apply (Hθ x t' σ' Hxt Hxσ). }
    assert (Hdisjdom : dom θ_σ ## dom (list_to_map (zip xs σs) : gmap var sort)).
    { rewrite Hdomxs. intros z Hz1 Hz2. apply (Hdisj z); [exact Hz2|].
      apply elem_of_union_r. rewrite <- Hdom in Hz1. exact Hz1. }
    eapply H3; eauto; [set_solver | exact
      (signatures_agree_except_sorts_add_sorts_mono _ _ _ Hsym) |].
    change (list_to_map (zip xs σs) ∪ Σ.(sorts)
      = θ_σ ∪ (list_to_map (zip xs σs) ∪ Σ0.(sorts))).
    rewrite Hag, !(assoc_L (∪)),
      (map_union_comm (list_to_map (zip xs σs)) θ_σ); [reflexivity|].
    apply map_disjoint_dom. symmetry. exact Hdisjdom.
  - (* S_TMatch_PApp *)
    simpl.
    pose (Lfv := ⋃ ((fun (p : var * term) => fv p.2) <$> map_to_list θ_t)
                 : gset var).
    pose (Ldom := dom θ_t : gset var).
    apply S_TMatch_PApp with (L := L ∪ Lfv ∪ Ldom) (δ := δ) (s := s).
    + apply (IHHsort Σ0 θ_t θ_σ Hdom Hθ Hsym Hag).
    + exact (adt_signatures_agree_except_sorts _ _ _ Hsym H).
    + exact H0.
    + simpl. rewrite (map_fst_map_second (term_subst θ_t)).
      rewrite <- (signatures_agree_except_sorts_constructors_for_sort _ _ Hsym).
      exact H1.
    + simpl. rewrite (map_fst_map_second (term_subst θ_t)). exact H2.
    + intros c n tb σs xs Hpts Hrank Hnodup Hlenxs Hdisj. simpl.
      apply (monomorphic_rank_signatures_agree_except_sorts _ _ _ _ _
        (signatures_agree_except_sorts_sym _ _ Hsym)) in Hrank.
      apply list_elem_of_fmap in Hpts as ([p0 tb0] & Heq & Hin0).
      simpl in Heq. injection Heq as Hp0 Htb0. subst tb.
      destruct p0; try discriminate. injection Hp0 as -> ->.
      assert (Hxsθ : forall x, x ∈ xs -> θ_t !! x = None).
      { intros x Hx. apply not_elem_of_dom. intro Hin. apply (Hdisj x).
        - apply elem_of_list_to_set. exact Hx.
        - apply elem_of_union_r. exact Hin. }
      assert (Hlccod : forall x u, θ_t !! x = Some u -> lc u).
      { intros x u Hxt.
        assert (Hin : x ∈ dom θ_σ)
          by (rewrite <- Hdom; apply elem_of_dom; eauto).
        apply elem_of_dom in Hin. destruct Hin as [σ' Hxσ].
        apply (term_has_sort_lc Σ0 u σ'). apply (Hθ x u σ' Hxt Hxσ). }
      rewrite <- (term_subst_open_TFVar_comm θ_t tb0 0 xs Hlccod Hxsθ).
      assert (Hdomxs : forall z,
                 z ∈ dom (list_to_map (zip xs σs) : gmap var sort) ->
                 z ∈ list_to_set (C:=gset var) xs).
      { intros z Hz. apply elem_of_dom in Hz. destruct Hz as [v Hv].
        apply elem_of_list_to_map_2 in Hv.
        apply elem_of_zip_l in Hv. apply elem_of_list_to_set. exact Hv. }
      assert (Hθ' : forall x t' σ', θ_t !! x = Some t' -> θ_σ !! x = Some σ' ->
         list_to_map (zip xs σs) ⊍ Σ0 ⊢ t' : σ').
      { intros x t' σ' Hxt Hxσ. apply term_has_sort_weaken.
        - intros z Hz Hzfv. apply Hdomxs in Hz.
          apply (Hdisj z); [exact Hz|].
          apply elem_of_union_l. apply elem_of_union_r.
          apply elem_of_union_list. exists (fv t'). split; [|exact Hzfv].
          apply list_elem_of_fmap. exists (x, t'). split; [reflexivity|].
          apply elem_of_map_to_list. exact Hxt.
        - apply (Hθ x t' σ' Hxt Hxσ). }
      assert (Hdisjdom :
                dom θ_σ ## dom (list_to_map (zip xs σs) : gmap var sort)).
      { intros z Hz1 Hz2. apply Hdomxs in Hz2.
        apply (Hdisj z); [exact Hz2|].
        apply elem_of_union_r. rewrite <- Hdom in Hz1. exact Hz1. }
      eapply H4; eauto; [set_solver | exact
        (signatures_agree_except_sorts_add_sorts_mono _ _ _ Hsym) |].
      change (list_to_map (zip xs σs) ∪ Σ.(sorts)
        = θ_σ ∪ (list_to_map (zip xs σs) ∪ Σ0.(sorts))).
      rewrite Hag, !(assoc_L (∪)),
        (map_union_comm (list_to_map (zip xs σs)) θ_σ); [reflexivity|].
      apply map_disjoint_dom. symmetry. exact Hdisjdom.
    + intros c n tb Hpts.
      apply list_elem_of_fmap in Hpts as ([p0 tb0] & Heq & Hin0).
      simpl in Heq. injection Heq as Hp0 Htb0. subst tb.
      destruct p0; try discriminate. injection Hp0 as -> ->.
      destruct (H5 c0 arity tb0 Hin0) as (σs & Hrank & Hlenσs).
      exists σs. split; [| exact Hlenσs].
      exact (monomorphic_rank_signatures_agree_except_sorts _ _ _ _ _
               Hsym Hrank).
  - (* S_TMatch_PVar *)
    simpl.
    pose (Lfv := ⋃ ((fun (p : var * term) => fv p.2) <$> map_to_list θ_t)
                 : gset var).
    pose (Ldom := dom θ_t : gset var).
    apply S_TMatch_PVar with (L := L ∪ Lfv ∪ Ldom) (δ := δ) (s := s).
    + apply (IHHsort Σ0 θ_t θ_σ Hdom Hθ Hsym Hag).
    + exact (adt_signatures_agree_except_sorts _ _ _ Hsym H).
    + exact H0.
    + simpl. rewrite (map_fst_map_second (term_subst θ_t)).
      rewrite <- (signatures_agree_except_sorts_constructors_for_sort _ _ Hsym).
      exact H1.
    + simpl. rewrite (map_fst_map_second (term_subst θ_t)). exact H2.
    + intros c n tb σs xs Hpts Hrank Hnodup Hlenxs Hdisj. simpl.
      apply (monomorphic_rank_signatures_agree_except_sorts _ _ _ _ _
        (signatures_agree_except_sorts_sym _ _ Hsym)) in Hrank.
      apply list_elem_of_fmap in Hpts as ([p0 tb0] & Heq & Hin0).
      simpl in Heq. injection Heq as Hp0 Htb0. subst tb.
      destruct p0; try discriminate. injection Hp0 as -> ->.
      assert (Hxsθ : forall x, x ∈ xs -> θ_t !! x = None).
      { intros x Hx. apply not_elem_of_dom. intro Hin. apply (Hdisj x).
        - apply elem_of_list_to_set. exact Hx.
        - apply elem_of_union_r. exact Hin. }
      assert (Hlccod : forall x u, θ_t !! x = Some u -> lc u).
      { intros x u Hxt.
        assert (Hin : x ∈ dom θ_σ)
          by (rewrite <- Hdom; apply elem_of_dom; eauto).
        apply elem_of_dom in Hin. destruct Hin as [σ' Hxσ].
        apply (term_has_sort_lc Σ0 u σ'). apply (Hθ x u σ' Hxt Hxσ). }
      rewrite <- (term_subst_open_TFVar_comm θ_t tb0 0 xs Hlccod Hxsθ).
      assert (Hdomxs : forall z,
                 z ∈ dom (list_to_map (zip xs σs) : gmap var sort) ->
                 z ∈ list_to_set (C:=gset var) xs).
      { intros z Hz. apply elem_of_dom in Hz. destruct Hz as [v Hv].
        apply elem_of_list_to_map_2 in Hv.
        apply elem_of_zip_l in Hv. apply elem_of_list_to_set. exact Hv. }
      assert (Hθ' : forall x t' σ', θ_t !! x = Some t' -> θ_σ !! x = Some σ' ->
         list_to_map (zip xs σs) ⊍ Σ0 ⊢ t' : σ').
      { intros x t' σ' Hxt Hxσ. apply term_has_sort_weaken.
        - intros z Hz Hzfv. apply Hdomxs in Hz.
          apply (Hdisj z); [exact Hz|].
          apply elem_of_union_l. apply elem_of_union_r.
          apply elem_of_union_list. exists (fv t'). split; [|exact Hzfv].
          apply list_elem_of_fmap. exists (x, t'). split; [reflexivity|].
          apply elem_of_map_to_list. exact Hxt.
        - apply (Hθ x t' σ' Hxt Hxσ). }
      assert (Hdisjdom :
                dom θ_σ ## dom (list_to_map (zip xs σs) : gmap var sort)).
      { intros z Hz1 Hz2. apply Hdomxs in Hz2.
        apply (Hdisj z); [exact Hz2|].
        apply elem_of_union_r. rewrite <- Hdom in Hz1. exact Hz1. }
      eapply H4; eauto; [set_solver | exact
        (signatures_agree_except_sorts_add_sorts_mono _ _ _ Hsym) |].
      change (list_to_map (zip xs σs) ∪ Σ.(sorts)
        = θ_σ ∪ (list_to_map (zip xs σs) ∪ Σ0.(sorts))).
      rewrite Hag, !(assoc_L (∪)),
        (map_union_comm (list_to_map (zip xs σs)) θ_σ); [reflexivity|].
      apply map_disjoint_dom. symmetry. exact Hdisjdom.
    + intros x0 tb Hx0 Hpts. simpl.
      apply list_elem_of_fmap in Hpts as ([p0 tb0] & Heq & Hin0).
      simpl in Heq. injection Heq as Hp0 Htb0. subst tb.
      destruct p0; try discriminate.
      assert (Hx0dom : θ_t !! x0 = None).
      { apply not_elem_of_dom. intro Hin. apply Hx0.
        apply elem_of_union_r. exact Hin. }
      assert (Hweak : forall x t' σ', θ_t !! x = Some t' -> θ_σ !! x = Some σ' ->
                        <[x0:=δ]> Σ0 ⊢ t' : σ').
      { intros x t' σ' Hxt Hxσ.
        apply term_has_sort_weaken1.
        - intro Hfvin. apply Hx0. apply elem_of_union_l. apply elem_of_union_r.
          apply elem_of_union_list. exists (fv t'). split; [|exact Hfvin].
          apply list_elem_of_fmap. exists (x, t'). split; [reflexivity|].
          apply elem_of_map_to_list. exact Hxt.
        - apply (Hθ x t' σ' Hxt Hxσ). }
      assert (Hlccod : forall x u, θ_t !! x = Some u -> lc u).
      { intros x u Hxt.
        assert (Hin : x ∈ dom θ_σ)
          by (rewrite <- Hdom; apply elem_of_dom; eauto).
        apply elem_of_dom in Hin. destruct Hin as [σ' Hxσ].
        apply (term_has_sort_lc Σ0 u σ'). apply (Hθ x u σ' Hxt Hxσ). }
      assert (Hfreshxs : forall x, x ∈ [x0] -> θ_t !! x = None).
      { intros x Hx. apply list_elem_of_singleton in Hx. subst x.
        exact Hx0dom. }
      change [TFVar x0] with (map TFVar [x0]).
      rewrite <- (term_subst_open_TFVar_comm θ_t tb0 0 [x0] Hlccod Hfreshxs).
      change (map TFVar [x0]) with [TFVar x0].
      assert (Hσnone : θ_σ !! x0 = None).
      { apply not_elem_of_dom. rewrite <- Hdom. apply not_elem_of_dom.
        exact Hx0dom. }
      eapply H6; eauto; [set_solver | exact
        (signatures_agree_except_sorts_insert_mono _ _ _ _ Hsym) |].
      change (<[x0:=δ]> Σ.(sorts) = θ_σ ∪ <[x0:=δ]> Σ0.(sorts)).
      rewrite Hag; apply (insert_union_r θ_σ Σ0.(sorts) x0 δ Hσnone).
    + intros c n tb Hpts.
      apply list_elem_of_fmap in Hpts as ([p0 tb0] & Heq & Hin0).
      simpl in Heq. injection Heq as Hp0 Htb0. subst tb.
      destruct p0; try discriminate. injection Hp0 as -> ->.
      destruct (H7 c0 arity tb0 Hin0) as (σs & Hrank & Hlenσs).
      exists σs. split; [| exact Hlenσs].
      exact (monomorphic_rank_signatures_agree_except_sorts _ _ _ _ _
               Hsym Hrank).
Qed.

(** Only the variables [t] mentions need a well-sorted replacement: the rest
    of the substitution leaves [t] unchanged. *)
Corollary term_has_sort_term_subst_fv :
  forall Σ (θ_t : gmap var term) t σ (θ_σ : gmap var sort),
    dom θ_t = dom θ_σ ->
    ( forall x t' σ',
        x ∈ fv t ->
        θ_t !! x = Some t' ->
        θ_σ !! x = Some σ' ->
        Σ ⊢ t' : σ') ->
    θ_σ ⊍ Σ ⊢ t : σ ->
    Σ ⊢ term_subst θ_t t : σ.
Proof.
  intros Σ θ_t t σ θ_σ Hdom Hθ Hsort.
  rewrite (term_subst_ext θ_t (filter (fun kv => kv.1 ∈ fv t) θ_t) t).
  2:{ intros x Hx. destruct (θ_t !! x) as [u|] eqn:Hxu.
      - symmetry. apply map_lookup_filter_Some_2; [exact Hxu | exact Hx].
      - symmetry. apply map_lookup_filter_None_2. left. exact Hxu. }
  apply (term_has_sort_term_subst Σ _ t σ (filter (fun kv => kv.1 ∈ fv t) θ_σ)).
  - (* the two restrictions have the same domain *)
    apply set_eq. intros z. rewrite !elem_of_dom. split.
    + intros [u Hu]. apply map_lookup_filter_Some in Hu as [Hu Hz].
      assert (Hzσ : z ∈ dom θ_σ) by (rewrite <- Hdom; apply elem_of_dom; eauto).
      apply elem_of_dom in Hzσ as [τ Hτ].
      exists τ. apply map_lookup_filter_Some_2; [exact Hτ | exact Hz].
    + intros [τ Hτ]. apply map_lookup_filter_Some in Hτ as [Hτ Hz].
      assert (Hzt : z ∈ dom θ_t) by (rewrite Hdom; apply elem_of_dom; eauto).
      apply elem_of_dom in Hzt as [u Hu].
      exists u. apply map_lookup_filter_Some_2; [exact Hu | exact Hz].
  - intros x t' σ' Hxt Hxσ.
    apply map_lookup_filter_Some in Hxt as [Hxt Hx].
    apply map_lookup_filter_Some in Hxσ as [Hxσ _].
    exact (Hθ x t' σ' Hx Hxt Hxσ).
  - (* the restricted context agrees with the full one on [fv t] *)
    apply (term_has_sort_cong _ _ _ Hsort).
    { eapply signatures_agree_except_sorts_trans;
        [apply signatures_agree_except_sorts_add_sorts |].
      apply signatures_agree_except_sorts_sym,
        signatures_agree_except_sorts_add_sorts. }
    intros z Hz. rewrite !signature_lookup_add_sorts.
    destruct (θ_σ !! z) as [τ|] eqn:Hzτ.
    + assert (Hzτ' : filter (fun kv => kv.1 ∈ fv t) θ_σ !! z = Some τ)
        by (apply map_lookup_filter_Some_2; [exact Hzτ | exact Hz]).
      rewrite (lookup_union_Some_l _ _ _ _ Hzτ), (lookup_union_Some_l _ _ _ _ Hzτ').
      reflexivity.
    + assert (Hzτ' : filter (fun kv => kv.1 ∈ fv t) θ_σ !! z = None)
        by (apply map_lookup_filter_None_2; left; exact Hzτ).
      rewrite (lookup_union_r _ _ _ Hzτ), (lookup_union_r _ _ _ Hzτ').
      reflexivity.
Qed.

(** Renaming a single free variable: [t] sorted with [y'] declared at [σ']
    is, with [y'] renamed to a [y] fresh for [t], sorted with [y] declared
    there instead. *)
Corollary term_has_sort_rename : forall Σ t σ (y' y : var) (σ' : sort),
    <[y' := σ']> Σ ⊢ t : σ ->
    y ∉ fv t ->
    <[y := σ']> Σ ⊢ term_subst {[y' := TFVar y]} t : σ.
Proof.
  intros Σ t σ y' y σ' Hsort Hy.
  apply (term_has_sort_term_subst_fv (<[y := σ']> Σ) {[y' := TFVar y]} t σ
           {[y' := σ']}).
  - by rewrite !dom_singleton_L.
  - (* [y'] occurs in [t], so [Hsort] declares it at a well-formed sort *)
    intros x u τ Hx Hxu Hxτ.
    apply lookup_singleton_Some in Hxu as [<- <-].
    apply lookup_singleton_Some in Hxτ as [_ <-].
    destruct (term_has_sort_fv_lookup _ t σ y' Hsort Hx) as (τ & Hτ & Hwf & Hmono).
    rewrite signature_lookup_insert_eq in Hτ. injection Hτ as <-.
    apply S_TFVar; [apply signature_lookup_insert_eq | exact Hwf | exact Hmono].
  - apply (term_has_sort_cong _ t σ Hsort).
    + eapply signatures_agree_except_sorts_trans;
        [apply signatures_agree_except_sorts_insert |].
      apply signatures_agree_except_sorts_sym.
      eapply signatures_agree_except_sorts_trans;
        [ apply signatures_agree_except_sorts_add_sorts
        | apply signatures_agree_except_sorts_insert ].
    + intros z Hz. rewrite signature_lookup_add_sorts.
      destruct (decide (z = y')) as [->|Hne].
      * rewrite signature_lookup_insert_eq. symmetry.
        apply lookup_union_Some_l, lookup_singleton_eq.
      * assert (Hzy : z <> y) by (intros ->; contradiction).
        rewrite signature_lookup_insert_ne by congruence.
        rewrite lookup_union_r by (apply lookup_singleton_ne; congruence).
        change (Σ.(sorts) !! z = <[y := σ']> Σ.(sorts) !! z).
        rewrite lookup_insert_ne by congruence. reflexivity.
Qed.

(** Substitution of a single variable. *)
Corollary term_has_sort_term_subst1 : forall t Σ x t' σ σ',
    Σ ⊢ t' : σ' ->
    <[x := σ']> Σ ⊢ t : σ ->
    Σ ⊢ term_subst {[x := t']} t : σ.
Proof.
  intros t Σ x t' σ σ' Ht' Ht.
  apply (term_has_sort_term_subst Σ {[x := t']} t σ {[x := σ']}).
  - rewrite !dom_singleton_L. reflexivity.
  - intros y ty σy Hty Hσy.
    rewrite lookup_singleton_Some in Hty. destruct Hty as [-> <-].
    rewrite lookup_singleton_Some in Hσy. destruct Hσy as [_ <-].
    exact Ht'.
  - apply (term_has_sort_cong _ t σ Ht).
    + eapply signatures_agree_except_sorts_trans;
        [apply signatures_agree_except_sorts_insert |].
      apply signatures_agree_except_sorts_sym,
        signatures_agree_except_sorts_add_sorts.
    + intros z _. rewrite signature_lookup_add_sorts, <- insert_union_singleton_l.
      reflexivity.
Qed.

(** Closing over [xs] and reopening with fresh [ys] preserves sorting, provided
    the two binder lists have the same length and [ys] is repetition-free and
    fresh for [t].  The sorts [σs] are carried across unchanged, so this is the
    sense in which the choice of binder names does not matter. *)
Theorem term_has_sort_term_open_term_close : forall Σ xs ys t σs σ,
    length xs = length ys ->
    length σs = length xs ->
    NoDup ys ->
    disjoint (list_to_set ys) (fv t) ->
    lc t ->
    let t' := term_open 0 (map TFVar ys) (term_close xs 0 t) in
    list_to_map (zip ys σs) ⊍ Σ ⊢ t' : σ
    <-> list_to_map (zip xs σs) ⊍ Σ ⊢ t : σ.
Proof.
  intros Σ xs ys t σs σ Hlenxy Hlenσ Hnodup Hdisj Hlc. simpl.
  assert (Hlcat : lc_at [] t) by (apply lc_lc_at; exact Hlc).
  assert (Hlenxy' : length xs = length (map TFVar ys))
    by (rewrite length_map; exact Hlenxy).
  rewrite (term_open_close_subst_nil t xs (map TFVar ys) Hlenxy' Hlcat).
  split.
  - (* ==> direction *)
    intro Hsort.
    pose (inner := term_subst (list_to_map (zip xs (map TFVar ys))) t).
    pose (R := fv inner : gset var).
    pose (θyx := (list_to_map (zip ys (map TFVar xs)) : gmap var term)).
    pose (θyx' := filter (fun kv => kv.1 ∈ R) θyx).
    pose (θσ := (list_to_map (zip ys σs) : gmap var sort)).
    pose (θσ' := filter (fun kv => kv.1 ∈ R) θσ).
    assert (Hlenyx : length ys = length (map TFVar xs))
      by (rewrite length_map; lia).
    assert (Hlenxx : length xs = length (map TFVar xs))
      by (rewrite length_map; lia).
    assert (Hdisjc : list_to_set ys ## fv (term_close xs 0 t)).
    { pose proof (fv_term_close_subseteq xs 0 t) as Hsub. set_solver. }
    assert (Hround : term_subst θyx inner = t).
    { unfold inner, θyx.
      rewrite <- (term_open_close_subst_nil t xs (map TFVar ys) Hlenxy' Hlcat).
      rewrite (term_subst_open_TFVar_rename ys xs (term_close xs 0 t) 0
                 (eq_sym Hlenxy) Hnodup Hdisjc).
      rewrite (term_open_close_subst_nil t xs (map TFVar xs) Hlenxx Hlcat).
      apply term_subst_id_zip. }
    assert (Hext : term_subst θyx' inner = term_subst θyx inner).
    { apply term_subst_ext. intros z Hz. unfold θyx'.
      destruct (θyx !! z) as [w|] eqn:Hzw.
      - apply map_lookup_filter_Some_2; [exact Hzw| simpl; exact Hz].
      - apply map_lookup_filter_None_2. left. exact Hzw. }
    assert (Hroundr : term_subst θyx' inner = t) by (rewrite Hext; exact Hround).
    unfold inner in Hroundr. rewrite <- Hroundr.
    apply (term_has_sort_term_subst (list_to_map (zip xs σs) ⊍ Σ)
             θyx' inner σ θσ').
    + (* dom θyx' = dom θσ' *)
      transitivity (R ∩ list_to_set ys).
      2:{ symmetry. unfold θσ'. apply dom_filter_L. intros z. simpl. split.
          2:{ intros [v [Hv Hr]]. rewrite elem_of_intersection. split; [exact Hr|].
              apply elem_of_dom_2 in Hv. unfold θσ in Hv.
              rewrite dom_list_to_map_L in Hv. rewrite fst_zip in Hv by lia. exact Hv. }
          rewrite elem_of_intersection. intros [Hr Hin].
          rewrite elem_of_list_to_set in Hin.
          apply list_elem_of_lookup in Hin as [j Hj].
          assert (Hsj : exists sj, σs !! j = Some sj)
            by (apply lookup_lt_is_Some_2; apply lookup_lt_Some in Hj; lia).
          destruct Hsj as [sj Hsj].
          exists sj. split; [|exact Hr]. unfold θσ.
          apply elem_of_list_to_map_1.
          2:{ apply elem_of_lookup_zip_with. exists j, z, sj.
              split; [reflexivity|]. split; [exact Hj| exact Hsj]. }
          rewrite fst_zip by lia. exact Hnodup. }
      unfold θyx'. apply dom_filter_L. intros z. simpl. split.
      2:{ intros [v [Hv Hr]]. rewrite elem_of_intersection. split; [exact Hr|].
          apply elem_of_dom_2 in Hv. unfold θyx in Hv.
          rewrite dom_list_to_map_L in Hv.
          rewrite fst_zip in Hv by (rewrite length_map; lia). exact Hv. }
      rewrite elem_of_intersection. intros [Hr Hin].
      rewrite elem_of_list_to_set in Hin.
      apply list_elem_of_lookup in Hin as [j Hj].
      assert (Hxj : exists xj, xs !! j = Some xj)
        by (apply lookup_lt_is_Some_2; apply lookup_lt_Some in Hj; lia).
      destruct Hxj as [xj Hxj].
      exists (TFVar xj). split; [|exact Hr]. unfold θyx.
      apply elem_of_list_to_map_1.
      2:{ apply elem_of_lookup_zip_with. exists j, z, (TFVar xj).
          split; [reflexivity|]. split; [exact Hj|].
          rewrite list_lookup_fmap. rewrite Hxj. reflexivity. }
      rewrite fst_zip by (rewrite length_map; lia). exact Hnodup.
    + (* per-key *)
      intros x t' τ Hxt' Hxτ.
      apply map_lookup_filter_Some in Hxt' as [Hxt'0 HxR].
      apply map_lookup_filter_Some in Hxτ as [Hxτ0 _].
      simpl in HxR.
      unfold θyx in Hxt'0. unfold θσ in Hxτ0.
      apply elem_of_list_to_map_2 in Hxt'0.
      apply elem_of_lookup_zip_with in Hxt'0 as (j & a & b & Heq & Hyj & Hxb).
      injection Heq as -> ->.
      rewrite list_lookup_fmap in Hxb.
      destruct (xs !! j) as [xj|] eqn:Hxj; simpl in Hxb; [|discriminate].
      injection Hxb as <-.
      assert (Hσj : σs !! j = Some τ).
      { apply elem_of_list_to_map_2 in Hxτ0.
        apply elem_of_lookup_zip_with in Hxτ0 as (j2 & a2 & s2 & Heq2 & Hyj2 & Hσj2).
        injection Heq2 as Ha2 Hs2. subst a2 s2.
        assert (j2 = j) by (apply (NoDup_lookup ys j2 j a Hnodup Hyj2 Hyj)).
        subst j2. exact Hσj2. }
      assert (Hain : a ∈ fv (term_open 0 (map TFVar ys) (term_close xs 0 t))).
      { rewrite (term_open_close_subst_nil t xs (map TFVar ys) Hlenxy' Hlcat).
        exact HxR. }
      assert (Hays : a ∈ ys) by (apply list_elem_of_lookup; eauto).
      pose proof (fv_term_open_close_image_nil t xs ys a Hlenxy Hnodup Hlcat Hdisj Hays Hain)
        as (j0 & Hj0lt & Hyj0 & Hfind).
      assert (j0 = j) by (apply (NoDup_lookup ys j0 j a Hnodup Hyj0 Hyj)).
      subst j0.
      assert (Hxxj : xs !!! j = xj) by (apply list_lookup_total_correct; exact Hxj).
      rewrite Hxxj in Hfind.
      (* [a] is declared at [τ] where [Hsort] reads it, so [τ] is well formed *)
      destruct (term_has_sort_fv_lookup _ _ _ a Hsort HxR)
        as (τ' & Hτ' & Hwfτ & Hmonoτ).
      rewrite signature_lookup_add_sorts, (lookup_union_Some_l _ _ _ _ Hxτ0) in Hτ'.
      injection Hτ' as <-.
      apply S_TFVar; [| exact Hwfτ | exact Hmonoτ].
      rewrite signature_lookup_add_sorts. apply lookup_union_Some_l.
      pose proof (list_find_eq_list_to_map_zip xs σs xj τ (eq_sym Hlenσ)) as Hlk.
      rewrite Hfind in Hlk. rewrite nth_lookup in Hlk. rewrite Hσj in Hlk.
      simpl in Hlk.
      destruct (list_to_map (zip xs σs) !! xj) as [u|] eqn:Hu; simpl in *.
      * subst u. reflexivity.
      * exfalso.
        assert (Hxjin : xj ∈ xs) by (apply list_elem_of_lookup; eauto).
        assert (Hsome : exists v, (list_to_map (zip xs σs) : gmap var sort) !! xj = Some v).
        { apply elem_of_dom. rewrite dom_list_to_map_L. rewrite fst_zip by lia.
          rewrite elem_of_list_to_set. exact Hxjin. }
        destruct Hsome as [v Hv]. rewrite Hv in Hu. discriminate.
    + (* context reconciliation: both contexts agree on [fv inner] *)
      apply (term_has_sort_cong _ inner σ Hsort).
      { eapply signatures_agree_except_sorts_trans;
          [apply signatures_agree_except_sorts_add_sorts |].
        apply signatures_agree_except_sorts_sym.
        eapply signatures_agree_except_sorts_trans;
          [apply signatures_agree_except_sorts_add_sorts |].
        apply signatures_agree_except_sorts_add_sorts. }
      intros z Hzfv.
      rewrite !signature_lookup_add_sorts, signature_add_sorts_sorts.
      assert (Hzin : z ∈ (fv t ∖ list_to_set xs) ∪ list_to_set ys).
      { unfold inner in Hzfv.
        rewrite <- (term_open_close_subst_nil t xs (map TFVar ys) Hlenxy' Hlcat) in Hzfv.
        pose proof (fv_term_open_TFVar_subseteq (term_close xs 0 t) 0 ys) as Hsub.
        apply (elem_of_weaken _ _ _ Hzfv) in Hsub.
        rewrite (fv_term_close t xs 0) in Hsub. exact Hsub. }
      destruct (θσ !! z) as [s|] eqn:Hθσz.
      * (* [z] is a new binder, which [θσ'] keeps because it is free in [inner] *)
        assert (Hθ'z : θσ' !! z = Some s).
        { unfold θσ'. apply map_lookup_filter_Some_2; [exact Hθσz| simpl; exact Hzfv]. }
        rewrite (lookup_union_Some_l _ _ _ _ Hθ'z).
        exact (lookup_union_Some_l _ _ _ _ Hθσz).
      * (* otherwise [z] is free in [t] and not an old binder *)
        assert (Hθ'z : θσ' !! z = None).
        { unfold θσ'. apply map_lookup_filter_None_2. left. exact Hθσz. }
        assert (Hzys : z ∉ list_to_set (C:=gset var) ys).
        { rewrite elem_of_list_to_set. intros Hzys.
          apply not_elem_of_list_to_map_2 in Hθσz. apply Hθσz.
          rewrite fst_zip by lia. exact Hzys. }
        assert (Hzxs : z ∉ xs).
        { rewrite <- (elem_of_list_to_set (C:=gset var)). set_solver. }
        rewrite (lookup_union_r _ _ _ Hθ'z),
          (lookup_union_r _ _ _ (lookup_list_to_map_zip_None _ _ _ Hzxs)).
        exact (lookup_union_r _ _ _ Hθσz).
  - (* <== direction *)
    intro Hsort.
    apply (term_has_sort_term_subst_fv (list_to_map (zip ys σs) ⊍ Σ)
             (list_to_map (zip xs (map TFVar ys))) t σ
             (list_to_map (zip xs σs))).
    + rewrite !dom_list_to_map_L. f_equal. rewrite !fst_zip.
      * reflexivity.
      * lia.
      * rewrite length_map. lia.
    + intros x u τ Hxfv Hxu Hxτ.
      (* [x] is free in [t], so [Hsort] declares it at a well-formed sort *)
      destruct (term_has_sort_fv_lookup _ _ _ x Hsort Hxfv)
        as (τ' & Hτ' & Hwfτ & Hmonoτ).
      rewrite signature_lookup_add_sorts, (lookup_union_Some_l _ _ _ _ Hxτ) in Hτ'.
      injection Hτ' as <-.
      pose proof (list_find_eq_list_to_map_zip xs (map TFVar ys) x (TFVar x) Hlenxy') as Hu.
      rewrite Hxu in Hu.
      pose proof (list_find_eq_list_to_map_zip xs σs x σ (eq_sym Hlenσ)) as Hs.
      rewrite Hxτ in Hs.
      destruct (list_find (fun y => x = y) xs) as [[j w]|] eqn:Hf.
      2:{ exfalso. rewrite list_find_None in Hf.
          assert (Hxnotin : x ∉ xs).
          { intro Hin. rewrite Forall_forall in Hf.
            apply (Hf x); [rewrite list_elem_of_In in Hin; exact Hin | reflexivity]. }
          assert (Hnone : (list_to_map (zip xs (map TFVar ys)) : gmap var term) !! x = None)
            by (apply lookup_list_to_map_zip_None; exact Hxnotin).
          rewrite Hnone in Hxu. discriminate. }
      rewrite list_find_Some in Hf. destruct Hf as (Hxsj & Hxw & Hmin). subst w.
      assert (Hjlt : j < length xs) by (apply lookup_lt_Some in Hxsj; exact Hxsj).
      rewrite nth_lookup in Hu.
      assert (Hyj : ys !! j = Some (ys !!! j)) by (apply list_lookup_lookup_total_lt; lia).
      rewrite list_lookup_fmap in Hu. rewrite Hyj in Hu. simpl in Hu. subst u.
      rewrite nth_lookup in Hs.
      assert (Hσjex : exists s, σs !! j = Some s) by (apply lookup_lt_is_Some_2; lia).
      destruct Hσjex as [s Hσj]. rewrite Hσj in Hs. simpl in Hs. subst s.
      apply S_TFVar; [| exact Hwfτ | exact Hmonoτ].
      rewrite signature_lookup_add_sorts. apply lookup_union_Some_l.
      apply elem_of_list_to_map_1.
      * rewrite fst_zip by lia. exact Hnodup.
      * apply elem_of_lookup_zip_with. exists j, (ys !!! j), τ.
        split; [reflexivity|]. split; [exact Hyj | exact Hσj].
    + (* both contexts agree on [fv t], which avoids the new binders *)
      apply (term_has_sort_cong _ t σ Hsort).
      { eapply signatures_agree_except_sorts_trans;
          [apply signatures_agree_except_sorts_add_sorts |].
        apply signatures_agree_except_sorts_sym.
        eapply signatures_agree_except_sorts_trans;
          [apply signatures_agree_except_sorts_add_sorts |].
        apply signatures_agree_except_sorts_add_sorts. }
      intros z Hzfv.
      rewrite !signature_lookup_add_sorts, signature_add_sorts_sorts.
      destruct ((list_to_map (zip xs σs) : gmap var sort) !! z) as [s|] eqn:Hz.
      * rewrite !(lookup_union_Some_l _ _ _ _ Hz). reflexivity.
      * assert (Hzys : z ∉ ys).
        { rewrite <- (elem_of_list_to_set (C:=gset var)). intros Hzys.
          exact (Hdisj z Hzys Hzfv). }
        rewrite !(lookup_union_r _ _ _ Hz).
        rewrite (lookup_union_r _ _ _ (lookup_list_to_map_zip_None _ _ _ Hzys)).
        reflexivity.
Qed.

(** The one-binder case. *)
Corollary term_has_sort_term_open_term_close1 : forall t Σ y y' σ σ',
    y ∉ fv t ->
    lc t ->
    let t' := term_open 0 [TFVar y] (term_close [y'] 0 t) in
    <[y := σ']> Σ ⊢ t' : σ <-> <[y' := σ']> Σ ⊢ t : σ.
Proof.
  intros t Σ y y' σ σ' Hfv Hlc.
  assert (Hdisj : (list_to_set [y] : gset var) ## fv t) by set_solver.
  pose proof (term_has_sort_term_open_term_close Σ [y'] [y] t [σ'] σ
                eq_refl eq_refl (NoDup_singleton y) Hdisj Hlc) as Hgen.
  (* a one-binder extension is the insert at that binder *)
  assert (Hone : forall a,
             signatures_agree_except_sorts (<[a := σ']> Σ)
               (list_to_map (zip [a] [σ']) ⊍ Σ)
             /\ (<[a := σ']> Σ).(sorts) = (list_to_map (zip [a] [σ']) ⊍ Σ).(sorts)).
  { intros a. split.
    - eapply signatures_agree_except_sorts_trans;
        [apply signatures_agree_except_sorts_insert |].
      apply signatures_agree_except_sorts_sym,
        signatures_agree_except_sorts_add_sorts.
    - rewrite signature_insert_sorts, signature_add_sorts_sorts.
      apply insert_union_singleton_l. }
  simpl in *. split; intros Hsort.
  - destruct (Hone y') as [Hsym' Hsorts'].
    destruct (Hone y) as [Hsym Hsorts].
    apply (term_has_sort_sorts_eq _ _ _ _
             (signatures_agree_except_sorts_sym _ _ Hsym') (eq_sym Hsorts')).
    apply Hgen. exact (term_has_sort_sorts_eq _ _ _ _ Hsym Hsorts Hsort).
  - destruct (Hone y') as [Hsym' Hsorts'].
    destruct (Hone y) as [Hsym Hsorts].
    apply (term_has_sort_sorts_eq _ _ _ _
             (signatures_agree_except_sorts_sym _ _ Hsym) (eq_sym Hsorts)).
    apply Hgen. exact (term_has_sort_sorts_eq _ _ _ _ Hsym' Hsorts' Hsort).
Qed.
