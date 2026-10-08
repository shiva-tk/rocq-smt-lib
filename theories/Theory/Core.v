From Stdlib Require Import ClassicalEpsilon.
From stdpp Require Import functions.
From SMTLIB Require Import Utils Symbols Term Sorting Signature Theory Eval.

Open Scope smt_scope.

(* https://smt-lib.org/theories-Core.shtml *)

(* NOTE: The Core theory as given on the SMT-LIB website (see the URL above) declares
         the sort Bool via a :sorts attribute, as if it were defined by the theory.
         In the SMT-LIB standard itself, however, Bool is a built-in sort available in
         every logic, not a sort introduced by a theory. Consequently Bool is not defined
         in this theory file. *)

Definition f_true : func := "true".
Definition f_false : func := "false".
Definition f_not : func := "not".
Definition f_impl : func := "=>".
Definition f_and : func := "and".
Definition f_or : func := "or".
Definition f_xor : func := "xor".
Definition f_eq : func := "=".
Definition f_distinct : func := "distinct".
Definition f_ite : func := "ite".
Definition core_funcs : gset func :=
  {[ f_true; f_false; f_not; f_impl; f_and; f_or; f_xor; f_eq; f_distinct; f_ite ]}.

Definition true_ := TApp f_true None [].
Definition false_ := TApp f_false None [].
Definition bool_ (b : bool) := if b then true_ else false_.
Definition not_ t := TApp f_not None [t].
Definition impl_ t1 t2 := TApp f_impl None [t1; t2].
Definition and_ t1 t2 := TApp f_and None [t1; t2].
Definition ands_ (ts : list term) (t : term) := foldr (fun t1 t2 => and_ t1 t2) t ts.
Definition or_ t1 t2 := TApp f_or None [t1; t2].
Definition ors_ (ts : list term) (t : term) := foldr (fun t1 t2 => or_ t1 t2) t ts.
Definition xor_ t1 t2 := TApp f_xor None [t1; t2].
Definition eq_ t1 t2 := TApp f_eq None [t1; t2].
Definition distinct_ t1 t2 := TApp f_distinct None [t1; t2].
Definition ite_ t1 t2 t3 := TApp f_ite None [t1; t2; t3].

Inductive rank_core : func -> list sort -> sort -> Prop :=
| rank_f_true: rank_core f_true [] σ_bool
| rank_f_false: rank_core f_false [] σ_bool
| rank_f_not: rank_core f_not [ σ_bool ] σ_bool
| rank_f_impl: rank_core f_impl [ σ_bool; σ_bool ] σ_bool
| rank_f_and: rank_core f_and [ σ_bool; σ_bool ] (σ_bool)
| rank_f_or: rank_core f_or [ σ_bool; σ_bool ] (σ_bool)
| rank_f_xor: rank_core f_xor [ σ_bool; σ_bool ] (σ_bool)
| rank_f_eq: rank_core f_eq [ τ_A; τ_A ] σ_bool
| rank_f_distinct: rank_core f_distinct [ τ_A; τ_A ] σ_bool
| rank_f_ite: rank_core f_ite [ σ_bool; τ_A; τ_A ] τ_A.

Program Definition Σ_core : signature :=
  {|
    sort_symbols := {[ s_bool; s_map ]};

    funcs (f : func) := f ∈ core_funcs;
    funcs_dec f := decide (f ∈ core_funcs);

    constructors := ∅;
    selectors := ∅;
    testers := ∅;

    constructors_for_sort (s : sortsymb) := ∅;

    arity (s : sortsymb) :=
      if identifier_eqb s s_map
      then 2
      else 0;

    selectors_for_constructor (c : func) := [];
    tester_for_constructor (c : func) := c;
    constructor_for_tester (p : func) := p;

    sorts := ∅;

    rank := rank_core;
  |}.
Next Obligation.
Proof. set_solver. Qed.
Next Obligation.
Proof. set_solver. Qed.
Next Obligation.
Proof. set_solver. Qed.
Next Obligation.
Proof. set_solver. Qed.
Next Obligation.
Proof. set_solver. Qed.
Next Obligation.
Proof. set_solver. Qed.
Next Obligation.
Proof. set_solver. Qed.
Next Obligation.
Proof. reflexivity. Qed.
Next Obligation.
Proof. reflexivity. Qed.
Next Obligation.
Proof. set_solver. Qed.
Next Obligation.
Proof. set_solver. Qed.
Next Obligation.
Proof. set_solver. Qed.
Next Obligation.
Proof. set_solver. Qed.
Next Obligation.
Proof. set_solver. Qed.
Next Obligation.
Proof.
  intros f τs τ Hf.
  inversion Hf; split; repeat constructor.
Qed.
Next Obligation.
Proof. sauto lq:on rew:off. Qed.
Next Obligation.
Proof.
  intros f Hf. unfold funcs in Hf.
  assert (Hf': f = f_true \/ f = f_false \/ f = f_not \/ f = f_impl \/ f = f_and \/ f = f_or \/ f = f_xor \/ f = f_eq \/ f = f_distinct \/ f = f_ite) by set_solver.
  clear Hf. destruct_or! Hf'; subst f; eexists; econstructor; constructor.
Qed.
Next Obligation.
Proof. set_solver. Qed.
Next Obligation.
Proof. set_solver. Qed.
Next Obligation.
Proof. set_solver. Qed.
Next Obligation.
Proof. set_solver. Qed.

Section CoreModels.

  Variable A : structure.

  Definition cast_to_bool := cast A.(domain_σ_bool).

  Definition models_f_true : Prop :=
    let F := A.(interp) f_true [] σ_bool in
    cast_to_bool F = true.

  Definition models_f_false : Prop :=
    let F := A.(interp) f_false [] σ_bool in
    cast_to_bool F = false.

  Definition models_f_not : Prop :=
    let F := A.(interp) f_not [ σ_bool ] σ_bool in
    (forall b, cast_to_bool (F b) = negb (cast A.(domain_σ_bool)  b)).

  Definition models_f_impl : Prop :=
    let F := A.(interp) f_impl [ σ_bool; σ_bool ] σ_bool in
    (forall b1 b2, cast_to_bool (F b1 b2) = implb (cast_to_bool b1) (cast_to_bool b2)).

  Definition models_f_and : Prop :=
    let F := A.(interp) f_and [ σ_bool; σ_bool ] σ_bool in
    (forall b1 b2, cast_to_bool (F b1 b2) = andb (cast_to_bool b1) (cast_to_bool b2)).

  Definition models_f_or : Prop :=
    let F := A.(interp) f_or [ σ_bool; σ_bool ] σ_bool in
    (forall b1 b2, cast_to_bool (F b1 b2) = orb (cast_to_bool b1) (cast_to_bool b2)).

  Definition models_f_xor : Prop :=
    let F := A.(interp) f_xor [ σ_bool; σ_bool ] σ_bool in
    (forall b1 b2, cast_to_bool (F b1 b2) =  xorb (cast_to_bool b1) (cast_to_bool b2)).

  Definition models_f_eq : Prop :=
    forall σ,
      let F := A.(interp) f_eq [ σ; σ ] σ_bool in
      (forall v1 v2, cast_to_bool (F v1 v2) = true <-> v1 = v2).

  Definition models_f_distinct : Prop :=
    forall σ,
      let F := A.(interp) f_distinct [ σ; σ ] σ_bool in
      (forall v1 v2, cast_to_bool (F v1 v2) = true <-> v1 <> v2).

  Definition models_f_ite : Prop :=
    forall σ,
      let F := A.(interp) f_ite [ σ_bool; σ; σ ] σ in
      (forall b v1 v2, F b v1 v2 = if (cast_to_bool b) then v1 else v2).

  Record models_core : Prop := {
    mc_true : models_f_true;
    mc_false : models_f_false;
    mc_not : models_f_not;
    mc_impl : models_f_impl;
    mc_and : models_f_and;
    mc_or : models_f_or;
    mc_xor : models_f_xor;
    mc_eq : models_f_eq;
    mc_distinct : models_f_distinct;
    mc_ite : models_f_ite;
  }.

End CoreModels.

Arguments mc_true {_}.
Arguments mc_false {_}.
Arguments mc_not {_}.
Arguments mc_impl {_}.
Arguments mc_and {_}.
Arguments mc_or {_}.
Arguments mc_xor {_}.
Arguments mc_eq {_}.
Arguments mc_distinct {_}.
Arguments mc_ite {_}.

Definition T_core : pretheory :=
  {|
    pΣ := Σ_core;
    pmodels A := models_core A
  |}.

(** Every condition names one symbol, and all of them are in
    [core_funcs]. *)
Theorem T_core_local : pretheory_local T_core.
Proof.
  intros D Hbool Hmap i j Hagree Hm.
  assert (Hrw : forall f, f ∈ core_funcs -> forall σs σ, j f σs σ = i f σs σ)
    by (intros f Hf σs σ; symmetry; exact (Hagree f Hf σs σ)).
  destruct Hm as [Ht Hf Hn Him Han Hor Hxo Heq Hdi Hit].
  constructor;
    unfold models_f_true, models_f_false, models_f_not, models_f_impl,
      models_f_and, models_f_or, models_f_xor, models_f_eq, models_f_distinct,
      models_f_ite, cast_to_bool in *;
    cbv zeta in *; cbn [interp domain_σ_bool structure_of] in *.
  - rewrite (Hrw f_true); [exact Ht | set_solver].
  - rewrite (Hrw f_false); [exact Hf | set_solver].
  - intros b. rewrite (Hrw f_not); [apply Hn | set_solver].
  - intros b1 b2. rewrite (Hrw f_impl); [apply Him | set_solver].
  - intros b1 b2. rewrite (Hrw f_and); [apply Han | set_solver].
  - intros b1 b2. rewrite (Hrw f_or); [apply Hor | set_solver].
  - intros b1 b2. rewrite (Hrw f_xor); [apply Hxo | set_solver].
  - intros σ v1 v2. rewrite (Hrw f_eq); [apply Heq | set_solver].
  - intros σ v1 v2. rewrite (Hrw f_distinct); [apply Hdi | set_solver].
  - intros σ b v1 v2. rewrite (Hrw f_ite); [apply Hit | set_solver].
Qed.

(** [f_eq], [f_distinct] and [f_ite] are stated at every sort, so
    interpreting them decides equality on every domain type: the construction
    goes through [excluded_middle_informative]. *)
Section CoreInterpretable.

  Context (D : sort -> Type).
  Context (witness : forall σ, D σ).
  Context (Hbool : D σ_bool = bool).

  Local Notation base := (interp_const D witness).

  Local Definition core_lit (b : bool) : forall σs σ, interpretation D σs σ :=
    interp_insert_rank D [] σ_bool (cast_sym Hbool b) base.

  Local Definition core_unop (op : bool -> bool)
    : forall σs σ, interpretation D σs σ :=
    interp_insert_rank D [σ_bool] σ_bool
      (fun b : D σ_bool => cast_sym Hbool (op (cast Hbool b))) base.

  Local Definition core_binop (op : bool -> bool -> bool)
    : forall σs σ, interpretation D σs σ :=
    interp_insert_rank D [σ_bool; σ_bool] σ_bool
      (fun b1 b2 : D σ_bool =>
         cast_sym Hbool (op (cast Hbool b1) (cast Hbool b2))) base.

  (* [f_eq] at [neg = false] and [f_distinct] at [neg = true].  Arguments of
     different sorts cannot be equal, so that branch answers [neg] outright;
     the model conditions never look at it. *)
  Local Definition core_cmp (neg : bool) : forall σs σ, interpretation D σs σ :=
    fun σs σ =>
      match σs as l return interpretation D l σ with
      | [σ1; σ2] =>
          fun (v1 : D σ1) (v2 : D σ2) =>
            match decide (σ = σ_bool) with
            | left Hσ =>
                match decide (σ1 = σ2) with
                | left H12 =>
                    eq_rect_r D
                      (cast_sym Hbool
                         (xorb neg
                            (if excluded_middle_informative
                                  (eq_rect σ1 D v1 σ2 H12 = v2)
                             then true else false)))
                      Hσ
                | right _ => eq_rect_r D (cast_sym Hbool neg) Hσ
                end
            | right _ => witness σ
            end
      | l => base l σ
      end.

  Local Definition core_ite : forall σs σ, interpretation D σs σ :=
    fun σs σ =>
      match σs as l return interpretation D l σ with
      | [σ1; σ2; σ3] =>
          fun (b : D σ1) (v1 : D σ2) (v2 : D σ3) =>
            match decide (σ1 = σ_bool), decide (σ2 = σ), decide (σ3 = σ) with
            | left H1, left H2, left H3 =>
                if cast Hbool (eq_rect σ1 D b σ_bool H1)
                then eq_rect σ2 D v1 σ H2
                else eq_rect σ3 D v2 σ H3
            | _, _, _ => witness σ
            end
      | l => base l σ
      end.

  Definition core_interp : forall f σs σ, interpretation D σs σ :=
    interp_insert_func D f_true (core_lit true)
   (interp_insert_func D f_false (core_lit false)
   (interp_insert_func D f_not (core_unop negb)
   (interp_insert_func D f_impl (core_binop implb)
   (interp_insert_func D f_and (core_binop andb)
   (interp_insert_func D f_or (core_binop orb)
   (interp_insert_func D f_xor (core_binop xorb)
   (interp_insert_func D f_eq (core_cmp false)
   (interp_insert_func D f_distinct (core_cmp true)
   (interp_insert_func D f_ite core_ite
   (fun _ => base)))))))))).

  (* Reading one symbol out of the stack: miss until the name matches. *)
  Local Ltac core_func :=
    unfold core_interp;
    repeat (rewrite interp_insert_func_ne; [| discriminate]);
    rewrite interp_insert_func_eq; reflexivity.

  Local Lemma core_interp_true : forall σs σ,
      core_interp f_true σs σ = core_lit true σs σ.
  Proof. intros. core_func. Qed.
  Local Lemma core_interp_false : forall σs σ,
      core_interp f_false σs σ = core_lit false σs σ.
  Proof. intros. core_func. Qed.
  Local Lemma core_interp_not : forall σs σ,
      core_interp f_not σs σ = core_unop negb σs σ.
  Proof. intros. core_func. Qed.
  Local Lemma core_interp_impl : forall σs σ,
      core_interp f_impl σs σ = core_binop implb σs σ.
  Proof. intros. core_func. Qed.
  Local Lemma core_interp_and : forall σs σ,
      core_interp f_and σs σ = core_binop andb σs σ.
  Proof. intros. core_func. Qed.
  Local Lemma core_interp_or : forall σs σ,
      core_interp f_or σs σ = core_binop orb σs σ.
  Proof. intros. core_func. Qed.
  Local Lemma core_interp_xor : forall σs σ,
      core_interp f_xor σs σ = core_binop xorb σs σ.
  Proof. intros. core_func. Qed.
  Local Lemma core_interp_eq : forall σs σ,
      core_interp f_eq σs σ = core_cmp false σs σ.
  Proof. intros. core_func. Qed.
  Local Lemma core_interp_distinct : forall σs σ,
      core_interp f_distinct σs σ = core_cmp true σs σ.
  Proof. intros. core_func. Qed.
  Local Lemma core_interp_ite : forall σs σ,
      core_interp f_ite σs σ = core_ite σs σ.
  Proof. intros. core_func. Qed.

  Theorem core_interp_models :
    forall Hmap, models_core (structure_of D Hbool Hmap core_interp).
  Proof.
    intros Hmap.
    constructor;
      unfold models_f_true, models_f_false, models_f_not, models_f_impl,
        models_f_and, models_f_or, models_f_xor, models_f_eq,
        models_f_distinct, models_f_ite, cast_to_bool;
      cbv zeta; cbn [interp domain_σ_bool structure_of].
    - rewrite core_interp_true. unfold core_lit.
      rewrite interp_insert_rank_eq. apply cast_cast_sym.
    - rewrite core_interp_false. unfold core_lit.
      rewrite interp_insert_rank_eq. apply cast_cast_sym.
    - intros b. rewrite core_interp_not. unfold core_unop.
      rewrite interp_insert_rank_eq. apply cast_cast_sym.
    - intros b1 b2. rewrite core_interp_impl. unfold core_binop.
      rewrite interp_insert_rank_eq. apply cast_cast_sym.
    - intros b1 b2. rewrite core_interp_and. unfold core_binop.
      rewrite interp_insert_rank_eq. apply cast_cast_sym.
    - intros b1 b2. rewrite core_interp_or. unfold core_binop.
      rewrite interp_insert_rank_eq. apply cast_cast_sym.
    - intros b1 b2. rewrite core_interp_xor. unfold core_binop.
      rewrite interp_insert_rank_eq. apply cast_cast_sym.
    - intros σ v1 v2. rewrite core_interp_eq. unfold core_cmp.
      destruct (decide (σ_bool = σ_bool)) as [Hσ | Hne]; [| by contradiction].
      destruct (decide (σ = σ)) as [H12 | Hne]; [| by contradiction].
      rewrite (Eqdep_dec.UIP_dec (fun x y => decide (x = y)) Hσ eq_refl).
      rewrite (Eqdep_dec.UIP_dec (fun x y => decide (x = y)) H12 eq_refl).
      unfold eq_rect_r; cbn [eq_rect eq_sym].
      rewrite cast_cast_sym.
      destruct (excluded_middle_informative _) as [Heq | Hne2];
        cbn [xorb]; split; intros H; congruence.
    - intros σ v1 v2. rewrite core_interp_distinct. unfold core_cmp.
      destruct (decide (σ_bool = σ_bool)) as [Hσ | Hne]; [| by contradiction].
      destruct (decide (σ = σ)) as [H12 | Hne]; [| by contradiction].
      rewrite (Eqdep_dec.UIP_dec (fun x y => decide (x = y)) Hσ eq_refl).
      rewrite (Eqdep_dec.UIP_dec (fun x y => decide (x = y)) H12 eq_refl).
      unfold eq_rect_r; cbn [eq_rect eq_sym].
      rewrite cast_cast_sym.
      destruct (excluded_middle_informative _) as [Heq | Hne2];
        cbn [xorb]; split; intros H; congruence.
    - intros σ b v1 v2. rewrite core_interp_ite. unfold core_ite.
      destruct (decide (σ_bool = σ_bool)) as [H1 | Hne]; [| by contradiction].
      destruct (decide (σ = σ)) as [H2 | Hne]; [| by contradiction].
      rewrite (Eqdep_dec.UIP_dec (fun x y => decide (x = y)) H1 eq_refl).
      rewrite (Eqdep_dec.UIP_dec (fun x y => decide (x = y)) H2 eq_refl).
      cbn [eq_rect eq_sym]. reflexivity.
  Qed.

  Corollary T_core_interpretable :
    forall Hmap, pretheory_interpretable T_core D Hbool Hmap.
  Proof.
    intros Hmap. exists core_interp. apply core_interp_models.
  Qed.

End CoreInterpretable.

Theorem true_has_sort : forall Σ,
    Σ_core ⊑ Σ ->
    Σ ⊢ true_ : σ_bool.
Proof.
  intros * Hsub.
  econstructor; eauto.
  - sauto lq:on.
  - sblast use:monomorphic_rank_conservative.
  - reflexivity.
  - sauto q:on.
Qed.

Theorem false_has_sort : forall Σ,
    Σ_core ⊑ Σ ->
    Σ ⊢ false_ : σ_bool.
Proof.
  intros * Hsub.
  econstructor; eauto.
  - sauto q:on.
  - sblast use:monomorphic_rank_conservative.
  - reflexivity.
  - sauto q:on.
Qed.

Corollary bool_has_sort : forall Σ b,
    Σ_core ⊑ Σ ->
    Σ ⊢ bool_ b : σ_bool.
Proof.
  intros. destruct b; simpl.
  - apply true_has_sort. assumption.
  - apply false_has_sort. assumption.
Qed.

Theorem not_has_sort : forall Σ t,
    Σ_core ⊑ Σ ->
    (Σ ⊢ t : σ_bool) ->
    Σ ⊢ not_ t : σ_bool.
Proof.
  intros * Hsub Ht.
  econstructor.
  - sauto q:on.
  - sblast use:monomorphic_rank_conservative.
  - reflexivity.
  - intros * Ht_i Hσ_i.
    rewrite list_lookup_singleton in Ht_i.
    destruct i; try congruence. simpl in *.
    simplify_eq. assumption.
Qed.

(** A negation takes the value its body does not.  The introduction form for
    [not_], as [eval_or_true] is for [or_]. *)
Lemma eval_not :
  forall Σ A θ t (v : A.(domain) σ_bool),
    Σ_core ⊑ Σ ->
    models_core A ->
    ⟦ t : σ_bool ⟧(Σ, A, θ) ⇓ v ->
    ⟦ not_ t : σ_bool ⟧(Σ, A, θ)
      ⇓ cast_sym A.(domain_σ_bool) (negb (cast A.(domain_σ_bool) v)).
Proof.
  intros Σ A θ t v Hsub Hcore Ht.
  set (vnot := interp_apply A.(domain)
    (A.(interp) f_not [σ_bool] σ_bool)
    (HCons σ_bool [] v HNil)).
  assert (Hnot : ⟦ not_ t : σ_bool ⟧(Σ, A, θ) ⇓ vnot).
  { unfold not_, vnot.
    eapply E_TApp with (σs := [σ_bool]) (vs := HCons σ_bool [] v HNil).
    - repeat constructor; exact Ht.
    - constructor.
    - apply rank_monomorphic;
        [ apply (rank_extends Hsub); constructor
        | repeat constructor | repeat constructor ].
    - reflexivity. }
  replace (cast_sym A.(domain_σ_bool) (negb (cast A.(domain_σ_bool) v)))
    with vnot; [exact Hnot |].
  apply (proj1 (cast_eq_iff_eq_cast_sym A.(domain_σ_bool) vnot _)).
  unfold vnot. autorewrite with interp_apply.
  exact (mc_not Hcore v).
Qed.

Theorem impl_has_sort : forall Σ t1 t2,
    Σ_core ⊑ Σ ->
    (Σ ⊢ t1 : σ_bool) ->
    (Σ ⊢ t2 : σ_bool) ->
    Σ ⊢ impl_ t1 t2 : σ_bool.
Proof.
  intros * Hsub Ht1 Ht2.
  econstructor.
  - sauto.
  - scrush use:monomorphic_rank_conservative.
  - reflexivity.
  - intros * Ht_i Hσ_i.
    destruct i; simpl in *.
    + simplify_eq. assumption.
    + rewrite list_lookup_singleton in Ht_i.
      destruct i; try congruence. simpl in *.
      simplify_eq. assumption.
Qed.

Lemma eval_impl :
  forall Σ A θ t1 t2 b1 b2,
    Σ_core ⊑ Σ ->
    models_core A ->
    ⟦ t1 : σ_bool ⟧(Σ, A, θ) ⇓ cast_sym A.(domain_σ_bool) b1 ->
    ⟦ t2 : σ_bool ⟧(Σ, A, θ) ⇓ cast_sym A.(domain_σ_bool) b2 ->
    ⟦ impl_ t1 t2 : σ_bool ⟧(Σ, A, θ)
      ⇓ cast_sym A.(domain_σ_bool) (implb b1 b2).
Proof.
  intros Σ A θ t1 t2 b1 b2 Hsub Hcore Ht1 Ht2.
  unfold impl_. eapply E_TApp with (σs := [σ_bool; σ_bool])
    (vs := HCons σ_bool [σ_bool] (cast_sym A.(domain_σ_bool) b1)
      (HCons σ_bool [] (cast_sym A.(domain_σ_bool) b2) HNil)).
  - repeat constructor; [exact Ht1 | exact Ht2].
  - constructor.
  - apply rank_monomorphic;
      [ apply (rank_extends Hsub); constructor
      | repeat constructor | repeat constructor ].
  - apply (proj1 (cast_eq_iff_eq_cast_sym A.(domain_σ_bool)
      (interp_apply A.(domain)
        (A.(interp) f_impl [σ_bool; σ_bool] σ_bool)
        (HCons σ_bool [σ_bool] (cast_sym A.(domain_σ_bool) b1)
          (HCons σ_bool [] (cast_sym A.(domain_σ_bool) b2) HNil)))
      (implb b1 b2))).
    autorewrite with interp_apply.
    change (Core.cast_to_bool A
      (A.(interp) f_impl [σ_bool; σ_bool] σ_bool
        (cast_sym A.(domain_σ_bool) b1)
        (cast_sym A.(domain_σ_bool) b2)) = implb b1 b2).
    rewrite (mc_impl Hcore).
    unfold Core.cast_to_bool.
    rewrite !cast_cast_sym.
    reflexivity.
Qed.

Lemma eval_ite :
  forall Σ A θ σ c t1 t2 b (v1 v2 : A.(domain) σ),
    Σ_core ⊑ Σ ->
    models_core A ->
    monomorphic σ ->
    ⟦ c : σ_bool ⟧(Σ, A, θ) ⇓ cast_sym A.(domain_σ_bool) b ->
    ⟦ t1 : σ ⟧(Σ, A, θ) ⇓ v1 ->
    ⟦ t2 : σ ⟧(Σ, A, θ) ⇓ v2 ->
    ⟦ ite_ c t1 t2 : σ ⟧(Σ, A, θ) ⇓ (if b then v1 else v2).
Proof.
  intros Σ A θ σ c t1 t2 b v1 v2 Hsub Hcore Hmono Hc Ht1 Ht2.
  unfold ite_. eapply E_TApp with (σs := [σ_bool; σ; σ])
    (vs := HCons σ_bool [σ; σ] (cast_sym A.(domain_σ_bool) b)
      (HCons σ [σ] v1 (HCons σ [] v2 HNil))).
  - repeat constructor; [exact Hc | exact Ht1 | exact Ht2].
  - constructor.
  - exists {[ u_A := σ ]}, [σ_bool; τ_A; τ_A], τ_A.
    split_and!.
    + apply (rank_extends Hsub). constructor.
    + split; [| exact Hmono].
      unfold instance_of, τ_A. simpl. by rewrite lookup_singleton_eq.
    + constructor; [| constructor; [| constructor; [| constructor]]].
      all: split.
      all: try (unfold instance_of, τ_A; simpl;
                try rewrite lookup_singleton_eq; reflexivity).
      all: try exact Hmono.
      apply monomorphic_σ_bool.
  - autorewrite with interp_apply.
    rewrite (mc_ite Hcore σ).
    unfold cast_to_bool. rewrite cast_cast_sym.
    by destruct b.
Qed.

Lemma eval_impl_true_consequent :
  forall Σ A θ t1 t2,
    adt_constructed Σ A ->
    Σ_core ⊑ Σ ->
    models_core A ->
    (Σ ⊢ t1 : σ_bool) ->
    (Σ ⊢ t2 : σ_bool) ->
    valuation_well_sorted Σ.(sorts) θ ->
    ⟦ t1 : σ_bool ⟧(Σ, A, θ) ⇓ cast_sym A.(domain_σ_bool) true ->
    ⟦ impl_ t1 t2 : σ_bool ⟧(Σ, A, θ) ⇓ cast_sym A.(domain_σ_bool) true ->
    ⟦ t2 : σ_bool ⟧(Σ, A, θ) ⇓ cast_sym A.(domain_σ_bool) true.
Proof.
  intros Σ A θ t1 t2 Hadt Hsub Hcore Ht1 Ht2 Hθ Ht1_true Himpl_true.
  destruct (eval_total Σ A θ t2 σ_bool Hadt Ht2 Hθ) as (v2 & Ht2_eval).
  set (b2 := cast A.(domain_σ_bool) v2).
  assert (Hv2 : v2 = cast_sym A.(domain_σ_bool) b2).
  { subst b2. symmetry. apply cast_sym_cast. }
  rewrite Hv2 in Ht2_eval.
  pose proof (eval_impl Σ A θ t1 t2 true b2
    Hsub Hcore Ht1_true Ht2_eval) as Himpl_b.
  assert (Hb2 : b2 = true).
  { assert (Himpl_sort : Σ ⊢ impl_ t1 t2 : σ_bool).
    { apply impl_has_sort; [apply Hsub | exact Ht1 | exact Ht2]. }
    pose proof (eval_deterministic Σ A θ σ_bool
      (impl_ t1 t2)
      (cast_sym A.(domain_σ_bool) (implb true b2))
      (cast_sym A.(domain_σ_bool) true)
      Himpl_sort Hθ Himpl_b Himpl_true) as Hdet.
    apply (f_equal (cast A.(domain_σ_bool))) in Hdet.
    rewrite !cast_cast_sym in Hdet. exact Hdet. }
  rewrite Hb2 in Ht2_eval. exact Ht2_eval.
Qed.

Lemma eval_impl_true :
  forall Σ A θ t1 t2 (v1 v2 : A.(domain) σ_bool),
    Σ_core ⊑ Σ ->
    models_core A ->
    ⟦ t1 : σ_bool ⟧(Σ, A, θ) ⇓ v1 ->
    ⟦ t2 : σ_bool ⟧(Σ, A, θ) ⇓ v2 ->
    cast A.(domain_σ_bool) v1 = false \/
      cast A.(domain_σ_bool) v2 = true ->
    ⟦ impl_ t1 t2 : σ_bool ⟧(Σ, A, θ) ⇓ cast_sym A.(domain_σ_bool) true.
Proof.
  intros Σ A θ t1 t2 v1 v2 Hsub Hcore Ht1 Ht2 Hbool.
  set (vimpl := interp_apply A.(domain)
    (A.(interp) f_impl [σ_bool; σ_bool] σ_bool)
    (HCons σ_bool [σ_bool] v1 (HCons σ_bool [] v2 HNil))).
  assert (Himpl : ⟦ impl_ t1 t2 : σ_bool ⟧(Σ, A, θ) ⇓ vimpl).
  { unfold impl_, vimpl.
    eapply E_TApp with (σs := [σ_bool; σ_bool])
      (vs := HCons σ_bool [σ_bool] v1 (HCons σ_bool [] v2 HNil)).
    - repeat constructor; [exact Ht1 | exact Ht2].
    - constructor.
    - apply rank_monomorphic;
        [ apply (rank_extends Hsub); constructor
        | repeat constructor | repeat constructor ].
    - reflexivity. }
  replace (cast_sym A.(domain_σ_bool) true) with vimpl; [exact Himpl|].
  apply (proj1 (cast_eq_iff_eq_cast_sym A.(domain_σ_bool) vimpl true)).
  unfold vimpl. autorewrite with interp_apply.
  pose proof (mc_impl Hcore v1 v2) as Hmimpl.
  change (Core.cast_to_bool A
    (A.(interp) f_impl [σ_bool; σ_bool] σ_bool v1 v2) = true).
  rewrite Hmimpl.
  change (cast A.(domain_σ_bool) v1) with (Core.cast_to_bool A v1) in Hbool.
  change (cast A.(domain_σ_bool) v2) with (Core.cast_to_bool A v2) in Hbool.
  destruct Hbool as [Hfalse | Htrue].
  - rewrite Hfalse. reflexivity.
  - rewrite Htrue. destruct (Core.cast_to_bool A v1); reflexivity.
Qed.

Lemma eval_eq_true :
  forall Σ A θ σ t1 t2 (w1 w2 : A.(domain) σ),
    Σ_core ⊑ Σ ->
    models_core A ->
    monomorphic σ ->
    ⟦ t1 : σ ⟧(Σ, A, θ) ⇓ w1 ->
    ⟦ t2 : σ ⟧(Σ, A, θ) ⇓ w2 ->
    w1 = w2 ->
    ⟦ eq_ t1 t2 : σ_bool ⟧(Σ, A, θ) ⇓ cast_sym A.(domain_σ_bool) true.
Proof.
  intros Σ A θ σ t1 t2 w1 w2 Hsub Hcore Hmono Ht1 Ht2 Heq.
  subst w2.
  set (veq := interp_apply A.(domain)
    (A.(interp) f_eq [σ; σ] σ_bool)
    (HCons σ [σ] w1 (HCons σ [] w1 HNil))).
  assert (Heval : ⟦ eq_ t1 t2 : σ_bool ⟧(Σ, A, θ) ⇓ veq).
  { unfold eq_, veq. eapply E_TApp with (σs := [σ; σ])
      (vs := HCons σ [σ] w1 (HCons σ [] w1 HNil)).
    - repeat constructor; [exact Ht1 | exact Ht2].
    - constructor.
    - exists {[ u_A := σ ]}, [τ_A; τ_A], σ_bool.
      split_and!.
      + apply (rank_extends Hsub). constructor.
      + unfold monomorphic_instance_of. split; [|repeat constructor].
        unfold instance_of. reflexivity.
      + constructor.
        * unfold monomorphic_instance_of. split.
          -- unfold instance_of, τ_A; simpl.
             rewrite lookup_singleton_eq. reflexivity.
          -- exact Hmono.
        * constructor.
          -- unfold monomorphic_instance_of. split.
             ++ unfold instance_of, τ_A; simpl.
                rewrite lookup_singleton_eq. reflexivity.
             ++ exact Hmono.
          -- constructor.
    - reflexivity. }
  replace (cast_sym A.(domain_σ_bool) true) with veq; [exact Heval|].
  apply (proj1 (cast_eq_iff_eq_cast_sym A.(domain_σ_bool) veq true)).
  unfold veq. autorewrite with interp_apply.
  pose proof (mc_eq Hcore σ w1 w1) as Hmeq.
  unfold Core.cast_to_bool in Hmeq.
  change (Core.cast_to_bool A
    (A.(interp) f_eq [σ; σ] σ_bool w1 w1) = true).
  apply Hmeq. reflexivity.
Qed.

Lemma eval_eq_false :
  forall Σ A θ σ t1 t2 (w1 w2 : A.(domain) σ),
    Σ_core ⊑ Σ ->
    models_core A ->
    monomorphic σ ->
    ⟦ t1 : σ ⟧(Σ, A, θ) ⇓ w1 ->
    ⟦ t2 : σ ⟧(Σ, A, θ) ⇓ w2 ->
    w1 <> w2 ->
    ⟦ eq_ t1 t2 : σ_bool ⟧(Σ, A, θ) ⇓ cast_sym A.(domain_σ_bool) false.
Proof.
  intros Σ A θ σ t1 t2 w1 w2 Hsub Hcore Hmono Ht1 Ht2 Hneq.
  set (veq := interp_apply A.(domain)
    (A.(interp) f_eq [σ; σ] σ_bool)
    (HCons σ [σ] w1 (HCons σ [] w2 HNil))).
  assert (Heval : ⟦ eq_ t1 t2 : σ_bool ⟧(Σ, A, θ) ⇓ veq).
  { unfold eq_, veq. eapply E_TApp with (σs := [σ; σ])
      (vs := HCons σ [σ] w1 (HCons σ [] w2 HNil)).
    - repeat constructor; [exact Ht1 | exact Ht2].
    - constructor.
    - exists {[ u_A := σ ]}, [τ_A; τ_A], σ_bool.
      split_and!.
      + apply (rank_extends Hsub). constructor.
      + unfold monomorphic_instance_of. split; [|repeat constructor].
        unfold instance_of. reflexivity.
      + constructor.
        * unfold monomorphic_instance_of. split.
          -- unfold instance_of, τ_A; simpl.
             rewrite lookup_singleton_eq. reflexivity.
          -- exact Hmono.
        * constructor.
          -- unfold monomorphic_instance_of. split.
             ++ unfold instance_of, τ_A; simpl.
                rewrite lookup_singleton_eq. reflexivity.
             ++ exact Hmono.
          -- constructor.
    - reflexivity. }
  replace (cast_sym A.(domain_σ_bool) false) with veq; [exact Heval|].
  apply (proj1 (cast_eq_iff_eq_cast_sym A.(domain_σ_bool) veq false)).
  unfold veq. autorewrite with interp_apply.
  pose proof (mc_eq Hcore σ w1 w2) as Hmeq.
  unfold Core.cast_to_bool in Hmeq.
  change (Core.cast_to_bool A
    (A.(interp) f_eq [σ; σ] σ_bool w1 w2) = false).
  destruct (Core.cast_to_bool A
    (A.(interp) f_eq [σ; σ] σ_bool w1 w2)) eqn:Hb;
    [exfalso; apply Hneq; apply Hmeq; exact Hb | reflexivity].
Qed.

Lemma monomorphic_rank_f_eq_inv :
  forall Σ τs τ,
    Σ_core ⊑ Σ ->
    monomorphic_rank Σ f_eq τs τ ->
    exists δ, τs = [δ; δ] /\ τ = σ_bool.
Proof.
  intros Σ τs τ Hsub (θ & τs0 & τ0 & Hrk & Hinst_τ & Hinst_τs).
  pose proof (rank_conservative Hsub f_eq τs0 τ0 ltac:(constructor) Hrk) as Hcore.
  inversion Hcore; subst.
  destruct Hinst_τ as [Hinst_τ _].
  unfold instance_of in Hinst_τ. simpl in Hinst_τ. subst τ.
  inversion Hinst_τs as [|a la b lb Hab Hrest Heqa Heqb]; subst.
  inversion Hrest as [|a2 la2 b2 lb2 Hab2 Hrest2 Heqa2 Heqb2]; subst.
  inversion Hrest2; subst.
  destruct Hab as [Hab _]. destruct Hab2 as [Hab2 _].
  unfold instance_of in Hab, Hab2.
  exists (sort_subst θ τ_A). split; [|reflexivity].
  rewrite <- Hab, <- Hab2. reflexivity.
Qed.

Lemma eval_eq_true_inv :
  forall Σ A (V : valuation A) a b,
    Σ_core ⊑ Σ ->
    models_core A ->
    ⟦ eq_ a b : σ_bool ⟧(Σ, A, V) ⇓ cast_sym A.(domain_σ_bool) true ->
    exists δ (va vb : A.(domain) δ),
      ⟦ a : δ ⟧(Σ, A, V) ⇓ va /\ ⟦ b : δ ⟧(Σ, A, V) ⇓ vb /\ va = vb.
Proof.
  intros Σ A V a b Hsub Hcore Hev.
  unfold eq_ in Hev.
  apply eval_TApp_inv in Hev.
  destruct Hev as (σs'' & vs'' & Hargs' & _ & Hrank' & HF').
  apply monomorphic_rank_f_eq_inv in Hrank' as (δ & Hδ & _);
    [| exact Hsub].
  subst σs''.
  apply evals_cons_inv in Hargs'.
  destruct Hargs' as (va & vsa & -> & Hva & Hvtl).
  apply evals_cons_inv in Hvtl.
  destruct Hvtl as (vb & vsb & -> & Hvb & Hvnil).
  hlist_nil vsb.
  exists δ, va, vb.
  split; [exact Hva | split; [exact Hvb | ]].
  pose proof (mc_eq Hcore δ va vb) as Hmeq.
  unfold Core.cast_to_bool in Hmeq.
  assert (Hcb : cast A.(domain_σ_bool)
                  (A.(interp) f_eq [δ;δ] σ_bool va vb) = true).
  { cbn [interp_apply] in HF'. rewrite HF'.
    rewrite cast_eq_iff_eq_cast_sym. reflexivity. }
  apply Hmeq in Hcb. exact Hcb.
Qed.

Theorem and_has_sort : forall Σ t1 t2,
    Σ_core ⊑ Σ ->
    (Σ ⊢ t1 : σ_bool) ->
    (Σ ⊢ t2 : σ_bool) ->
    Σ ⊢ and_ t1 t2 : σ_bool.
Proof.
  intros * Hsub Ht1 Ht2.
  econstructor.
  - sauto.
  - sblast use:monomorphic_rank_conservative.
  - reflexivity.
  - intros * Ht_i Hσ_i.
    destruct i; simpl in *.
    + simplify_eq. assumption.
    + rewrite list_lookup_singleton in Ht_i.
      destruct i; try congruence. simpl in *.
      simplify_eq. assumption.
Qed.

Lemma eval_and :
  forall Σ A θ t1 t2 b1 b2,
    Σ_core ⊑ Σ ->
    models_core A ->
    ⟦ t1 : σ_bool ⟧(Σ, A, θ) ⇓ cast_sym A.(domain_σ_bool) b1 ->
    ⟦ t2 : σ_bool ⟧(Σ, A, θ) ⇓ cast_sym A.(domain_σ_bool) b2 ->
    ⟦ and_ t1 t2 : σ_bool ⟧(Σ, A, θ) ⇓ cast_sym A.(domain_σ_bool) (andb b1 b2).
Proof.
  intros Σ A θ t1 t2 b1 b2 Hsub Hcore Ht1 Ht2.
  unfold and_. eapply E_TApp with (σs := [σ_bool; σ_bool])
    (vs := HCons σ_bool [σ_bool] (cast_sym A.(domain_σ_bool) b1)
      (HCons σ_bool [] (cast_sym A.(domain_σ_bool) b2) HNil)).
  - repeat constructor; [exact Ht1 | exact Ht2].
  - constructor.
  - apply rank_monomorphic;
      [ apply (rank_extends Hsub); constructor
      | repeat constructor | repeat constructor ].
  - apply (proj1 (cast_eq_iff_eq_cast_sym A.(domain_σ_bool)
      (interp_apply A.(domain)
        (A.(interp) f_and [σ_bool; σ_bool] σ_bool)
        (HCons σ_bool [σ_bool] (cast_sym A.(domain_σ_bool) b1)
          (HCons σ_bool [] (cast_sym A.(domain_σ_bool) b2) HNil)))
      (andb b1 b2))).
    autorewrite with interp_apply.
    change (Core.cast_to_bool A
      (A.(interp) f_and [σ_bool; σ_bool] σ_bool
        (cast_sym A.(domain_σ_bool) b1)
        (cast_sym A.(domain_σ_bool) b2)) = andb b1 b2).
    rewrite (mc_and Hcore).
    unfold Core.cast_to_bool.
    rewrite !cast_cast_sym.
    reflexivity.
Qed.

Lemma monomorphic_rank_f_and_inv :
  forall Σ τs τ,
    Σ_core ⊑ Σ ->
    monomorphic_rank Σ f_and τs τ ->
    τs = [σ_bool; σ_bool] /\ τ = σ_bool.
Proof.
  intros Σ τs τ Hsub (θ & τs0 & τ0 & Hrk & Hinst_τ & Hinst_τs).
  pose proof (rank_conservative Hsub f_and τs0 τ0 ltac:(constructor) Hrk)
    as Hcore.
  inversion Hcore; subst.
  destruct Hinst_τ as [Hinst_τ _].
  unfold instance_of in Hinst_τ. simpl in Hinst_τ. subst τ.
  inversion Hinst_τs as [|a la b lb Hab Hrest Heqa Heqb]; subst.
  inversion Hrest as [|a2 la2 b2 lb2 Hab2 Hrest2 Heqa2 Heqb2]; subst.
  inversion Hrest2; subst.
  destruct Hab as [Hab _]. destruct Hab2 as [Hab2 _].
  unfold instance_of in Hab, Hab2. simpl in Hab, Hab2.
  subst la la2.
  split; reflexivity.
Qed.

Lemma eval_and_true_inv :
  forall Σ A θ t1 t2,
    Σ_core ⊑ Σ ->
    models_core A ->
    ⟦ and_ t1 t2 : σ_bool ⟧(Σ, A, θ) ⇓ cast_sym A.(domain_σ_bool) true ->
    ⟦ t1 : σ_bool ⟧(Σ, A, θ) ⇓ cast_sym A.(domain_σ_bool) true /\
    ⟦ t2 : σ_bool ⟧(Σ, A, θ) ⇓ cast_sym A.(domain_σ_bool) true.
Proof.
  intros Σ A θ t1 t2 Hsub Hcore Hand.
  unfold and_ in Hand.
  apply eval_TApp_inv in Hand.
  destruct Hand as (σs & vs & Hargs & _ & Hrank & H4).
  pose proof (monomorphic_rank_f_and_inv Σ σs σ_bool Hsub Hrank) as [Hσs _].
  subst σs.
  apply evals_cons_inv in Hargs.
  destruct Hargs as (v & vs1 & -> & H & Hargs).
  apply evals_cons_inv in Hargs.
  destruct Hargs as (v0 & vs2 & -> & H0 & Hargs).
  hlist_nil vs2.
  autorewrite with interp_apply in H4.
  pose proof (mc_and Hcore v v0) as Hand_sem.
  change (Core.cast_to_bool A
    (A.(interp) f_and [σ_bool; σ_bool] σ_bool v v0) =
    andb (Core.cast_to_bool A v) (Core.cast_to_bool A v0)) in Hand_sem.
  unfold Core.cast_to_bool in Hand_sem.
  apply cast_eq_iff_eq_cast_sym in H4.
  assert (Hand_true :
    cast A.(domain_σ_bool) v && cast A.(domain_σ_bool) v0 = true).
  { transitivity
      (cast A.(domain_σ_bool)
        (A.(interp) f_and [σ_bool; σ_bool] σ_bool v v0)).
    - symmetry. exact Hand_sem.
    - exact H4. }
  apply andb_true_iff in Hand_true as [Hv Hv0].
  split.
  - change (⟦ t1 : σ_bool ⟧(Σ, A, θ) ⇓ cast_sym A.(domain_σ_bool) true).
    replace (cast_sym A.(domain_σ_bool) true) with v.
    + exact H.
    + apply (proj1 (cast_eq_iff_eq_cast_sym A.(domain_σ_bool) v true)).
      exact Hv.
  - change (⟦ t2 : σ_bool ⟧(Σ, A, θ) ⇓ cast_sym A.(domain_σ_bool) true).
    replace (cast_sym A.(domain_σ_bool) true) with v0.
    + exact H0.
    + apply (proj1 (cast_eq_iff_eq_cast_sym A.(domain_σ_bool) v0 true)).
      exact Hv0.
Qed.

Lemma monomorphic_rank_f_or_inv :
  forall Σ τs τ,
    Σ_core ⊑ Σ ->
    monomorphic_rank Σ f_or τs τ ->
    τs = [σ_bool; σ_bool] /\ τ = σ_bool.
Proof.
  intros Σ τs τ Hsub (θ & τs0 & τ0 & Hrk & Hinst_τ & Hinst_τs).
  pose proof (rank_conservative Hsub f_or τs0 τ0 ltac:(constructor) Hrk)
    as Hcore.
  inversion Hcore; subst.
  destruct Hinst_τ as [Hinst_τ _].
  unfold instance_of in Hinst_τ. simpl in Hinst_τ. subst τ.
  inversion Hinst_τs as [|a la b lb Hab Hrest Heqa Heqb]; subst.
  inversion Hrest as [|a2 la2 b2 lb2 Hab2 Hrest2 Heqa2 Heqb2]; subst.
  inversion Hrest2; subst.
  destruct Hab as [Hab _]. destruct Hab2 as [Hab2 _].
  unfold instance_of in Hab, Hab2. simpl in Hab, Hab2.
  subst la la2.
  split; reflexivity.
Qed.

(** The disjunction counterpart of [eval_and_true_inv].  A true disjunction
    does not say which side holds, so this is where a proof reading a
    [repr_*_body] back learns which case it is in. *)
Lemma eval_or_true_inv :
  forall Σ A θ t1 t2,
    Σ_core ⊑ Σ ->
    models_core A ->
    ⟦ or_ t1 t2 : σ_bool ⟧(Σ, A, θ) ⇓ cast_sym A.(domain_σ_bool) true ->
    ⟦ t1 : σ_bool ⟧(Σ, A, θ) ⇓ cast_sym A.(domain_σ_bool) true \/
    ⟦ t2 : σ_bool ⟧(Σ, A, θ) ⇓ cast_sym A.(domain_σ_bool) true.
Proof.
  intros Σ A θ t1 t2 Hsub Hcore Hor.
  unfold or_ in Hor.
  apply eval_TApp_inv in Hor.
  destruct Hor as (σs & vs & Hargs & _ & Hrank & H4).
  pose proof (monomorphic_rank_f_or_inv Σ σs σ_bool Hsub Hrank) as [Hσs _].
  subst σs.
  apply evals_cons_inv in Hargs.
  destruct Hargs as (v & vs1 & -> & H & Hargs).
  apply evals_cons_inv in Hargs.
  destruct Hargs as (v0 & vs2 & -> & H0 & Hargs).
  hlist_nil vs2.
  autorewrite with interp_apply in H4.
  pose proof (mc_or Hcore v v0) as Hor_sem.
  change (Core.cast_to_bool A
    (A.(interp) f_or [σ_bool; σ_bool] σ_bool v v0) =
    orb (Core.cast_to_bool A v) (Core.cast_to_bool A v0)) in Hor_sem.
  unfold Core.cast_to_bool in Hor_sem.
  apply cast_eq_iff_eq_cast_sym in H4.
  assert (Hor_true :
    cast A.(domain_σ_bool) v || cast A.(domain_σ_bool) v0 = true).
  { transitivity
      (cast A.(domain_σ_bool)
        (A.(interp) f_or [σ_bool; σ_bool] σ_bool v v0)).
    - symmetry. exact Hor_sem.
    - exact H4. }
  apply orb_true_iff in Hor_true as [Hv | Hv0].
  - left.
    change (⟦ t1 : σ_bool ⟧(Σ, A, θ) ⇓ cast_sym A.(domain_σ_bool) true).
    replace (cast_sym A.(domain_σ_bool) true) with v; [exact H |].
    apply (proj1 (cast_eq_iff_eq_cast_sym A.(domain_σ_bool) v true)). exact Hv.
  - right.
    change (⟦ t2 : σ_bool ⟧(Σ, A, θ) ⇓ cast_sym A.(domain_σ_bool) true).
    replace (cast_sym A.(domain_σ_bool) true) with v0; [exact H0 |].
    apply (proj1 (cast_eq_iff_eq_cast_sym A.(domain_σ_bool) v0 true)). exact Hv0.
Qed.

(** The introduction form, which is what a proof *building* a guard needs.
    Both sides have to evaluate for the disjunction to, so the caller hands
    over a value for each and says which one is true. *)
Lemma eval_or_true :
  forall Σ A θ t1 t2 (v1 v2 : A.(domain) σ_bool),
    Σ_core ⊑ Σ ->
    models_core A ->
    ⟦ t1 : σ_bool ⟧(Σ, A, θ) ⇓ v1 ->
    ⟦ t2 : σ_bool ⟧(Σ, A, θ) ⇓ v2 ->
    cast A.(domain_σ_bool) v1 = true \/
      cast A.(domain_σ_bool) v2 = true ->
    ⟦ or_ t1 t2 : σ_bool ⟧(Σ, A, θ) ⇓ cast_sym A.(domain_σ_bool) true.
Proof.
  intros Σ A θ t1 t2 v1 v2 Hsub Hcore Ht1 Ht2 Hbool.
  set (vor := interp_apply A.(domain)
    (A.(interp) f_or [σ_bool; σ_bool] σ_bool)
    (HCons σ_bool [σ_bool] v1 (HCons σ_bool [] v2 HNil))).
  assert (Hor : ⟦ or_ t1 t2 : σ_bool ⟧(Σ, A, θ) ⇓ vor).
  { unfold or_, vor.
    eapply E_TApp with (σs := [σ_bool; σ_bool])
      (vs := HCons σ_bool [σ_bool] v1 (HCons σ_bool [] v2 HNil)).
    - repeat constructor; [exact Ht1 | exact Ht2].
    - constructor.
    - apply rank_monomorphic;
        [ apply (rank_extends Hsub); constructor
        | repeat constructor | repeat constructor ].
    - reflexivity. }
  replace (cast_sym A.(domain_σ_bool) true) with vor; [exact Hor|].
  apply (proj1 (cast_eq_iff_eq_cast_sym A.(domain_σ_bool) vor true)).
  unfold vor. autorewrite with interp_apply.
  pose proof (mc_or Hcore v1 v2) as Hmor.
  change (Core.cast_to_bool A
    (A.(interp) f_or [σ_bool; σ_bool] σ_bool v1 v2) = true).
  rewrite Hmor.
  change (cast A.(domain_σ_bool) v1) with (Core.cast_to_bool A v1) in Hbool.
  change (cast A.(domain_σ_bool) v2) with (Core.cast_to_bool A v2) in Hbool.
  destruct Hbool as [Htrue | Htrue]; rewrite Htrue;
    [reflexivity | destruct (Core.cast_to_bool A v1); reflexivity].
Qed.

(** [false_] is false, so a true [ors_] over the empty list is impossible and
    the member the disjunction picks out is one of the [ts]. *)
Lemma eval_false_not_true :
  forall Σ A θ,
    Σ_core ⊑ Σ ->
    models_core A ->
    ~ ⟦ false_ : σ_bool ⟧(Σ, A, θ) ⇓ cast_sym A.(domain_σ_bool) true.
Proof.
  intros Σ A θ Hsub Hcore Hfalse.
  unfold false_ in Hfalse.
  apply eval_TApp_inv in Hfalse.
  destruct Hfalse as (σs & vs & Hargs & _ & Hrank & H4).
  apply evals_nil_sorts in Hargs as Hσs. subst σs.
  hlist_nil vs.
  autorewrite with interp_apply in H4.
  pose proof (mc_false Hcore) as Hfalse_sem.
  change (Core.cast_to_bool A (A.(interp) f_false [] σ_bool) = false)
    in Hfalse_sem.
  unfold Core.cast_to_bool in Hfalse_sem.
  rewrite H4, cast_cast_sym in Hfalse_sem.
  discriminate.
Qed.

(** The dual: [true_] is true.  What an [ands_] over an empty tail, or a
    guard with no further conjunct, bottoms out at. *)
Lemma eval_true_true :
  forall Σ A θ,
    Σ_core ⊑ Σ ->
    models_core A ->
    ⟦ true_ : σ_bool ⟧(Σ, A, θ) ⇓ cast_sym A.(domain_σ_bool) true.
Proof.
  intros Σ A θ Hsub Hcore.
  unfold true_.
  eapply E_TApp with (σs := []) (vs := HNil).
  - constructor.
  - constructor.
  - apply rank_monomorphic;
      [ apply (rank_extends Hsub); constructor
      | constructor | repeat constructor ].
  - apply (proj1 (cast_eq_iff_eq_cast_sym A.(domain_σ_bool) _ true)).
    autorewrite with interp_apply.
    exact (mc_true Hcore).
Qed.

Lemma eval_ors_true_inv :
  forall Σ A θ ts,
    Σ_core ⊑ Σ ->
    models_core A ->
    ⟦ ors_ ts false_ : σ_bool ⟧(Σ, A, θ) ⇓ cast_sym A.(domain_σ_bool) true ->
    exists ψ, ψ ∈ ts /\
      ⟦ ψ : σ_bool ⟧(Σ, A, θ) ⇓ cast_sym A.(domain_σ_bool) true.
Proof.
  intros Σ A θ ts Hsub Hcore.
  induction ts as [|ϕ ts IH]; simpl; intros Hors.
  - exfalso. eapply eval_false_not_true; eassumption.
  - apply (eval_or_true_inv Σ A θ) in Hors as [Hϕ | Hrest];
      [| | exact Hsub | exact Hcore].
    + exists ϕ. split; [apply elem_of_cons; now left | exact Hϕ].
    + destruct (IH Hrest) as (ψ & Hψ & Heval).
      exists ψ. split; [apply elem_of_cons; now right | exact Heval].
Qed.

Lemma eval_ands_true_inv :
  forall Σ A θ ts t ψ,
    Σ_core ⊑ Σ ->
    models_core A ->
    ⟦ ands_ ts t : σ_bool ⟧(Σ, A, θ) ⇓ cast_sym A.(domain_σ_bool) true ->
    ψ ∈ ts ->
    ⟦ ψ : σ_bool ⟧(Σ, A, θ) ⇓ cast_sym A.(domain_σ_bool) true.
Proof.
  intros Σ A θ ts t ψ Hsub Hcore Hands Hψ.
  revert t ψ Hands Hψ.
  induction ts as [|ϕ ts IH]; intros t ψ Hands Hψ.
  - apply elem_of_nil in Hψ. contradiction.
  - simpl in Hands.
    destruct (eval_and_true_inv Σ A θ ϕ (ands_ ts t) Hsub Hcore Hands)
      as [Hϕ_true Htail_true].
    rewrite elem_of_cons in Hψ.
    destruct Hψ as [->|Hψ].
    + exact Hϕ_true.
    + apply (IH t ψ); [exact Htail_true|exact Hψ].
Qed.

(** The introduction form: every conjunct true, and the tail true, makes the
    whole conjunction true.  Unlike the disjunction below it needs no
    well-sortedness — every conjunct has to evaluate anyway. *)
Lemma eval_ands_true :
  forall Σ A θ ts t,
    Σ_core ⊑ Σ ->
    models_core A ->
    (forall ψ, ψ ∈ ts ->
       ⟦ ψ : σ_bool ⟧(Σ, A, θ) ⇓ cast_sym A.(domain_σ_bool) true) ->
    ⟦ t : σ_bool ⟧(Σ, A, θ) ⇓ cast_sym A.(domain_σ_bool) true ->
    ⟦ ands_ ts t : σ_bool ⟧(Σ, A, θ) ⇓ cast_sym A.(domain_σ_bool) true.
Proof.
  intros Σ A θ ts t Hsub Hcore.
  induction ts as [|ϕ ts IH]; intros Hall Ht; [exact Ht|].
  cbn [ands_ foldr].
  change (cast_sym A.(domain_σ_bool) true)
    with (cast_sym A.(domain_σ_bool) (andb true true)).
  apply eval_and; [exact Hsub | exact Hcore | |].
  - apply Hall, elem_of_cons; now left.
  - apply IH; [intros ψ Hψ; apply Hall, elem_of_cons; now right | exact Ht].
Qed.

Corollary ands_has_sort : forall ts Σ t,
    Σ_core ⊑ Σ ->
    (Σ ⊢ t : σ_bool) ->
    (forall t, t ∈ ts -> (Σ ⊢ t : σ_bool)) ->
    Σ ⊢ ands_ ts t : σ_bool.
Proof.
  induction ts as [|t0]; sauto use:and_has_sort.
Qed.

Lemma term_subst_ands :
  forall θ ts t,
    term_subst θ (ands_ ts t) =
    ands_ (term_subst θ <$> ts) (term_subst θ t).
Proof.
  intros θ ts.
  induction ts as [|ϕ ts IH]; intros t; simpl.
  - reflexivity.
  - unfold and_. simpl. rewrite IH. reflexivity.
Qed.

Theorem or_has_sort : forall Σ t1 t2,
    Σ_core ⊑ Σ ->
    (Σ ⊢ t1 : σ_bool) ->
    (Σ ⊢ t2 : σ_bool) ->
    Σ ⊢ or_ t1 t2 : σ_bool.
Proof.
  intros * Hsub Ht1 Ht2.
  econstructor.
  - sauto.
  - sblast use:monomorphic_rank_conservative.
  - reflexivity.
  - intros * Ht_i Hσ_i.
    destruct i; simpl in *.
    + simplify_eq. assumption.
    + rewrite list_lookup_singleton in Ht_i.
      destruct i; try congruence. simpl in *.
      simplify_eq. assumption.
Qed.

Corollary ors_has_sort : forall ts Σ t,
    Σ_core ⊑ Σ ->
    (Σ ⊢ t : σ_bool) ->
    (forall t, t ∈ ts -> (Σ ⊢ t : σ_bool)) ->
    Σ ⊢ ors_ ts t : σ_bool.
Proof.
  induction ts as [|t0]; sauto use:or_has_sort.
Qed.

Theorem xor_has_sort : forall Σ t1 t2,
    Σ_core ⊑ Σ ->
    (Σ ⊢ t1 : σ_bool) ->
    (Σ ⊢ t2 : σ_bool) ->
    Σ ⊢ xor_ t1 t2 : σ_bool.
Proof.
  intros * Hsub Ht1 Ht2.
  econstructor.
  - sauto.
  - sblast use:monomorphic_rank_conservative.
  - reflexivity.
  - intros * Ht_i Hσ_i.
    destruct i; simpl in *.
    + simplify_eq. assumption.
    + rewrite list_lookup_singleton in Ht_i.
      destruct i; try congruence. simpl in *.
      simplify_eq. assumption.
Qed.

Theorem eq_has_sort : forall Σ t1 t2 σ,
    Σ_core ⊑ Σ ->
    monomorphic σ ->
    (Σ ⊢ t1 : σ) ->
    (Σ ⊢ t2 : σ) ->
    Σ ⊢ eq_ t1 t2 : σ_bool.
Proof.
  intros * Hsub Hmono Ht1 Ht2.
  econstructor.
  - exists {[ u_A := σ ]}, [τ_A; τ_A], σ_bool. ecrush.
  - sblast use:monomorphic_rank_conservative.
  - reflexivity.
  - intros * Ht_i Hσ_i.
    destruct i; simpl in *.
    + simplify_eq. assumption.
    + rewrite list_lookup_singleton in Ht_i.
      destruct i; try congruence. simpl in *.
      simplify_eq. assumption.
Qed.

(** The converse of [eval_ors_true_inv].  The members other than the one
    that holds still have to evaluate, which is where the well-sortedness
    premise and [eval_total] come in. *)
Lemma eval_ors_true :
  forall Σ A θ ts ψ,
    adt_constructed Σ A ->
    Σ_core ⊑ Σ ->
    models_core A ->
    valuation_well_sorted Σ.(sorts) θ ->
    (forall t, t ∈ ts -> (Σ ⊢ t : σ_bool)) ->
    ψ ∈ ts ->
    ⟦ ψ : σ_bool ⟧(Σ, A, θ) ⇓ cast_sym A.(domain_σ_bool) true ->
    ⟦ ors_ ts false_ : σ_bool ⟧(Σ, A, θ) ⇓ cast_sym A.(domain_σ_bool) true.
Proof.
  intros Σ A θ ts ψ Hadt Hsub Hcore Hθ.
  induction ts as [|ϕ ts IH]; intros Hsort Hψ Htrue.
  - exfalso. eapply not_elem_of_nil. exact Hψ.
  - assert (Htail_sort : Σ ⊢ ors_ ts false_ : σ_bool).
    { apply ors_has_sort;
        [apply Hsub
        | apply false_has_sort, Hsub |].
      intros t Ht. apply Hsort, elem_of_cons; now right. }
    assert (Hhead_sort : Σ ⊢ ϕ : σ_bool)
      by (apply Hsort, elem_of_cons; now left).
    destruct (eval_total Σ A θ ϕ σ_bool Hadt Hhead_sort Hθ) as (vh & Hvh).
    destruct (eval_total Σ A θ (ors_ ts false_) σ_bool Hadt Htail_sort Hθ)
      as (vt & Hvt).
    cbn [ors_ foldr].
    apply elem_of_cons in Hψ as [-> | Hψ].
    + eapply (eval_or_true Σ A θ ϕ (ors_ ts false_) vh vt);
        [exact Hsub | exact Hcore | exact Hvh | exact Hvt |].
      left.
      assert (vh = cast_sym A.(domain_σ_bool) true)
        by (eapply eval_deterministic;
            [exact Hhead_sort | exact Hθ | exact Hvh | exact Htrue]).
      subst vh. apply cast_cast_sym.
    + eapply (eval_or_true Σ A θ ϕ (ors_ ts false_) vh vt);
        [exact Hsub | exact Hcore | exact Hvh | exact Hvt |].
      right.
      assert (vt = cast_sym A.(domain_σ_bool) true).
      { eapply eval_deterministic; [exact Htail_sort | exact Hθ | exact Hvt |].
        apply (IH ltac:(intros t Ht; apply Hsort, elem_of_cons; now right)
                 Hψ Htrue). }
      subst vt. apply cast_cast_sym.
Qed.

(* A true [distinct_] says the two values differ.  Same shape as the [and_]
   and [or_] inversions: build the application's evaluation, then read the
   model condition off it. *)
Lemma eval_distinct_true_inv :
  forall Σ A θ σ t1 t2 (w1 w2 : A.(domain) σ),
    Σ_core ⊑ Σ ->
    models_core A ->
    monomorphic σ ->
    (Σ ⊢ distinct_ t1 t2 : σ_bool) ->
    valuation_well_sorted Σ.(sorts) θ ->
    ⟦ t1 : σ ⟧(Σ, A, θ) ⇓ w1 ->
    ⟦ t2 : σ ⟧(Σ, A, θ) ⇓ w2 ->
    ⟦ distinct_ t1 t2 : σ_bool ⟧(Σ, A, θ) ⇓ cast_sym A.(domain_σ_bool) true ->
    w1 <> w2.
Proof.
  intros Σ A θ σ t1 t2 w1 w2 Hsub Hcore Hmono Hsort Hθ Ht1 Ht2 Htrue.
  assert (Heval : ⟦ distinct_ t1 t2 : σ_bool ⟧(Σ, A, θ)
                    ⇓ A.(interp) f_distinct [σ; σ] σ_bool w1 w2).
  { unfold distinct_. eapply E_TApp with (σs := [σ; σ])
      (vs := HCons σ [σ] w1 (HCons σ [] w2 HNil)).
    - repeat constructor; [exact Ht1 | exact Ht2].
    - constructor.
    - exists {[ u_A := σ ]}, [τ_A; τ_A], σ_bool.
      split_and!.
      + apply (rank_extends Hsub). constructor.
      + unfold monomorphic_instance_of. split; [|repeat constructor].
        unfold instance_of. reflexivity.
      + constructor.
        * unfold monomorphic_instance_of. split.
          -- unfold instance_of, τ_A; simpl.
             rewrite lookup_singleton_eq. reflexivity.
          -- exact Hmono.
        * constructor.
          -- unfold monomorphic_instance_of. split.
             ++ unfold instance_of, τ_A; simpl.
                rewrite lookup_singleton_eq. reflexivity.
             ++ exact Hmono.
          -- constructor.
    - autorewrite with interp_apply. reflexivity. }
  assert (Heq : A.(interp) f_distinct [σ; σ] σ_bool w1 w2
                = cast_sym A.(domain_σ_bool) true)
    by (eapply eval_deterministic; [exact Hsort | exact Hθ | exact Heval | exact Htrue]).
  apply (proj1 (mc_distinct Hcore σ w1 w2)).
  change (Core.cast_to_bool A
    (A.(interp) f_distinct [σ; σ] σ_bool w1 w2) = true).
  unfold Core.cast_to_bool. rewrite Heq. apply cast_cast_sym.
Qed.

(** The introduction form, for a proof building a guard rather than reading
    one back. *)
Lemma eval_distinct_true :
  forall Σ A θ σ t1 t2 (w1 w2 : A.(domain) σ),
    Σ_core ⊑ Σ ->
    models_core A ->
    monomorphic σ ->
    ⟦ t1 : σ ⟧(Σ, A, θ) ⇓ w1 ->
    ⟦ t2 : σ ⟧(Σ, A, θ) ⇓ w2 ->
    w1 <> w2 ->
    ⟦ distinct_ t1 t2 : σ_bool ⟧(Σ, A, θ) ⇓ cast_sym A.(domain_σ_bool) true.
Proof.
  intros Σ A θ σ t1 t2 w1 w2 Hsub Hcore Hmono Ht1 Ht2 Hne.
  assert (Heval : ⟦ distinct_ t1 t2 : σ_bool ⟧(Σ, A, θ)
                    ⇓ A.(interp) f_distinct [σ; σ] σ_bool w1 w2).
  { unfold distinct_. eapply E_TApp with (σs := [σ; σ])
      (vs := HCons σ [σ] w1 (HCons σ [] w2 HNil)).
    - repeat constructor; [exact Ht1 | exact Ht2].
    - constructor.
    - exists {[ u_A := σ ]}, [τ_A; τ_A], σ_bool.
      split_and!.
      + apply (rank_extends Hsub). constructor.
      + unfold monomorphic_instance_of. split; [|repeat constructor].
        unfold instance_of. reflexivity.
      + constructor.
        * unfold monomorphic_instance_of. split.
          -- unfold instance_of, τ_A; simpl.
             rewrite lookup_singleton_eq. reflexivity.
          -- exact Hmono.
        * constructor.
          -- unfold monomorphic_instance_of. split.
             ++ unfold instance_of, τ_A; simpl.
                rewrite lookup_singleton_eq. reflexivity.
             ++ exact Hmono.
          -- constructor.
    - autorewrite with interp_apply. reflexivity. }
  replace (cast_sym A.(domain_σ_bool) true)
    with (A.(interp) f_distinct [σ; σ] σ_bool w1 w2); [exact Heval|].
  apply (proj1 (cast_eq_iff_eq_cast_sym A.(domain_σ_bool)
    (A.(interp) f_distinct [σ; σ] σ_bool w1 w2) true)).
  exact (proj2 (mc_distinct Hcore σ w1 w2) Hne).
Qed.

Theorem distinct_has_sort : forall Σ t1 t2 σ,
    Σ_core ⊑ Σ ->
    monomorphic σ ->
    (Σ ⊢ t1 : σ) ->
    (Σ ⊢ t2 : σ) ->
    Σ ⊢ distinct_ t1 t2 : σ_bool.
Proof.
  intros * Hsub Hmono Ht1 Ht2.
  econstructor.
  - exists {[ u_A := σ ]}, [τ_A; τ_A], σ_bool. ecrush.
  - sblast use:monomorphic_rank_conservative.
  - reflexivity.
  - intros * Ht_i Hσ_i.
    destruct i; simpl in *.
    + simplify_eq. assumption.
    + rewrite list_lookup_singleton in Ht_i.
      destruct i; try congruence. simpl in *.
      simplify_eq. assumption.
Qed.

Theorem ite_has_sort : forall Σ t t1 t2 σ,
    Σ_core ⊑ Σ ->
    monomorphic σ ->
    (Σ ⊢ t : σ_bool) ->
    (Σ ⊢ t1 : σ) ->
    (Σ ⊢ t2 : σ) ->
    Σ ⊢ ite_ t t1 t2 : σ.
Proof.
  intros * Hsub Hmono Ht1 Ht2 Ht3.
  econstructor.
  - exists {[ u_A := σ ]}, [σ_bool; τ_A; τ_A], τ_A. ecrush.
  - intros * Hrank.
    eapply monomorphic_rank_conservative in Hrank; eauto.
    ecrush. set_solver.
  - reflexivity.
  - intros * Ht_i Hσ_i.
    destruct i; try destruct i; simpl in *.
    + simplify_eq. assumption.
    + simplify_eq. assumption.
    + rewrite list_lookup_singleton in Ht_i.
      destruct i; try congruence. simpl in *.
      simplify_eq. assumption.
Qed.

(* TODO: Move? *)
Definition define_fun
  (f : func) (xs : list var) (σs : list sort) (t : term)
  : term  :=
  foldr
    (fun '(x, σ) t => TForall σ (term_close [x] 0 t))
    (eq_ (TApp f None (map TFVar xs)) t)
    (zip xs σs).

Lemma define_fun_forall_telescope_lc : forall (xs : list var) (σs : list sort) e,
  lc_at [] e ->
  lc_at [] (foldr (fun '(x, σ) t => TForall σ (term_close [x] 0 t)) e
                 (zip xs σs)).
Proof.
  induction xs as [|x xs' IH]; intros σs e Hlc; [simpl; exact Hlc|].
  destruct σs as [|σ0 σs']; [simpl; exact Hlc|].
  cbn [zip zip_with foldr].
  apply LCA_TForall. apply lc_at_term_close1. apply IH. exact Hlc.
Qed.

Lemma define_fun_strip_forall_telescope :
  forall Σ (xs : list var) (σs : list sort)
      A (V : valuation A) (ws : hlist A.(domain) σs) e,
    NoDup xs ->
    length xs = length σs ->
    lc_at [] e ->
    ⟦ foldr (fun '(x, σ) t => TForall σ (term_close [x] 0 t)) e (zip xs σs)
      : σ_bool ⟧(Σ, A, V) ⇓ cast_sym A.(domain_σ_bool) true ->
    ⟦ e : σ_bool ⟧(Σ, A, list_to_map (zip xs (hlist_to_list ws)) ∪ V)
      ⇓ cast_sym A.(domain_σ_bool) true.
Proof.
  intros Σ xs.
  revert Σ.
  induction xs as [|x xs' IH]; intros Σ σs A V ws e Hnodup Hlen Hlc Hev.
  - destruct σs; [|discriminate Hlen].
    cbn [zip zip_with]. rewrite list_to_map_nil, (left_id_L ∅ (∪)). exact Hev.
  - destruct σs as [|σ0 σs']; [discriminate Hlen|].
    cbn [zip zip_with foldr] in Hev.
    hlist_cons ws.
    apply NoDup_cons in Hnodup as [Hx_notin Hnodup'].
    assert (Hxnone : (list_to_map (zip xs' (hlist_to_list ws)) : valuation A) !! x = None)
      by (apply lookup_list_to_map_zip_None; exact Hx_notin).
    (* the head binder joins the base valuation *)
    cbn [hlist_to_list zip zip_with].
    rewrite list_to_map_cons, <- insert_union_l, (insert_union_r _ _ _ _ Hxnone).
    apply IH; [ exact Hnodup' | simpl in Hlen; lia | exact Hlc | ].
    apply eval_TForall_true_inv in Hev.
    destruct Hev as [L HL].
    set (INNER := foldr (fun '(x0, σ) t => TForall σ (term_close [x0] 0 t)) e
                        (zip xs' σs')) in *.
    assert (Hlc_inner : lc_at [] INNER)
      by (apply define_fun_forall_telescope_lc; exact Hlc).
    pose (Y := L ∪ fv INNER ∪ {[ x ]}).
    pose (y := stringmap.fresh_string_of_set "" Y).
    assert (Hy_fresh : y ∉ Y) by (apply stringmap.fresh_string_of_set_fresh).
    assert (Hy_L : y ∉ L).
    { intro Hy. apply Hy_fresh.
      subst Y. rewrite! elem_of_union.
      left. left. assumption. }
    assert (Hy_inner : y ∉ fv INNER).
    { intro Hy. apply Hy_fresh.
      subst Y. rewrite! elem_of_union.
      left. right. assumption. }
    assert (Hy_x : y <> x).
    { intro Hy. apply Hy_fresh.
      subst Y. rewrite! elem_of_union.
      right. rewrite elem_of_singleton. assumption. }
    specialize (HL y Hy_L d).
    rewrite (term_open_close_subst1_nil INNER x y Hlc_inner) in HL.
    exact (eval_term_subst_TFVar1_alpha_inv Σ A V x y σ0 d σ_bool INNER _
             Hy_x Hy_inner HL).
Qed.

(** The converse of [define_fun_strip_forall_telescope]: a body true at every
    instance of the binders gives a true telescope.  Each binder is met at
    itself and renamed to the cofinite variable [E_TForall_true] asks for. *)
Lemma define_fun_intro_forall_telescope :
  forall Σ (xs : list var) (σs : list sort)
      A (V : valuation A) e,
    NoDup xs ->
    length xs = length σs ->
    lc_at [] e ->
    (forall ws : hlist A.(domain) σs,
        ⟦ e : σ_bool ⟧(Σ, A, list_to_map (zip xs (hlist_to_list ws)) ∪ V)
          ⇓ cast_sym A.(domain_σ_bool) true) ->
    ⟦ foldr (fun '(x, σ) t => TForall σ (term_close [x] 0 t)) e (zip xs σs)
      : σ_bool ⟧(Σ, A, V) ⇓ cast_sym A.(domain_σ_bool) true.
Proof.
  intros Σ xs.
  revert Σ.
  induction xs as [|x xs' IH]; intros Σ σs A V e Hnodup Hlen Hlc Hev.
  - destruct σs; [|discriminate Hlen].
    pose proof (Hev HNil) as Hnil. cbn [zip zip_with] in Hnil.
    rewrite list_to_map_nil, (left_id_L ∅ (∪)) in Hnil. exact Hnil.
  - destruct σs as [|σ0 σs']; [discriminate Hlen|].
    apply NoDup_cons in Hnodup as [Hx_notin Hnodup'].
    cbn [zip zip_with foldr].
    set (INNER := foldr (fun '(x0, σ) t => TForall σ (term_close [x0] 0 t)) e
                        (zip xs' σs')).
    assert (Hlc_inner : lc_at [] INNER)
      by (apply define_fun_forall_telescope_lc; exact Hlc).
    apply (E_TForall_true Σ A (fv (term_close [x] 0 INNER) ∪ {[x]})).
    intros y Hy d. cbv zeta.
    (* the instance at [x] itself *)
    assert (Hx : ⟦ term_open 0 [TFVar x] (term_close [x] 0 INNER)
                   : σ_bool ⟧(Σ, A, <[x := existT _ d]> V)
                   ⇓ cast_sym A.(domain_σ_bool) true).
    { rewrite term_open_close_subst1_nil by exact Hlc_inner.
      rewrite term_subst_id_singleton.
      apply IH; [exact Hnodup' | simpl in Hlen; lia | exact Hlc |].
      intros ws. pose proof (Hev (HCons σ0 σs' d ws)) as Hws.
      assert (Hxnone : (list_to_map (zip xs' (hlist_to_list ws)) : valuation A) !! x = None)
        by (apply lookup_list_to_map_zip_None; exact Hx_notin).
      cbn [hlist_to_list zip zip_with] in Hws.
      rewrite list_to_map_cons, <- insert_union_l,
        (insert_union_r _ _ _ _ Hxnone) in Hws.
      exact Hws. }
    destruct (decide (y = x)) as [-> | Hyx]; [exact Hx |].
    apply (eval_term_open_alpha1 Σ A V σ_bool _ _ x y σ0 d);
      [ intros ->; contradiction
      | rewrite fv_term_close; set_solver
      | set_solver
      | exact Hx ].
Qed.

(** A definition holds when, at every argument, the defined symbol's
    application and the body take one value. *)
Lemma define_fun_eval_intro :
  forall Σ A (V : valuation A)
         g (xs : list var) (σs : list sort) (t_body : term) σ,
    Σ_core ⊑ Σ ->
    models_core A ->
    monomorphic σ ->
    length xs = length σs ->
    NoDup xs ->
    lc_at [] t_body ->
    (forall ws : hlist A.(domain) σs,
        exists v,
          ⟦ TApp g None (map TFVar xs)
            : σ ⟧(Σ, A, list_to_map (zip xs (hlist_to_list ws)) ∪ V) ⇓ v
          /\ ⟦ t_body : σ ⟧(Σ, A, list_to_map (zip xs (hlist_to_list ws)) ∪ V)
               ⇓ v) ->
    ⟦ define_fun g xs σs t_body : σ_bool ⟧(Σ, A, V)
      ⇓ cast_sym A.(domain_σ_bool) true.
Proof.
  intros Σ A V g xs σs t_body σ Hsub Hcore Hmono Hlen Hnodup Hlc_body Hbody.
  unfold define_fun.
  apply define_fun_intro_forall_telescope; [exact Hnodup | exact Hlen | |].
  - unfold eq_. apply LCA_TApp. intros t Ht.
    rewrite elem_of_cons in Ht.
    destruct Ht as [-> | Ht].
    + apply LCA_TApp. intros u Hu.
      apply list_elem_of_fmap in Hu as (z & -> & _).
      apply LCA_TFVar.
    + rewrite list_elem_of_singleton in Ht. subst t. exact Hlc_body.
  - intros ws. destruct (Hbody ws) as (v & Happ & Hb).
    eapply eval_eq_true; [exact Hsub | exact Hcore | exact Hmono
                          | exact Happ | exact Hb | reflexivity].
Qed.

Lemma define_fun_eval_instantiate :
  forall Σ A (V : valuation A)
         g (xs : list var) (σs : list sort) (t_body : term)
         σ (v_b : A.(domain) σ) ts (ws : hlist A.(domain) σs),
    Σ_core ⊑ Σ ->
    models_core A ->
    valuation_well_sorted Σ.(sorts) V ->
    length xs = length σs ->
    NoDup xs ->
    lc_at [] t_body ->
    list_to_map (zip xs σs) ⊍ Σ ⊢ t_body : σ ->
    ⟦ define_fun g xs σs t_body : σ_bool ⟧(Σ, A, V)
      ⇓ cast_sym A.(domain_σ_bool) true ->
    ⟦ ts : σs ⟧*(Σ, A, V) ⇓ ws ->
    ⟦ t_body : σ ⟧(Σ, A, list_to_map (zip xs (hlist_to_list ws)) ∪ V) ⇓ v_b ->
    ⟦ TApp g None ts : σ ⟧(Σ, A, V) ⇓ v_b.
Proof.
  intros Σ A V g xs σs t_body σ v_b ts ws Hsub Hcore HV
    Hlen Hnodup Hlc_body Hbody_sort Hdef Harg Hbody.
  pose proof (valuation_well_sorted_union_lookup_list_to_map _ _ _ xs _ ws HV)
    as HV'.
  assert (Hlc_e : lc_at [] (eq_ (TApp g None (map TFVar xs)) t_body)).
  { unfold eq_. apply LCA_TApp. intros t Ht.
    rewrite elem_of_cons in Ht.
    destruct Ht as [-> | Ht].
    - apply LCA_TApp. intros u Hu.
      apply list_elem_of_fmap in Hu as (z & -> & _).
      apply LCA_TFVar.
    - rewrite list_elem_of_singleton in Ht. subst t. exact Hlc_body. }
  pose proof (define_fun_strip_forall_telescope Σ xs σs A V ws
                (eq_ (TApp g None (map TFVar xs)) t_body)
                Hnodup Hlen Hlc_e Hdef) as Heq.
  apply (eval_eq_true_inv Σ A) in Heq; [| exact Hsub | exact Hcore ].
  destruct Heq as (δ & va & vb & Hva & Hvb_body & Hvaeq).
  (* the body is sorted under the signature extended by the parameters *)
  pose proof (signatures_agree_except_sorts_sym _ _
    (signatures_agree_except_sorts_add_sorts Σ (list_to_map (zip xs σs))))
    as Hsym.
  pose proof (proj1 (eval_cong_signature _ _ _ _ _ _ _ Hsym) Hvb_body)
    as Hvb_ext.
  pose proof (proj1 (eval_cong_signature _ _ _ _ _ _ _ Hsym) Hbody)
    as Hbody_ext.
  assert (Hδσ : δ = σ)
    by (eapply eval_sort_of_well_sorted;
        [exact Hbody_sort | exact HV' | exact Hvb_ext]).
  subst δ.
  assert (Hvbeq : vb = v_b)
    by (eapply eval_deterministic;
        [exact Hbody_sort | exact HV' | exact Hvb_ext | exact Hbody_ext]).
  subst vb. subst va.
  apply eval_TApp_inv in Hva.
  destruct Hva as (σs0 & vs0 & Hargs0 & _ & Hrank0 & Heq5).
  pose proof (evals_map_TFVar Σ A xs σs V ws
                Hnodup Hlen) as Hargl.
  destruct (evals_map_TFVar_deterministic Σ A _ xs σs σs0 ws vs0 Hargl Hargs0)
    as [<- Hvs].
  apply eq_of_heq in Hvs. subst vs0.
  eapply E_TApp.
  - exact Harg.
  - constructor.
  - exact Hrank0.
  - exact Heq5.
Qed.

(** The converse, which is what a proof reading a guard back needs: the
    application's value is the body's, so a true application means a true body
    under the extended valuation.  It is [define_fun_eval_instantiate] run
    against a value [eval_total] supplies, with [eval_deterministic] tying the
    two together.

    Note the body is left *opened*, at the extended valuation: a client
    reasoning about which case of the body holds wants the argument as a
    variable standing for the value, not substituted back into the term. *)
Lemma define_fun_eval_instantiate_inv :
  forall Σ A (V : valuation A)
         g (xs : list var) (σs : list sort) (t_body : term)
         σ (v : A.(domain) σ) ts (ws : hlist A.(domain) σs),
    adt_constructed Σ A ->
    Σ_core ⊑ Σ ->
    models_core A ->
    valuation_well_sorted Σ.(sorts) V ->
    length xs = length σs ->
    NoDup xs ->
    lc_at [] t_body ->
    list_to_map (zip xs σs) ⊍ Σ ⊢ t_body : σ ->
    Σ ⊢ TApp g None ts : σ ->
    ⟦ define_fun g xs σs t_body : σ_bool ⟧(Σ, A, V)
      ⇓ cast_sym A.(domain_σ_bool) true ->
    ⟦ ts : σs ⟧*(Σ, A, V) ⇓ ws ->
    ⟦ TApp g None ts : σ ⟧(Σ, A, V) ⇓ v ->
    ⟦ t_body : σ ⟧(Σ, A, list_to_map (zip xs (hlist_to_list ws)) ∪ V) ⇓ v.
Proof.
  intros Σ A V g xs σs t_body σ v ts ws Hadt Hsub Hcore HV
    Hlen Hnodup Hlc_body Hbody_sort Happ_sort Hdef Hargs Happ.
  (* the body is sorted under the signature extended by the parameters *)
  pose proof (signatures_agree_except_sorts_add_sorts Σ
                (list_to_map (zip xs σs))) as Hsym.
  destruct (eval_total _ A (list_to_map (zip xs (hlist_to_list ws)) ∪ V) t_body σ
              (adt_constructed_signatures_agree_except_sorts _ _ _
                (signatures_agree_except_sorts_sym _ _ Hsym) Hadt)
              Hbody_sort
              (valuation_well_sorted_union_lookup_list_to_map _ _ _ xs _ ws HV))
    as [v_b Hbody].
  apply (eval_cong_signature _ _ _ _ _ _ _ Hsym) in Hbody.
  pose proof (define_fun_eval_instantiate Σ A V g xs σs t_body σ v_b ts ws
                Hsub Hcore HV Hlen Hnodup Hlc_body Hbody_sort Hdef Hargs Hbody)
    as Happ'.
  assert (v_b = v)
    by (eapply eval_deterministic; [exact Happ_sort | exact HV | exact Happ' | exact Happ]).
  subst v_b. exact Hbody.
Qed.

(** A definition read back at an argument: where the parameters are bound to
    [ws], the body takes the value the defined symbol's interpretation gives
    [ws]. *)
Lemma define_fun_eval_inserts :
  forall Σ A (V : valuation A)
         g (xs : list var) (σs : list sort) (t_body : term) σ (ws : hlist A.(domain) σs),
    Σ_core ⊑ Σ ->
    models_core A ->
    valuation_well_sorted Σ.(sorts) V ->
    length xs = length σs ->
    NoDup xs ->
    lc_at [] t_body ->
    list_to_map (zip xs σs) ⊍ Σ ⊢ t_body : σ ->
    ⟦ define_fun g xs σs t_body : σ_bool ⟧(Σ, A, V)
      ⇓ cast_sym A.(domain_σ_bool) true ->
    ⟦ t_body : σ ⟧(Σ, A, list_to_map (zip xs (hlist_to_list ws)) ∪ V)
      ⇓ interp_apply A.(domain) (A.(interp) g σs σ) ws.
Proof.
  intros Σ A V g xs σs t_body σ ws Hsub Hcore HV Hlen Hnodup Hlc_body Hbody_sort Hdef.
  pose proof (valuation_well_sorted_union_lookup_list_to_map _ _ _ xs _ ws HV)
    as HV'.
  assert (Hlc_e : lc_at [] (eq_ (TApp g None (map TFVar xs)) t_body)).
  { unfold eq_. apply LCA_TApp. intros t Ht.
    rewrite elem_of_cons in Ht.
    destruct Ht as [-> | Ht].
    - apply LCA_TApp. intros u Hu.
      apply list_elem_of_fmap in Hu as (z & -> & _).
      apply LCA_TFVar.
    - rewrite list_elem_of_singleton in Ht. subst t. exact Hlc_body. }
  pose proof (define_fun_strip_forall_telescope Σ xs σs A V ws
                (eq_ (TApp g None (map TFVar xs)) t_body)
                Hnodup Hlen Hlc_e Hdef) as Heq.
  apply (eval_eq_true_inv Σ A) in Heq; [| exact Hsub | exact Hcore].
  destruct Heq as (δ & va & vb & Hva & Hvb & <-).
  (* the body is sorted under the signature extended by the parameters *)
  pose proof (signatures_agree_except_sorts_sym _ _
    (signatures_agree_except_sorts_add_sorts Σ (list_to_map (zip xs σs))))
    as Hsym.
  assert (δ = σ) as ->
    by (eapply eval_sort_of_well_sorted;
        [ exact Hbody_sort | exact HV'
        | exact (proj1 (eval_cong_signature _ _ _ _ _ _ _ Hsym) Hvb) ]).
  (* the head application's arguments are the binders, whose values are [ws] *)
  apply eval_TApp_inv in Hva as (σs0 & vs0 & Hargs0 & _ & _ & <-).
  destruct (evals_map_TFVar_deterministic Σ A _ xs σs σs0 ws vs0
              (evals_map_TFVar Σ A xs σs V ws Hnodup Hlen) Hargs0)
    as [<- Hvs].
  apply eq_of_heq in Hvs. subst vs0. exact Hvb.
Qed.
