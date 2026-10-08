From SMTLIB Require Import Utils Symbols Term Sorting Signature Theory Eval.

Open Scope smt_scope.

(* https://smt-lib.org/theories-HO-Core.shtml *)

(* NOTE: The official name is HO-Core, but we can't have "-" in identifiers so we say HO_Core. *)

(* NOTE: The HO-Core theory as given on the SMT-LIB website (see the URL above) declares
         the map sort constructor -> via a :sorts attribute, as if it were defined by the theory.
         In the SMT-LIB standard itself, however, -> is a built-in sort available in
         every logic, not a sort introduced by a theory. Consequently -> is not defined
         in this theory file. *)

Definition f_app : func := "@".
Definition ho_core_funcs : gset func :=
  {[ f_app ]}.

Definition app_ t1 t2 := TApp f_app None [t1; t2].

Inductive rank_ho_core : func -> list sort -> sort -> Prop :=
| rank_f_app : rank_ho_core f_app [ τ_map τ_A τ_B; τ_A ] τ_B.

Program Definition Σ_ho_core : signature :=
  {|
    sort_symbols := {[ s_bool; s_map ]};

    funcs f := f ∈ ho_core_funcs;
    funcs_dec f := decide (f ∈ ho_core_funcs);

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

    rank := rank_ho_core;
  |}.
Next Obligation. Proof. set_solver. Qed.
Next Obligation. Proof. set_solver. Qed.
Next Obligation. Proof. set_solver. Qed.
Next Obligation. Proof. set_solver. Qed.
Next Obligation. Proof. set_solver. Qed.
Next Obligation. Proof. set_solver. Qed.
Next Obligation. Proof. set_solver. Qed.
Next Obligation. Proof. reflexivity. Qed.
Next Obligation. Proof. reflexivity. Qed.
Next Obligation. Proof. set_solver. Qed.
Next Obligation. Proof. set_solver. Qed.
Next Obligation. Proof. set_solver. Qed.
Next Obligation. Proof. set_solver. Qed.
Next Obligation. Proof. set_solver. Qed.
Next Obligation.
Proof.
  intros f τs τ Hf.
  inversion Hf.
  split; repeat constructor.
Qed.
Next Obligation. Proof. sauto lq:on rew:off. Qed.
Next Obligation.
Proof.
  intros f Hf. unfold funcs in Hf.
  assert (Hf': f = f_app) by set_solver.
  subst f. eexists. econstructor. constructor.
Qed.
Next Obligation. Proof. set_solver. Qed.
Next Obligation. Proof. set_solver. Qed.
Next Obligation. Proof. set_solver. Qed.
Next Obligation. Proof. set_solver. Qed.

Section HO_CoreModels.

  Variable A : structure.

  Definition cast_to_map σ1 σ2 := cast (A.(domain_σ_map) σ1 σ2).

  Definition models_f_app : Prop :=
    forall σ1 σ2 f x,
      let F := A.(interp) f_app [ τ_map σ1 σ2; σ1 ] σ2 in
      F f x = (cast_to_map σ1 σ2 f) x.

  Record models_ho_core : Prop := {
    mhc_app : models_f_app;
  }.

End HO_CoreModels.

Arguments mhc_app {_} {_}.

Definition T_ho_core : pretheory :=
  {|
    pΣ := Σ_ho_core;
    pmodels A := models_ho_core A
  |}.

(** The one condition names [f_app], which [Σ_ho_core] declares. *)
Theorem T_ho_core_local : pretheory_local T_ho_core.
Proof.
  intros D Hbool Hmap i j Hagree [A1].
  assert (Hrw : forall f, Σ_ho_core.(funcs) f ->
                  forall σs σ, j f σs σ = i f σs σ)
    by (intros f Hf σs σ; symmetry; exact (Hagree f Hf σs σ)).
  constructor.
  unfold models_f_app in A1 |- *; cbv zeta in A1 |- *;
    cbn [interp structure_of] in A1 |- *.
  intros. rewrite Hrw by set_solver. apply A1.
Qed.

(** [f_app] is interpreted by reading the domain's map-sort equation left to
    right. *)
Section HO_CoreInterpretable.

  Context (D : sort -> Type).
  Context (witness : forall σ, D σ).
  Context (Hbool : D σ_bool = bool).
  Context (Hmap : forall σ1 σ2, D (τ_map σ1 σ2) = (D σ1 -> D σ2)).

  Local Definition ho_app : forall σs σ, interpretation D σs σ :=
    fun σs σ =>
      match σs as l return interpretation D l σ with
      | [σ1; σ2] =>
          fun (fn : D σ1) (x : D σ2) =>
            match decide (σ1 = τ_map σ2 σ) with
            | left H => cast (Hmap σ2 σ) (eq_rect σ1 D fn (τ_map σ2 σ) H) x
            | right _ => witness σ
            end
      | l => interp_const D witness l σ
      end.

  Definition ho_core_interp : forall f σs σ, interpretation D σs σ :=
    interp_insert_func D f_app ho_app (fun _ => interp_const D witness).

  Theorem ho_core_interp_models :
    models_ho_core (structure_of D Hbool Hmap ho_core_interp).
  Proof.
    constructor.
    unfold models_f_app; cbv zeta; cbn [interp structure_of].
    intros σ1 σ2 f x.
    unfold ho_core_interp. rewrite interp_insert_func_eq. unfold ho_app.
    destruct (decide (τ_map σ1 σ2 = τ_map σ1 σ2)) as [H | Hne];
      [| by contradiction].
    rewrite (Eqdep_dec.UIP_dec (fun x y => decide (x = y)) H eq_refl).
    cbn [eq_rect].
    unfold cast_to_map. cbn [domain_σ_map structure_of]. reflexivity.
  Qed.

  Corollary T_ho_core_interpretable : pretheory_interpretable T_ho_core D Hbool Hmap.
  Proof. exists ho_core_interp. apply ho_core_interp_models. Qed.

End HO_CoreInterpretable.

Theorem app_has_sort : forall Σ t1 t2 σ1 σ2,
    Σ_ho_core ⊑ Σ ->
    monomorphic σ1 ->
    monomorphic σ2 ->
    (Σ ⊢ t1 : τ_map σ1 σ2) ->
    (Σ ⊢ t2 : σ1) ->
    Σ ⊢ app_ t1 t2 : σ2.
Proof.
  intros * Hsub Hmono1 Hmono2 Ht1 Ht2.
  econstructor.
  - exists {[ u_A := σ1; u_B := σ2 ]}, [τ_map τ_A τ_B; τ_A], τ_B. 
    sauto lq: on.
  - intros * Hrank.
    eapply monomorphic_rank_conservative in Hrank; eauto.
    ecrush. set_solver.
  - reflexivity.
  - intros * Ht_i Hσ_i.
    destruct i; simpl in *.
    + simplify_eq. assumption.
    + rewrite list_lookup_singleton in Ht_i.
      destruct i; try congruence. simpl in *.
      simplify_eq. assumption.
Qed.

(** Applying a map is reading the domain's map-sort equation left to
    right, which is what [models_f_app] says of the interpretation. *)
Lemma eval_app :
  forall Σ A θ σ1 σ2 t1 t2
         (fv : A.(domain) (τ_map σ1 σ2)) (x : A.(domain) σ1),
    Σ_ho_core ⊑ Σ ->
    models_ho_core A ->
    monomorphic σ1 ->
    monomorphic σ2 ->
    ⟦ t1 : τ_map σ1 σ2 ⟧(Σ, A, θ) ⇓ fv ->
    ⟦ t2 : σ1 ⟧(Σ, A, θ) ⇓ x ->
    ⟦ app_ t1 t2 : σ2 ⟧(Σ, A, θ) ⇓ cast (A.(domain_σ_map) σ1 σ2) fv x.
Proof.
  intros Σ A θ σ1 σ2 t1 t2 fv x Hsub Hho Hm1 Hm2 Ht1 Ht2.
  set (vapp := interp_apply A.(domain)
    (A.(interp) f_app [τ_map σ1 σ2; σ1] σ2)
    (HCons (τ_map σ1 σ2) [σ1] fv (HCons σ1 [] x HNil))).
  assert (Heval : ⟦ app_ t1 t2 : σ2 ⟧(Σ, A, θ) ⇓ vapp).
  { unfold app_, vapp.
    eapply E_TApp with (σs := [τ_map σ1 σ2; σ1])
      (vs := HCons (τ_map σ1 σ2) [σ1] fv (HCons σ1 [] x HNil)).
    - repeat constructor; [exact Ht1 | exact Ht2].
    - constructor.
    - exists {[ u_A := σ1; u_B := σ2 ]}, [τ_map τ_A τ_B; τ_A], τ_B.
      split_and!.
      + apply (rank_extends Hsub). constructor.
      + unfold monomorphic_instance_of; split; [| exact Hm2]. sauto lq: on.
      + constructor.
        * unfold monomorphic_instance_of; split.
          -- sauto lq: on.
          -- constructor. repeat constructor; assumption.
        * constructor; [| constructor].
          unfold monomorphic_instance_of; split; [| exact Hm1]. sauto lq: on.
    - reflexivity. }
  replace (cast (A.(domain_σ_map) σ1 σ2) fv x) with vapp; [exact Heval |].
  unfold vapp. autorewrite with interp_apply.
  pose proof (Hho.(mhc_app) σ1 σ2 fv x) as Happ.
  cbv zeta in Happ. unfold cast_to_map in Happ. exact Happ.
Qed.
