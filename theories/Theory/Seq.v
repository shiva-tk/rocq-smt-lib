From Stdlib Require Import ClassicalEpsilon.
From SMTLIB Require Import Utils Symbols Term Signature Theory Sorting Eval.
From SMTLIB.Theory Require Import Reals_Ints.

Open Scope smt_scope.

(* Seq is not a standard theory specified by SMT-LIB.

   The theory presented here includes elements of the documentation of
   z3 and cvc5 (see https://microsoft.github.io/z3guide/docs/theories/Sequences/
   and https://cvc5.github.io/docs-ci/docs-main/theories/sequences.html) *)

Definition s_seq : sortsymb := "Seq".
Definition τ_seq (τ : sort) : sort := SApp s_seq [τ].

(** Whether a sort is a sequence sort.  [generator_sort] and
    [seq_embeddable_sort] below record this decision rather than a negation,
    which is what makes them irrelevant: the generator case of a sequence
    ground term is indexed by such a proof. *)
Definition is_seqb (σ : sort) : bool :=
  match σ with
  | SApp s [_] => bool_decide (s = s_seq)
  | _ => false
  end.

Lemma is_seqb_false : forall σ, is_seqb σ = false <-> forall σ', σ ≠ τ_seq σ'.
Proof.
  intros σ. split.
  - intros Hb σ' ->. cbn in Hb. by rewrite bool_decide_eq_true_2 in Hb.
  - intros Hns. destruct σ as [u | s τs]; [reflexivity|].
    destruct τs as [| σ1 [| σ2 τs']]; [reflexivity| | reflexivity].
    cbn. apply bool_decide_eq_false_2. intros ->. by apply (Hns σ1).
Qed.

Definition f_seq_empty : func := "seq.empty".
Definition f_seq_unit : func := "seq.unit".
Definition f_seq_concat : func := "seq.++".
Definition f_seq_len : func := "seq.len".
Definition f_seq_nth : func := "seq.nth".
Definition f_seq_contains : func := "seq.contains".
Definition f_seq_map : func := "seq.map".

Definition seq_funcs : gset func :=
      {[ f_seq_empty; f_seq_unit; f_seq_concat;
         f_seq_len; f_seq_nth; f_seq_contains; f_seq_map ]}.

Definition seq_empty σ := TApp f_seq_empty (Some (τ_seq σ)) [].
Definition seq_unit t := TApp f_seq_unit None [t].
Definition seq_concat t1 t2 := TApp f_seq_concat None [t1; t2].
Definition seq_len t := TApp f_seq_len None [t].
Definition seq_nth t1 t2 := TApp f_seq_nth None [t1; t2].
Definition seq_contains t1 t2 := TApp f_seq_contains None [t1; t2].
Definition seq_map t1 t2 := TApp f_seq_map None [t1; t2].

Inductive rank_seq : func -> list sort -> sort -> Prop :=
| rank_f_seq_empty : rank_seq f_seq_empty [] (τ_seq τ_A)
| rank_f_seq_unit : rank_seq f_seq_unit [τ_A] (τ_seq τ_A)
| rank_f_seq_concat : rank_seq f_seq_concat [τ_seq τ_A; τ_seq τ_A] (τ_seq τ_A)
| rank_f_seq_len : rank_seq f_seq_len [τ_seq τ_A] σ_int
| rank_f_seq_nth : rank_seq f_seq_nth [τ_seq τ_A; σ_int] τ_A
| rank_f_seq_contains : rank_seq f_seq_contains [τ_seq τ_A; τ_seq τ_A] σ_bool
| rank_f_seq_map : rank_seq f_seq_map [τ_map τ_A τ_B; τ_seq τ_A]  (τ_seq τ_B).

Program Definition Σ_seq : signature :=
  {|
    sort_symbols := {[ s_bool; s_map; s_int; s_seq ]};

    funcs f := f ∈ seq_funcs;
    funcs_dec f := decide (f ∈ seq_funcs);

    constructors := ∅;
    selectors := ∅;
    testers := ∅;

    constructors_for_sort (s : sortsymb) := ∅;

    arity (s : sortsymb) :=
      if identifier_eqb s_seq s
      then 1
      else if identifier_eqb s_map s
      then 2
      else 0;

    selectors_for_constructor (c : func) := [];
    tester_for_constructor (c : func) := c;
    constructor_for_tester (p : func) := p;

    sorts := ∅;

    rank := rank_seq;
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
Next Obligation. sauto. Qed.
Next Obligation.
Proof.
  intros f Hf.
  assert (Hf': f = f_seq_empty \/ f = f_seq_unit \/ f = f_seq_concat \/ f = f_seq_len \/ f = f_seq_nth \/ f = f_seq_contains \/ f = f_seq_map) by set_solver.
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

Section SeqModels.

  Variable A : structure.
  Variable domain_σ_int : A.(domain) σ_int = Z.
  Variable domain_σ_seq : forall σ, A.(domain) (τ_seq σ) = list (A.(domain) σ).

  Definition cast_to_list σ := cast (domain_σ_seq σ).
  Definition cast_to_Z := cast domain_σ_int.
  Definition cast_to_map σ1 σ2 := cast (A.(domain_σ_map) σ1 σ2).
  Definition cast_to_bool := cast A.(domain_σ_bool).

  Definition models_f_seq_empty : Prop :=
    forall σ,
      let F := A.(interp) f_seq_empty [] (τ_seq σ) in
      cast_to_list σ F = [].

  Definition models_f_seq_unit : Prop :=
    forall σ v,
      let F := A.(interp) f_seq_unit [ σ ] (τ_seq σ) in
      cast_to_list σ (F v) = [ v ].

  Definition models_f_seq_concat : Prop :=
    forall σ l1 l2,
      let F := A.(interp) f_seq_concat [ τ_seq σ; τ_seq σ ] (τ_seq σ) in
      cast_to_list σ (F l1 l2)
      = (cast_to_list σ l1) ++ (cast_to_list σ l2).

  Definition models_f_seq_len : Prop :=
    forall σ l,
      let F := A.(interp) f_seq_len [ τ_seq σ ] σ_int in
      cast_to_Z (F l) = Z.of_nat $ length (cast_to_list σ l).

  Definition models_f_seq_nth : Prop :=
    forall σ l n i v,
      let F := A.(interp) f_seq_nth [ τ_seq σ; σ_int ] σ in
      (cast_to_list σ l) !! n = Some v ->
      cast_to_Z i = Z.of_nat n ->
      F l i = v.

  Definition models_f_seq_contains : Prop :=
    forall σ l1 l2,
      let F := A.(interp) f_seq_contains [ τ_seq σ; τ_seq σ ] σ_bool in
      (cast_to_list σ l2) `infix_of` (cast_to_list σ l1) <->
      cast_to_bool (F l1 l2) = true.

  Definition models_f_seq_map : Prop :=
    forall σ1 σ2 l f,
      let F := A.(interp) f_seq_map [ τ_map σ1 σ2; τ_seq σ1 ] (τ_seq σ2) in
      map (cast_to_map σ1 σ2 f) (cast_to_list σ1 l)
      = cast_to_list σ2 (F f l).

  Record models_seq : Prop := {
    ms_empty : models_f_seq_empty;
    ms_unit : models_f_seq_unit;
    ms_concat : models_f_seq_concat;
    ms_len : models_f_seq_len;
    ms_nth : models_f_seq_nth;
    ms_contains: models_f_seq_contains;
    ms_map: models_f_seq_map;
  }.

End SeqModels.

Arguments ms_empty {_} {_} {_}.
Arguments ms_unit {_} {_} {_}.
Arguments ms_concat {_} {_} {_}.
Arguments ms_len {_} {_} {_}.
Arguments ms_nth {_} {_} {_}.
Arguments ms_contains {_} {_} {_}.
Arguments ms_map {_} {_} {_}.

(** A [pretheory]: the datatype condition belongs to the finished signature,
    not to a component.  A stack that ends in a sequence-nesting datatype
    closes with [theory_init_seq] at the foot of this file rather than with
    [theory_init]. *)
Definition T_seq : pretheory :=
  {|
    pΣ := Σ_seq;
    pmodels A :=
      {HZ : A.(domain) σ_int = Z &
              {Hlist : forall σ, A.(domain) (τ_seq σ) = list (A.(domain) σ) &
                      models_seq A HZ Hlist}};
  |}.

(** Every condition names one symbol, and all of them are in
    [seq_funcs]. *)
Theorem T_seq_local : pretheory_local T_seq.
Proof.
  intros D Hbool Hmap i j Hagree [HZ [Hlist Hm]].
  exists HZ, Hlist.
  assert (Hrw : forall f, Σ_seq.(funcs) f -> forall σs σ, j f σs σ = i f σs σ)
    by (intros f Hf σs σ; symmetry; exact (Hagree f Hf σs σ)).
  destruct Hm as [A1 A2 A3 A4 A5 A6 A7].
  constructor.
  - unfold models_f_seq_empty in A1 |- *; cbv zeta in A1 |- *;
    cbn [interp structure_of] in A1 |- *;
    intros; rewrite Hrw by set_solver; eapply A1; eauto.
  - unfold models_f_seq_unit in A2 |- *; cbv zeta in A2 |- *;
    cbn [interp structure_of] in A2 |- *;
    intros; rewrite Hrw by set_solver; eapply A2; eauto.
  - unfold models_f_seq_concat in A3 |- *; cbv zeta in A3 |- *;
    cbn [interp structure_of] in A3 |- *;
    intros; rewrite Hrw by set_solver; eapply A3; eauto.
  - unfold models_f_seq_len in A4 |- *; cbv zeta in A4 |- *;
    cbn [interp structure_of] in A4 |- *;
    intros; rewrite Hrw by set_solver; eapply A4; eauto.
  - unfold models_f_seq_nth in A5 |- *; cbv zeta in A5 |- *;
    cbn [interp structure_of] in A5 |- *;
    intros; rewrite Hrw by set_solver; eapply A5; eauto.
  - unfold models_f_seq_contains in A6 |- *; cbv zeta in A6 |- *;
    cbn [interp structure_of] in A6 |- *;
    intros; rewrite Hrw by set_solver; eapply A6; eauto.
  - unfold models_f_seq_map in A7 |- *; cbv zeta in A7 |- *;
    cbn [interp structure_of] in A7 |- *;
    intros; rewrite Hrw by set_solver; eapply A7; eauto.
Qed.

(** The operations are the ordinary list operations on the canonical domain.
    [f_seq_contains] asks whether one list occurs in another as a contiguous
    run, which is decided classically. *)
Section SeqInterpretable.

  Context (D : sort -> Type).
  Context (witness : forall σ, D σ).
  Context (Hbool : D σ_bool = bool).
  Context (Hmap : forall σ1 σ2, D (τ_map σ1 σ2) = (D σ1 -> D σ2)).
  Context (HZ : D σ_int = Z).
  Context (Hlist : forall σ, D (τ_seq σ) = list (D σ)).

  Local Notation base := (interp_const D witness).

  (* Run [k] at the element sort of a sequence sort; any other sort falls
     through to [base].  Every condition below is stated at a sequence sort,
     so each interpretation has to make this test. *)
  Local Definition seq_at {P : sort -> Type} (σ : sort)
    (k : forall σ', P (τ_seq σ')) (base : forall σ, P σ) : P σ :=
    match σ as s return P s with
    | SApp sy [σ'] =>
        match decide (sy = s_seq) with
        | left H => eq_rect_r (fun x => P (SApp x [σ'])) (k σ') H
        | right _ => base (SApp sy [σ'])
        end
    | s => base s
    end.

  Local Lemma seq_at_τ_seq : forall P σ' k base,
      @seq_at P (τ_seq σ') k base = k σ'.
  Proof.
    intros P σ' k base. unfold seq_at, τ_seq.
    destruct (decide (s_seq = s_seq)) as [H | H]; [| by contradiction].
    by rewrite (Eqdep_dec.UIP_dec (fun x y => decide (x = y)) H eq_refl).
  Qed.

  Local Definition seq_empty_interp : forall σs σ, interpretation D σs σ :=
    fun σs σ =>
      match σs as l return interpretation D l σ with
      | [] => seq_at (P := D) σ (fun σ' => cast_sym (Hlist σ') []) witness
      | l => base l σ
      end.

  Local Definition seq_unit_interp : forall σs σ, interpretation D σs σ :=
    fun σs σ =>
      match σs as l return interpretation D l σ with
      | [σ1] =>
          fun v : D σ1 =>
            match decide (σ = τ_seq σ1) with
            | left H => eq_rect_r D (cast_sym (Hlist σ1) [v]) H
            | right _ => witness σ
            end
      | l => base l σ
      end.

  Local Definition seq_concat_interp : forall σs σ, interpretation D σs σ :=
    fun σs σ =>
      match σs as l return interpretation D l σ with
      | [σ1; σ2] =>
          fun (v1 : D σ1) (v2 : D σ2) =>
            seq_at (P := D) σ
              (fun σ' =>
                 match decide (σ1 = τ_seq σ'), decide (σ2 = τ_seq σ') with
                 | left H1, left H2 =>
                     cast_sym (Hlist σ')
                       (cast (Hlist σ') (eq_rect σ1 D v1 (τ_seq σ') H1)
                        ++ cast (Hlist σ') (eq_rect σ2 D v2 (τ_seq σ') H2))
                 | _, _ => witness (τ_seq σ')
                 end)
              witness
      | l => base l σ
      end.

  Local Definition seq_len_interp : forall σs σ, interpretation D σs σ :=
    fun σs σ =>
      match σs as l return interpretation D l σ with
      | [σ1] =>
          seq_at (P := fun s => D s -> D σ) σ1
            (fun σ' (l : D (τ_seq σ')) =>
               match decide (σ = σ_int) with
               | left H =>
                   eq_rect_r D
                     (cast_sym HZ (Z.of_nat (length (cast (Hlist σ') l)))) H
               | right _ => witness σ
               end)
            (fun _ _ => witness σ)
      | l => base l σ
      end.

  Local Definition seq_nth_interp : forall σs σ, interpretation D σs σ :=
    fun σs σ =>
      match σs as l return interpretation D l σ with
      | [σ1; σ2] =>
          fun (l : D σ1) (i : D σ2) =>
            match decide (σ1 = τ_seq σ), decide (σ2 = σ_int) with
            | left H1, left H2 =>
                default (witness σ)
                  (cast (Hlist σ) (eq_rect σ1 D l (τ_seq σ) H1)
                   !! Z.to_nat (cast HZ (eq_rect σ2 D i σ_int H2)))
            | _, _ => witness σ
            end
      | l => base l σ
      end.

  Local Definition seq_contains_interp : forall σs σ, interpretation D σs σ :=
    fun σs σ =>
      match σs as l return interpretation D l σ with
      | [σ1; σ2] =>
          fun (l1 : D σ1) (l2 : D σ2) =>
            seq_at (P := fun s => D s -> D σ) σ1
              (fun σ' (l1' : D (τ_seq σ')) =>
                 match decide (σ = σ_bool), decide (σ2 = τ_seq σ') with
                 | left H1, left H2 =>
                     eq_rect_r D
                       (cast_sym Hbool
                          (if excluded_middle_informative
                                (cast (Hlist σ') (eq_rect σ2 D l2 (τ_seq σ') H2)
                                 `infix_of` cast (Hlist σ') l1')
                           then true else false)) H1
                 | _, _ => witness σ
                 end)
              (fun _ _ => witness σ)
              l1
      | l => base l σ
      end.

  Local Definition seq_map_interp : forall σs σ, interpretation D σs σ :=
    fun σs σ =>
      match σs as l return interpretation D l σ with
      | [σ1; σ2] =>
          fun (fn : D σ1) (l : D σ2) =>
            seq_at (P := D) σ
              (fun σ_out =>
                 seq_at (P := fun s => D s -> D (τ_seq σ_out)) σ2
                   (fun σ_in (l' : D (τ_seq σ_in)) =>
                      match decide (σ1 = τ_map σ_in σ_out) with
                      | left H =>
                          cast_sym (Hlist σ_out)
                            (map (cast (Hmap σ_in σ_out)
                                    (eq_rect σ1 D fn (τ_map σ_in σ_out) H))
                               (cast (Hlist σ_in) l'))
                      | right _ => witness (τ_seq σ_out)
                      end)
                   (fun _ _ => witness (τ_seq σ_out))
                   l)
              witness
      | l => base l σ
      end.

  Definition seq_interp : forall f σs σ, interpretation D σs σ :=
    interp_insert_func D f_seq_empty seq_empty_interp
   (interp_insert_func D f_seq_unit seq_unit_interp
   (interp_insert_func D f_seq_concat seq_concat_interp
   (interp_insert_func D f_seq_len seq_len_interp
   (interp_insert_func D f_seq_nth seq_nth_interp
   (interp_insert_func D f_seq_contains seq_contains_interp
   (interp_insert_func D f_seq_map seq_map_interp
   (fun _ => base))))))).

  (* Read one symbol out of the stack: miss until the name matches. *)
  Local Ltac seq_sym :=
    unfold seq_interp;
    repeat (rewrite interp_insert_func_ne; [| discriminate]);
    rewrite interp_insert_func_eq.

  (* The sort comparisons all succeed at the rank a condition is stated at;
     they are dependent matches, so the branch is taken by [destruct] and the
     equation is [eq_refl] up to proof irrelevance. *)
  Local Ltac dec_refl :=
    match goal with
    | |- context[decide ?P] =>
        let H := fresh "Hdec" in
        destruct (decide P) as [H | H]; [| by contradiction];
        rewrite (Eqdep_dec.UIP_dec (fun x y => decide (x = y)) H eq_refl)
    end.

  Theorem T_seq_interpretable :
    pretheory_interpretable T_seq D Hbool Hmap.
  Proof.
    exists seq_interp. exists HZ, Hlist.
    constructor;
      unfold models_f_seq_empty, models_f_seq_unit, models_f_seq_concat,
        models_f_seq_len, models_f_seq_nth, models_f_seq_contains,
        models_f_seq_map, cast_to_list, cast_to_Z, cast_to_bool, cast_to_map;
      cbv zeta; cbn [interp domain structure_of domain_σ_map].
    - intros σ. seq_sym. cbn [seq_empty_interp].
      rewrite seq_at_τ_seq. apply cast_cast_sym.
    - intros σ v. seq_sym. cbn [seq_unit_interp].
      repeat dec_refl. cbn [eq_rect_r eq_rect eq_sym]. apply cast_cast_sym.
    - intros σ l1 l2. seq_sym. cbn [seq_concat_interp].
      rewrite seq_at_τ_seq. repeat dec_refl. cbn [eq_rect].
      apply cast_cast_sym.
    - intros σ l. seq_sym. cbn [seq_len_interp].
      rewrite seq_at_τ_seq. repeat dec_refl.
      cbn [eq_rect_r eq_rect eq_sym]. apply cast_cast_sym.
    - intros σ l n i v Hnth Hi. seq_sym. cbn [seq_nth_interp].
      repeat dec_refl. cbn [eq_rect].
      rewrite Hi, Nat2Z.id, Hnth. reflexivity.
    - intros σ l1 l2. seq_sym. cbn [seq_contains_interp].
      rewrite seq_at_τ_seq. repeat dec_refl.
      cbn [eq_rect_r eq_rect eq_sym]. rewrite cast_cast_sym.
      destruct (excluded_middle_informative _) as [Hsub | Hsub].
      + split; [intros _; reflexivity | intros _; exact Hsub].
      + split; [intros Hc; contradiction | intros Hc; discriminate].
    - intros σ1 σ2 l fn. seq_sym. cbn [seq_map_interp].
      rewrite !seq_at_τ_seq. repeat dec_refl. cbn [eq_rect].
      symmetry. apply cast_cast_sym.
  Qed.

End SeqInterpretable.

Theorem seq_empty_has_sort : forall Σ σ,
    Σ_seq ⊑ Σ ->
    monomorphic σ ->
    Σ ⊢ seq_empty σ : τ_seq σ.
Proof.
  intros * Hsub Hmono.
  econstructor.
  - exists {[ u_A := σ ]}, [], (τ_seq τ_A). sauto lq:on.
  - reflexivity.
  - intros * Ht_i Hσ_i. inversion Ht_i.
Qed.

Theorem seq_unit_has_sort : forall Σ t σ,
    Σ_seq ⊑ Σ ->
    monomorphic σ ->
    (Σ ⊢ t : σ) ->
    Σ ⊢ seq_unit t : τ_seq σ.
Proof.
  intros * Hsub Ht.
  econstructor.
  - exists {[ u_A := σ ]}, [τ_A], (τ_seq τ_A). sauto q:on dep:on.
  - intros * Hrank.
    eapply monomorphic_rank_conservative in Hrank; eauto.
    ecrush. set_solver.
  - reflexivity.
  - intros * Ht_i Hσ_i.
    rewrite list_lookup_singleton in Ht_i.
    destruct i; try congruence. simpl in *.
    simplify_eq. assumption.
Qed.

Theorem seq_concat_has_sort : forall Σ t1 t2 σ,
    Σ_seq ⊑ Σ ->
    monomorphic σ ->
    (Σ ⊢ t1 : τ_seq σ) ->
    (Σ ⊢ t2 : τ_seq σ) ->
    Σ ⊢ seq_concat t1 t2 : τ_seq σ.
Proof.
  intros * Hsub Ht.
  econstructor.
  - exists {[ u_A := σ ]}, [τ_seq τ_A; τ_seq τ_A], (τ_seq τ_A).
    sauto qb:on dep:on.
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

Lemma eval_seq_concat :
  forall Σ A θ σ t1 t2 (v1 v2 : A.(domain) (τ_seq σ)),
    Σ_seq ⊑ Σ ->
    monomorphic σ ->
    ⟦ t1 : τ_seq σ ⟧(Σ, A, θ) ⇓ v1 ->
    ⟦ t2 : τ_seq σ ⟧(Σ, A, θ) ⇓ v2 ->
    ⟦ seq_concat t1 t2 : τ_seq σ ⟧(Σ, A, θ)
      ⇓ interp_apply A.(domain)
         (A.(interp) f_seq_concat [τ_seq σ; τ_seq σ] (τ_seq σ))
         (HCons (τ_seq σ) [τ_seq σ] v1 (HCons (τ_seq σ) [] v2 HNil)).
Proof.
  intros Σ A θ σ t1 t2 v1 v2 Hsub Hmono Ht1 Ht2.
  unfold seq_concat. eapply E_TApp with (σs := [τ_seq σ; τ_seq σ])
    (vs := HCons (τ_seq σ) [τ_seq σ] v1 (HCons (τ_seq σ) [] v2 HNil)).
  - repeat constructor; [exact Ht1 | exact Ht2].
  - constructor.
  - exists {[ u_A := σ ]}, [τ_seq τ_A; τ_seq τ_A], (τ_seq τ_A).
    split; [apply (rank_extends Hsub); constructor|].
    split.
    + unfold monomorphic_instance_of. split.
      * unfold instance_of, τ_seq, τ_A; simpl.
        rewrite lookup_singleton_eq. reflexivity.
      * repeat constructor. exact Hmono.
    + constructor.
      * unfold monomorphic_instance_of. split.
        -- unfold instance_of, τ_seq, τ_A; simpl.
           rewrite lookup_singleton_eq. reflexivity.
        -- repeat constructor. exact Hmono.
      * constructor.
        -- unfold monomorphic_instance_of. split.
           ++ unfold instance_of, τ_seq, τ_A; simpl.
              rewrite lookup_singleton_eq. reflexivity.
           ++ repeat constructor. exact Hmono.
        -- constructor.
  - reflexivity.
Qed.


Theorem seq_len_has_sort : forall Σ t σ,
    Σ_seq ⊑ Σ ->
    monomorphic σ ->
    (Σ ⊢ t : τ_seq σ) ->
    Σ ⊢ seq_len t : σ_int.
Proof.
  intros * Hsub Ht.
  econstructor.
  - exists {[ u_A := σ ]}, [τ_seq τ_A], σ_int. sauto dep:on.
  - intros * Hrank.
    eapply monomorphic_rank_conservative in Hrank; eauto.
    sauto. set_solver.
  - reflexivity.
  - intros * Ht_i Hσ_i.
    rewrite list_lookup_singleton in Ht_i.
    destruct i; try congruence. simpl in *.
    simplify_eq. assumption.
Qed.

Lemma eval_seq_len :
  forall Σ A θ σ t (v : A.(domain) (τ_seq σ)),
    Σ_seq ⊑ Σ ->
    monomorphic σ ->
    ⟦ t : τ_seq σ ⟧(Σ, A, θ) ⇓ v ->
    ⟦ seq_len t : σ_int ⟧(Σ, A, θ)
      ⇓ interp_apply A.(domain)
         (A.(interp) f_seq_len [τ_seq σ] σ_int)
         (HCons (τ_seq σ) [] v HNil).
Proof.
  intros Σ A θ σ t v Hsub Hmono Ht.
  unfold seq_len. eapply E_TApp with (σs := [τ_seq σ])
    (vs := HCons (τ_seq σ) [] v HNil).
  - repeat constructor. exact Ht.
  - constructor.
  - exists {[ u_A := σ ]}, [τ_seq τ_A], σ_int.
    split; [apply (rank_extends Hsub); constructor|].
    split.
    + unfold monomorphic_instance_of. split.
      * unfold instance_of. reflexivity.
      * repeat constructor.
    + constructor.
      * unfold monomorphic_instance_of. split.
        -- unfold instance_of, τ_seq, τ_A; simpl.
           rewrite lookup_singleton_eq. reflexivity.
        -- repeat constructor. exact Hmono.
      * constructor.
  - reflexivity.
Qed.


Theorem seq_nth_has_sort : forall Σ t1 t2 σ,
    Σ_seq ⊑ Σ ->
    monomorphic σ ->
    (Σ ⊢ t1 : τ_seq σ) ->
    (Σ ⊢ t2 : σ_int) ->
    Σ ⊢ seq_nth t1 t2 : σ.
Proof.
  intros * Hsub Ht.
  econstructor.
  - exists {[ u_A := σ ]}, [τ_seq τ_A; σ_int], τ_A.
    sauto qb:on dep:on.
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

Lemma eval_seq_nth :
  forall Σ A θ σ t_seq t_i
         (v_seq : A.(domain) (τ_seq σ)) (v_i : A.(domain) σ_int),
    Σ_seq ⊑ Σ ->
    monomorphic σ ->
    ⟦ t_seq : τ_seq σ ⟧(Σ, A, θ) ⇓ v_seq ->
    ⟦ t_i : σ_int ⟧(Σ, A, θ) ⇓ v_i ->
    ⟦ seq_nth t_seq t_i : σ ⟧(Σ, A, θ)
      ⇓ interp_apply A.(domain)
         (A.(interp) f_seq_nth [τ_seq σ; σ_int] σ)
         (HCons (τ_seq σ) [σ_int] v_seq
           (HCons σ_int [] v_i HNil)).
Proof.
  intros Σ A θ σ t_seq t_i v_seq v_i Hsub Hmono Hseq Hi.
  unfold seq_nth. eapply E_TApp with (σs := [τ_seq σ; σ_int])
    (vs := HCons (τ_seq σ) [σ_int] v_seq
      (HCons σ_int [] v_i HNil)).
  - repeat constructor; [exact Hseq | exact Hi].
  - constructor.
  - exists {[ u_A := σ ]}, [τ_seq τ_A; σ_int], τ_A.
    split; [apply (rank_extends Hsub); constructor|].
    split.
    + unfold monomorphic_instance_of. split.
      * unfold instance_of, τ_A; simpl.
        rewrite lookup_singleton_eq. reflexivity.
      * exact Hmono.
    + constructor.
      * unfold monomorphic_instance_of. split.
        -- unfold instance_of, τ_seq, τ_A; simpl.
           rewrite lookup_singleton_eq. reflexivity.
        -- repeat constructor. exact Hmono.
      * constructor.
        -- unfold monomorphic_instance_of. split.
           ++ unfold instance_of. reflexivity.
           ++ repeat constructor.
        -- constructor.
  - reflexivity.
Qed.


Theorem seq_contains_has_sort : forall Σ t1 t2 σ,
    Σ_seq ⊑ Σ ->
    monomorphic σ ->
    (Σ ⊢ t1 : τ_seq σ) ->
    (Σ ⊢ t2 : τ_seq σ) ->
    Σ ⊢ seq_contains t1 t2 : σ_bool.
Proof.
  intros * Hsub Ht.
  econstructor.
  - exists {[ u_A := σ ]}, [τ_seq τ_A; τ_seq τ_A], σ_bool.
    sauto qb:on dep:on.
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

Theorem seq_map_has_sort : forall Σ t1 t2 σ1 σ2,
    Σ_seq ⊑ Σ ->
    monomorphic σ1 ->
    monomorphic σ2 ->
    (Σ ⊢ t1 : τ_map σ1 σ2) ->
    (Σ ⊢ t2 : τ_seq σ1) ->
    Σ ⊢ seq_map t1 t2 : τ_seq σ2.
Proof.
  intros * Hsub Ht.
  econstructor.
  - exists {[ u_A := σ1; u_B := σ2 ]}, [τ_map τ_A τ_B; τ_seq τ_A], (τ_seq τ_B).
    sauto.
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

(** * Datatypes Nested Under Sequences *)

(** SMT-LIB 2.7 §4.2.3, restriction (iv) on [declare-datatypes], requires that
    a constructor's argument sort contain no occurrence of the datatypes being
    declared below its top symbol.  A datatype [δ] with a field of sort
    [τ_seq δ] violates it: the top symbol is the sequence symbol and [δ] sits
    below it.  That restriction is what makes Definition 8 self-supporting —
    generators are elements of datatype-free domains, so the term-building
    recursion descends only through constructor arguments, and "the set of
    well-sorted ground terms" is an inductive definition.  Allow the nesting
    and terms contain leaves that contain terms.

    Neither solver enforces (iv).  Measured on z3 4.15.4 and cvc5 1.3.4 and
    1.4.1, both accept a declaration group in which one datatype nests another
    under [Seq] or [Array].  cvc5 rejects recursion through any sort
    constructor as a nested-recursive datatype — a limit of its datatype
    solver rather than a conformance check — while z3 accepts recursion
    through [Seq] and returns models for it.  We follow z3 in this one place,
    as an extension of the standard: [seq_ground_term] lifts restriction (iv)
    for exactly one sort constructor, with the descent the restriction was
    protecting put back by hand as the [SGSeq] case.  [SMTLIB.Theory]'s
    [ground_term] remains the standard's reading, and a theory wanting the
    extension opts into it by name, at [theory_init_seq] rather than
    [theory_init]. *)

(** A sort a term may sit at as an opaque leaf: a datatype-free sort — not a
    datatype sort, whose elements are constructor applications, and mentioning
    no datatype anywhere, for the reason [adt_free] gives — and not a sequence
    sort, whose elements are lists of further terms.  Excluding sequence sorts
    is what stops [SGGen] from subsuming [SGSeq] and the variant from saying
    nothing new. *)
Definition generator_sort (Σ : signature) (σ : sort) : Prop :=
  adt_free Σ σ /\ is_seqb σ = false.

Theorem generator_sort_irrelevant : forall Σ σ (H1 H2 : generator_sort Σ σ),
    H1 = H2.
Proof.
  intros Σ σ [Ha1 Hs1] [Ha2 Hs2].
  by rewrite (adt_free_irrelevant _ _ Ha1 Ha2),
    (Eqdep_dec.UIP_dec Bool.bool_dec Hs1 Hs2).
Qed.

(** The stratification this file assumes: sequences are not datatypes.  It is a
    condition on the signature, not on a structure, so it is discharged once by
    whoever builds the signature.  Without it a sort could be asked to be both
    a list of terms and a constructor application, and the embedding below
    would have to choose. *)
Definition seq_sorts_not_adt (Σ : signature) : Prop :=
  forall σ, ~ adt Σ (τ_seq σ).

(** [embeddable_sort] extended by the same one sort constructor: the sorts a
    domain element can be read back at, which under a sequence means the
    element sort must be readable too.

    The leaf case carries its own "not a sequence" side condition, which is
    what makes the inversion at [τ_seq] unconditional: the leaf case cannot
    apply there, so the sequence case is the only one, and no appeal to
    [seq_sorts_not_adt] is needed.  That matters because the crossing below
    performs that inversion, and a signature condition may not leak into
    [seq_adt_conditions]. *)
(** Whether the crossing reaches a leaf it can read back: peel the sequence
    layers, and at the first sort that is not one ask [embeddable_sort].  Like
    the predicates it is built from, it is recorded by its decision, so the
    ground terms indexed by it are indexed by something irrelevant. *)
Fixpoint seq_embeddableb (Σ : signature) (σ : sort) : bool :=
  match σ with
  | SApp s [σ1] =>
      if bool_decide (s = s_seq)
      then seq_embeddableb Σ σ1
      else bool_decide (embeddable_sort Σ (SApp s [σ1]))
  | _ => bool_decide (embeddable_sort Σ σ)
  end.

Definition seq_embeddable_sort (Σ : signature) (σ : sort) : Prop :=
  seq_embeddableb Σ σ = true.

Theorem seq_embeddable_sort_irrelevant :
  forall Σ σ (H1 H2 : seq_embeddable_sort Σ σ), H1 = H2.
Proof. intros Σ σ H1 H2. apply (Eqdep_dec.UIP_dec Bool.bool_dec). Qed.

Global Instance seq_embeddable_sort_dec (Σ : signature) (σ : sort) :
  Decision (seq_embeddable_sort Σ σ).
Proof. unfold seq_embeddable_sort. apply _. Defined.

(** A sort that is not a sequence is reached as a leaf. *)
Theorem seq_embeddable_leaf : forall Σ σ,
    is_seqb σ = false -> embeddable_sort Σ σ -> seq_embeddable_sort Σ σ.
Proof.
  intros Σ σ Hns Hi. unfold seq_embeddable_sort.
  destruct σ as [u | s τs]; [by apply (bool_decide_eq_true_2 (embeddable_sort Σ _)) |].
  destruct τs as [| σ1 [| σ2 τs']];
    [by apply (bool_decide_eq_true_2 (embeddable_sort Σ _))
    | | by apply (bool_decide_eq_true_2 (embeddable_sort Σ _))].
  cbn [seq_embeddableb]. cbn [is_seqb] in Hns. rewrite Hns.
  by apply (bool_decide_eq_true_2 (embeddable_sort Σ _)).
Qed.

Theorem embeddable_sort_of_seq_embeddable : forall Σ σ,
    is_seqb σ = false -> seq_embeddable_sort Σ σ -> embeddable_sort Σ σ.
Proof.
  intros Σ σ Hns Hi. unfold seq_embeddable_sort in Hi.
  destruct σ as [u | s τs]; [by apply (bool_decide_eq_true_1 (embeddable_sort Σ _)) |].
  destruct τs as [| σ1 [| σ2 τs']];
    [by apply (bool_decide_eq_true_1 (embeddable_sort Σ _))
    | | by apply (bool_decide_eq_true_1 (embeddable_sort Σ _))].
  cbn [seq_embeddableb] in Hi. cbn [is_seqb] in Hns. rewrite Hns in Hi.
  by apply (bool_decide_eq_true_1 (embeddable_sort Σ _)).
Qed.

(** The step at a sequence sort, in both directions. *)
Theorem seq_embeddable_seq : forall Σ σ,
    seq_embeddable_sort Σ σ -> seq_embeddable_sort Σ (τ_seq σ).
Proof.
  intros Σ σ H. unfold seq_embeddable_sort, τ_seq.
  cbn [seq_embeddableb]. by rewrite (bool_decide_eq_true_2 (s_seq = s_seq) eq_refl).
Qed.

Theorem seq_embeddable_sort_elem : forall Σ σ,
    seq_embeddable_sort Σ (τ_seq σ) -> seq_embeddable_sort Σ σ.
Proof.
  intros Σ σ H. unfold seq_embeddable_sort, τ_seq in *.
  cbn [seq_embeddableb] in H. by rewrite (bool_decide_eq_true_2 (s_seq = s_seq) eq_refl) in H.
Qed.

(** What [SGGen] needs at a sort the crossing has reached as a leaf. *)
Lemma generator_sort_of_seq_embeddable : forall Σ σ,
    is_seqb σ = false -> ~ adt Σ σ ->
    seq_embeddable_sort Σ σ -> generator_sort Σ σ.
Proof.
  intros Σ σ Hns Hnadt Hi. split; [| exact Hns].
  apply (adt_free_of_embeddable Σ σ); [| exact Hnadt].
  apply (embeddable_sort_of_seq_embeddable Σ σ); [exact Hns | exact Hi].
Qed.

(** The sort shapes that are not sequence applications, in the form the
    embedding's branches need them: as terms, since they are arguments to a
    definition rather than steps in a proof. *)

Lemma not_τ_seq_SParam : forall u σ', SParam u ≠ τ_seq σ'.
Proof. intros u σ' H. discriminate. Qed.

Lemma not_τ_seq_nil : forall s σ', SApp s [] ≠ τ_seq σ'.
Proof. intros s σ' H. discriminate. Qed.

Lemma not_τ_seq_cons2 : forall s σ1 σ2 τs σ', SApp s (σ1 :: σ2 :: τs) ≠ τ_seq σ'.
Proof. intros s σ1 σ2 τs σ' H. discriminate. Qed.

Lemma not_τ_seq_symb : forall s σ0, s ≠ s_seq -> forall σ', SApp s [σ0] ≠ τ_seq σ'.
Proof. intros s σ0 Hne σ' H. injection H as -> _. contradiction. Qed.

Corollary seq_embeddable_sort_app_nil : forall Σ s,
    seq_embeddable_sort Σ (SApp s []).
Proof.
  intros Σ s. apply seq_embeddable_leaf;
    [reflexivity | apply embeddable_sort_app_nil].
Qed.

Section SeqGroundTerm.

  Variables (Σ : signature) (gen : forall σ, generator_sort Σ σ -> Type).

  Unset Elimination Schemes.

  Inductive seq_ground_term : sort -> Type :=
  | SGGen :
    forall σ (H : generator_sort Σ σ),
      gen σ H ->
      seq_ground_term σ
  | SGSeq :
    forall σ,
      list (seq_ground_term σ) ->
      seq_ground_term (τ_seq σ)
  | SGConstr :
    forall c σs δ s,
      s ∈ Σ.(sort_symbols) ->
      sort_top_symbol δ = Some s ->
      c ∈ Σ.(constructors_for_sort) s ->
      monomorphic_rank Σ c σs δ ->
      sort_wf Σ δ ->
      hlist seq_ground_term σs ->
      seq_ground_term δ.

  Set Elimination Schemes.

End SeqGroundTerm.

Arguments SGGen {_} {_}.
Arguments SGSeq {_} {_}.
Arguments SGConstr {_} {_}.

Definition seq_ground_term_constructor {Σ gen δ} (g : seq_ground_term Σ gen δ)
  : option func :=
  match g with
  | SGGen _ _ _ => None
  | SGSeq _ _ => None
  | SGConstr c _ _ _ _ _ _ _ _ _ => Some c
  end.

Lemma seq_ground_term_constructor_Some :
  forall Σ gen δ (g : seq_ground_term Σ gen δ) c,
    seq_ground_term_constructor g = Some c ->
    exists σs s Hs Hδ Hc Hrank Hwf ws,
      g = SGConstr c σs δ s Hs Hδ Hc Hrank Hwf ws.
Proof.
  intros Σ gen δ g c Hg. destruct g; try discriminate.
  injection Hg as ->. do 8 eexists. reflexivity.
Qed.

(** ** Elimination *)

(** [seq_ground_term] nests through [list] at [SGSeq] and through [hlist] at
    [SGConstr], and Rocq's generated eliminator gives an induction hypothesis
    for neither.  These are the usable ones.  Both inner recursions have to be
    inner [fix]es for the reason given at [ground_term_rect]: neither [list]
    nor [hlist] is in [seq_ground_term]'s inductive block, so only inlining
    lets the guard checker see an element as a subterm. *)

Section SeqGroundTermRect.

  Context (Σ : signature) (gen : forall σ, generator_sort Σ σ -> Type).
  Context (P : forall σ, seq_ground_term Σ gen σ -> Type).
  Context (Hgen : forall σ H (x : gen σ H), P σ (SGGen σ H x)).
  Context (Hseq : forall σ (gs : list (seq_ground_term Σ gen σ)),
              list_ForallT (P σ) gs -> P (τ_seq σ) (SGSeq σ gs)).
  Context (Hconstr :
            forall c σs δ s Hs Hδ Hc Hrank Hwf (vs : hlist (seq_ground_term Σ gen) σs),
              hlist_ForallT (seq_ground_term Σ gen) P vs ->
              P δ (SGConstr c σs δ s Hs Hδ Hc Hrank Hwf vs)).

  Fixpoint seq_ground_term_rect σ (g : seq_ground_term Σ gen σ) {struct g}
    : P σ g :=
    match g with
    | SGGen σ H x => Hgen σ H x
    | SGSeq σ gs =>
        Hseq σ gs
          ((fix go (l : list (seq_ground_term Σ gen σ)) {struct l}
              : list_ForallT (P σ) l :=
              match l with
              | [] => tt
              | g' :: l' => (seq_ground_term_rect σ g', go l')
              end) gs)
    | SGConstr c σs δ s Hs Hδ Hc Hrank Hwf vs =>
        Hconstr c σs δ s Hs Hδ Hc Hrank Hwf vs
          ((fix go σs' (ws : hlist (seq_ground_term Σ gen) σs') {struct ws}
              : hlist_ForallT (seq_ground_term Σ gen) P ws :=
              match ws with
              | HNil => tt
              | HCons σ' σs'' w ws' => (seq_ground_term_rect σ' w, go σs'' ws')
              end) σs vs)
    end.

End SeqGroundTermRect.

Lemma seq_ground_term_ind :
  forall (Σ : signature) (gen : forall σ, generator_sort Σ σ -> Type)
    (P : forall σ, seq_ground_term Σ gen σ -> Prop),
    (forall σ H (x : gen σ H), P σ (SGGen σ H x)) ->
    (forall σ (gs : list (seq_ground_term Σ gen σ)),
        (forall i g, gs !! i = Some g -> P σ g) ->
        P (τ_seq σ) (SGSeq σ gs)) ->
    (forall c σs δ s Hs Hδ Hc Hrank Hwf (vs : hlist (seq_ground_term Σ gen) σs),
        (forall i p, hlist_lookup (seq_ground_term Σ gen) vs i = Some p ->
                     P (projT1 p) (projT2 p)) ->
        P δ (SGConstr c σs δ s Hs Hδ Hc Hrank Hwf vs)) ->
    forall σ g, P σ g.
Proof.
  intros Σ gen P Hgen Hseq Hconstr.
  apply (seq_ground_term_rect Σ gen P Hgen).
  - intros σ gs Hall. apply Hseq. now apply list_ForallT_lookup.
  - intros c σs δ s Hs Hδ Hc Hrank Hwf vs Hall.
    apply Hconstr. now apply hlist_ForallT_lookup.
Qed.

(** ** Size *)

(** A measure on ground terms, so that a proof recursing through a value can
    use strong induction on a number rather than the hand-rolled eliminator.
    Both are available; the measure is easier to use when the statement being
    proved is about several sorts at once, since the induction hypothesis is
    then "at any sort, for any smaller term" and needs no sort equations. *)

Section SeqGroundTermSize.

  Context (Σ : signature) (gen : forall σ, generator_sort Σ σ -> Type).

  Fixpoint seq_ground_term_size {σ} (g : seq_ground_term Σ gen σ) {struct g}
    : nat :=
    match g with
    | SGGen _ _ _ => 1
    | SGSeq σ0 gs =>
        S ((fix go (l : list (seq_ground_term Σ gen σ0)) {struct l} : nat :=
              match l with
              | [] => 0
              | g' :: l' => seq_ground_term_size g' + go l'
              end) gs)
    | SGConstr c σs δ s Hs Hδ Hc Hrank Hwf vs =>
        S ((fix go σs' (ws : hlist (seq_ground_term Σ gen) σs') {struct ws}
              : nat :=
              match ws with
              | HNil => 0
              | HCons σ' σs'' w ws' => seq_ground_term_size w + go σs'' ws'
              end) σs vs)
    end.

  (** A sequence's elements and a constructor's arguments are smaller. *)

  Lemma seq_ground_term_size_SGSeq :
    forall σ (gs : list (seq_ground_term Σ gen σ)) g,
      g ∈ gs ->
      seq_ground_term_size g < seq_ground_term_size (SGSeq σ gs).
  Proof.
    intros σ gs. induction gs as [| g0 gs IH]; intros g Hin.
    - exfalso. eapply not_elem_of_nil. exact Hin.
    - apply elem_of_cons in Hin as [-> | Hin]; simpl; [lia |].
      specialize (IH g Hin). simpl in IH. lia.
  Qed.

  Lemma seq_ground_term_size_SGConstr :
    forall c σs δ s Hs Hδ Hc Hrank Hwf (vs : hlist (seq_ground_term Σ gen) σs) i p,
      hlist_lookup (seq_ground_term Σ gen) vs i = Some p ->
      seq_ground_term_size (projT2 p)
      < seq_ground_term_size (SGConstr c σs δ s Hs Hδ Hc Hrank Hwf vs).
  Proof.
    intros c σs δ s Hs Hδ Hc Hrank Hwf vs. simpl. clear Hs Hδ Hc Hrank Hwf.
    induction vs as [| σ0 σs0 v vs IH]; intros i p Hlk.
    - destruct i; simpl in Hlk; discriminate.
    - destruct i; simpl in Hlk.
      + injection Hlk as <-. simpl. lia.
      + specialize (IH i p Hlk). simpl in IH |- *. lia.
  Qed.

End SeqGroundTermSize.

Arguments seq_ground_term_size {_} {_} {_}.

(** ** Moving Between the Domain and the Term Algebra *)

(** As in [SMTLIB.Theory], the constructor condition has to equate a
    domain-level application with a term-level one, so it needs to send a
    constructor's arguments across.  Here the crossing is recursive: a
    sequence-sorted argument is a list whose elements must themselves be sent
    across, which is the whole point of the extension. *)

Section SeqEmbedProject.

  Context (Σ : signature) (Hseq_not_adt : seq_sorts_not_adt Σ) (A : structure).

  Definition seq_domain_gen : forall σ, generator_sort Σ σ -> Type :=
    fun σ _ => A.(domain) σ.

  Context (Hdom : forall δ, adt Σ δ ->
                            A.(domain) δ = seq_ground_term Σ seq_domain_gen δ).
  Context (Hlist : forall σ, A.(domain) (τ_seq σ) = list (A.(domain) σ)).

  (** At a sort that is not a sequence, the crossing is [ground_term_embed]'s:
      a datatype element transports by the domain equation, a datatype-free
      one is a leaf.  As there, a sort that is neither has no ground terms to
      cross to, which is what the [seq_embeddable_sort] premise rules
      out. *)
  Definition seq_ground_term_leaf (σ : sort) (Hns : is_seqb σ = false)
    (Hi : seq_embeddable_sort Σ σ) (v : A.(domain) σ)
    : seq_ground_term Σ seq_domain_gen σ :=
    match decide (adt Σ σ) with
    | left  H => cast (Hdom σ H) v
    | right H => SGGen σ (generator_sort_of_seq_embeddable Σ σ Hns H Hi) v
    end.

  (** Structural on the *sort*, not on the value: the sequence case recurses at
      the element sort, and no domain element is being destructed.  This is
      why [Hseq_not_adt] is needed — at a sort that was both a sequence and a
      datatype the two branches would disagree.

      The premise descends with the recursion.  [seq_embeddable_sort] steps
      at [τ_seq] by conversion, so the sequence case can hand its own premise
      down without an inversion that would drag [Hseq_not_adt] into the
      crossing itself — and so into [seq_adt_conditions], where a signature
      condition does not belong. *)
  Fixpoint seq_ground_term_embed (σ : sort) {struct σ}
    : seq_embeddable_sort Σ σ -> A.(domain) σ
      -> seq_ground_term Σ seq_domain_gen σ :=
    match σ as σ0
      return seq_embeddable_sort Σ σ0 -> A.(domain) σ0
             -> seq_ground_term Σ seq_domain_gen σ0 with
    | SParam u => seq_ground_term_leaf (SParam u) eq_refl
    | SApp s τs =>
        match τs as τs0
          return seq_embeddable_sort Σ (SApp s τs0)
                 -> A.(domain) (SApp s τs0)
                 -> seq_ground_term Σ seq_domain_gen (SApp s τs0) with
        | [] => seq_ground_term_leaf (SApp s []) eq_refl
        | [σ'] =>
            match decide (s = s_seq) with
            | left Heq =>
                match eq_sym Heq in _ = s0
                  return seq_embeddable_sort Σ (SApp s0 [σ'])
                         -> A.(domain) (SApp s0 [σ'])
                         -> seq_ground_term Σ seq_domain_gen (SApp s0 [σ']) with
                | eq_refl =>
                    fun Hi v =>
                      SGSeq σ'
                        (map (seq_ground_term_embed σ'
                                (seq_embeddable_sort_elem Σ σ' Hi))
                           (cast (Hlist σ') v))
                end
            | right Hne =>
                seq_ground_term_leaf (SApp s [σ'])
                  (bool_decide_eq_false_2 (s = s_seq) Hne)
            end
        | σ1 :: σ2 :: τs' =>
            seq_ground_term_leaf (SApp s (σ1 :: σ2 :: τs')) eq_refl
        end
    end.

  (** The left inverse.  A leaf gives its generator back, a sequence maps back
      elementwise, and a constructor application transports by the domain
      equation. *)
  Fixpoint seq_ground_term_project (σ : sort)
    (g : seq_ground_term Σ seq_domain_gen σ) {struct g} : A.(domain) σ :=
    match g in seq_ground_term _ _ σ0 return A.(domain) σ0 with
    | SGGen σ0 H x => x
    | SGSeq σ0 gs =>
        cast_sym (Hlist σ0) (map (seq_ground_term_project σ0) gs)
    | SGConstr c σs δ s Hs Hδ Hc Hrank Hwf vs =>
        cast_sym (Hdom δ (adt_intro Σ δ s c Hs Hδ Hc Hwf))
          (SGConstr c σs δ s Hs Hδ Hc Hrank Hwf vs)
    end.

  (** ** How the Two Read Off Each Constructor *)

  Lemma seq_ground_term_embed_seq : forall σ Hi v,
      seq_ground_term_embed (τ_seq σ) Hi v
      = SGSeq σ (map (seq_ground_term_embed σ
                        (seq_embeddable_sort_elem Σ σ Hi))
                  (cast (Hlist σ) v)).
  Proof.
    intros σ Hi v. simpl.
    destruct (decide (s_seq = s_seq)) as [Heq | Hne]; [| exfalso; now apply Hne].
    now rewrite (Eqdep_dec.UIP_dec (fun x y => decide (x = y)) Heq eq_refl).
  Qed.

  Lemma seq_ground_term_embed_not_seq :
    forall σ (Hns : is_seqb σ = false) Hi v,
      seq_ground_term_embed σ Hi v = seq_ground_term_leaf σ Hns Hi v.
  Proof.
    intros σ Hns Hi v. unfold seq_ground_term_leaf.
    destruct σ as [u | s τs]; [| destruct τs as [| σ1 [| σ2 τs']]].
    - simpl. now rewrite (Eqdep_dec.UIP_dec Bool.bool_dec Hns eq_refl).
    - simpl. now rewrite (Eqdep_dec.UIP_dec Bool.bool_dec Hns eq_refl).
    - simpl. destruct (decide (s = s_seq)) as [-> | Hne].
      + exfalso. by apply (proj1 (is_seqb_false _) Hns σ1).
      + simpl. now rewrite (Eqdep_dec.UIP_dec Bool.bool_dec Hns
                              (bool_decide_eq_false_2 (s = s_seq) Hne)).
    - simpl. now rewrite (Eqdep_dec.UIP_dec Bool.bool_dec Hns eq_refl).
  Qed.

  Lemma seq_ground_term_embed_adt : forall σ Hi (H : adt Σ σ) v,
      seq_ground_term_embed σ Hi v = cast (Hdom σ H) v.
  Proof.
    intros σ Hi H v.
    assert (Hns : is_seqb σ = false)
      by (apply is_seqb_false; intros σ' ->; exact (Hseq_not_adt σ' H)).
    rewrite (seq_ground_term_embed_not_seq σ Hns).
    unfold seq_ground_term_leaf.
    destruct (decide (adt Σ σ)) as [H' | H']; [| contradiction].
    now rewrite (adt_irrelevant _ _ H' H).
  Qed.

  Lemma seq_ground_term_embed_gen : forall σ Hi (H : generator_sort Σ σ) v,
      seq_ground_term_embed σ Hi v = SGGen σ H v.
  Proof.
    intros σ Hi H v. pose proof H as [Hfree Hns].
    rewrite (seq_ground_term_embed_not_seq σ Hns).
    unfold seq_ground_term_leaf.
    destruct (decide (adt Σ σ)) as [H' | H'];
      [destruct (adt_free_not_adt Σ σ Hfree H') |].
    now rewrite (generator_sort_irrelevant _ _
                   (generator_sort_of_seq_embeddable Σ σ Hns H' Hi) H).
  Qed.

  Lemma seq_ground_term_project_adt : forall σ (H : adt Σ σ) g,
      seq_ground_term_project σ g = cast_sym (Hdom σ H) g.
  Proof.
    intros σ Hadt g. revert Hadt.
    destruct g as [σ0 [Hfree Hns] x | σ0 gs | c σs δ s Hs Hδ Hc Hrank Hwf vs];
      intros Hadt.
    - destruct (adt_free_not_adt Σ σ0 Hfree Hadt).
    - exfalso. exact (Hseq_not_adt σ0 Hadt).
    - simpl. now rewrite (adt_irrelevant _ _ (adt_intro _ _ _ _ Hs Hδ Hc Hwf) Hadt).
  Qed.

  Lemma seq_ground_term_project_seq : forall σ gs,
      seq_ground_term_project (τ_seq σ) (SGSeq σ gs)
      = cast_sym (Hlist σ) (map (seq_ground_term_project σ) gs).
  Proof. reflexivity. Qed.

  Lemma seq_ground_term_project_leaf : forall σ Hns Hi v,
      seq_ground_term_project σ (seq_ground_term_leaf σ Hns Hi v) = v.
  Proof.
    intros σ Hns Hi v. unfold seq_ground_term_leaf.
    destruct (decide (adt Σ σ)) as [H | H].
    - now rewrite (seq_ground_term_project_adt σ H), cast_sym_cast.
    - reflexivity.
  Qed.

  (** ** The Two Round Trips *)

  (** The projection is a genuine inverse, not merely a retraction, which is
      what lets a destructured [SGConstr] be put back together after its
      arguments have been read off. *)

  Lemma seq_ground_term_project_embed : forall σ Hi v,
      seq_ground_term_project σ (seq_ground_term_embed σ Hi v) = v.
  Proof.
    intros σ. induction σ as [u | s τs IH];
      [| destruct τs as [| σ1 [| σ2 τs']]]; intros Hi v.
    - rewrite (seq_ground_term_embed_not_seq (SParam u) eq_refl).
      apply seq_ground_term_project_leaf.
    - rewrite (seq_ground_term_embed_not_seq (SApp s []) eq_refl).
      apply seq_ground_term_project_leaf.
    - destruct (decide (s = s_seq)) as [-> | Hne].
      + change (SApp s_seq [σ1]) with (τ_seq σ1) in *.
        rewrite seq_ground_term_embed_seq, seq_ground_term_project_seq, map_map.
        rewrite (map_ext_in _ id); [now rewrite map_id, cast_sym_cast |].
        intros a _. apply IH. apply elem_of_cons. now left.
      + rewrite (seq_ground_term_embed_not_seq (SApp s [σ1])
                 (bool_decide_eq_false_2 (s = s_seq) Hne)).
        apply seq_ground_term_project_leaf.
    - rewrite (seq_ground_term_embed_not_seq (SApp s (σ1 :: σ2 :: τs')) eq_refl).
      apply seq_ground_term_project_leaf.
  Qed.

  Lemma seq_ground_term_embed_project : forall σ g Hi,
      seq_ground_term_embed σ Hi (seq_ground_term_project σ g) = g.
  Proof.
    intros σ g. induction g as [σ0 H x | σ0 gs IH | c σs δ s Hs Hδ Hc Hrank Hwf vs IH]
                                 using seq_ground_term_ind;
      intros Hi.
    - simpl. now rewrite (seq_ground_term_embed_gen σ0 Hi H).
    - rewrite seq_ground_term_project_seq, seq_ground_term_embed_seq,
        cast_cast_sym, map_map.
      f_equal. rewrite (map_ext_in _ id); [apply map_id |].
      intros a Ha. apply list_elem_of_In, list_elem_of_lookup in Ha as [i Ha].
      now apply (IH i).
    - assert (Hadt : adt Σ δ) by exact (adt_intro Σ δ s c Hs Hδ Hc Hwf).
      simpl. rewrite (seq_ground_term_embed_adt δ Hi Hadt).
      now rewrite (adt_irrelevant _ _ (adt_intro _ _ _ _ Hs Hδ Hc Hwf) Hadt),
        cast_cast_sym.
  Qed.

  Lemma seq_ground_term_embed_inj : forall σ Hi v1 v2,
      seq_ground_term_embed σ Hi v1 = seq_ground_term_embed σ Hi v2 -> v1 = v2.
  Proof.
    intros σ Hi v1 v2 Heq.
    rewrite <- (seq_ground_term_project_embed σ Hi v1),
      <- (seq_ground_term_project_embed σ Hi v2).
    now f_equal.
  Qed.

  (* The premise is a [Prop], so which one the crossing was given is invisible
     to its value; a proof that needs a particular one says so here. *)
  Lemma seq_ground_term_embed_irrel : forall σ Hi Hi' v,
      seq_ground_term_embed σ Hi v = seq_ground_term_embed σ Hi' v.
  Proof.
    intros σ Hi Hi' v. now rewrite (seq_embeddable_sort_irrelevant _ _ Hi Hi').
  Qed.

  (** ** Crossing a Constructor's Argument List *)

  (** As [hlist_map_embed] in [SMTLIB.Theory], and for the same reason: the
      crossing takes a proof, so the map threads one per element, taking the
      [Forall] apart a cons at a time as the [hlist] is consumed. *)
  Fixpoint hlist_map_seq_embed {σs} (vs : hlist A.(domain) σs)
    : Forall (seq_embeddable_sort Σ) σs ->
      hlist (seq_ground_term Σ seq_domain_gen) σs :=
    match vs in hlist _ σs0
          return Forall (seq_embeddable_sort Σ) σs0 ->
                 hlist (seq_ground_term Σ seq_domain_gen) σs0 with
    | HNil => fun _ => HNil
    | HCons σ σs' v vs' =>
        fun H =>
          HCons σ σs' (seq_ground_term_embed σ (Forall_cons_head H) v)
            (hlist_map_seq_embed vs' (Forall_cons_tail H))
    end.

  (* Which premise a crossed element carries does not matter to a caller, so
     the lookup lemma quantifies it: proof irrelevance reconciles it with the
     one the [Forall] actually threaded. *)
  Lemma hlist_lookup_seq_embed :
    forall σs (vs : hlist A.(domain) σs) H i σ (v : A.(domain) σ) Hi,
      hlist_lookup A.(domain) vs i = Some (existT σ v) ->
      hlist_lookup (seq_ground_term Σ seq_domain_gen)
        (hlist_map_seq_embed vs H) i
      = Some (existT σ (seq_ground_term_embed σ Hi v)).
  Proof.
    intros σs vs. induction vs as [| σ0 σs' v0 vs' IH];
      intros H i σ v Hi Hlk.
    - destruct i; discriminate.
    - destruct i as [| i]; cbn [hlist_map_seq_embed hlist_lookup] in *.
      + injection Hlk as Hσ Hv. subst σ0.
        apply (Eqdep_dec.inj_pair2_eq_dec _ (fun x y => decide (x = y)))
    in Hv. subst v0.
        by rewrite (seq_embeddable_sort_irrelevant _ _ (Forall_cons_head H) Hi).
      + apply IH, Hlk.
  Qed.

  Lemma hlist_map_project_seq_embed :
    forall σs (vs : hlist A.(domain) σs) H,
      hlist_map seq_ground_term_project (hlist_map_seq_embed vs H) = vs.
  Proof.
    intros σs vs. induction vs as [| σ σs' v vs' IH]; intros H.
    - reflexivity.
    - cbn [hlist_map hlist_map_seq_embed].
      f_equal; [apply seq_ground_term_project_embed | apply IH].
  Qed.

  Lemma hlist_map_seq_embed_project :
    forall σs (gs : hlist (seq_ground_term Σ seq_domain_gen) σs) H,
      hlist_map_seq_embed (hlist_map seq_ground_term_project gs) H = gs.
  Proof.
    intros σs gs. induction gs as [| σ σs' g gs' IH]; intros H.
    - reflexivity.
    - cbn [hlist_map hlist_map_seq_embed].
      f_equal; [apply seq_ground_term_embed_project | apply IH].
  Qed.

End SeqEmbedProject.

(* [simpl] and [cbn] would unfold these into the sort match they recurse on,
   which is never what a proof about a constructor equation wants: the
   equations above are the interface. *)
Arguments seq_ground_term_leaf : simpl never.
Arguments seq_ground_term_embed : simpl never.
Arguments seq_ground_term_project : simpl never.

(** ** The Datatype Conditions, Read Through Sequences *)

Section SeqAdtConditions.

  Context (Σ : signature) (A : structure).
  Context (Hdom : forall δ, adt Σ δ ->
                            A.(domain) δ
                            = seq_ground_term Σ (seq_domain_gen Σ A) δ).
  Context (Hlist : forall σ, A.(domain) (τ_seq σ) = list (A.(domain) σ)).

  (** [adt_constructor_condition] read over [seq_ground_term] instead of
      [ground_term].

      [Hσs] is §4.2.3(iv) as this file's extension reads it, asked of one
      rank: the argument sorts are ones the crossing is defined at, which here
      admits a datatype under any number of sequences.  A rank outside it is
      left uninterpreted rather than modelless, exactly as in
      [SMTLIB.Theory]. *)
  Definition seq_adt_constructor_condition : Prop :=
    forall c σs δ s
      (Hs : s ∈ Σ.(sort_symbols))
      (Hδ : sort_top_symbol δ = Some s)
      (Hc : c ∈ Σ.(constructors_for_sort) s)
      (Hrank : monomorphic_rank Σ c σs δ)
      (Hwf : sort_wf Σ δ)
      (Hσs : Forall (seq_embeddable_sort Σ) σs),
      let C := A.(interp) c σs δ in
      forall vs, cast (Hdom δ (adt_intro Σ δ s c Hs Hδ Hc Hwf))
                   (interp_apply A.(domain) C vs) =
                 SGConstr c σs δ s Hs Hδ Hc Hrank Hwf
                   (hlist_map_seq_embed Σ A Hdom Hlist vs Hσs).

  (** [adt_axioms]' conditions with the constructor condition read through
      sequences.  The selector and tester conditions are [SMTLIB.Theory]'s,
      unchanged: neither mentions the term algebra, so neither has anything to
      extend. *)
  Record seq_adt_conditions : Prop :=
    {
      seq_adt_interp_constructor : seq_adt_constructor_condition;
      seq_adt_interp_selector :
        adt_selector_condition Σ (seq_embeddable_sort Σ) A;
      seq_adt_interp_tester : adt_tester_condition Σ A;
    }.

End SeqAdtConditions.

Arguments seq_adt_interp_constructor {_} {_} {_} {_}.
Arguments seq_adt_interp_selector {_} {_} {_} {_}.
Arguments seq_adt_interp_tester {_} {_} {_} {_}.

(** The extended reading of Definition 8 and Definition 9's ADT requirement, as
    one predicate on a structure.  It is an existential over the two domain
    equations rather than a record, because the constructor condition mentions
    [seq_ground_term_embed], which needs Seq's own domain equation — a
    condition belonging to a different theory's model predicate, and so not
    something a field of this record could refer to.  This is the shape
    [T_seq.(pmodels)] already has, and it stays in [Prop]: [sigT] is
    sort-polymorphic, so a [sigT] over [Prop]s is a [Prop]. *)
Definition seq_adt_axioms (Σ : signature) (A : structure) : Prop :=
  { Hdom : forall δ, adt Σ δ ->
                     A.(domain) δ = seq_ground_term Σ (seq_domain_gen Σ A) δ &
  { Hlist : forall σ, A.(domain) (τ_seq σ) = list (A.(domain) σ) &
    seq_adt_conditions Σ A Hdom Hlist } }.

(** ** What a Consumer Gets Out of Them *)

Theorem seq_adt_interp_constructor_disjoint :
  forall Σ (A : structure) Hdom Hlist
    (Hcond : seq_adt_conditions Σ A Hdom Hlist)
    c1 c2 σs1 σs2 δ s
    (Hs : s ∈ Σ.(sort_symbols)) (Hδ : sort_top_symbol δ = Some s)
    (Hc1 : c1 ∈ Σ.(constructors_for_sort) s)
    (Hc2 : c2 ∈ Σ.(constructors_for_sort) s)
    (Hrank1 : monomorphic_rank Σ c1 σs1 δ)
    (Hrank2 : monomorphic_rank Σ c2 σs2 δ)
    (Hwf : sort_wf Σ δ)
    (Hσs1 : Forall (seq_embeddable_sort Σ) σs1)
    (Hσs2 : Forall (seq_embeddable_sort Σ) σs2)
    vs1 vs2,
    interp_apply A.(domain) (A.(interp) c1 σs1 δ) vs1
      = interp_apply A.(domain) (A.(interp) c2 σs2 δ) vs2 ->
    c1 = c2.
Proof.
  intros Σ A Hdom Hlist Hcond c1 c2 σs1 σs2 δ s Hs Hδ Hc1 Hc2 Hrank1 Hrank2 Hwf
    Hσs1 Hσs2 vs1 vs2 Heq.
  pose proof (seq_adt_interp_constructor Hcond c1 σs1 δ s Hs Hδ Hc1 Hrank1 Hwf Hσs1
                vs1) as H1.
  pose proof (seq_adt_interp_constructor Hcond c2 σs2 δ s Hs Hδ Hc2 Hrank2 Hwf Hσs2
                vs2) as H2.
  simpl in H1, H2.
  set (P1 := Hdom δ (adt_intro Σ δ s c1 Hs Hδ Hc1 Hwf)) in *.
  set (P2 := Hdom δ (adt_intro Σ δ s c2 Hs Hδ Hc2 Hwf)) in *.
  assert (Hcast : cast P1 (interp_apply A.(domain) (A.(interp) c1 σs1 δ) vs1)
               = cast P1 (interp_apply A.(domain) (A.(interp) c2 σs2 δ) vs2))
    by (f_equal; exact Heq).
  assert (HP : P1 = P2) by (unfold P1, P2; f_equal; apply adt_irrelevant).
  rewrite H1, HP, H2 in Hcast.
  pose proof (f_equal seq_ground_term_constructor Hcast) as Hcc. simpl in Hcc.
  now injection Hcc.
Qed.

Arguments seq_adt_interp_constructor_disjoint {_} {_} {_} {_}.

(** [constructor_args_embeddable] as this file extends it.  Unlike there,
    the no-junk clause needs it too: [SGSeq σ []] is a ground term at [τ_seq σ]
    for every σ, so a constructor's argument sorts cannot be recovered from the
    term the way [embeddable_sort_of_ground_term] recovers them in the
    standard's reading.  They are read off the signature instead. *)
Definition constructor_args_seq_embeddable (Σ : signature) : Prop :=
  forall c σs δ s,
    s ∈ Σ.(sort_symbols) ->
    sort_top_symbol δ = Some s ->
    c ∈ Σ.(constructors_for_sort) s ->
    monomorphic_rank Σ c σs δ ->
    Forall (seq_embeddable_sort Σ) σs.

(** The way in to [adt_constructed], and so to [eval_total] and to every
    consequence [SMTLIB.Theory] proves against the tester condition.  The
    stratification is a premise here rather than part of [seq_adt_axioms]: a
    signature condition inside a model predicate would make the theory silently
    modelless where it fails. *)
Theorem adt_constructed_of_seq_adt_axioms :
  forall Σ (A : structure),
    seq_sorts_not_adt Σ ->
    constructor_args_seq_embeddable Σ ->
    seq_adt_axioms Σ A -> adt_constructed Σ A.
Proof.
  intros Σ A Hseq_not_adt Hiv (Hdom & Hlist & Hcond). constructor.
  - intros δ v Hδ.
    (* the domain of a datatype sort is the ground terms at that sort; a leaf
       is not a datatype element, and a sequence sort is not a datatype sort *)
    destruct (cast (Hdom δ Hδ) v)
      as [σ0 [Hfree Hns] x | σ0 gs | c σs δ' s Hs Hhead Hc Hrank Hwf vs] eqn:Hg.
    + destruct (adt_free_not_adt Σ σ0 Hfree Hδ).
    + exfalso. exact (Hseq_not_adt σ0 Hδ).
    + pose proof (Hiv c σs δ' s Hs Hhead Hc Hrank) as Hσs.
      exists c, σs, s,
        (hlist_map (seq_ground_term_project Σ A Hdom Hlist) vs).
      split_and!; try assumption.
      pose proof (seq_adt_interp_constructor Hcond c σs δ' s Hs Hhead Hc Hrank Hwf
                    Hσs
                    (hlist_map (seq_ground_term_project Σ A Hdom Hlist) vs))
        as Hconstr.
      simpl in Hconstr.
      rewrite (hlist_map_seq_embed_project Σ Hseq_not_adt A Hdom Hlist)
        in Hconstr.
      rewrite (adt_irrelevant _ _ (adt_intro Σ δ' s c Hs Hhead Hc Hwf) Hδ)
        in Hconstr.
      rewrite <- Hg in Hconstr.
      apply (f_equal (cast_sym (Hdom δ' Hδ))) in Hconstr.
      rewrite !cast_sym_cast in Hconstr.
      exact Hconstr.
  - intros c1 c2 σs1 σs2 δ s Hs Hδ Hc1 Hc2 Hrank1 Hrank2 Hwf vs1 vs2 Heq.
    eapply (seq_adt_interp_constructor_disjoint Hcond c1 c2 σs1 σs2 δ s
              Hs Hδ Hc1 Hc2 Hrank1 Hrank2 Hwf
              (Hiv c1 σs1 δ s Hs Hδ Hc1 Hrank1)
              (Hiv c2 σs2 δ s Hs Hδ Hc2 Hrank2)).
    exact Heq.
Qed.

(** ** Closing a Pretheory with the Extended Reading *)

(** [theory_init]'s counterpart: same place in the stack, same obligation, read
    through [seq_ground_term].  A theory that wants datatypes nested under
    sequences opts in by closing with this instead, which is the whole of the
    extension described at the head of this section. *)
Definition theory_init_seq (P : pretheory) : theory :=
  {|
    Σ := P.(pΣ);
    models A := P.(pmodels) A /\ seq_adt_axioms P.(pΣ) A;
  |}.

(** ** Interpreting the Datatype Symbols *)

(** [seq_adt_axioms] can be met.  Over a domain satisfying its two domain
    equations, constructors build the term they name, selectors read an
    argument back off it, and testers look at its head; every other symbol,
    and every rank the conditions say nothing about, falls through to a base
    interpretation, which is what lets this be laid over the interpretation of
    the rest of a theory. *)

Section SeqAdtInterp.

  Context (Σ : signature) (Hseq_not_adt : seq_sorts_not_adt Σ).
  Context (D : sort -> Type).
  Context (Hbool : D σ_bool = bool).
  Context (Hmap : forall σ1 σ2, D (τ_map σ1 σ2) = (D σ1 -> D σ2)).
  Context (Hdom : forall δ, adt Σ δ -> D δ = seq_ground_term Σ (fun σ _ => D σ) δ).
  Context (Hlist : forall σ, D (τ_seq σ) = list (D σ)).
  Context (base : forall (f : func) σs σ, interpretation D σs σ).

  (* The crossing into the term algebra reads nothing of a structure but its
     domain, so any structure over [D] serves to state it. *)
  Local Notation A0 := (structure_of D Hbool Hmap base).
  Local Notation G := (seq_ground_term Σ (fun σ _ => D σ)).

  (** Everything [SGConstr] needs to build a term at [c : σs → δ].  A sort
      has at most one top symbol, so it is read off [δ] rather than
      quantified. *)
  Definition seq_constructor_rank_ok (c : func) (σs : list sort) (δ : sort)
    : Prop :=
    default s_bool (sort_top_symbol δ) ∈ Σ.(sort_symbols)
    /\ sort_top_symbol δ = Some (default s_bool (sort_top_symbol δ))
    /\ c ∈ Σ.(constructors_for_sort) (default s_bool (sort_top_symbol δ))
    /\ monomorphic_rank Σ c σs δ
    /\ sort_wf Σ δ
    /\ Forall (seq_embeddable_sort Σ) σs.

  Definition seq_constructor_interp (c : func) (σs : list sort) (δ : sort)
    : interpretation D σs δ :=
    match excluded_middle_informative (seq_constructor_rank_ok c σs δ) with
    | left (conj Hs (conj Hδ (conj Hc (conj Hrank (conj Hwf Hσs))))) =>
        interp_curry D (fun vs =>
          cast_sym (Hdom δ (adt_intro Σ δ _ c Hs Hδ Hc Hwf))
            (SGConstr c σs δ _ Hs Hδ Hc Hrank Hwf
               (hlist_map_seq_embed Σ A0 Hdom Hlist vs Hσs)))
    | right _ => base c σs δ
    end.

  (** The argument [g] selects, when [v] is built by a constructor listing
      [g] among its selectors and that argument has sort [σ]. *)
  Definition seq_selector_value (g : func) (δ σ : sort) (v : D δ) : D σ :=
    let junk := base g [δ] σ v in
    match decide (adt Σ δ) with
    | left H =>
        match cast (Hdom δ H) v with
        | SGConstr c _ _ _ _ _ _ _ _ ws =>
            match list_find (fun g' => g' = g) (Σ.(selectors_for_constructor) c) with
            | Some (i, _) =>
                match hlist_lookup G ws i with
                | Some (existT σ' w) =>
                    match decide (σ' = σ) with
                    | left e =>
                        seq_ground_term_project Σ A0 Hdom Hlist σ
                          (eq_rect σ' G w σ e)
                    | right _ => junk
                    end
                | None => junk
                end
            | None => junk
            end
        | _ => junk
        end
    | right _ => junk
    end.

  (** Whether [v] is built by the constructor [p] tests for. *)
  Definition seq_tester_value (p : func) (δ : sort) (v : D δ) : bool :=
    match decide (adt Σ δ) with
    | left H =>
        bool_decide (seq_ground_term_constructor (cast (Hdom δ H) v)
                     = Some (Σ.(constructor_for_tester) p))
    | right _ => false
    end.

  Definition seq_selector_interp (g : func) (σs : list sort) (σ : sort)
    : interpretation D σs σ :=
    match σs return interpretation D σs σ with
    | [δ] => seq_selector_value g δ σ
    | σs' => base g σs' σ
    end.

  Definition seq_tester_interp (p : func) (σs : list sort) (σ : sort)
    : interpretation D σs σ :=
    match σs return interpretation D σs σ with
    | [δ] =>
        match decide (σ = σ_bool) with
        | left e =>
            fun v => cast_sym (eq_trans (f_equal D e) Hbool) (seq_tester_value p δ v)
        | right _ => base p [δ] σ
        end
    | σs' => base p σs' σ
    end.

  Definition seq_adt_interpretation (f : func) (σs : list sort) (σ : sort)
    : interpretation D σs σ :=
    if decide (f ∈ Σ.(constructors)) then seq_constructor_interp f σs σ
    else if decide (f ∈ Σ.(selectors)) then seq_selector_interp f σs σ
    else if decide (f ∈ Σ.(testers)) then seq_tester_interp f σs σ
    else base f σs σ.

  Local Notation A := (structure_of D Hbool Hmap seq_adt_interpretation).

  Lemma seq_adt_interpretation_constructor : forall c σs σ,
      c ∈ Σ.(constructors) -> seq_adt_interpretation c σs σ = seq_constructor_interp c σs σ.
  Proof. intros c σs σ Hc. unfold seq_adt_interpretation. by rewrite decide_True. Qed.

  Lemma seq_adt_interpretation_selector : forall g σs σ,
      g ∈ Σ.(selectors) -> seq_adt_interpretation g σs σ = seq_selector_interp g σs σ.
  Proof.
    intros g σs σ Hg. unfold seq_adt_interpretation.
    rewrite decide_False by (pose proof Σ.(selectors_disj); set_solver).
    by rewrite decide_True.
  Qed.

  Lemma seq_adt_interpretation_tester : forall p σs σ,
      p ∈ Σ.(testers) -> seq_adt_interpretation p σs σ = seq_tester_interp p σs σ.
  Proof.
    intros p σs σ Hp. unfold seq_adt_interpretation.
    pose proof Σ.(testers_disj) as [Hpc Hpg].
    rewrite decide_False by set_solver. rewrite decide_False by set_solver.
    by rewrite decide_True.
  Qed.

  (** At a rank it can build a term at, a constructor builds that term. *)
  Lemma seq_constructor_interp_apply :
    forall c σs δ s Hs Hδ Hc Hrank Hwf Hσs (vs : hlist D σs),
      interp_apply D (seq_constructor_interp c σs δ) vs
      = cast_sym (Hdom δ (adt_intro Σ δ s c Hs Hδ Hc Hwf))
          (SGConstr c σs δ s Hs Hδ Hc Hrank Hwf
             (hlist_map_seq_embed Σ A0 Hdom Hlist vs Hσs)).
  Proof.
    intros c σs δ s Hs Hδ Hc Hrank Hwf Hσs vs.
    unfold seq_constructor_interp.
    destruct (excluded_middle_informative _)
      as [(Hs' & Hδ' & Hc' & Hrank' & Hwf' & Hσs') | Hno].
    - rewrite interp_apply_curry.
      assert (Es : default s_bool (sort_top_symbol δ) = s) by (rewrite Hδ; reflexivity).
      subst s.
      by rewrite (proof_irrelevance _ Hs' Hs), (proof_irrelevance _ Hδ' Hδ),
        (proof_irrelevance _ Hc' Hc), (proof_irrelevance _ Hrank' Hrank),
        (proof_irrelevance _ Hwf' Hwf), (proof_irrelevance _ Hσs' Hσs).
    - exfalso. apply Hno. unfold seq_constructor_rank_ok. rewrite Hδ. cbn.
      split_and!; done.
  Qed.

  Theorem seq_adt_interpretation_other : forall f σs σ,
      f ∉ Σ.(constructors) -> f ∉ Σ.(selectors) -> f ∉ Σ.(testers) ->
      seq_adt_interpretation f σs σ = base f σs σ.
  Proof.
    intros f σs σ Hc Hg Hp. unfold seq_adt_interpretation.
    by rewrite !decide_False.
  Qed.

  (** Two conditions on the signature, both about its constructors: every
      rank of a constructor is one [SGConstr] can build a term at, and no
      constructor lists a selector twice.  Each is needed.  A rank of the
      first kind that failed would have its selectors read back arguments
      from an application nothing pins, and a selector listed twice would
      have to return two arguments at once. *)
  Context (Hranks : forall c σs δ,
              c ∈ Σ.(constructors) -> monomorphic_rank Σ c σs δ ->
              seq_constructor_rank_ok c σs δ).
  Context (Hsel_nodup : forall c,
              c ∈ Σ.(constructors) -> NoDup (Σ.(selectors_for_constructor) c)).

  Theorem seq_adt_interpretation_conditions : seq_adt_conditions Σ A Hdom Hlist.
  Proof.
    constructor.
    - (* constructors *)
      intros c σs δ s Hs Hδ Hc Hrank Hwf Hσs C vs. unfold C.
      cbn [interp structure_of].
      rewrite seq_adt_interpretation_constructor
        by (eapply Σ.(constructors_for_sort_wf); eassumption).
      rewrite (seq_constructor_interp_apply c σs δ s Hs Hδ Hc Hrank Hwf Hσs).
      rewrite cast_cast_sym.
      (* the crossing reads only the domain, which [A0] and [A] share *)
      reflexivity.
    - (* selectors *)
      intros c σs δ i g σi vi Hc Hrank _ Hg G' vs Hvi C. unfold G', C.
      cbn [interp structure_of domain].
      assert (Hgsel : g ∈ Σ.(selectors)).
      { apply (Σ.(selectors_for_constructor_wf) c Hc), elem_of_list_to_set.
        eapply list_elem_of_lookup_2. exact Hg. }
      rewrite seq_adt_interpretation_selector by exact Hgsel.
      rewrite seq_adt_interpretation_constructor by exact Hc.
      destruct (Hranks c σs δ Hc Hrank) as (Hs & Hδ & Hcs & _ & Hwf & Hσs).
      rewrite (seq_constructor_interp_apply c σs δ _ Hs Hδ Hcs Hrank Hwf Hσs).
      cbn [seq_selector_interp]. unfold seq_selector_value.
      destruct (decide (adt Σ δ)) as [H | H];
        [| exfalso; exact (H (adt_intro Σ δ _ c Hs Hδ Hcs Hwf))].
      rewrite (adt_irrelevant _ _ H (adt_intro Σ δ _ c Hs Hδ Hcs Hwf)), cast_cast_sym.
      cbn.
      assert (Hfind : list_find (λ g', g' = g) (Σ.(selectors_for_constructor) c)
                      = Some (i, g)).
      { apply list_find_Some. split_and!; [exact Hg | reflexivity |].
        intros j y Hj Hji ->.
        pose proof (NoDup_lookup _ _ _ _ (Hsel_nodup c Hc) Hj Hg). lia. }
      rewrite Hfind.
      assert (Hσi : σs !! i = Some σi) by (eapply hlist_lookup_Some_1; exact Hvi).
      assert (Hi : seq_embeddable_sort Σ σi) by (eapply Forall_lookup_1; eassumption).
      pose proof (hlist_lookup_seq_embed Σ A0 Hdom Hlist σs vs Hσs i σi vi Hi Hvi)
        as Hlk.
      change (seq_ground_term Σ (seq_domain_gen Σ A0)) with G in Hlk.
      rewrite Hlk.
      destruct (decide (σi = σi)) as [e | Hne]; [| contradiction].
      rewrite (Eqdep_dec.UIP_dec (fun x y => decide (x = y)) e eq_refl).
      cbn [eq_rect].
      exact (seq_ground_term_project_embed Σ Hseq_not_adt A0 Hdom Hlist σi Hi vi).
    - (* testers *)
      intros c σs δ Hc Hrank P C v. unfold P, C.
      cbn [interp structure_of domain domain_σ_bool].
      pose proof (Σ.(tester_for_constructor_wf) c Hc) as Hp.
      rewrite seq_adt_interpretation_tester by exact Hp.
      cbn [seq_tester_interp].
      destruct (decide (σ_bool = σ_bool)) as [e | Hne]; [| contradiction].
      rewrite (Eqdep_dec.UIP_dec (fun x y => decide (x = y)) e eq_refl).
      rewrite eq_trans_refl_l, cast_cast_sym.
      unfold seq_tester_value. rewrite (Σ.(constructor_tester_bijection) c Hc).
      split.
      + destruct (decide (adt Σ δ)) as [H | H]; [| discriminate].
        intros Hb. apply bool_decide_eq_true_1 in Hb.
        destruct (seq_ground_term_constructor_Some _ _ δ _ c Hb)
          as (σs' & s & Hs & Hδ & Hcs & Hrank' & Hwf & ws & Hg).
        assert (σs' = σs) as ->
          by (eapply monomorphic_rank_constructor_args_eq; eauto).
        exists (hlist_map (seq_ground_term_project Σ A0 Hdom Hlist) ws).
        destruct (Hranks c σs δ Hc Hrank') as (_ & _ & _ & _ & _ & Hσs).
        rewrite seq_adt_interpretation_constructor by exact Hc.
        rewrite (seq_constructor_interp_apply c σs δ s Hs Hδ Hcs Hrank' Hwf Hσs).
        rewrite (hlist_map_seq_embed_project Σ Hseq_not_adt A0 Hdom Hlist σs ws Hσs).
        rewrite (adt_irrelevant _ _ (adt_intro Σ δ s c Hs Hδ Hcs Hwf) H).
        transitivity (cast_sym (Hdom δ H) (cast (Hdom δ H) v));
          [by rewrite Hg | apply cast_sym_cast].
      + intros (vs & <-).
        rewrite seq_adt_interpretation_constructor by exact Hc.
        destruct (Hranks c σs δ Hc Hrank) as (Hs & Hδ & Hcs & _ & Hwf & Hσs).
        rewrite (seq_constructor_interp_apply c σs δ _ Hs Hδ Hcs Hrank Hwf Hσs).
        destruct (decide (adt Σ δ)) as [H | H];
          [| exfalso; exact (H (adt_intro Σ δ _ c Hs Hδ Hcs Hwf))].
        rewrite (adt_irrelevant _ _ H (adt_intro Σ δ _ c Hs Hδ Hcs Hwf)), cast_cast_sym.
        by apply bool_decide_eq_true_2.
  Qed.

  Corollary seq_adt_interpretation_axioms : seq_adt_axioms Σ A.
  Proof.
    exists Hdom, Hlist. exact seq_adt_interpretation_conditions.
  Qed.

End SeqAdtInterp.
