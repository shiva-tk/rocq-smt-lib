(** * SMTLIB.tests.UnitTests : The Semantics on Four Small Examples *)

(** Four questions of the kind a solver is asked, answered against the
    mechanised semantics: [1 + 1 = 2] and [x ∨ ¬x] hold in every model of the
    theory, while [0 / 0 = 4] and [f 0 = 4] hold in one.  The satisfiable pair
    is the interesting direction, since such a statement is worth exactly as
    much as the model exhibited for it.

    The theory [T_test], its domain and the model family [A_free] the
    satisfiable pair exhibits are all in [SMTLIB.tests.TestTheory]. *)

From Stdlib Require Import ZArith QArith Qcanon Reals Lra
  FunctionalExtensionality Classical_Prop.
From stdpp Require Import functions stringmap.
From SMTLIB Require Import Utils Symbols Term Sorting Signature Theory Eval
  Domain.
From SMTLIB.Theory Require Import Core Reals_Ints HO_Core.
From SMTLIB.tests Require Import TestTheory.

Open Scope smt_scope.


(** The decimals below are all integral, and spelling the two conversions out
    at each use buries the number.  [Qc_of_Z] is the rational the integer
    denotes, [decimal_of_Z] the SMT-LIB literal for it — what the standard's
    concrete syntax writes [4.0] — and [R_of_Qc] the real a rational denotes.
    All three are abbreviations, so the terms are unchanged. *)
Local Notation Qc_of_Z i := (Q2Qc (inject_Z i)).
Local Notation decimal_of_Z i := (decimal_literal (Qc_of_Z i)).
Local Notation R_of_Qc q := (Q2R (Qcanon.this q)).

(** * 1 + 1 = 2 holds in every model *)

Theorem one_plus_one_has_sort :
  Σ_test ⊢
    eq_ (plus_ (int_literal 1) (int_literal 1)) (int_literal 2) : σ_bool.
Proof.
  apply (eq_has_sort _ _ _ σ_int Σ_core_extends_Σ_test
           (monomorphic_SApp_const s_int)).
  - apply plus_has_sort_int;
      [ exact Σ_reals_ints_extends_Σ_test
      | apply int_literal_has_sort; exact Σ_reals_ints_extends_Σ_test
      | apply int_literal_has_sort; exact Σ_reals_ints_extends_Σ_test ].
  - apply int_literal_has_sort. exact Σ_reals_ints_extends_Σ_test.
Qed.

Theorem valid_one_plus_one : entails T_test ∅
      (eq_ (plus_ (int_literal 1) (int_literal 1)) (int_literal 2)).
Proof.
  intros A V (((Hcore & HZ & HR & Hri) & _) & _) _ _.
  apply holds_iff_eval; [reflexivity |].
  apply (eval_eq_true Σ_test A V σ_int _ _
           (cast_sym HZ 2%Z) (cast_sym HZ 2%Z));
    [ exact Σ_core_extends_Σ_test
    | exact Hcore
    | apply monomorphic_SApp_const
    | | | reflexivity ].
  - apply (eval_plus_int Σ_test A V HZ HR Hri _ _ 1%Z 1%Z);
      [ exact Σ_reals_ints_extends_Σ_test
      | apply (eval_int_literal Σ_test A V HZ HR Hri 1%Z);
        exact Σ_reals_ints_extends_Σ_test
      | apply (eval_int_literal Σ_test A V HZ HR Hri 1%Z);
        exact Σ_reals_ints_extends_Σ_test ].
  - apply (eval_int_literal Σ_test A V HZ HR Hri 2%Z).
    exact Σ_reals_ints_extends_Σ_test.
Qed.

Corollary sat_one_plus_one :
  sat T_test {[ eq_ (plus_ (int_literal 1) (int_literal 1)) (int_literal 2) ]}.
Proof. apply sat_of_entails. exact valid_one_plus_one. Qed.

(** * Excluded middle holds in every model *)

Theorem excluded_middle_has_sort :
  Σ_test ⊢
    TForall σ_bool (or_ (TBVar 0 0) (not_ (TBVar 0 0))) : σ_bool.
Proof.
  apply (S_TForall Σ_test ∅);
    [ apply sort_wf_σ_bool | apply monomorphic_σ_bool |].
  intros x _ t'. subst t'. simpl.
  apply or_has_sort; [exact Σ_core_extends_Σ_test | |].
  - apply S_TFVar;
      [apply signature_lookup_insert_eq | apply sort_wf_σ_bool | apply monomorphic_σ_bool].
  - apply not_has_sort; [exact Σ_core_extends_Σ_test |].
    apply S_TFVar;
      [apply signature_lookup_insert_eq | apply sort_wf_σ_bool | apply monomorphic_σ_bool].
Qed.

Theorem valid_excluded_middle : entails T_test ∅
      (TForall σ_bool (or_ (TBVar 0 0) (not_ (TBVar 0 0)))).
Proof.
  intros A V (((Hcore & _) & _) & _) _ _.
  apply holds_iff_eval; [reflexivity |].
  apply (E_TForall_true Σ_test A ∅).
  intros x _ v' t' V'. subst t' V'. simpl.
  pose proof (eval_inserted_TFVar Σ_test A V x σ_bool v') as Hx.
  apply (eval_or_true Σ_test A _ _ _ v'
           (cast_sym A.(domain_σ_bool) (negb (cast A.(domain_σ_bool) v'))));
    [ exact Σ_core_extends_Σ_test
    | exact Hcore
    | exact Hx
    | exact (eval_not Σ_test A _ _ v' Σ_core_extends_Σ_test Hcore Hx)
    | ].
  rewrite cast_cast_sym.
  destruct (cast A.(domain_σ_bool) v'); [by left | by right].
Qed.

Corollary sat_excluded_middle :
  sat T_test {[ TForall σ_bool (or_ (TBVar 0 0) (not_ (TBVar 0 0))) ]}.
Proof. apply sat_of_entails. exact valid_excluded_middle. Qed.

(** * 0 / 0 is underspecified *)

(** Reals_Ints constrains [/] only where the denominator is non-zero, so a
    model may send [0 / 0] anywhere.  Both facts below come from one proof run
    at two values of [A_free]'s parameters: that [0 / 0 = 4] is satisfiable, and
    that it is not valid, because another model answers 5. *)

Theorem zero_over_zero_has_sort : forall q,
  Σ_test ⊢
    eq_ (div_ zero_real zero_real) (decimal_literal q) : σ_bool.
Proof.
  intros q.
  apply (eq_has_sort _ _ _ σ_real Σ_core_extends_Σ_test
           (monomorphic_SApp_const s_real)).
  - apply div_has_sort;
      [ exact Σ_reals_ints_extends_Σ_test
      | apply decimal_literal_has_sort; exact Σ_reals_ints_extends_Σ_test
      | apply decimal_literal_has_sort; exact Σ_reals_ints_extends_Σ_test ].
  - apply decimal_literal_has_sort. exact Σ_reals_ints_extends_Σ_test.
Qed.

Theorem sat_zero_over_zero : forall q : Qc,
  sat T_test {[ eq_ (div_ zero_real zero_real) (decimal_literal q) ]}.
Proof.
  intros q. set (d := R_of_Qc q). set (k := 0%Z).
  exists (A_free d k), (V_free d k). split; [exact (A_free_models d k) |].
  split; [apply map_empty_subseteq |].
  intros ϕ Hϕ. apply elem_of_singleton in Hϕ as ->.
  apply holds_iff_eval; [reflexivity |].
  apply (eval_eq_true Σ_test (A_free d k) (V_free d k) σ_real _ _
           (cast_sym D_test_σ_real d) (cast_sym D_test_σ_real d));
    [ exact Σ_core_extends_Σ_test
    | exact (A_free_models_core d k)
    | apply monomorphic_SApp_const
    | exact (eval_zero_over_zero d k)
    | apply (eval_decimal_literal Σ_test (A_free d k) (V_free d k)
               D_test_σ_int D_test_σ_real (A_free_models_reals_ints d k));
      exact Σ_reals_ints_extends_Σ_test
    | reflexivity ].
Qed.

Corollary sat_zero_over_zero_is_four :
  sat T_test {[ eq_ (div_ zero_real zero_real)
                    (decimal_of_Z 4) ]}.
Proof. exact (sat_zero_over_zero (Qc_of_Z 4)). Qed.

(** Satisfiable in one model and refuted in another: that is what
    "underspecified" means, and neither test alone says it. *)
Theorem not_valid_zero_over_zero_is_four : ~ entails T_test ∅
  (eq_ (div_ zero_real zero_real) (decimal_of_Z 4)).
Proof.
  intros Hvalid.
  assert (H4 : R_of_Qc (Qc_of_Z 4) = 4%R)
    by (unfold Q2R; simpl; field).
  assert (H5 : R_of_Qc (Qc_of_Z 5) = 5%R)
    by (unfold Q2R; simpl; field).
  set (d := R_of_Qc (Qc_of_Z 5)). set (k := 0%Z).
  pose proof (Hvalid (A_free d k) (V_free d k) (A_free_models d k) (map_empty_subseteq _)
                 ltac:(intros ψ Hψ; set_solver)) as Htrue.
  apply holds_iff_eval in Htrue; [| reflexivity].
  assert (Hfalse : ⟦ eq_ (div_ zero_real zero_real)
                         (decimal_of_Z 4)
                     : σ_bool ⟧(Σ_test, A_free d k, V_free d k)
                     ⇓ cast_sym (A_free d k).(domain_σ_bool) false).
  { apply (eval_eq_false Σ_test (A_free d k) (V_free d k) σ_real _ _
             (cast_sym D_test_σ_real d)
             (cast_sym D_test_σ_real (R_of_Qc (Qc_of_Z 4))));
      [ exact Σ_core_extends_Σ_test
      | exact (A_free_models_core d k)
      | apply monomorphic_SApp_const
      | exact (eval_zero_over_zero d k)
      | apply (eval_decimal_literal Σ_test (A_free d k) (V_free d k)
                 D_test_σ_int D_test_σ_real (A_free_models_reals_ints d k));
        exact Σ_reals_ints_extends_Σ_test
      | intros Heq; apply cast_sym_inj in Heq;
        unfold d in Heq; rewrite H4, H5 in Heq; lra ]. }
  eapply cast_sym_true_neq_false.
  exact (eval_deterministic Σ_test (A_free d k) (V_free d k) σ_bool _ _ _
           (zero_over_zero_has_sort _) (map_empty_subseteq _) Htrue Hfalse).
Qed.

(** * f 0 = 4 holds in some model, for an uninterpreted f *)

Theorem uninterpreted_f_at_zero_has_sort :
  Σ_test ⊢
    eq_ (TApp f_f None [ zero_int ]) (int_literal 4) : σ_bool.
Proof.
  apply (eq_has_sort _ _ _ σ_int Σ_core_extends_Σ_test
           (monomorphic_SApp_const s_int));
    [| apply int_literal_has_sort; exact Σ_reals_ints_extends_Σ_test].
  apply (S_TApp Σ_test f_f _ [ σ_int ]).
  - apply rank_monomorphic;
      [ cbn; right; constructor | repeat constructor | repeat constructor ].
  - (* [f] has the one rank, so the unannotated application determines it *)
    intros σ' Hσ'.
    apply (monomorphic_rank_conservative Σ_uninterp) in Hσ';
      [| exact Σ_uninterp_extends_Σ_test | reflexivity].
    destruct Hσ' as (θ & τs & τ & Hrank & Hinst & _).
    inversion Hrank; subst.
    symmetry.
    exact (monomorphic_instance_of_mono θ σ_int σ'
             (monomorphic_SApp_const s_int) Hinst).
  - reflexivity.
  - intros i t_i σ_i Ht Hσ. destruct i; simpl in *; [| destruct i; discriminate].
    simplify_eq. apply int_literal_has_sort. exact Σ_reals_ints_extends_Σ_test.
Qed.

Theorem sat_uninterpreted_f_at_zero_is_four :
  sat T_test {[ eq_ (TApp f_f None [ zero_int ]) (int_literal 4) ]}.
Proof.
  set (d := 0%R). set (k := 4%Z).
  exists (A_free d k), (V_free d k). split; [exact (A_free_models d k) |].
  split; [apply map_empty_subseteq |].
  intros ϕ Hϕ. apply elem_of_singleton in Hϕ as ->.
  apply holds_iff_eval; [reflexivity |].
  apply (eval_eq_true Σ_test (A_free d k) (V_free d k) σ_int _ _
           (cast_sym D_test_σ_int k) (cast_sym D_test_σ_int 4%Z));
    [ exact Σ_core_extends_Σ_test
    | exact (A_free_models_core d k)
    | apply monomorphic_SApp_const
    | exact (eval_f_at_zero d k)
    | apply (eval_int_literal Σ_test (A_free d k) (V_free d k)
               D_test_σ_int D_test_σ_real (A_free_models_reals_ints d k) 4%Z);
      exact Σ_reals_ints_extends_Σ_test
    | reflexivity ].
Qed.

(** And another model answers 5, so the formula is contingent.  Without this
    the test above would show the freedom being used, not that it exists. *)
Theorem not_valid_uninterpreted_f_at_zero_is_four : ~ entails T_test ∅
  (eq_ (TApp f_f None [ zero_int ]) (int_literal 4)).
Proof.
  intros Hvalid.
  set (d := 0%R). set (k := 5%Z).
  pose proof (Hvalid (A_free d k) (V_free d k) (A_free_models d k) (map_empty_subseteq _)
                 ltac:(intros ψ Hψ; set_solver)) as Htrue.
  apply holds_iff_eval in Htrue; [| reflexivity].
  assert (Hfalse : ⟦ eq_ (TApp f_f None [ zero_int ]) (int_literal 4)
                     : σ_bool ⟧(Σ_test, A_free d k, V_free d k)
                     ⇓ cast_sym (A_free d k).(domain_σ_bool) false).
  { apply (eval_eq_false Σ_test (A_free d k) (V_free d k) σ_int _ _
             (cast_sym D_test_σ_int k) (cast_sym D_test_σ_int 4%Z));
      [ exact Σ_core_extends_Σ_test
      | exact (A_free_models_core d k)
      | apply monomorphic_SApp_const
      | exact (eval_f_at_zero d k)
      | apply (eval_int_literal Σ_test (A_free d k) (V_free d k)
                 D_test_σ_int D_test_σ_real (A_free_models_reals_ints d k) 4%Z);
        exact Σ_reals_ints_extends_Σ_test
      | intros Heq; apply cast_sym_inj in Heq; discriminate ]. }
  eapply cast_sym_true_neq_false.
  exact (eval_deterministic Σ_test (A_free d k) (V_free d k)
           σ_bool _ _ _ uninterpreted_f_at_zero_has_sort (map_empty_subseteq _)
           Htrue Hfalse).
Qed.

(** * 1 = 2 is unsatisfiable *)

(** The tests above establish that formulas hold; this one establishes that
    one cannot, which is what distinguishes the semantics from one that
    accepts everything.  Unsatisfiability is the whole classification: with
    [T_test] consistent, non-validity follows and needs no second proof. *)

Theorem one_eq_two_has_sort :
  Σ_test ⊢
    eq_ (int_literal 1) (int_literal 2) : σ_bool.
Proof.
  apply (eq_has_sort _ _ _ σ_int Σ_core_extends_Σ_test
           (monomorphic_SApp_const s_int));
    apply int_literal_has_sort; exact Σ_reals_ints_extends_Σ_test.
Qed.

(** Unsatisfiability is the stronger statement: no model at all, rather than
    some model where it fails. *)
Theorem not_sat_one_eq_two :
  ~ sat T_test {[ eq_ (int_literal 1) (int_literal 2) ]}.
Proof.
  intros (A & V & Hmodels & HV & Hall).
  specialize (Hall _ (elem_of_singleton_2 _ _ eq_refl)).
  apply holds_iff_eval in Hall; [| reflexivity].
  destruct Hmodels as (((Hcore & HZ & HR & Hri) & _) & _).
  destruct (eval_eq_true_inv Σ_test A V _ _
              Σ_core_extends_Σ_test Hcore Hall)
    as (δ & va & vb & Hva & Hvb & Hab).
  (* both sides are integer literals, so [δ] can only be [σ_int] *)
  assert (Hδ : δ = σ_int).
  { eapply eval_sort_of_well_sorted; [| exact HV | exact Hva].
    apply int_literal_has_sort. exact Σ_reals_ints_extends_Σ_test. }
  subst δ.
  assert (Hva' : va = cast_sym HZ 1%Z).
  { eapply (eval_deterministic Σ_test A V σ_int);
      [ apply int_literal_has_sort; exact Σ_reals_ints_extends_Σ_test
      | exact HV
      | exact Hva
      | apply (eval_int_literal Σ_test A V HZ HR Hri 1%Z);
        exact Σ_reals_ints_extends_Σ_test ]. }
  assert (Hvb' : vb = cast_sym HZ 2%Z).
  { eapply (eval_deterministic Σ_test A V σ_int);
      [ apply int_literal_has_sort; exact Σ_reals_ints_extends_Σ_test
      | exact HV
      | exact Hvb
      | apply (eval_int_literal Σ_test A V HZ HR Hri 2%Z);
        exact Σ_reals_ints_extends_Σ_test ]. }
  rewrite Hva', Hvb' in Hab.
  apply cast_sym_inj in Hab. discriminate.
Qed.

Corollary not_valid_one_eq_two : ~ ∅ ⊨[ T_test ] (eq_ (int_literal 1) (int_literal 2)).
Proof. apply not_entails_of_not_sat. exact not_sat_one_eq_two. Qed.

(** * Excluded middle at Int, and a universal that is false *)

(** [valid_excluded_middle] closes by a case split on a Rocq [bool], because
    [structure] pins every model's Bool domain to [bool].  At Int the
    bivalence has a different source — [T_reals_ints] pins the domain to [Z]
    — so the same statement holds for a reason the Bool case does not show.
    Either way the split is decidable and no classical axiom is used. *)

Theorem excluded_middle_int_has_sort :
  Σ_test ⊢
    TForall σ_int (or_ (eq_ (TBVar 0 0) zero_int)
                       (not_ (eq_ (TBVar 0 0) zero_int))) : σ_bool.
Proof.
  apply (S_TForall Σ_test ∅);
    [ apply sort_wf_Σ_test_σ_int | apply monomorphic_SApp_const |].
  intros x _ t'. subst t'. simpl.
  apply or_has_sort; [exact Σ_core_extends_Σ_test | |].
  - apply (eq_has_sort _ _ _ σ_int);
      [ exact Σ_core_extends_Σ_test
      | apply monomorphic_SApp_const
      | apply S_TFVar;
          [ apply signature_lookup_insert_eq
          | apply sort_wf_Σ_test_σ_int
          | apply monomorphic_SApp_const ]
      | apply int_literal_has_sort; exact Σ_reals_ints_extends_Σ_test ].
  - apply not_has_sort; [exact Σ_core_extends_Σ_test |].
    apply (eq_has_sort _ _ _ σ_int);
      [ exact Σ_core_extends_Σ_test
      | apply monomorphic_SApp_const
      | apply S_TFVar;
          [ apply signature_lookup_insert_eq
          | apply sort_wf_Σ_test_σ_int
          | apply monomorphic_SApp_const ]
      | apply int_literal_has_sort; exact Σ_reals_ints_extends_Σ_test ].
Qed.

Theorem valid_excluded_middle_int : entails T_test ∅
      (TForall σ_int (or_ (eq_ (TBVar 0 0) zero_int)
                          (not_ (eq_ (TBVar 0 0) zero_int)))).
Proof.
  intros A V (((Hcore & HZ & HR & Hri) & _) & _) _ _.
  apply holds_iff_eval; [reflexivity |].
  apply (E_TForall_true Σ_test A ∅).
  intros x _ v' t' V'. subst t' V'. simpl.
  (* [Z.eq_dec], not [excluded_middle_informative]: the domain at Int is [Z],
     so whether the body holds at [v'] is decidable. *)
  assert (Hbody : exists b : A.(domain) σ_bool,
             ⟦ eq_ (TFVar x) zero_int
               : σ_bool ⟧(Σ_test, A, <[x := existT _ v']> V) ⇓ b).
  { destruct (Z.eq_dec (cast HZ v') 0%Z) as [Hz | Hz].
    - exists (cast_sym A.(domain_σ_bool) true).
      apply (eval_eq_true Σ_test A _ σ_int _ _ v' (cast_sym HZ 0%Z));
        [ exact Σ_core_extends_Σ_test
        | exact Hcore
        | apply monomorphic_SApp_const
        | apply eval_inserted_TFVar
        | apply (eval_int_literal Σ_test A _ HZ HR Hri 0%Z);
          exact Σ_reals_ints_extends_Σ_test
        | by apply (cast_eq_iff_eq_cast_sym HZ) ].
    - exists (cast_sym A.(domain_σ_bool) false).
      apply (eval_eq_false Σ_test A _ σ_int _ _ v' (cast_sym HZ 0%Z));
        [ exact Σ_core_extends_Σ_test
        | exact Hcore
        | apply monomorphic_SApp_const
        | apply eval_inserted_TFVar
        | apply (eval_int_literal Σ_test A _ HZ HR Hri 0%Z);
          exact Σ_reals_ints_extends_Σ_test
        | intros Hv; apply Hz; by apply (cast_eq_iff_eq_cast_sym HZ) ]. }
  destruct Hbody as (b & Hb).
  apply (eval_or_true Σ_test A _ _ _ b
           (cast_sym A.(domain_σ_bool) (negb (cast A.(domain_σ_bool) b))));
    [ exact Σ_core_extends_Σ_test
    | exact Hcore
    | exact Hb
    | apply eval_not; [exact Σ_core_extends_Σ_test | exact Hcore | exact Hb]
    | rewrite cast_cast_sym;
      destruct (cast A.(domain_σ_bool) b); [by left | by right] ].
Qed.

Corollary sat_excluded_middle_int :
  sat T_test {[ TForall σ_int (or_ (eq_ (TBVar 0 0) zero_int)
                     (not_ (eq_ (TBVar 0 0) zero_int))) ]}.
Proof. apply sat_of_entails. exact valid_excluded_middle_int. Qed.

(** The false-quantifier rule, [E_TForall_false], read at a formula that
    exercises it: the rule carries the counterexample, and here it is 1.

    This says strictly more than [not_sat_forall_int_is_zero] below.  That
    result rules out a model making the formula *true*; this one gives a
    family where it is definitely *false*, and the gap between the two is
    bivalence.  Two constructors and [eval_deterministic] give at most one
    answer; that there is at least one is [eval_total], the half needing
    [classic] at the quantifier cases.  Object-level excluded middle is
    unaffected — [valid_excluded_middle] proves it with no axiom, because the
    Bool domain is [bool]. *)

Theorem forall_int_is_zero_has_sort :
  Σ_test ⊢
    TForall σ_int (eq_ (TBVar 0 0) zero_int) : σ_bool.
Proof.
  apply (S_TForall Σ_test ∅);
    [ apply sort_wf_Σ_test_σ_int | apply monomorphic_SApp_const |].
  intros x _ t'. subst t'. simpl.
  apply (eq_has_sort _ _ _ σ_int);
    [ exact Σ_core_extends_Σ_test
    | apply monomorphic_SApp_const
    | apply S_TFVar;
        [ apply signature_lookup_insert_eq
        | apply sort_wf_Σ_test_σ_int
        | apply monomorphic_SApp_const ]
    | apply int_literal_has_sort; exact Σ_reals_ints_extends_Σ_test ].
Qed.

Theorem eval_forall_int_is_zero_false : forall d k,
  ⟦ TForall σ_int (eq_ (TBVar 0 0) zero_int)
    : σ_bool ⟧(Σ_test, A_free d k, V_free d k)
    ⇓ cast_sym (A_free d k).(domain_σ_bool) false.
Proof.
  intros d k.
  apply (E_TForall_false Σ_test (A_free d k) ∅ (V_free d k) σ_int
           (eq_ (TBVar 0 0) zero_int) (cast_sym D_test_σ_int 1%Z)).
  intros x _ t' V'. subst t' V'. simpl.
  apply (eval_eq_false Σ_test (A_free d k) _ σ_int _ _
           (cast_sym D_test_σ_int 1%Z) (cast_sym D_test_σ_int 0%Z));
    [ exact Σ_core_extends_Σ_test
    | exact (A_free_models_core d k)
    | apply monomorphic_SApp_const
    | apply eval_inserted_TFVar
    | apply (eval_int_literal Σ_test (A_free d k) _
               D_test_σ_int D_test_σ_real (A_free_models_reals_ints d k) 0%Z);
      exact Σ_reals_ints_extends_Σ_test
    | intros Heq; apply cast_sym_inj in Heq; discriminate ].
Qed.

(** Stronger than non-validity, and the whole classification: every model
    pins Int to [Z], so every model has a non-zero element and the universal
    fails in all of them. *)
Theorem not_sat_forall_int_is_zero :
  ~ sat T_test {[ TForall σ_int (eq_ (TBVar 0 0) zero_int) ]}.
Proof.
  intros (A & V & Hmodels & HV & Hall).
  specialize (Hall _ (elem_of_singleton_2 _ _ eq_refl)).
  apply holds_iff_eval in Hall; [| reflexivity].
  destruct Hmodels as (((Hcore & HZ & HR & Hri) & _) & _).
  destruct (eval_TForall_true_inv Σ_test A V σ_int _ Hall)
    as (L & Hbody).
  (* read the body at 1, which no model can make equal to 0 *)
  pose (x := fresh_string_of_set "" L).
  assert (Hx : x ∉ L) by apply fresh_string_of_set_fresh.
  specialize (Hbody x Hx (cast_sym HZ 1%Z)). simpl in Hbody.
  destruct (eval_eq_true_inv Σ_test A _ _ _
              Σ_core_extends_Σ_test Hcore Hbody)
    as (δ & va & vb & Hva & Hvb & Hab).
  assert (Hδ : δ = σ_int).
  { eapply (eval_sort_of_well_sorted Σ_test); [| apply map_empty_subseteq | exact Hvb].
    apply int_literal_has_sort. exact Σ_reals_ints_extends_Σ_test. }
  subst δ.
  assert (Hva' : va = cast_sym HZ 1%Z).
  { (* [x] is declared only in the signature extended at it *)
    pose proof (signatures_agree_except_sorts_sym _ _
      (signatures_agree_except_sorts_insert Σ_test x σ_int)) as Hsym.
    eapply (eval_deterministic (<[x := σ_int]> Σ_test) A _ σ_int);
      [ apply S_TFVar;
          [ apply signature_lookup_insert_eq
          | apply sort_wf_Σ_test_σ_int
          | apply monomorphic_SApp_const ]
      | apply valuation_well_sorted_insert, HV
      | exact (proj1 (eval_cong_signature _ _ _ _ _ _ _ Hsym) Hva)
      | apply (eval_cong_signature _ _ _ _ _ _ _ Hsym), eval_inserted_TFVar ]. }
  assert (Hvb' : vb = cast_sym HZ 0%Z).
  { eapply (eval_deterministic Σ_test A _ σ_int);
      [ apply int_literal_has_sort; exact Σ_reals_ints_extends_Σ_test
      | apply map_empty_subseteq
      | exact Hvb
      | apply (eval_int_literal Σ_test A _ HZ HR Hri 0%Z);
        exact Σ_reals_ints_extends_Σ_test ]. }
  rewrite Hva', Hvb' in Hab.
  apply cast_sym_inj in Hab. discriminate.
Qed.

Corollary not_valid_forall_int_is_zero :
  ~ ∅ ⊨[ T_test ] (TForall σ_int (eq_ (TBVar 0 0) zero_int)).
Proof. apply not_entails_of_not_sat. exact not_sat_forall_int_is_zero. Qed.

(** * Equality at a map sort *)

(** [domain_σ_map] makes a value at [Bool ⇒ Bool] a function, so
    [models_f_eq] at that sort is equality of functions: the semantics is
    extensional without any theory saying so.  SMT-LIB's HO-Core theory asks
    for exactly that, and both solvers deliver it — on [f] and [g] at
    [(-> Int Int)], z3 5.1.0 and cvc5 1.4.0 both answer [sat] to [(= f g)] and
    to [(distinct f g)], and [unsat] to
    [(and (forall ((x Int)) (= (f x) (g x))) (distinct f g))].

    [Σ_test] declares no variables, so a term of a map sort is a lambda
    here rather than a free variable.  Nothing below leaves Core: double negation
    supplies the pointwise agreement that the third query turns into an
    equation.  Congruence, the solvers' [(= f g)] with [(distinct (f 0) (g 0))],
    needs an application term and so a signature carrying HO-Core's [@]. *)

Definition id_bool : term := TLambda σ_bool (TBVar 0 0).
Definition neg_bool : term := TLambda σ_bool (not_ (TBVar 0 0)).
Definition nn_bool : term := TLambda σ_bool (not_ (not_ (TBVar 0 0))).

Lemma monomorphic_τ_map_bool : monomorphic (τ_map σ_bool σ_bool).
Proof. constructor. repeat constructor. Qed.

(** The domain function a [Bool ⇒ Bool] lambda denotes, given the boolean
    function its body computes. *)
Definition dom_fun (A : structure) (g : bool -> bool)
  : A.(domain) σ_bool -> A.(domain) σ_bool :=
  fun b => cast_sym A.(domain_σ_bool) (g (cast A.(domain_σ_bool) b)).

Lemma eval_lambda_bool :
  forall Σ A (V : valuation A) t g,
    (forall x (b : A.(domain) σ_bool),
        ⟦ term_open 0 [ TFVar x ] t : σ_bool ⟧(Σ, A, <[x := existT _ b]> V)
          ⇓ dom_fun A g b) ->
    ⟦ TLambda σ_bool t : τ_map σ_bool σ_bool ⟧(Σ, A, V)
      ⇓ cast_sym (A.(domain_σ_map) σ_bool σ_bool) (dom_fun A g).
Proof.
  intros Σ A V t g Hbody.
  apply (E_TLambda Σ A ∅).
  intros x _ t' v' V'. subst t' V'.
  rewrite cast_cast_sym. apply Hbody.
Qed.

Lemma eval_id_bool : forall Σ A (V : valuation A),
    ⟦ id_bool : τ_map σ_bool σ_bool ⟧(Σ, A, V)
      ⇓ cast_sym (A.(domain_σ_map) σ_bool σ_bool) (dom_fun A (fun b => b)).
Proof.
  intros Σ A V. apply eval_lambda_bool. intros x b. simpl.
  unfold dom_fun. rewrite cast_sym_cast. apply eval_inserted_TFVar.
Qed.

Lemma eval_neg_bool : forall Σ A (V : valuation A),
    Σ_core ⊑ Σ ->
    models_core A ->
    ⟦ neg_bool : τ_map σ_bool σ_bool ⟧(Σ, A, V)
      ⇓ cast_sym (A.(domain_σ_map) σ_bool σ_bool) (dom_fun A negb).
Proof.
  intros Σ A V Hsub Hcore. apply eval_lambda_bool. intros x b. simpl.
  unfold dom_fun.
  apply (eval_not Σ A _ _ b Hsub Hcore).
  apply eval_inserted_TFVar.
Qed.

Lemma eval_nn_bool : forall Σ A (V : valuation A),
    Σ_core ⊑ Σ ->
    models_core A ->
    ⟦ nn_bool : τ_map σ_bool σ_bool ⟧(Σ, A, V)
      ⇓ cast_sym (A.(domain_σ_map) σ_bool σ_bool)
          (dom_fun A (fun b => negb (negb b))).
Proof.
  intros Σ A V Hsub Hcore. apply eval_lambda_bool. intros x b. simpl.
  pose proof (eval_not Σ A
                (<[x := existT _ b]> V) (TFVar x) b
                Hsub Hcore
                (eval_inserted_TFVar Σ A V x σ_bool b)) as H1.
  pose proof (eval_not Σ A
                (<[x := existT _ b]> V) (not_ (TFVar x)) _
                Hsub Hcore H1) as H2.
  rewrite cast_cast_sym in H2. unfold dom_fun. exact H2.
Qed.

(** Two lambdas denoting the same function are equal. *)
Theorem sat_fun_eq : sat T_test {[ eq_ id_bool id_bool ]}.
Proof.
  exists (A_free 0%R 0%Z), (V_free 0%R 0%Z).
  split; [exact (A_free_models 0%R 0%Z) |].
  split; [apply map_empty_subseteq |].
  intros ϕ Hϕ. apply elem_of_singleton in Hϕ as ->.
  apply holds_iff_eval; [reflexivity |].
  apply (eval_eq_true Σ_test (A_free 0%R 0%Z) _ (τ_map σ_bool σ_bool)
           id_bool id_bool _ _
           Σ_core_extends_Σ_test (A_free_models_core 0%R 0%Z)
           monomorphic_τ_map_bool (eval_id_bool _ _ _) (eval_id_bool _ _ _)).
  reflexivity.
Qed.

(** Two lambdas denoting different functions are distinct. *)
Theorem sat_fun_distinct : sat T_test {[ distinct_ id_bool neg_bool ]}.
Proof.
  exists (A_free 0%R 0%Z), (V_free 0%R 0%Z).
  split; [exact (A_free_models 0%R 0%Z) |].
  split; [apply map_empty_subseteq |].
  intros ϕ Hϕ. apply elem_of_singleton in Hϕ as ->.
  apply holds_iff_eval; [reflexivity |].
  apply (eval_distinct_true Σ_test (A_free 0%R 0%Z) _ (τ_map σ_bool σ_bool)
           id_bool neg_bool _ _
           Σ_core_extends_Σ_test (A_free_models_core 0%R 0%Z)
           monomorphic_τ_map_bool (eval_id_bool _ _ _)
           (eval_neg_bool _ _ _ Σ_core_extends_Σ_test (A_free_models_core 0%R 0%Z))).
  (* they differ at [true] *)
  intros Heq. apply cast_sym_inj in Heq.
  apply (f_equal (fun F => F (cast_sym (A_free 0%R 0%Z).(domain_σ_bool) true)))
    in Heq.
  unfold dom_fun in Heq. rewrite !cast_cast_sym in Heq.
  apply cast_sym_inj in Heq. discriminate.
Qed.

(** Pointwise agreement of two lambdas is an equation between them.  This is
    the solvers' extensionality answer, and it is where the semantics spends
    [functional_extensionality]: the two values are literal functions. *)
Theorem valid_fun_ext : ∅ ⊨[ T_test ] (eq_ id_bool nn_bool).
Proof.
  intros A V (((Hcore & _) & _) & _) _ _.
  apply holds_iff_eval; [reflexivity |].
  apply (eval_eq_true Σ_test A _ (τ_map σ_bool σ_bool) id_bool nn_bool _ _
           Σ_core_extends_Σ_test Hcore monomorphic_τ_map_bool
           (eval_id_bool _ _ _) (eval_nn_bool _ _ _ Σ_core_extends_Σ_test Hcore)).
  f_equal. apply functional_extensionality. intros b.
  unfold dom_fun. by rewrite Bool.negb_involutive.
Qed.

(** * Congruence, in a theory that can apply a function *)

(** [Σ_test] has no application symbol, so the queries above can compare two
    function values but never apply one.  [T_ho] is Core composed with
    HO-Core, which adds [@].  Equal functions then agree at every argument,
    which is what the solvers report by answering [unsat] to [(= f g)] taken
    together with [(distinct (f 0) (g 0))]. *)

Lemma eval_app_lambda :
  forall Σ A (V : valuation A) t g,
    Σ_core ⊑ Σ ->
    Σ_ho_core ⊑ Σ ->
    models_core A ->
    models_ho_core A ->
    ⟦ TLambda σ_bool t : τ_map σ_bool σ_bool ⟧(Σ, A, V)
      ⇓ cast_sym (A.(domain_σ_map) σ_bool σ_bool) (dom_fun A g) ->
    ⟦ app_ (TLambda σ_bool t) true_ : σ_bool ⟧(Σ, A, V)
      ⇓ cast_sym A.(domain_σ_bool) (g true).
Proof.
  intros Σ A V t g Hsub Hsub_ho Hcore Hho Hlam.
  pose proof (eval_app Σ A V σ_bool σ_bool (TLambda σ_bool t) true_ _ _
                Hsub_ho Hho monomorphic_σ_bool monomorphic_σ_bool
                Hlam (eval_true_true Σ A V Hsub Hcore)) as Happ.
  rewrite cast_cast_sym in Happ. unfold dom_fun in Happ.
  by rewrite cast_cast_sym in Happ.
Qed.

Definition V_ho : valuation A_ho := ∅.

(** The lambdas of the previous section, in the theory that can apply them. *)
Theorem valid_ho_ext : ∅ ⊨[ T_ho ] (eq_ id_bool nn_bool).
Proof.
  intros A V ((Hcore & Hho) & _) _ _.
  apply holds_iff_eval; [reflexivity |].
  apply (eval_eq_true Σ_ho A _ (τ_map σ_bool σ_bool) id_bool nn_bool _ _
           Σ_core_extends_Σ_ho Hcore monomorphic_τ_map_bool
           (eval_id_bool _ _ _)
           (eval_nn_bool _ _ _ Σ_core_extends_Σ_ho Hcore)).
  f_equal. apply functional_extensionality. intros b.
  unfold dom_fun. by rewrite Bool.negb_involutive.
Qed.

(** Congruence: applying the two to the same argument gives the same value. *)
Theorem valid_ho_app :
  ∅ ⊨[ T_ho ] (eq_ (app_ id_bool true_) (app_ nn_bool true_)).
Proof.
  intros A V ((Hcore & Hho) & _) _ _.
  apply holds_iff_eval; [reflexivity |].
  apply (eval_eq_true Σ_ho A _ σ_bool
           (app_ id_bool true_) (app_ nn_bool true_) _ _
           Σ_core_extends_Σ_ho Hcore monomorphic_σ_bool
           (eval_app_lambda Σ_ho A _ _ (fun b => b)
              Σ_core_extends_Σ_ho Σ_ho_core_extends_Σ_ho Hcore Hho
              (eval_id_bool _ _ _))
           (eval_app_lambda Σ_ho A _ _ (fun b => negb (negb b))
              Σ_core_extends_Σ_ho Σ_ho_core_extends_Σ_ho Hcore Hho
              (eval_nn_bool _ _ _ Σ_core_extends_Σ_ho Hcore))).
  reflexivity.
Qed.

Corollary sat_ho_app :
  sat T_ho {[ eq_ (app_ id_bool true_) (app_ nn_bool true_) ]}.
Proof.
  exists A_ho, V_ho. split; [exact A_ho_models |]. split; [apply map_empty_subseteq |].
  intros ϕ Hϕ. apply elem_of_singleton in Hϕ as ->.
  apply (valid_ho_app A_ho V_ho A_ho_models (map_empty_subseteq _)).
  intros ψ Hψ. by apply not_elem_of_empty in Hψ.
Qed.

(** * A formula with a sort parameter *)

(** [(∀ x:A. x = x)] writes the parameter [A], so it means all its instances
    ([holds]): one for each monomorphic sort [T_test] has.  Each instance is
    reflexivity at that sort, which every model of Core satisfies. *)
Definition refl_A : term := TForall τ_A (eq_ (TBVar 0 0) (TBVar 0 0)).

(** It has no sort itself: the sorting judgment is monomorphic, and a
    well-sorted term writes no parameter. *)
Theorem refl_A_not_well_sorted : forall σ, ~ (Σ_test ⊢ refl_A : σ).
Proof.
  intros σ Hsort. apply term_has_sort_pars_empty in Hsort.
  simpl in Hsort. set_solver.
Qed.

Theorem valid_refl_A : ∅ ⊨[ T_test ] refl_A.
Proof.
  intros A V (((Hcore & _) & _) & _) _ _ θ [Hdom Hθ].
  (* the one parameter, and the monomorphic sort this instance gives it *)
  assert (Hu : u_A ∈ dom θ) by (rewrite Hdom; simpl; set_solver).
  apply elem_of_dom in Hu as [σ Hσ].
  destruct (Hθ u_A σ Hσ) as [_ Hmono].
  unfold refl_A. simpl. rewrite Hσ.
  apply (E_TForall_true Σ_test A ∅).
  intros x _ v' t' V'. subst t' V'. simpl.
  apply (eval_eq_true Σ_test A _ σ _ _ v' v');
    [ exact Σ_core_extends_Σ_test | exact Hcore | exact Hmono
    | apply eval_inserted_TFVar | apply eval_inserted_TFVar | reflexivity ].
Qed.

Corollary sat_refl_A : sat T_test {[ refl_A ]}.
Proof. apply sat_of_entails. exact valid_refl_A. Qed.

(** * Refutation fails for a formula with a sort parameter *)

(** "Every sort has at most two elements", [(∀ x y z:A. ¬(x ≠ y ∧ x ≠ z ∧
    y ≠ z))], is false at Int in every model, so it is not valid.  Its
    negation is not satisfiable either: that would need every instance of the
    negation to hold in one model, and the one at Bool fails.  So for a
    formula writing a sort parameter, validity is not unsatisfiability of the
    negation, which §2.1 of the standard asserts for any class of formulae
    closed under negation.  Asserting [¬ϕ] asserts every instance of [¬ϕ],
    which is not the negation of asserting every instance of [ϕ]. *)
Definition at_most_two_body (x y z : term) : term :=
  not_ (and_ (not_ (eq_ x y)) (and_ (not_ (eq_ x z)) (not_ (eq_ y z)))).

Definition at_most_two (τ : sort) : term :=
  TForall τ (TForall τ (TForall τ
    (at_most_two_body (TBVar 2 0) (TBVar 1 0) (TBVar 0 0)))).

Lemma term_sort_subst_at_most_two : forall θ σ,
    θ !! u_A = Some σ -> term_sort_subst θ (at_most_two τ_A) = at_most_two σ.
Proof. intros θ σ Hσ. simpl. by rewrite Hσ. Qed.

Lemma monomorphic_sort_subst_at_most_two : forall σ,
    sort_wf Σ_test σ -> monomorphic σ ->
    monomorphic_sort_subst Σ_test (at_most_two τ_A) {[ u_A := σ ]}.
Proof.
  intros σ Hwf Hmono. split.
  - rewrite dom_singleton_L. simpl. set_solver.
  - by apply map_Forall_singleton.
Qed.

Lemma at_most_two_has_sort : forall σ,
    sort_wf Σ_test σ -> monomorphic σ ->
    Σ_test ⊢ at_most_two σ : σ_bool.
Proof.
  intros σ Hwf Hmono.
  apply (S_TForall Σ_test ∅); [exact Hwf | exact Hmono |].
  intros x _ t'. subst t'. simpl.
  apply (S_TForall _ {[x]}); [exact Hwf | exact Hmono |].
  intros y Hy t'. subst t'. simpl.
  apply (S_TForall _ {[x; y]}); [exact Hwf | exact Hmono |].
  intros z Hz t'. subst t'. simpl.
  assert (Hxy : x ≠ y) by set_solver. assert (Hxz : x ≠ z) by set_solver.
  assert (Hyz : y ≠ z) by set_solver.
  unfold at_most_two_body.
  repeat first [ apply not_has_sort; [exact Σ_core_extends_Σ_test |]
               | apply and_has_sort; [exact Σ_core_extends_Σ_test | |]
               | apply (eq_has_sort _ _ _ σ); [exact Σ_core_extends_Σ_test | exact Hmono | |];
                 (apply S_TFVar;
                   [ rewrite ?signature_lookup_insert_ne by congruence;
                     apply signature_lookup_insert_eq
                   | exact Hwf | exact Hmono ]) ].
Qed.

(** The body's value is whether two of its three values coincide. *)
Lemma eval_at_most_two_body : forall A (V : valuation A) x y z σ
    (a b c : A.(domain) σ),
    models_core A -> monomorphic σ ->
    V !! x = Some (existT σ a) -> V !! y = Some (existT σ b) ->
    V !! z = Some (existT σ c) ->
    exists e, ⟦ at_most_two_body (TFVar x) (TFVar y) (TFVar z)
                : σ_bool ⟧(Σ_test, A, V) ⇓ cast_sym A.(domain_σ_bool) e
              /\ (e = true <-> a = b \/ a = c \/ b = c).
Proof.
  intros A V x y z σ a b c Hcore Hmono Hx Hy Hz.
  (* each equation's value is whether its two values coincide, which is
     classical: nothing decides equality on an arbitrary domain *)
  assert (Heq : forall u w (vu vw : A.(domain) σ),
             V !! u = Some (existT σ vu) -> V !! w = Some (existT σ vw) ->
             exists e, ⟦ eq_ (TFVar u) (TFVar w) : σ_bool ⟧(Σ_test, A, V)
                         ⇓ cast_sym A.(domain_σ_bool) e
                       /\ (e = true <-> vu = vw)).
  { intros u w vu vw Hu Hw. destruct (classic (vu = vw)) as [<- | Hne].
    - exists true. split; [| tauto].
      apply (eval_eq_true Σ_test A V σ _ _ vu vu);
        [ exact Σ_core_extends_Σ_test | exact Hcore | exact Hmono
        | by apply E_TFVar | by apply E_TFVar | reflexivity ].
    - exists false. split; [| split; [discriminate | contradiction]].
      apply (eval_eq_false Σ_test A V σ _ _ vu vw);
        [ exact Σ_core_extends_Σ_test | exact Hcore | exact Hmono
        | by apply E_TFVar | by apply E_TFVar | exact Hne ]. }
  destruct (Heq x y a b Hx Hy) as (e1 & He1 & Hab).
  destruct (Heq x z a c Hx Hz) as (e2 & He2 & Hac).
  destruct (Heq y z b c Hy Hz) as (e3 & He3 & Hbc).
  exists (negb (negb e1 && (negb e2 && negb e3))). split.
  - pose proof (eval_not Σ_test A V _ _ Σ_core_extends_Σ_test Hcore He1) as Hn1.
    pose proof (eval_not Σ_test A V _ _ Σ_core_extends_Σ_test Hcore He2) as Hn2.
    pose proof (eval_not Σ_test A V _ _ Σ_core_extends_Σ_test Hcore He3) as Hn3.
    rewrite cast_cast_sym in Hn1, Hn2, Hn3.
    pose proof (eval_and Σ_test A V _ _ _ _ Σ_core_extends_Σ_test Hcore Hn2 Hn3)
      as Ha23.
    pose proof (eval_and Σ_test A V _ _ _ _ Σ_core_extends_Σ_test Hcore Hn1 Ha23)
      as Ha.
    pose proof (eval_not Σ_test A V _ _ Σ_core_extends_Σ_test Hcore Ha) as Hn.
    rewrite cast_cast_sym in Hn. exact Hn.
  - destruct e1, e2, e3; simpl; naive_solver.
Qed.

Theorem not_valid_at_most_two : ~ ∅ ⊨[ T_test ] (at_most_two τ_A).
Proof.
  intros Hvalid. set (d := 0%R). set (k := 0%Z).
  pose proof (Hvalid (A_free d k) (V_free d k) (A_free_models d k)
                (map_empty_subseteq _) ltac:(intros ψ Hψ; set_solver)) as Hholds.
  specialize (Hholds _ (monomorphic_sort_subst_at_most_two σ_int
                          sort_wf_Σ_test_σ_int
                          (monomorphic_SApp_const s_int))).
  rewrite (term_sort_subst_at_most_two _ σ_int) in Hholds
    by apply lookup_singleton_eq.
  (* the instance at Int is false, witnessed by 0, 1 and 2 *)
  assert (Hfalse : ⟦ at_most_two σ_int
                     : σ_bool ⟧(Σ_test, A_free d k, V_free d k)
                     ⇓ cast_sym (A_free d k).(domain_σ_bool) false).
  { apply (E_TForall_false Σ_test (A_free d k) ∅ _ _ _
             (cast_sym D_test_σ_int 0%Z)).
    intros x _ t' V'. subst t' V'. simpl.
    apply (E_TForall_false Σ_test (A_free d k) {[x]} _ _ _
             (cast_sym D_test_σ_int 1%Z)).
    intros y Hy t' V'. subst t' V'. simpl.
    apply (E_TForall_false Σ_test (A_free d k) {[x; y]} _ _ _
             (cast_sym D_test_σ_int 2%Z)).
    intros z Hz t' V'. subst t' V'. simpl.
    assert (Hxy : x ≠ y) by set_solver. assert (Hxz : x ≠ z) by set_solver.
    assert (Hyz : y ≠ z) by set_solver.
    match goal with
    | |- ⟦ _ : _ ⟧(_, _, ?V) ⇓ _ =>
        destruct (eval_at_most_two_body (A_free d k) V x y z σ_int
                    (cast_sym D_test_σ_int 0%Z) (cast_sym D_test_σ_int 1%Z)
                    (cast_sym D_test_σ_int 2%Z) (A_free_models_core d k)
                    (monomorphic_SApp_const s_int))
          as (e & He & Hiff);
          [by simplify_map_eq | by simplify_map_eq | by simplify_map_eq |]
    end.
    destruct e; [| exact He].
    exfalso. destruct (proj1 Hiff eq_refl) as [Heq | [Heq | Heq]];
      apply cast_sym_inj in Heq; discriminate. }
  pose proof (eval_deterministic Σ_test (A_free d k) (V_free d k)
                σ_bool _ _ _
                (at_most_two_has_sort σ_int sort_wf_Σ_test_σ_int
                   (monomorphic_SApp_const s_int))
                (map_empty_subseteq _) Hholds Hfalse) as Hc.
  exact (cast_sym_true_neq_false _ Hc).
Qed.

Theorem not_sat_not_at_most_two : ~ sat T_test {[ not_ (at_most_two τ_A) ]}.
Proof.
  intros (A & V & Hmodels & HV & Hall).
  specialize (Hall _ (elem_of_singleton_2 _ _ eq_refl)).
  destruct Hmodels as (((Hcore & _) & _) & _).
  assert (Hθ : monomorphic_sort_subst Σ_test (not_ (at_most_two τ_A))
                      {[ u_A := σ_bool ]}).
  { split; [rewrite dom_singleton_L; simpl; set_solver |].
    apply map_Forall_singleton.
    split; [apply sort_wf_σ_bool | apply monomorphic_σ_bool]. }
  specialize (Hall _ Hθ).
  assert (Hsubst : term_sort_subst {[ u_A := σ_bool ]} (not_ (at_most_two τ_A))
                   = not_ (at_most_two σ_bool))
    by (simpl; by rewrite lookup_singleton_eq).
  rewrite Hsubst in Hall.
  (* the instance at Bool is true: of any three Booleans two coincide *)
  assert (Htrue : ⟦ at_most_two σ_bool : σ_bool ⟧(Σ_test, A, V)
                    ⇓ cast_sym A.(domain_σ_bool) true).
  { apply (E_TForall_true Σ_test A ∅). intros x _ a t' V'. subst t' V'. simpl.
    apply (E_TForall_true Σ_test A {[x]}).
    intros y Hy b t' V'. subst t' V'. simpl.
    apply (E_TForall_true Σ_test A {[x; y]}).
    intros z Hz c t' V'. subst t' V'. simpl.
    assert (Hxy : x ≠ y) by set_solver. assert (Hxz : x ≠ z) by set_solver.
    assert (Hyz : y ≠ z) by set_solver.
    match goal with
    | |- ⟦ _ : _ ⟧(_, _, ?V') ⇓ _ =>
        destruct (eval_at_most_two_body A V' x y z σ_bool a b c Hcore
                    monomorphic_σ_bool)
          as (e & He & Hiff);
          [by simplify_map_eq | by simplify_map_eq | by simplify_map_eq |]
    end.
    destruct e; [exact He |]. exfalso.
    assert (Hpigeon : a = b \/ a = c \/ b = c).
    { destruct (cast_sym_true_or_false A.(domain_σ_bool) a) as [-> | ->],
        (cast_sym_true_or_false A.(domain_σ_bool) b) as [-> | ->],
        (cast_sym_true_or_false A.(domain_σ_bool) c) as [-> | ->];
        naive_solver. }
    apply Hiff in Hpigeon. discriminate. }
  (* so the instance of the negation is false, where [Hall] has it true *)
  pose proof (eval_not Σ_test A V _ _ Σ_core_extends_Σ_test Hcore Htrue) as Hnot.
  rewrite cast_cast_sym in Hnot. simpl in Hnot.
  pose proof (eval_deterministic Σ_test A V σ_bool _ _ _
                (not_has_sort _ _ Σ_core_extends_Σ_test
                   (at_most_two_has_sort σ_bool (sort_wf_σ_bool Σ_test)
                      monomorphic_σ_bool))
                HV Hall Hnot) as Hc.
  exact (cast_sym_true_neq_false _ Hc).
Qed.
