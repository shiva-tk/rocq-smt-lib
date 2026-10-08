(** * SMTLIB.tests.TestTheory : A Theory and a Model to Test Against *)

(** The shared setting for [SMTLIB.tests.UnitTests].  [T_test] is Core and
    Reals_Ints composed, extended with one uninterpreted symbol
    [f : Int Int].  It declares no datatype, so its domain [D_test] is
    [SMTLIB.Domain]'s first pass — [bool] at Bool, [Z] at Int, [R] at Real,
    functions at the map sorts and [unit] elsewhere — and the datatype condition
    [theory_init] conjoins is vacuous at it.

    _Where the freedom is._  Reals_Ints constrains [/] only where the
    denominator is non-zero, and nothing at all constrains a symbol it does
    not declare.  [test_interp] takes both liberties: it sends [x / 0] to 4
    and interprets [f] as the constant 4.  That freedom is what the two
    satisfiability tests exercise. *)

From Stdlib Require Import ZArith QArith Qcanon Reals
  ClassicalEpsilon.
From stdpp Require Import functions.
From SMTLIB Require Import Utils Symbols Term Sorting Signature Theory Eval
  Domain.
From SMTLIB.Theory Require Import Core Reals_Ints HO_Core.

Open Scope smt_scope.

(** * A Signature with an Uninterpreted Symbol *)

(** One unary symbol on the integers, with a rank and no model condition: the
    theory says which applications are well-sorted and leaves every model free
    to interpret them. *)

Definition f_f : func := "f".

Inductive rank_uninterp : func -> list sort -> sort -> Prop :=
| rank_f_f : rank_uninterp f_f [ σ_int ] σ_int.

Program Definition Σ_uninterp : signature :=
  {|
    sort_symbols := {[ s_bool; s_map; s_int ]};

    funcs (f : func) := f = f_f;
    funcs_dec f := decide (f = f_f);

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

    rank := rank_uninterp;
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
  intros f τs τ Hf. inversion Hf; subst. split.
  - constructor; [set_solver | reflexivity | constructor].
  - constructor; [| constructor].
    constructor; [set_solver | reflexivity | constructor].
Qed.
Next Obligation.
Proof. intros f τs τ Hf. by inversion Hf. Qed.
Next Obligation.
Proof. intros f ->. exists [ σ_int ], σ_int. constructor. Qed.
Next Obligation.
Proof. set_solver. Qed.
Next Obligation.
Proof. set_solver. Qed.
Next Obligation.
Proof. set_solver. Qed.
Next Obligation.
Proof. set_solver. Qed.

Definition T_uninterp : pretheory :=
  {|
    pΣ := Σ_uninterp;
    pmodels A := True;
  |}.

(** * The Theory *)

Lemma Σ_core_Σ_reals_ints_composable : signatures_composable Σ_core Σ_reals_ints.
Proof. constructor; intros; first [reflexivity | set_solver]. Qed.

Definition C_arith : pretheories_composable T_core T_reals_ints :=
  Build_pretheories_composable T_core T_reals_ints
    Σ_core_Σ_reals_ints_composable.

Definition T_arith : pretheory := T_core ⊕[ C_arith ] T_reals_ints.

Lemma Σ_arith_Σ_uninterp_composable :
  signatures_composable T_arith.(pΣ) Σ_uninterp.
Proof.
  constructor; intros; simpl in *; repeat case_decide;
    first [reflexivity | set_solver].
Qed.

Definition C_test : pretheories_composable T_arith T_uninterp :=
  Build_pretheories_composable T_arith T_uninterp
    Σ_arith_Σ_uninterp_composable.

Definition T_test : theory :=
  theory_init (T_arith ⊕[ C_test ] T_uninterp).

Definition Σ_test : signature := T_test.(Σ).

(** No symbol is declared twice, which is what lets each component's
    interpretation be read off the composite, and makes every rank the
    composite proves one of its components already proved. *)
Lemma core_funcs_reals_ints_funcs_disjoint :
  forall f, Σ_core.(funcs) f -> Σ_reals_ints.(funcs) f -> False.
Proof.
  intros f Hcore Hri.
  assert (Hf : f = f_true \/ f = f_false \/ f = f_not \/ f = f_impl
               \/ f = f_and \/ f = f_or \/ f = f_xor \/ f = f_eq
               \/ f = f_distinct \/ f = f_ite) by set_solver.
  destruct Hri as [Hset | [(n & _ & <-) | [(i & <-) | (q & <-)]]].
  - set_solver.
  - destruct_or! Hf; discriminate.
  - destruct_or! Hf; discriminate.
  - destruct_or! Hf; discriminate.
Qed.

Lemma f_f_not_core_func : ~ Σ_core.(funcs) f_f.
Proof. intros Hf. set_solver. Qed.

Lemma f_f_not_reals_ints_func : ~ Σ_reals_ints.(funcs) f_f.
Proof.
  intros [Hset | [(n & _ & Heq) | [(i & Heq) | (q & Heq)]]];
    [set_solver | discriminate | discriminate | discriminate].
Qed.

Lemma Σ_core_extends_Σ_arith : Σ_core ⊑ T_arith.(pΣ).
Proof.
  apply signature_compose_extends_rank_left.
  intros f τs τ Hcore Hri.
  destruct (core_funcs_reals_ints_funcs_disjoint f Hcore Hri).
Qed.

Lemma Σ_reals_ints_extends_Σ_arith : Σ_reals_ints ⊑ T_arith.(pΣ).
Proof.
  apply signature_compose_extends_rank_right.
  intros f τs τ Hcore Hri.
  destruct (core_funcs_reals_ints_funcs_disjoint f Hcore Hri).
Qed.

Lemma Σ_arith_extends_Σ_test : T_arith.(pΣ) ⊑ Σ_test.
Proof.
  apply signature_compose_extends_rank_left.
  intros f τs τ Harith ->.
  destruct Harith as [Hcore | Hri];
    [ destruct (f_f_not_core_func Hcore)
    | destruct (f_f_not_reals_ints_func Hri) ].
Qed.

Lemma Σ_uninterp_extends_Σ_test : Σ_uninterp ⊑ Σ_test.
Proof.
  apply signature_compose_extends_rank_right.
  intros f τs τ Harith ->.
  destruct Harith as [Hcore | Hri];
    [ destruct (f_f_not_core_func Hcore)
    | destruct (f_f_not_reals_ints_func Hri) ].
Qed.

Lemma Σ_core_extends_Σ_test : Σ_core ⊑ Σ_test.
Proof.
  transitivity T_arith.(pΣ);
    [exact Σ_core_extends_Σ_arith | exact Σ_arith_extends_Σ_test].
Qed.

Lemma Σ_reals_ints_extends_Σ_test : Σ_reals_ints ⊑ Σ_test.
Proof.
  transitivity T_arith.(pΣ);
    [exact Σ_reals_ints_extends_Σ_arith | exact Σ_arith_extends_Σ_test].
Qed.

(** [sort_wf] at [σ_bool] holds in every signature ([sort_wf_σ_bool]); at
    [σ_int] it is a fact about this one, since a signature need not declare
    [s_int] at all. *)
Lemma sort_wf_Σ_test_σ_int : sort_wf Σ_test σ_int.
Proof. constructor; auto. cbn. set_solver. Qed.

(** * The Domain *)

(** What Core and Reals_Ints pin at the nullary sort symbols: [bool] at
    [s_bool] is [structure]'s own [domain_σ_bool], [Z] and [R] are
    Reals_Ints'.  Every other symbol goes to [unit]. *)
Definition test_base (s : sortsymb) : Type :=
  if decide (s = s_bool) then bool
  else if decide (s = s_int) then Z
  else if decide (s = s_real) then R
  else unit.

Definition test_base_witness : forall s, test_base s.
Proof.
  intros s. unfold test_base. repeat case_decide;
    [exact true | exact 0%Z | exact 0%R | exact tt].
Defined.

(** [Σ_test] declares no datatype, so [SMTLIB.Domain]'s first pass, the one
    blind to datatypes, is already its domain. *)
Definition D_test : sort -> Type := adt_free_domain test_base.

Lemma D_test_σ_bool : D_test σ_bool = bool.
Proof.
  unfold D_test, σ_bool. cbn [adt_free_domain]. unfold test_base.
  by rewrite decide_True.
Qed.

Lemma D_test_σ_int : D_test σ_int = Z.
Proof.
  unfold D_test, σ_int. cbn [adt_free_domain]. unfold test_base.
  rewrite decide_False by done. by rewrite decide_True.
Qed.

Lemma D_test_σ_real : D_test σ_real = R.
Proof.
  unfold D_test, σ_real. cbn [adt_free_domain]. unfold test_base.
  rewrite decide_False by done. rewrite decide_False by done.
  by rewrite decide_True.
Qed.

Lemma D_test_τ_map :
  forall σ1 σ2, D_test (τ_map σ1 σ2) = (D_test σ1 -> D_test σ2).
Proof.
  intros σ1 σ2. unfold D_test, τ_map. cbn [adt_free_domain].
  by rewrite decide_True.
Qed.

Definition test_witness : forall σ, D_test σ :=
  adt_free_domain_witness test_base test_base_witness.

(** * The Interpretation *)

(** Away from [f] and [/] each symbol is interpreted by the component that
    declares it. *)
Definition base_interp : forall f σs σ, interpretation D_test σs σ :=
  fun f σs σ =>
    if excluded_middle_informative (Σ_core.(funcs) f)
    then core_interp D_test test_witness D_test_σ_bool f σs σ
    else reals_ints_interp D_test test_witness D_test_σ_bool
           D_test_σ_int D_test_σ_real f σs σ.

(** The theory leaves two things open: Reals_Ints constrains [/] only where
    the denominator is non-zero, and nothing at all constrains [f], which no
    component declares a model condition for.  Both are parameters rather than
    constants, so that [A_free d k] is a model at every [d] and [k] and the
    tests can show each freedom is real rather than merely unused. *)
Section WhereTheFreedomIs.

  Variable d : R.
  Variable k : Z.

(** [f] is uninterpreted, so it may be the constant [k]. *)
Definition uninterp_f : forall σs σ, interpretation D_test σs σ :=
  interp_insert_rank D_test [ σ_int ] σ_int
    (fun _ : D_test σ_int => cast_sym D_test_σ_int k)
    (interp_const D_test test_witness).

(** Real division, except that a zero denominator gives [d]. *)
Definition div_by_zero : forall σs σ, interpretation D_test σs σ :=
  interp_insert_rank D_test [ σ_real; σ_real ] σ_real
    (fun x y : D_test σ_real =>
       if excluded_middle_informative (cast D_test_σ_real y = 0%R)
       then cast_sym D_test_σ_real d
       else cast_sym D_test_σ_real
              (cast D_test_σ_real x / cast D_test_σ_real y)%R)
    (interp_const D_test test_witness).

Definition test_interp : forall f σs σ, interpretation D_test σs σ :=
  interp_insert_func D_test f_div div_by_zero
    (interp_insert_func D_test f_f uninterp_f base_interp).

Definition A_free : structure :=
  structure_of D_test D_test_σ_bool D_test_τ_map test_interp.

Lemma A_free_models_core : models_core A_free.
Proof.
  eapply (T_core_local D_test D_test_σ_bool D_test_τ_map
            (core_interp D_test test_witness D_test_σ_bool) test_interp);
    [| apply core_interp_models].
  intros f Hf σs σ. cbn in Hf. unfold test_interp, base_interp.
  rewrite interp_insert_func_ne by (intros ->; set_solver).
  rewrite interp_insert_func_ne by (intros ->; set_solver).
  destruct (excluded_middle_informative _) as [_ | Hno];
    [reflexivity | by destruct Hno].
Qed.

Lemma A_free_models_reals_ints :
  models_reals_ints A_free D_test_σ_int D_test_σ_real.
Proof.
  (* [f] is not a Reals_Ints symbol, so interpreting it disturbs nothing. *)
  assert (Hagree : interp_agree_on D_test Σ_reals_ints.(funcs)
            (reals_ints_interp D_test test_witness D_test_σ_bool
               D_test_σ_int D_test_σ_real)
            (interp_insert_func D_test f_f uninterp_f base_interp)).
  { intros f Hf σs σ. unfold base_interp.
    rewrite interp_insert_func_ne
      by (intros ->; by apply f_f_not_reals_ints_func).
    destruct (excluded_middle_informative _) as [Hc | _];
      [ by destruct (core_funcs_reals_ints_funcs_disjoint f Hc Hf)
      | reflexivity ]. }
  assert (Hmodel : pmodels T_reals_ints
            (structure_of D_test D_test_σ_bool D_test_τ_map
               (reals_ints_interp D_test test_witness D_test_σ_bool
                  D_test_σ_int D_test_σ_real))).
  { exists D_test_σ_int, D_test_σ_real.
    exact (reals_ints_interp_models D_test test_witness D_test_σ_bool
             D_test_τ_map D_test_σ_int D_test_σ_real). }
  destruct (T_reals_ints_local D_test D_test_σ_bool D_test_τ_map _ _ Hagree
              Hmodel) as (HZ & HR & Hri).
  rewrite (proof_irrelevance _ HZ D_test_σ_int) in Hri.
  rewrite (proof_irrelevance _ HR D_test_σ_real) in Hri.
  destruct Hri as [A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16
                   A17 A18 A19 A20 A21 A22 A23 A24 A25 A26].
  (* [/] is the one symbol where the two interpretations differ, and its
     condition is silent at a zero denominator. *)
  unfold A_free, test_interp. constructor.
  - unfold models_f_minus_neg_int; cbv zeta; cbn [interp structure_of].
    intros i. rewrite interp_insert_func_ne by discriminate. exact (A1 i).
  - unfold models_f_minus_sub_int; cbv zeta; cbn [interp structure_of].
    intros i j. rewrite interp_insert_func_ne by discriminate. exact (A2 i j).
  - unfold models_f_plus_int; cbv zeta; cbn [interp structure_of].
    intros i j. rewrite interp_insert_func_ne by discriminate. exact (A3 i j).
  - unfold models_f_times_int; cbv zeta; cbn [interp structure_of].
    intros i j. rewrite interp_insert_func_ne by discriminate. exact (A4 i j).
  - unfold models_f_idiv; cbv zeta; cbn [interp structure_of].
    intros i j Hj. rewrite interp_insert_func_ne by discriminate.
    exact (A5 i j Hj).
  - unfold models_f_mod; cbv zeta; cbn [interp structure_of].
    intros i j Hj. rewrite interp_insert_func_ne by discriminate.
    exact (A6 i j Hj).
  - unfold models_f_abs; cbv zeta; cbn [interp structure_of].
    intros i. rewrite interp_insert_func_ne by discriminate. exact (A7 i).
  - unfold models_f_leq_int; cbv zeta; cbn [interp structure_of].
    intros i j. rewrite interp_insert_func_ne by discriminate. exact (A8 i j).
  - unfold models_f_lt_int; cbv zeta; cbn [interp structure_of].
    intros i j. rewrite interp_insert_func_ne by discriminate. exact (A9 i j).
  - unfold models_f_geq_int; cbv zeta; cbn [interp structure_of].
    intros i j. rewrite interp_insert_func_ne by discriminate. exact (A10 i j).
  - unfold models_f_gt_int; cbv zeta; cbn [interp structure_of].
    intros i j. rewrite interp_insert_func_ne by discriminate. exact (A11 i j).
  - unfold models_f_minus_neg_real; cbv zeta; cbn [interp structure_of].
    intros x. rewrite interp_insert_func_ne by discriminate. exact (A12 x).
  - unfold models_f_minus_sub_real; cbv zeta; cbn [interp structure_of].
    intros x y. rewrite interp_insert_func_ne by discriminate. exact (A13 x y).
  - unfold models_f_plus_real; cbv zeta; cbn [interp structure_of].
    intros x y. rewrite interp_insert_func_ne by discriminate. exact (A14 x y).
  - unfold models_f_times_real; cbv zeta; cbn [interp structure_of].
    intros x y. rewrite interp_insert_func_ne by discriminate. exact (A15 x y).
  - (* the one condition that is not inherited: division away from zero *)
    unfold models_f_div, cast_to_R; cbv zeta; cbn [interp structure_of].
    intros x y Hy. rewrite interp_insert_func_eq.
    unfold div_by_zero. rewrite interp_insert_rank_eq.
    destruct (excluded_middle_informative _) as [Hzero | _];
      [by destruct (Hy Hzero) |].
    by rewrite cast_cast_sym.
  - unfold models_f_leq_real; cbv zeta; cbn [interp structure_of].
    intros x y b Hb. rewrite interp_insert_func_ne in Hb by discriminate.
    exact (A17 x y b Hb).
  - unfold models_f_lt_real; cbv zeta; cbn [interp structure_of].
    intros x y b Hb. rewrite interp_insert_func_ne in Hb by discriminate.
    exact (A18 x y b Hb).
  - unfold models_f_geq_real; cbv zeta; cbn [interp structure_of].
    intros x y b Hb. rewrite interp_insert_func_ne in Hb by discriminate.
    exact (A19 x y b Hb).
  - unfold models_f_gt_real; cbv zeta; cbn [interp structure_of].
    intros x y b Hb. rewrite interp_insert_func_ne in Hb by discriminate.
    exact (A20 x y b Hb).
  - unfold models_f_to_real; cbv zeta; cbn [interp structure_of].
    intros i. rewrite interp_insert_func_ne by discriminate. exact (A21 i).
  - unfold models_f_to_int; cbv zeta; cbn [interp structure_of].
    intros x. rewrite interp_insert_func_ne by discriminate. exact (A22 x).
  - unfold models_f_is_int; cbv zeta; cbn [interp structure_of].
    intros x b Hb. rewrite interp_insert_func_ne in Hb by discriminate.
    exact (A23 x b Hb).
  - unfold models_f_divisible; cbv zeta; cbn [interp structure_of].
    intros n x Hn. rewrite interp_insert_func_ne by discriminate.
    exact (A24 n x Hn).
  - unfold models_f_int_literal; cbv zeta; cbn [interp structure_of].
    intros i. rewrite interp_insert_func_ne by discriminate. exact (A25 i).
  - unfold models_f_decimal_literal; cbv zeta; cbn [interp structure_of].
    intros q. rewrite interp_insert_func_ne by discriminate. exact (A26 q).
Qed.

(** Nothing in [Σ_test] is a datatype, so every clause of the datatype
    condition is empty. *)
Lemma Σ_test_no_adt : forall δ, ~ adt Σ_test δ.
Proof.
  intros δ Hadt.
  apply adt_spec_of_adt in Hadt as (_ & s & c & _ & _ & Hc).
  cbn in Hc. repeat case_decide; set_solver.
Qed.

Lemma A_free_adt_axioms : adt_axioms (Σ := Σ_test) A_free.
Proof.
  unshelve econstructor.
  - intros δ Hδ. by destruct (Σ_test_no_adt δ Hδ).
  - intros c σs δ s Hs Hδ Hc Hrank Hwf Hσs C vs. exfalso.
    by destruct (Σ_test_no_adt δ (adt_intro Σ_test δ s c Hs Hδ Hc Hwf)).
  - intros c σs δ i g σi vi Hc Hrank Hg. exfalso.
    cbn in Hg. repeat case_decide; by destruct i.
  - intros c σs δ Hc. exfalso. cbn in Hc. set_solver.
Qed.

Theorem A_free_models : T_test.(models) A_free.
Proof.
  split; [| exact A_free_adt_axioms].
  split; [| exact I].
  split; [exact A_free_models_core |].
  exists D_test_σ_int, D_test_σ_real. exact A_free_models_reals_ints.
Qed.

End WhereTheFreedomIs.

(** Casting along a domain equation is injective, so distinct literals denote
    distinct domain elements.  Without it a model could collapse everything to
    one value, and no test here could refute anything. *)
Lemma cast_sym_inj :
  forall {T U : Type} (H : T = U) (x y : U), cast_sym H x = cast_sym H y -> x = y.
Proof.
  intros T U H x y Heq.
  apply (f_equal (cast H)) in Heq. by rewrite !cast_cast_sym in Heq.
Qed.

(** The formulas the tests use are closed, and [Σ_test] declares no
    variables, so the empty valuation is a valuation for it.  It is indexed by
    [d] and [k] only to be typed at [A_free d k]. *)
Definition V_free (d : R) (k : Z) : valuation (A_free d k) := ∅.

(** [A_free d k] answers [d] at [0 / 0], which is the whole content of the parameter. *)
Lemma eval_zero_over_zero : forall d k,
  ⟦ div_ zero_real zero_real : σ_real ⟧(Σ_test, A_free d k, V_free d k)
    ⇓ cast_sym D_test_σ_real d.
Proof.
  intros d k.
  assert (Hzero : ⟦ zero_real : σ_real ⟧(Σ_test, A_free d k, V_free d k)
                    ⇓ (cast_sym D_test_σ_real 0%R)).
  { apply (eval_zero_real Σ_test (A_free d k) (V_free d k)
             D_test_σ_int D_test_σ_real (A_free_models_reals_ints d k)).
    exact Σ_reals_ints_extends_Σ_test. }
  pose proof (eval_div_real Σ_test (A_free d k) (V_free d k)
                zero_real zero_real _ _ Σ_reals_ints_extends_Σ_test
                Hzero Hzero) as Hd.
  unfold A_free, test_interp in Hd. cbn [interp structure_of] in Hd.
  rewrite interp_insert_func_eq in Hd.
  unfold div_by_zero in Hd. rewrite interp_insert_rank_eq in Hd.
  autorewrite with interp_apply in Hd.
  rewrite cast_cast_sym in Hd.
  destruct (excluded_middle_informative (0%R = 0%R)) as [_ | Hne];
    [exact Hd | by destruct (Hne eq_refl)].
Qed.

(** [A_free d k] answers [k] at [f], which is the whole content of that
    parameter: no component of [T_test] declares a model condition for [f]. *)
Lemma eval_f_at_zero : forall d k,
  ⟦ TApp f_f None [ zero_int ] : σ_int ⟧(Σ_test, A_free d k, V_free d k)
    ⇓ cast_sym D_test_σ_int k.
Proof.
  intros d k.
  assert (Hzero : ⟦ zero_int : σ_int ⟧(Σ_test, A_free d k, V_free d k)
                    ⇓ (cast_sym D_test_σ_int 0%Z)).
  { apply (eval_zero_int Σ_test (A_free d k) (V_free d k)
             D_test_σ_int D_test_σ_real (A_free_models_reals_ints d k)).
    exact Σ_reals_ints_extends_Σ_test. }
  eapply E_TApp with (σs := [ σ_int ])
    (vs := HCons σ_int [] (cast_sym D_test_σ_int 0%Z) HNil).
  - repeat constructor; exact Hzero.
  - constructor.
  - apply rank_monomorphic;
      [ cbn; right; constructor | repeat constructor | repeat constructor ].
  - autorewrite with interp_apply.
    unfold A_free, test_interp. cbn [interp structure_of].
    rewrite interp_insert_func_ne by discriminate.
    rewrite interp_insert_func_eq.
    unfold uninterp_f. by rewrite interp_insert_rank_eq.
Qed.

(** * Consistency *)

(** [Eval.v]'s [entails_sat] and [not_sat_not_entails] are relative to the
    premise set being satisfiable.  At [∅] that is just [T_test] having a
    model, and [sat T_test ∅] says exactly that — which is why no separate
    notion of consistency is needed here.

    Both [∅ ⊨[ T_test ] ϕ] and [~ sat T_test {[ϕ]}] quantify over models,
    so each is vacuous at a theory with none; this is what their content
    rests on. *)
Theorem T_test_consistent : sat T_test ∅.
Proof.
  exists (A_free 0%R 0%Z), (V_free 0%R 0%Z).
  split; [exact (A_free_models 0%R 0%Z) |].
  split; [apply map_empty_subseteq |].
  intros ψ Hψ. set_solver.
Qed.

(** [Eval.v]'s bridges specialised: consistency discharged, and the [∪ ∅] a
    premise-free entailment leaves behind normalised away.  Every derived
    half of a classification below goes through one of these. *)
Corollary sat_of_entails : forall ϕ,
    ∅ ⊨[ T_test ] ϕ -> sat T_test {[ ϕ ]}.
Proof.
  intros ϕ Hentails.
  rewrite <- (union_empty_r_L {[ ϕ ]}).
  apply entails_sat; [exact T_test_consistent | exact Hentails].
Qed.

Corollary not_entails_of_not_sat : forall ϕ,
    ~ sat T_test {[ ϕ ]} -> ~ ∅ ⊨[ T_test ] ϕ.
Proof.
  intros ϕ Hunsat.
  apply (not_sat_not_entails T_test ∅); [exact T_test_consistent |].
  by rewrite union_empty_r_L.
Qed.

(** * A Higher-Order Test Theory *)

(** [Σ_test] declares no application symbol, so a term of a map sort can
    be built there and compared, but never applied.  Core composed with
    HO-Core adds [@].  The domain is the same [D_test], so the two theories
    differ only in what they interpret. *)

Lemma core_funcs_ho_core_funcs_disjoint :
  forall f, Σ_core.(funcs) f -> Σ_ho_core.(funcs) f -> False.
Proof. intros f Hc Hh. cbn in Hc, Hh. set_solver. Qed.

Lemma Σ_core_Σ_ho_core_composable : signatures_composable Σ_core Σ_ho_core.
Proof.
  constructor; intros; simpl in *; repeat case_decide;
    first [reflexivity | set_solver].
Qed.

Definition C_ho : pretheories_composable T_core T_ho_core :=
  Build_pretheories_composable T_core T_ho_core Σ_core_Σ_ho_core_composable.

Definition T_ho_pre : pretheory := T_core ⊕[ C_ho ] T_ho_core.
Definition Σ_ho : signature := T_ho_pre.(pΣ).
Definition T_ho : theory := theory_init T_ho_pre.

Lemma Σ_core_extends_Σ_ho : Σ_core ⊑ Σ_ho.
Proof.
  apply signature_compose_extends_rank_left.
  intros f τs τ Hc Hh. destruct (core_funcs_ho_core_funcs_disjoint f Hc Hh).
Qed.

Lemma Σ_ho_core_extends_Σ_ho : Σ_ho_core ⊑ Σ_ho.
Proof.
  apply signature_compose_extends_rank_right.
  intros f τs τ Hc Hh. destruct (core_funcs_ho_core_funcs_disjoint f Hc Hh).
Qed.

(** Each symbol is interpreted by the component that declares it. *)
Definition ho_interp : forall f σs σ, interpretation D_test σs σ :=
  fun f σs σ =>
    if decide (Σ_core.(funcs) f)
    then core_interp D_test test_witness D_test_σ_bool f σs σ
    else ho_core_interp D_test test_witness D_test_τ_map f σs σ.

Definition A_ho : structure :=
  structure_of D_test D_test_σ_bool D_test_τ_map ho_interp.

Lemma A_ho_models_core : models_core A_ho.
Proof.
  eapply (T_core_local D_test D_test_σ_bool D_test_τ_map
            (core_interp D_test test_witness D_test_σ_bool) ho_interp);
    [| apply core_interp_models].
  intros f Hf σs σ. unfold ho_interp. by rewrite decide_True.
Qed.

Lemma A_ho_models_ho_core : models_ho_core A_ho.
Proof.
  eapply (T_ho_core_local D_test D_test_σ_bool D_test_τ_map
            (ho_core_interp D_test test_witness D_test_τ_map) ho_interp);
    [| apply ho_core_interp_models].
  intros f Hf σs σ. unfold ho_interp.
  rewrite decide_False; [reflexivity |].
  intros Hc. exact (core_funcs_ho_core_funcs_disjoint f Hc Hf).
Qed.

Lemma Σ_ho_no_adt : forall δ, ~ adt Σ_ho δ.
Proof.
  intros δ Hadt.
  apply adt_spec_of_adt in Hadt as (_ & s & c & _ & _ & Hc).
  cbn in Hc. repeat case_decide; set_solver.
Qed.

Lemma A_ho_adt_axioms : adt_axioms (Σ := Σ_ho) A_ho.
Proof.
  unshelve econstructor.
  - intros δ Hδ. by destruct (Σ_ho_no_adt δ Hδ).
  - intros c σs δ s Hs Hδ Hc Hrank Hwf Hσs C vs. exfalso.
    by destruct (Σ_ho_no_adt δ (adt_intro Σ_ho δ s c Hs Hδ Hc Hwf)).
  - intros c σs δ i g σi vi Hc Hrank Hg. exfalso.
    cbn in Hg. repeat case_decide; by destruct i.
  - intros c σs δ Hc. exfalso. cbn in Hc. set_solver.
Qed.

Theorem A_ho_models : T_ho.(models) A_ho.
Proof.
  split; [| exact A_ho_adt_axioms].
  split; [exact A_ho_models_core | exact A_ho_models_ho_core].
Qed.
