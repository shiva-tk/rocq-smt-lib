From SMTLIB Require Import Utils Symbols Term Signature Theory Sorting Eval.
From Stdlib Require Import ZArith QArith QArith.Qcanon Reals Lra Znumtheory.
From Stdlib Require Import Ascii.
From stdpp Require Import base pretty numbers.

Open Scope smt_scope.

(* https://smt-lib.org/theories-Reals_Ints.shtml *)

Definition s_int : sortsymb := "Int".
Definition σ_int : sort := SApp s_int [].

Definition s_real : sortsymb := "Real".
Definition σ_real : sort := SApp s_real [].

Definition f_minus : func := "-".
Definition f_plus : func := "+".
Definition f_times : func := "*".
Definition f_idiv : func := "div".
Definition f_div : func := "/".
Definition f_mod : func := "mod".
Definition f_abs : func := "abs".
Definition f_leq : func := "<=".
Definition f_lt : func := "<".
Definition f_geq : func := ">=".
Definition f_gt : func := ">".
Definition f_to_real : func := "to_real".
Definition f_to_int : func := "to_int".
Definition f_is_int : func := "is_int".

Definition reals_ints_funcs : gset func :=
  {[ f_minus; f_plus; f_times; f_idiv; f_div; f_mod;
     f_abs; f_leq; f_lt; f_geq; f_gt;
     f_to_real; f_to_int; f_is_int ]}.

Definition f_divisible (n : nat) :=
  IdIndexed "divisible" [IdxNum n].
Definition divisible_func f :=
  exists n, n <> 0 /\ f_divisible n = f.

Definition f_int_literal (i : Z) : func :=
  IdSimple ("int_literal_" ++ pretty i).
Definition int_literals f := exists i, f_int_literal i = f.

(* No pretty instance for Q: this is a hack to uniquely represent decimals. *)
Definition f_decimal_literal (q : Qc) : func :=
  IdSimple ("decimal_literal_" ++ pretty (Qnum q) ++ "/" ++ pretty (Qden q)).
Definition decimal_literals f := exists q, f_decimal_literal q = f.

(** ** Reading a Literal Back

    Each family renders its payload, so deciding whether a symbol belongs to
    one, and recovering what it carries, needs the inverse of that rendering.
    Only agreement on the image is proved; a candidate is checked by
    rendering it again. *)

Definition parse_divisible (f : func) : option nat :=
  match f with
  | IdIndexed "divisible" [IdxNum n] => Some n
  | _ => None
  end.

Lemma parse_divisible_eq : forall n, parse_divisible (f_divisible n) = Some n.
Proof. intros n. reflexivity. Qed.

Definition parse_int_literal (f : func) : option Z :=
  match f with
  | IdSimple s =>
      match string_strip_prefix "int_literal_" s with
      | Some r => parse_Z r
      | None => None
      end
  | _ => None
  end.

Lemma parse_int_literal_eq : forall i,
    parse_int_literal (f_int_literal i) = Some i.
Proof.
  intros i. unfold parse_int_literal, f_int_literal.
  rewrite (string_strip_prefix_app "int_literal_" (pretty i)).
  apply parse_Z_pretty.
Qed.

(** The slash is neither a digit nor the minus sign, so it is the one the
    rendering put between numerator and denominator. *)
Definition parse_decimal_literal (f : func) : option Qc :=
  match f with
  | IdSimple s =>
      match string_strip_prefix "decimal_literal_" s with
      | Some r =>
          match string_split_at "/"%char r with
          | Some (num, den) =>
              match parse_Z num, parse_positive den with
              | Some n, Some d => Some (Q2Qc (Qmake n d))
              | _, _ => None
              end
          | None => None
          end
      | None => None
      end
  | _ => None
  end.

Lemma parse_decimal_literal_eq : forall q,
    parse_decimal_literal (f_decimal_literal q) = Some q.
Proof.
  intros q. unfold parse_decimal_literal, f_decimal_literal.
  rewrite (string_strip_prefix_app "decimal_literal_"
             (pretty (Qnum q) ++ "/" ++ pretty (Qden q))).
  change ("/" ++ pretty (Qden q))%string
    with (String "/"%char (pretty (Qden q))).
  rewrite (string_split_at_app "/"%char (pretty (Qnum q)) (pretty (Qden q))).
  2:{ apply string_occurs_pretty_Z; [done|].
      intros m Hm Hq. revert Hq.
      assert (m = 0 \/ m = 1 \/ m = 2 \/ m = 3 \/ m = 4 \/
              m = 5 \/ m = 6 \/ m = 7 \/ m = 8 \/ m = 9)%N as Hm10 by lia.
      by repeat (destruct Hm10 as [->|Hm10]; [done|]); subst m. }
  rewrite parse_Z_pretty, parse_positive_pretty.
  f_equal. apply Qc_decomp. by destruct q as [[n d] Hc].
Qed.

(** A symbol belongs to a family exactly when reading it back gives a
    payload that renders to it. *)
Global Instance divisible_func_dec (f : func) : Decision (divisible_func f).
Proof.
  unfold divisible_func.
  destruct (parse_divisible f) as [n|] eqn:Hp.
  - destruct (decide (n <> 0 /\ f_divisible n = f)) as [Hok|Hne].
    + left. by exists n.
    + right. intros (m & Hm & Heq). apply Hne.
      subst f. rewrite parse_divisible_eq in Hp. by injection Hp as <-.
  - right. intros (m & Hm & Heq).
    subst f. by rewrite parse_divisible_eq in Hp.
Qed.

Global Instance int_literals_dec (f : func) : Decision (int_literals f).
Proof.
  unfold int_literals.
  destruct (parse_int_literal f) as [i|] eqn:Hp.
  - destruct (decide (f_int_literal i = f)) as [Hok|Hne].
    + left. by exists i.
    + right. intros [j Heq]. apply Hne.
      subst f. rewrite parse_int_literal_eq in Hp. by injection Hp as <-.
  - right. intros [j Heq]. subst f. by rewrite parse_int_literal_eq in Hp.
Qed.

Global Instance decimal_literals_dec (f : func) : Decision (decimal_literals f).
Proof.
  unfold decimal_literals.
  destruct (parse_decimal_literal f) as [q|] eqn:Hp.
  - destruct (decide (f_decimal_literal q = f)) as [Hok|Hne].
    + left. by exists q.
    + right. intros [r Heq]. apply Hne.
      subst f. rewrite parse_decimal_literal_eq in Hp. by injection Hp as <-.
  - right. intros [r Heq]. subst f. by rewrite parse_decimal_literal_eq in Hp.
Qed.

Definition neg_ t := TApp f_minus None [t].
Definition minus_ t1 t2 := TApp f_minus None [t1; t2].
Definition plus_ t1 t2 := TApp f_plus None [t1; t2].
Definition times_ t1 t2 := TApp f_times None [t1; t2].
Definition idiv_ t1 t2 := TApp f_idiv None [t1; t2].
Definition div_ t1 t2 := TApp f_div None [t1; t2].
Definition mod_ t1 t2 := TApp f_mod None [t1; t2].
Definition abs_ t := TApp f_abs None [t].
Definition leq_ t1 t2 := TApp f_leq None [t1; t2].
Definition lt_ t1 t2 := TApp f_lt None [t1; t2].
Definition geq_ t1 t2 := TApp f_geq None [t1; t2].
Definition gt_ t1 t2 := TApp f_gt None [t1; t2].
Definition to_real t := TApp f_to_real None [t].
Definition to_int t := TApp f_to_int None [t].
Definition is_int t := TApp f_is_int None [t].
Definition divisible t1 t2 := TApp (f_divisible t2) None [t1].
Definition int_literal i := TApp (f_int_literal i) None [].
Definition decimal_literal q := TApp (f_decimal_literal q) None [].
Definition zero_int := int_literal 0.
Definition zero_real := decimal_literal 0.

Inductive rank_reals_ints : func -> list sort -> sort -> Prop :=
(* Several function symbols are overloaded between int and reals. *)
| rank_f_minus_neg_int : rank_reals_ints f_minus [ σ_int ] σ_int
| rank_f_minus_sub_int : rank_reals_ints f_minus [ σ_int; σ_int ] σ_int
| rank_f_plus_int : rank_reals_ints f_plus [ σ_int; σ_int ] σ_int
| rank_f_times_int : rank_reals_ints f_times [ σ_int; σ_int ] σ_int
| rank_f_idiv : rank_reals_ints f_idiv [ σ_int; σ_int ] σ_int
| rank_f_mod : rank_reals_ints f_mod [ σ_int; σ_int ] σ_int
| rank_f_abs : rank_reals_ints f_abs [ σ_int ] σ_int
| rank_f_leq_int : rank_reals_ints f_leq [ σ_int; σ_int ] σ_bool
| rank_f_lt_int : rank_reals_ints f_lt [ σ_int; σ_int ] σ_bool
| rank_f_geq_int : rank_reals_ints f_geq [ σ_int; σ_int ] σ_bool
| rank_f_gt_int : rank_reals_ints f_gt [ σ_int; σ_int ] σ_bool
| rank_f_minus_neg_real : rank_reals_ints f_minus [ σ_real ] σ_real
| rank_f_minus_sub_real : rank_reals_ints f_minus [ σ_real; σ_real ] σ_real
| rank_f_plus_real : rank_reals_ints f_plus [ σ_real; σ_real ] σ_real
| rank_f_times_real : rank_reals_ints f_times [ σ_real; σ_real ] σ_real
| rank_f_div : rank_reals_ints f_div [ σ_real; σ_real] σ_real
| rank_f_leq_real : rank_reals_ints f_leq [ σ_real; σ_real ] σ_bool
| rank_f_lt_real : rank_reals_ints f_lt [ σ_real; σ_real ] σ_bool
| rank_f_geq_real : rank_reals_ints f_geq [ σ_real; σ_real ] σ_bool
| rank_f_gt_real : rank_reals_ints f_gt [ σ_real; σ_real ] σ_bool
| rank_f_to_real : rank_reals_ints f_to_real [ σ_int ] σ_real
| rank_f_to_int : rank_reals_ints f_to_int [ σ_real ] σ_int
| rank_f_is_int : rank_reals_ints f_is_int [ σ_real ] σ_bool
| rank_f_divisible : forall n, n <> 0 -> rank_reals_ints (f_divisible n) [ σ_int ] σ_bool
| rank_f_int_literal : forall i, rank_reals_ints (f_int_literal i) [] σ_int
| rank_f_decimal_literal : forall q, rank_reals_ints (f_decimal_literal q) [] σ_real.

Program Definition Σ_reals_ints : signature :=
  {|
    sort_symbols := {[ s_bool; s_map; s_int; s_real ]};

    funcs f :=
      f ∈ reals_ints_funcs \/ divisible_func f \/ int_literals f \/ decimal_literals f;
    funcs_dec f :=
      decide (f ∈ reals_ints_funcs \/ divisible_func f \/ int_literals f
              \/ decimal_literals f);

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

    rank := rank_reals_ints;
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
  intros f Hf. unfold funcs in Hf.
  destruct_or! Hf.
  - assert (Hf': f = f_minus \/ f = f_plus \/ f = f_times \/ f = f_idiv \/ f = f_div \/ f = f_mod \/ f = f_abs \/ f = f_leq \/ f = f_lt \/ f = f_geq \/ f = f_gt \/ f = f_to_int \/ f = f_to_real \/ f = f_is_int) by set_solver.
    clear Hf. destruct_or! Hf'; subst f; eexists; econstructor; constructor.
  - destruct Hf as (n&Hn&<-). eexists. eexists. constructor; auto.
  - destruct Hf as [i Hf]. simplify_eq. eexists. eexists. constructor.
  - destruct Hf as [i Hf]. simplify_eq. eexists. eexists. constructor.
Qed.
Next Obligation.
Proof. set_solver. Qed.
Next Obligation.
Proof. set_solver. Qed.
Next Obligation.
Proof. set_solver. Qed.
Next Obligation.
Proof. set_solver. Qed.

Open Scope Z_scope.

(* Euclidean definition of div and mod *)

Definition smt_div (i j : Z) :=
 Z.sgn j * (Z.div i (Z.abs j)).

Theorem smt_div_pos : forall i j,
 0 < j ->
 smt_div i j = Z.div i j.
Proof.
 intros * Hpos.
 unfold smt_div.
 rewrite Z.sgn_pos, Z.mul_1_l.
 2: { lia. }
 rewrite Z.abs_eq.
 2: { lia. }
 reflexivity.
Qed.

Definition smt_mod (i j : Z) : Z :=
 Z.modulo i (Z.abs j).

Theorem smt_mod_pos : forall i j,
 0 < j ->
 smt_mod i j = Z.modulo i j.
Proof.
 intros * Hpos.
 unfold smt_mod.
 rewrite Z.abs_eq.
 2: { lia. }
 reflexivity.
Qed.

(* Confirm definitions correct *)
Theorem div_mod_euclidean : forall m n,
 n <> 0 ->
 let q := smt_div m n in
 let r := smt_mod m n in
  m = n * q + r /\
  0 <= r < Z.abs n.
Proof.
 intros * Hzero.

 split.
 2: { unfold smt_mod. apply Z.mod_pos_bound. lia. }

 destruct_decide (decide (0 <= n)) as Hpos.

 - rewrite smt_div_pos, smt_mod_pos.
   2: { lia. }
   2: { lia. }
   apply Z.div_mod; auto.

 - unfold smt_div, smt_mod.
   rewrite Z.sgn_neg.
   2: { lia. }
   rewrite Z.abs_neq.
   2: { lia. }

   rewrite (Z.div_mod m n) at 1; auto.

   destruct_decide (decide (m `mod` n = 0)) as Hzero'.
   + rewrite Z_div_zero_opp_r, Z_mod_zero_opp_r; auto. lia.
   + rewrite Z_div_nz_opp_r, Z_mod_nz_opp_r; auto. lia.
Qed.

Close Scope Z_scope.

Section Reals_IntsModels.

  Variable A : structure.
  Variable domain_σ_int : A.(domain) σ_int = Z.
  Variable domain_σ_real : A.(domain) σ_real = R.

  Definition cast_to_Z := cast domain_σ_int.
  Definition cast_to_R := cast domain_σ_real.
  Definition cast_to_bool := cast A.(domain_σ_bool).

  Open Scope Z_scope.

  Definition models_f_minus_neg_int : Prop :=
    let F := A.(interp) f_minus [ σ_int ] σ_int in
    (forall i, cast_to_Z (F i) = - (cast_to_Z i)).

  Definition models_f_minus_sub_int : Prop :=
    let F := A.(interp) f_minus [ σ_int; σ_int ] σ_int in
    (forall i j, cast_to_Z (F i j) = (cast_to_Z i) - (cast_to_Z j)).

  Definition models_f_plus_int : Prop :=
    let F := A.(interp) f_plus [ σ_int; σ_int ] σ_int in
    (forall i j, cast_to_Z (F i j) = (cast_to_Z i) + (cast_to_Z j)).

  Definition models_f_times_int : Prop :=
    let F := A.(interp) f_times [ σ_int; σ_int ] σ_int in
    (forall i j, cast_to_Z (F i j) = (cast_to_Z i) * (cast_to_Z j)).

  Definition models_f_idiv : Prop :=
    let F := A.(interp) f_idiv [ σ_int; σ_int ] σ_int in
    (forall i j,
     let jZ := cast_to_Z j in
      jZ <> 0 ->
      cast_to_Z (F i j) = smt_div (cast_to_Z i) jZ).

  Definition models_f_mod : Prop :=
    let F := A.(interp) f_mod [ σ_int; σ_int ] σ_int in
    (forall i j,
     let jZ := cast_to_Z j in
      jZ <> 0 ->
      cast_to_Z (F i j) = smt_mod (cast_to_Z i) jZ).

  Definition models_f_abs : Prop :=
    let F := A.(interp) f_abs [ σ_int ] σ_int in
    (forall i, cast_to_Z (F i) = Z.abs (cast_to_Z i)).

  Definition models_f_leq_int : Prop :=
    let F := A.(interp) f_leq [ σ_int; σ_int ] σ_bool in
    (forall i j, cast_to_bool (F i j) = ((cast_to_Z i) <=? (cast_to_Z j))%Z).

  Definition models_f_lt_int : Prop :=
    let F := A.(interp) f_lt [ σ_int; σ_int ] σ_bool in
    (forall i j, cast_to_bool (F i j) = ((cast_to_Z i) <? (cast_to_Z j))%Z).

  Definition models_f_geq_int : Prop :=
    let F := A.(interp) f_geq [ σ_int; σ_int ] σ_bool in
    (forall i j, cast_to_bool (F i j) = ((cast_to_Z i) >=? (cast_to_Z j))%Z).

  Definition models_f_gt_int : Prop :=
    let F := A.(interp) f_gt [ σ_int; σ_int ] σ_bool in
    (forall i j, cast_to_bool (F i j) = ((cast_to_Z i) >? (cast_to_Z j))%Z).

  Close Scope Z_scope.

  Open Scope R_scope.

  Definition models_f_minus_neg_real : Prop :=
    let F := A.(interp) f_minus [ σ_real ] σ_real in
    (forall x, cast_to_R (F x) = - (cast_to_R x)).

  Definition models_f_minus_sub_real : Prop :=
    let F := A.(interp) f_minus [ σ_real; σ_real ] σ_real in
    (forall x y, cast_to_R (F x y) = (cast_to_R x) - (cast_to_R y)).

  Definition models_f_plus_real : Prop :=
    let F := A.(interp) f_plus [ σ_real; σ_real ] σ_real in
    (forall x y, cast_to_R (F x y) = (cast_to_R x) + (cast_to_R y)).

  Definition models_f_times_real : Prop :=
    let F := A.(interp) f_times [ σ_real; σ_real ] σ_real in
    (forall x y, cast_to_R (F x y) = (cast_to_R x) * (cast_to_R y)).

  Definition models_f_div : Prop :=
    let F := A.(interp) f_div [ σ_real; σ_real ] σ_real in
    (forall x y,
     let yR := cast_to_R y in
     yR <> 0 ->
     cast_to_R (F x y) = (cast_to_R x) / yR).

  Definition models_f_leq_real : Prop :=
    let F := A.(interp) f_leq [ σ_real; σ_real ] σ_bool in
    (forall x y b,
        cast_to_bool (F x y) = b ->
        b = true <-> (cast_to_R x) <= (cast_to_R y)).

  Definition models_f_lt_real : Prop :=
    let F := A.(interp) f_lt [ σ_real; σ_real ] σ_bool in
    (forall x y b,
        cast_to_bool (F x y) = b ->
        b = true <-> (cast_to_R x) < (cast_to_R y)).

  Definition models_f_geq_real : Prop :=
    let F := A.(interp) f_geq [ σ_real; σ_real ] σ_bool in
    (forall x y b,
        cast_to_bool (F x y) = b ->
        b = true <-> (cast_to_R x) >= (cast_to_R y)).

  Definition models_f_gt_real : Prop :=
    let F := A.(interp) f_gt [ σ_real; σ_real ] σ_bool in
    (forall x y b,
        cast_to_bool (F x y) = b ->
        b = true <-> (cast_to_R x) > (cast_to_R y)).

  Close Scope R_scope.

  Definition models_f_to_real : Prop :=
    let F := A.(interp) f_to_real [ σ_int ] σ_real in
    (forall i, cast_to_R (F i) = IZR (cast_to_Z i)).

  Definition models_f_to_int : Prop :=
    let F := A.(interp) f_to_int [ σ_real ] σ_int in
    (forall x, cast_to_Z (F x) = Int_part (cast_to_R x)).

  Definition models_f_is_int : Prop :=
    let F := A.(interp) f_is_int [ σ_real ] σ_bool in
    (forall x b,
        cast_to_bool (F x) = b ->
        b = true <-> (exists (i : Z), IZR i = (cast_to_R x))).

  Definition models_f_divisible : Prop := forall n,
    let F := A.(interp) (f_divisible n) [ σ_int ] σ_bool in
    (forall x,
      n <> 0 ->
      cast_to_bool (F x) = true <-> Z.divide (Z.of_nat n) (cast_to_Z x)).

  Definition models_f_int_literal : Prop := forall i,
    let F := A.(interp) (f_int_literal i) [] σ_int in
    cast_to_Z F = i.

  Definition models_f_decimal_literal : Prop := forall q,
    let F := A.(interp) (f_decimal_literal q) [] σ_real in
    cast_to_R F = Q2R (Qcanon.this q).

  Record models_reals_ints : Prop := {
    mri_minus_neg_int : models_f_minus_neg_int;
    mri_minus_sub_int : models_f_minus_sub_int;
    mri_plus_int : models_f_plus_int;
    mri_times_int : models_f_times_int;
    mri_idiv : models_f_idiv;
    mri_mod : models_f_mod;
    mri_abs : models_f_abs;
    mri_leq_int : models_f_leq_int;
    mri_lt_int : models_f_lt_int;
    mri_geq_int : models_f_geq_int;
    mri_gt_int : models_f_gt_int;
    mri_minus_neg_real : models_f_minus_neg_real;
    mri_minus_sub_real : models_f_minus_sub_real;
    mri_plus_real : models_f_plus_real;
    mri_times_real : models_f_times_real;
    mri_div : models_f_div;
    mri_leq_real : models_f_leq_real;
    mri_lt_real : models_f_lt_real;
    mri_geq_real : models_f_geq_real;
    mri_gt_real : models_f_gt_real;
    mri_to_real : models_f_to_real;
    mri_to_int : models_f_to_int;
    mri_is_int : models_f_is_int;
    mri_divisible : models_f_divisible;
    mri_int_literal : models_f_int_literal;
    mri_decimal_literal : models_f_decimal_literal;
  }.

End Reals_IntsModels.

Arguments cast_to_Z {_}.

Arguments mri_minus_neg_int {_} {_} {_}.
Arguments mri_minus_sub_int {_} {_} {_}.
Arguments mri_plus_int {_} {_} {_}.
Arguments mri_times_int {_} {_} {_}.
Arguments mri_idiv {_} {_} {_}.
Arguments mri_mod {_} {_} {_}.
Arguments mri_abs {_} {_} {_}.
Arguments mri_leq_int {_} {_} {_}.
Arguments mri_lt_int {_} {_} {_}.
Arguments mri_geq_int {_} {_} {_}.
Arguments mri_gt_int {_} {_} {_}.
Arguments mri_minus_neg_real {_} {_} {_}.
Arguments mri_minus_sub_real {_} {_} {_}.
Arguments mri_plus_real {_} {_} {_}.
Arguments mri_times_real {_} {_} {_}.
Arguments mri_div {_} {_} {_}.
Arguments mri_leq_real {_} {_} {_}.
Arguments mri_lt_real {_} {_} {_}.
Arguments mri_geq_real {_} {_} {_}.
Arguments mri_gt_real {_} {_} {_}.
Arguments mri_to_real {_} {_} {_}.
Arguments mri_to_int {_} {_} {_}.
Arguments mri_is_int {_} {_} {_}.
Arguments mri_divisible {_} {_} {_}.
Arguments mri_int_literal {_} {_} {_}.
Arguments mri_decimal_literal {_} {_} {_}.

Definition T_reals_ints : pretheory :=
  {|
    pΣ := Σ_reals_ints;
    pmodels A :=
      {HZ : A.(domain) σ_int = Z &
              {HR : A.(domain) σ_real = R &
                      models_reals_ints A HZ HR}}
  |}.

(* The symbol is one of [Σ_reals_ints]'s.  The three infinite families are
   tried first: they fail immediately on a symbol from the finite set, whereas
   [set_solver] on a non-member of that set is slow enough to matter. *)
Local Ltac ri_func :=
  cbn [funcs Σ_reals_ints];
  first
    [ right; left; eexists; split; [eassumption | reflexivity]
    | right; right; left; eexists; reflexivity
    | right; right; right; eexists; reflexivity
    | left; set_solver ].

(** Every condition names one symbol, and all of them are declared by
    [Σ_reals_ints]. *)
Theorem T_reals_ints_local : pretheory_local T_reals_ints.
Proof.
  intros D Hbool Hmap i j Hagree [HZ [HR Hm]].
  exists HZ, HR.
  assert (Hrw : forall f, Σ_reals_ints.(funcs) f ->
                  forall σs σ, j f σs σ = i f σs σ)
    by (intros f Hf σs σ; symmetry; exact (Hagree f Hf σs σ)).
  destruct Hm as [A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26].
  (* The four real comparisons and [is_int] put the interpretation on the left
     of an implication, so for those the rewrite lands in the hypothesis. *)
  constructor.
  - unfold models_f_minus_neg_int in A1 |- *; cbv zeta in A1 |- *;
    cbn [interp structure_of] in A1 |- *;
    intros; rewrite Hrw by ri_func; apply A1; auto.
  - unfold models_f_minus_sub_int in A2 |- *; cbv zeta in A2 |- *;
    cbn [interp structure_of] in A2 |- *;
    intros; rewrite Hrw by ri_func; apply A2; auto.
  - unfold models_f_plus_int in A3 |- *; cbv zeta in A3 |- *;
    cbn [interp structure_of] in A3 |- *;
    intros; rewrite Hrw by ri_func; apply A3; auto.
  - unfold models_f_times_int in A4 |- *; cbv zeta in A4 |- *;
    cbn [interp structure_of] in A4 |- *;
    intros; rewrite Hrw by ri_func; apply A4; auto.
  - unfold models_f_idiv in A5 |- *; cbv zeta in A5 |- *;
    cbn [interp structure_of] in A5 |- *;
    intros; rewrite Hrw by ri_func; apply A5; auto.
  - unfold models_f_mod in A6 |- *; cbv zeta in A6 |- *;
    cbn [interp structure_of] in A6 |- *;
    intros; rewrite Hrw by ri_func; apply A6; auto.
  - unfold models_f_abs in A7 |- *; cbv zeta in A7 |- *;
    cbn [interp structure_of] in A7 |- *;
    intros; rewrite Hrw by ri_func; apply A7; auto.
  - unfold models_f_leq_int in A8 |- *; cbv zeta in A8 |- *;
    cbn [interp structure_of] in A8 |- *;
    intros; rewrite Hrw by ri_func; apply A8; auto.
  - unfold models_f_lt_int in A9 |- *; cbv zeta in A9 |- *;
    cbn [interp structure_of] in A9 |- *;
    intros; rewrite Hrw by ri_func; apply A9; auto.
  - unfold models_f_geq_int in A10 |- *; cbv zeta in A10 |- *;
    cbn [interp structure_of] in A10 |- *;
    intros; rewrite Hrw by ri_func; apply A10; auto.
  - unfold models_f_gt_int in A11 |- *; cbv zeta in A11 |- *;
    cbn [interp structure_of] in A11 |- *;
    intros; rewrite Hrw by ri_func; apply A11; auto.
  - unfold models_f_minus_neg_real in A12 |- *; cbv zeta in A12 |- *;
    cbn [interp structure_of] in A12 |- *;
    intros; rewrite Hrw by ri_func; apply A12; auto.
  - unfold models_f_minus_sub_real in A13 |- *; cbv zeta in A13 |- *;
    cbn [interp structure_of] in A13 |- *;
    intros; rewrite Hrw by ri_func; apply A13; auto.
  - unfold models_f_plus_real in A14 |- *; cbv zeta in A14 |- *;
    cbn [interp structure_of] in A14 |- *;
    intros; rewrite Hrw by ri_func; apply A14; auto.
  - unfold models_f_times_real in A15 |- *; cbv zeta in A15 |- *;
    cbn [interp structure_of] in A15 |- *;
    intros; rewrite Hrw by ri_func; apply A15; auto.
  - unfold models_f_div in A16 |- *; cbv zeta in A16 |- *;
    cbn [interp structure_of] in A16 |- *;
    intros; rewrite Hrw by ri_func; apply A16; auto.
  - unfold models_f_leq_real in A17 |- *; cbv zeta in A17 |- *;
    cbn [interp structure_of] in A17 |- *;
    intros x y b Hb; rewrite Hrw in Hb by ri_func; exact (A17 x y b Hb).
  - unfold models_f_lt_real in A18 |- *; cbv zeta in A18 |- *;
    cbn [interp structure_of] in A18 |- *;
    intros x y b Hb; rewrite Hrw in Hb by ri_func; exact (A18 x y b Hb).
  - unfold models_f_geq_real in A19 |- *; cbv zeta in A19 |- *;
    cbn [interp structure_of] in A19 |- *;
    intros x y b Hb; rewrite Hrw in Hb by ri_func; exact (A19 x y b Hb).
  - unfold models_f_gt_real in A20 |- *; cbv zeta in A20 |- *;
    cbn [interp structure_of] in A20 |- *;
    intros x y b Hb; rewrite Hrw in Hb by ri_func; exact (A20 x y b Hb).
  - unfold models_f_to_real in A21 |- *; cbv zeta in A21 |- *;
    cbn [interp structure_of] in A21 |- *;
    intros; rewrite Hrw by ri_func; apply A21; auto.
  - unfold models_f_to_int in A22 |- *; cbv zeta in A22 |- *;
    cbn [interp structure_of] in A22 |- *;
    intros; rewrite Hrw by ri_func; apply A22; auto.
  - unfold models_f_is_int in A23 |- *; cbv zeta in A23 |- *;
    cbn [interp structure_of] in A23 |- *;
    intros x b Hb; rewrite Hrw in Hb by ri_func; exact (A23 x b Hb).
  - unfold models_f_divisible in A24 |- *; cbv zeta in A24 |- *;
    cbn [interp structure_of] in A24 |- *;
    intros n x Hn; rewrite Hrw by ri_func; exact (A24 n x Hn).
  - unfold models_f_int_literal in A25 |- *; cbv zeta in A25 |- *;
    cbn [interp structure_of] in A25 |- *;
    intros; rewrite Hrw by ri_func; apply A25; auto.
  - unfold models_f_decimal_literal in A26 |- *; cbv zeta in A26 |- *;
    cbn [interp structure_of] in A26 |- *;
    intros; rewrite Hrw by ri_func; apply A26; auto.
Qed.

(** The operations are the ordinary arithmetic on the canonical domains.
    The three families of literal symbols carry their own payloads. *)
(** The decisions the interpretation of a comparison makes.  Each is
    constructive relative to [R]: Stdlib proves the order decisions and
    [Req_dec_T] from [R]'s own two axioms, and divisibility is decidable
    outright. *)
Local Instance Rle_decision (x y : R) : Decision (Rle x y) := Rle_dec x y.
Local Instance Rlt_decision (x y : R) : Decision (Rlt x y) := Rlt_dec x y.
Local Instance Rge_decision (x y : R) : Decision (Rge x y) := Rge_dec x y.
Local Instance Rgt_decision (x y : R) : Decision (Rgt x y) := Rgt_dec x y.

Local Instance Zdivide_decision (a b : Z) : Decision (Z.divide a b) :=
  Znumtheory.Zdivide_dec a b.

(** A real is an integer exactly when it is its own integer part. *)
Local Instance real_is_int_decision (x : R) :
  Decision (exists i : Z, IZR i = x).
Proof.
  destruct (Req_dec_T (IZR (Int_part x)) x) as [Hx|Hx].
  - left. by exists (Int_part x).
  - right. intros [i Hi]. apply Hx. subst x. f_equal. symmetry.
    apply Int_part_spec. lra.
Qed.

Section Reals_IntsInterpretable.

  Context (D : sort -> Type).
  Context (witness : forall σ, D σ).
  Context (Hbool : D σ_bool = bool).
  Context (Hmap : forall σ1 σ2, D (τ_map σ1 σ2) = (D σ1 -> D σ2)).
  Context (HZ : D σ_int = Z).
  Context (HR : D σ_real = R).

  Local Notation base := (interp_const D witness).

  (* Recovering a literal's payload from its symbol.  Unlike the string
     literals of [Theory.Strings], these symbols are decimal renderings, which
     no simple function inverts; the payload is recovered by choice, and that
     is sound because the renderings are injective.  [pretty] is injective
     already (stdpp); what has to be added is that it never emits the "/" that
     separates a decimal's two halves. *)

  Local Fixpoint slash_free (s : string) : Prop :=
    match s with
    | EmptyString => True
    | String c s' => c <> "/"%char /\ slash_free s'
    end.

  Local Lemma pretty_N_go_slash_free : forall (x : N) s,
      slash_free s -> slash_free (pretty_N_go x s).
  Proof.
    intros x. induction (N.lt_wf_0 x) as [x _ IH]; intros s Hs.
    destruct (decide (0 < x)%N) as [Hx | Hx].
    - rewrite pretty_N_go_step by done.
      apply IH; [by apply N.div_lt |]. split; [| exact Hs].
      unfold pretty_N_char. repeat case_match; discriminate.
    - assert (x = 0)%N as -> by lia. by rewrite pretty_N_go_0.
  Qed.

  Local Lemma pretty_N_slash_free : forall n : N, slash_free (pretty n).
  Proof.
    intros n. unfold pretty, pretty_N.
    destruct (decide (n = 0)%N); [by cbn | by apply pretty_N_go_slash_free].
  Qed.

  Local Lemma pretty_Z_slash_free : forall z : Z, slash_free (pretty z).
  Proof.
    intros [| p | p]; cbn; [by cbn | apply pretty_N_slash_free |].
    split; [discriminate | apply pretty_N_slash_free].
  Qed.

  Local Lemma pretty_positive_slash_free : forall p : positive,
      slash_free (pretty p).
  Proof. intros p. apply pretty_N_slash_free. Qed.

  (* Two slash-free prefixes followed by a slash split a string uniquely. *)
  Local Lemma app_slash_inj : forall s1 s2 t1 t2,
      slash_free s1 -> slash_free s2 ->
      (s1 ++ String "/" t1)%string = (s2 ++ String "/" t2)%string ->
      s1 = s2 /\ t1 = t2.
  Proof.
    induction s1 as [| c1 s1 IH]; intros [| c2 s2] t1 t2 H1 H2 Heq; cbn in *.
    - injection Heq as <-. done.
    - injection Heq as Hc _. destruct H2 as [Hne _]. by destruct Hne.
    - injection Heq as Hc _. destruct H1 as [Hne _]. by destruct Hne.
    - injection Heq as <- Heq. destruct H1 as [_ H1], H2 as [_ H2].
      destruct (IH s2 t1 t2 H1 H2 Heq) as [-> ->]. done.
  Qed.

  (* The three renderings are injective, so a symbol determines its payload.
     [injection] peels a shared prefix character by character and leaves an
     empty append behind, which [String.append]'s [simpl] settings will not
     discharge; these two conversions do. *)

  Local Lemma app_empty_l : forall s, String.append "" s = s.
  Proof. reflexivity. Qed.

  Local Lemma app_slash : forall t, ("/" ++ t)%string = String "/" t.
  Proof. reflexivity. Qed.

  Local Lemma f_divisible_inj : forall n1 n2,
      f_divisible n1 = f_divisible n2 -> n1 = n2.
  Proof. intros n1 n2 Heq. unfold f_divisible in Heq. by simplify_eq. Qed.

  Local Lemma f_int_literal_inj : forall i1 i2,
      f_int_literal i1 = f_int_literal i2 -> i1 = i2.
  Proof.
    intros i1 i2 Heq. unfold f_int_literal in Heq. injection Heq as Heq.
    (* [injection] peels the shared prefix character by character *)
    rewrite !app_empty_l in Heq. by apply (inj pretty) in Heq.
  Qed.

  Local Lemma f_decimal_literal_inj : forall q1 q2,
      f_decimal_literal q1 = f_decimal_literal q2 -> q1 = q2.
  Proof.
    intros q1 q2 Heq. unfold f_decimal_literal in Heq. injection Heq as Heq.
    rewrite !app_empty_l, !app_slash in Heq.
    destruct (app_slash_inj _ _ _ _ (pretty_Z_slash_free (Qnum q1))
                (pretty_Z_slash_free (Qnum q2)) Heq) as [Hn Hd].
    apply (inj pretty) in Hn. apply (inj pretty) in Hd.
    apply Qc_decomp.
    destruct q1 as [[n1 d1] ?], q2 as [[n2 d2] ?]. cbn in *. by subst.
  Qed.

  (* The payload is read back off the rendering, and the candidate is
     checked by rendering it again, so a symbol outside the family gets the
     default rather than another family member's payload. *)

  Local Definition divisible_value (f : func) : nat :=
    match parse_divisible f with
    | Some n => if decide (n <> 0 /\ f_divisible n = f) then n else 1
    | None => 1
    end.

  Local Lemma divisible_value_eq : forall n,
      n <> 0 -> divisible_value (f_divisible n) = n.
  Proof.
    intros n Hn. unfold divisible_value.
    rewrite parse_divisible_eq. by rewrite decide_True.
  Qed.

  Local Definition int_literal_value (f : func) : Z :=
    match parse_int_literal f with
    | Some i => if decide (f_int_literal i = f) then i else 0%Z
    | None => 0%Z
    end.

  Local Lemma int_literal_value_eq : forall i,
      int_literal_value (f_int_literal i) = i.
  Proof.
    intros i. unfold int_literal_value.
    rewrite parse_int_literal_eq. by rewrite decide_True.
  Qed.

  Local Definition decimal_literal_value (f : func) : Qc :=
    match parse_decimal_literal f with
    | Some q => if decide (f_decimal_literal q = f) then q else Q2Qc 0
    | None => Q2Qc 0
    end.

  Local Lemma decimal_literal_value_eq : forall q,
      decimal_literal_value (f_decimal_literal q) = q.
  Proof.
    intros q. unfold decimal_literal_value.
    rewrite parse_decimal_literal_eq. by rewrite decide_True.
  Qed.

  Local Notation Zop1 op := (fun x : D σ_int => cast_sym HZ (op (cast HZ x))).
  Local Notation Zop2 op :=
    (fun x y : D σ_int => cast_sym HZ (op (cast HZ x) (cast HZ y))).
  Local Notation Zcmp op :=
    (fun x y : D σ_int => cast_sym Hbool (op (cast HZ x) (cast HZ y))).
  Local Notation Rop1 op := (fun x : D σ_real => cast_sym HR (op (cast HR x))).
  Local Notation Rop2 op :=
    (fun x y : D σ_real => cast_sym HR (op (cast HR x) (cast HR y))).
  Local Notation Rcmp P :=
    (fun x y : D σ_real =>
       cast_sym Hbool
         (if decide (P (cast HR x) (cast HR y))
          then true else false)).

  (* The three literal families are keyed on the symbol rather than on a fixed
     name, so they sit at the bottom: every symbol gets these three ranks, and
     the declared operations are layered on top. *)
  Local Definition ri_literals (f : func) : forall σs σ, interpretation D σs σ :=
    interp_insert_rank D [σ_int] σ_bool
      (fun x : D σ_int =>
         cast_sym Hbool
           (if decide
                 (Z.divide (Z.of_nat (divisible_value f)) (cast HZ x))
            then true else false))
   (interp_insert_rank D [] σ_int (cast_sym HZ (int_literal_value f))
   (interp_insert_rank D [] σ_real
      (cast_sym HR (Q2R (Qcanon.this (decimal_literal_value f))))
    base)).

  Definition reals_ints_interp : forall f σs σ, interpretation D σs σ :=
    interp_insert_func D f_minus
      (interp_insert_rank D [σ_int] σ_int (Zop1 Z.opp)
      (interp_insert_rank D [σ_int; σ_int] σ_int (Zop2 Z.sub)
      (interp_insert_rank D [σ_real] σ_real (Rop1 Ropp)
      (interp_insert_rank D [σ_real; σ_real] σ_real (Rop2 Rminus) base))))
   (interp_insert_func D f_plus
      (interp_insert_rank D [σ_int; σ_int] σ_int (Zop2 Z.add)
      (interp_insert_rank D [σ_real; σ_real] σ_real (Rop2 Rplus) base))
   (interp_insert_func D f_times
      (interp_insert_rank D [σ_int; σ_int] σ_int (Zop2 Z.mul)
      (interp_insert_rank D [σ_real; σ_real] σ_real (Rop2 Rmult) base))
   (interp_insert_func D f_idiv
      (interp_insert_rank D [σ_int; σ_int] σ_int (Zop2 smt_div) base)
   (interp_insert_func D f_mod
      (interp_insert_rank D [σ_int; σ_int] σ_int (Zop2 smt_mod) base)
   (interp_insert_func D f_abs
      (interp_insert_rank D [σ_int] σ_int (Zop1 Z.abs) base)
   (interp_insert_func D f_leq
      (interp_insert_rank D [σ_int; σ_int] σ_bool (Zcmp Z.leb)
      (interp_insert_rank D [σ_real; σ_real] σ_bool (Rcmp Rle) base))
   (interp_insert_func D f_lt
      (interp_insert_rank D [σ_int; σ_int] σ_bool (Zcmp Z.ltb)
      (interp_insert_rank D [σ_real; σ_real] σ_bool (Rcmp Rlt) base))
   (interp_insert_func D f_geq
      (interp_insert_rank D [σ_int; σ_int] σ_bool (Zcmp Z.geb)
      (interp_insert_rank D [σ_real; σ_real] σ_bool (Rcmp Rge) base))
   (interp_insert_func D f_gt
      (interp_insert_rank D [σ_int; σ_int] σ_bool (Zcmp Z.gtb)
      (interp_insert_rank D [σ_real; σ_real] σ_bool (Rcmp Rgt) base))
   (interp_insert_func D f_div
      (interp_insert_rank D [σ_real; σ_real] σ_real (Rop2 Rdiv) base)
   (interp_insert_func D f_to_real
      (interp_insert_rank D [σ_int] σ_real
         (fun x : D σ_int => cast_sym HR (IZR (cast HZ x))) base)
   (interp_insert_func D f_to_int
      (interp_insert_rank D [σ_real] σ_int
         (fun x : D σ_real => cast_sym HZ (Int_part (cast HR x))) base)
   (interp_insert_func D f_is_int
      (interp_insert_rank D [σ_real] σ_bool
         (fun x : D σ_real =>
            cast_sym Hbool
              (if decide (exists i : Z, IZR i = cast HR x)
               then true else false)) base)
    ri_literals))))))))))))).

  (* Read one symbol, then one rank, out of the stack. *)
  Local Ltac ri_peel :=
    repeat (rewrite interp_insert_func_ne; [| discriminate]);
    rewrite interp_insert_func_eq;
    repeat (rewrite interp_insert_rank_ne; [| discriminate]);
    rewrite interp_insert_rank_eq.

  Local Ltac ri_peel_in H :=
    unfold reals_ints_interp in H;
    repeat (rewrite interp_insert_func_ne in H; [| discriminate]);
    rewrite interp_insert_func_eq in H;
    repeat (rewrite interp_insert_rank_ne in H; [| discriminate]);
    rewrite interp_insert_rank_eq in H.

  (* The literal families are at the bottom, so there is no symbol to hit. *)
  Local Ltac ri_peel_literal :=
    repeat (rewrite interp_insert_func_ne; [| discriminate]);
    unfold ri_literals;
    repeat (rewrite interp_insert_rank_ne; [| discriminate]);
    rewrite interp_insert_rank_eq.

  Theorem reals_ints_interp_models :
    models_reals_ints (structure_of D Hbool Hmap reals_ints_interp) HZ HR.
  Proof.
    constructor;
      unfold models_f_minus_neg_int, models_f_minus_sub_int, models_f_plus_int,
        models_f_times_int, models_f_idiv, models_f_mod, models_f_abs,
        models_f_leq_int, models_f_lt_int, models_f_geq_int, models_f_gt_int,
        models_f_minus_neg_real, models_f_minus_sub_real, models_f_plus_real,
        models_f_times_real, models_f_div, models_f_leq_real, models_f_lt_real,
        models_f_geq_real, models_f_gt_real, models_f_to_real, models_f_to_int,
        models_f_is_int, models_f_divisible, models_f_int_literal,
        models_f_decimal_literal, cast_to_Z, cast_to_R, cast_to_bool;
      cbv zeta; cbn [interp domain structure_of].
    - intros i. unfold reals_ints_interp. ri_peel. apply cast_cast_sym.
    - intros i j. unfold reals_ints_interp. ri_peel. apply cast_cast_sym.
    - intros i j. unfold reals_ints_interp. ri_peel. apply cast_cast_sym.
    - intros i j. unfold reals_ints_interp. ri_peel. apply cast_cast_sym.
    - intros i j Hj. unfold reals_ints_interp. ri_peel. apply cast_cast_sym.
    - intros i j Hj. unfold reals_ints_interp. ri_peel. apply cast_cast_sym.
    - intros i. unfold reals_ints_interp. ri_peel. apply cast_cast_sym.
    - intros i j. unfold reals_ints_interp. ri_peel. apply cast_cast_sym.
    - intros i j. unfold reals_ints_interp. ri_peel. apply cast_cast_sym.
    - intros i j. unfold reals_ints_interp. ri_peel. apply cast_cast_sym.
    - intros i j. unfold reals_ints_interp. ri_peel. apply cast_cast_sym.
    - intros x. unfold reals_ints_interp. ri_peel. apply cast_cast_sym.
    - intros x y. unfold reals_ints_interp. ri_peel. apply cast_cast_sym.
    - intros x y. unfold reals_ints_interp. ri_peel. apply cast_cast_sym.
    - intros x y. unfold reals_ints_interp. ri_peel. apply cast_cast_sym.
    - intros x y Hy. unfold reals_ints_interp. ri_peel. apply cast_cast_sym.
    - intros x y b Hb. ri_peel_in Hb. rewrite cast_cast_sym in Hb.
      destruct (decide _) as [Hc | Hc];
        symmetry in Hb; subst b.
      + split; [intros _; exact Hc | intros _; reflexivity].
      + split; [intros Hd; discriminate | intros Hd; contradiction].
    - intros x y b Hb. ri_peel_in Hb. rewrite cast_cast_sym in Hb.
      destruct (decide _) as [Hc | Hc];
        symmetry in Hb; subst b.
      + split; [intros _; exact Hc | intros _; reflexivity].
      + split; [intros Hd; discriminate | intros Hd; contradiction].
    - intros x y b Hb. ri_peel_in Hb. rewrite cast_cast_sym in Hb.
      destruct (decide _) as [Hc | Hc];
        symmetry in Hb; subst b.
      + split; [intros _; exact Hc | intros _; reflexivity].
      + split; [intros Hd; discriminate | intros Hd; contradiction].
    - intros x y b Hb. ri_peel_in Hb. rewrite cast_cast_sym in Hb.
      destruct (decide _) as [Hc | Hc];
        symmetry in Hb; subst b.
      + split; [intros _; exact Hc | intros _; reflexivity].
      + split; [intros Hd; discriminate | intros Hd; contradiction].
    - intros i. unfold reals_ints_interp. ri_peel. apply cast_cast_sym.
    - intros x. unfold reals_ints_interp. ri_peel. apply cast_cast_sym.
    - intros x b Hb. ri_peel_in Hb. rewrite cast_cast_sym in Hb.
      destruct (decide _) as [Hc | Hc];
        symmetry in Hb; subst b.
      + split; [intros _; exact Hc | intros _; reflexivity].
      + split; [intros Hd; discriminate | intros Hd; contradiction].
    - intros n x Hn. unfold reals_ints_interp. ri_peel_literal.
      rewrite (divisible_value_eq n Hn), cast_cast_sym.
      destruct (decide _) as [Hc | Hc].
      + split; [intros _; exact Hc | intros _; reflexivity].
      + split; [intros Hd; discriminate | intros Hd; contradiction].
    - intros i. unfold reals_ints_interp. ri_peel_literal.
      rewrite int_literal_value_eq. apply cast_cast_sym.
    - intros q. unfold reals_ints_interp. ri_peel_literal.
      rewrite decimal_literal_value_eq. apply cast_cast_sym.
  Qed.

  Corollary T_reals_ints_interpretable :
    pretheory_interpretable T_reals_ints D Hbool Hmap.
  Proof.
    exists reals_ints_interp, HZ, HR. exact reals_ints_interp_models.
  Qed.

End Reals_IntsInterpretable.

Theorem neg_has_sort_int : forall Σ t,
    Σ_reals_ints ⊑ Σ ->
    (Σ ⊢ t : σ_int) ->
    Σ ⊢ neg_ t : σ_int.
Proof.
  intros * Hsub Ht.
  econstructor.
  - exists ∅. sauto l:on.
  - intros * Hrank.
    eapply monomorphic_rank_conservative in Hrank; eauto.
    fcrush. set_solver.
  - reflexivity.
  - intros * Ht_i Hσ_i.
    rewrite list_lookup_singleton in Ht_i.
    destruct i; try congruence. simpl in *.
    simplify_eq. assumption.
Qed.

Theorem minus_has_sort_int : forall Σ t1 t2,
    Σ_reals_ints ⊑ Σ ->
    (Σ ⊢ t1 : σ_int) ->
    (Σ ⊢ t2 : σ_int) ->
    Σ ⊢ minus_ t1 t2 : σ_int.
Proof.
  intros * Hsub Ht.
  econstructor.
  - exists ∅, [σ_int; σ_int], σ_int. sauto qb:on dep:on.
  - intros * Hrank.
    eapply monomorphic_rank_conservative in Hrank; eauto.
    fcrush. set_solver.
  - reflexivity.
  - intros * Ht_i Hσ_i.
    destruct i; simpl in *.
    + simplify_eq. assumption.
    + rewrite list_lookup_singleton in Ht_i.
      destruct i; try congruence. simpl in *.
      simplify_eq. assumption.
Qed.

Theorem plus_has_sort_int : forall Σ t1 t2,
    Σ_reals_ints ⊑ Σ ->
    (Σ ⊢ t1 : σ_int) ->
    (Σ ⊢ t2 : σ_int) ->
    Σ ⊢ plus_ t1 t2 : σ_int.
Proof.
  intros * Hsub Ht.
  econstructor.
  - exists ∅, [σ_int; σ_int], σ_int. sauto qb:on dep:on.
  - intros * Hrank.
    eapply monomorphic_rank_conservative in Hrank; eauto.
    fcrush. set_solver.
  - reflexivity.
  - intros * Ht_i Hσ_i.
    destruct i; simpl in *.
    + simplify_eq. assumption.
    + rewrite list_lookup_singleton in Ht_i.
      destruct i; try congruence. simpl in *.
      simplify_eq. assumption.
Qed.

(** Addition on the integers is addition in [Z]. *)
Lemma eval_plus_int :
  forall Σ A θ HZ HR (Hri : models_reals_ints A HZ HR) t1 t2 i j,
    Σ_reals_ints ⊑ Σ ->
    ⟦ t1 : σ_int ⟧(Σ, A, θ) ⇓ cast_sym HZ i ->
    ⟦ t2 : σ_int ⟧(Σ, A, θ) ⇓ cast_sym HZ j ->
    ⟦ plus_ t1 t2 : σ_int ⟧(Σ, A, θ) ⇓ (cast_sym HZ (i + j)%Z).
Proof.
  intros Σ A θ HZ HR Hri t1 t2 i j Hsub Ht1 Ht2.
  set (vplus := interp_apply A.(domain)
    (A.(interp) f_plus [σ_int; σ_int] σ_int)
    (HCons σ_int [σ_int] (cast_sym HZ i) (HCons σ_int [] (cast_sym HZ j) HNil))).
  assert (Hplus : ⟦ plus_ t1 t2 : σ_int ⟧(Σ, A, θ) ⇓ vplus).
  { unfold plus_, vplus.
    eapply E_TApp with (σs := [σ_int; σ_int])
      (vs := HCons σ_int [σ_int] (cast_sym HZ i)
               (HCons σ_int [] (cast_sym HZ j) HNil)).
    - repeat constructor; [exact Ht1 | exact Ht2].
    - constructor.
    - apply rank_monomorphic;
        [ apply (rank_extends Hsub); constructor
        | repeat constructor | repeat constructor ].
    - reflexivity. }
  replace (cast_sym HZ (i + j)%Z) with vplus; [exact Hplus |].
  apply (proj1 (cast_eq_iff_eq_cast_sym HZ vplus (i + j)%Z)).
  unfold vplus. autorewrite with interp_apply.
  pose proof (mri_plus_int Hri (cast_sym HZ i) (cast_sym HZ j)) as Hp.
  unfold models_f_plus_int, cast_to_Z in Hp. cbv zeta in Hp.
  rewrite Hp, !cast_cast_sym. reflexivity.
Qed.

Theorem times_has_sort_int : forall Σ t1 t2,
    Σ_reals_ints ⊑ Σ ->
    (Σ ⊢ t1 : σ_int) ->
    (Σ ⊢ t2 : σ_int) ->
    Σ ⊢ times_ t1 t2 : σ_int.
Proof.
  intros * Hsub Ht.
  econstructor.
  - exists ∅, [σ_int; σ_int], σ_int. sauto qb:on dep:on.
  - intros * Hrank.
    eapply monomorphic_rank_conservative in Hrank; eauto.
    fcrush. set_solver.
  - reflexivity.
  - intros * Ht_i Hσ_i.
    destruct i; simpl in *.
    + simplify_eq. assumption.
    + rewrite list_lookup_singleton in Ht_i.
      destruct i; try congruence. simpl in *.
      simplify_eq. assumption.
Qed.

Lemma eval_times_int :
  forall Σ A θ t1 t2 (w1 w2 : A.(domain) σ_int),
    Σ_reals_ints ⊑ Σ ->
    ⟦ t1 : σ_int ⟧(Σ, A, θ) ⇓ w1 ->
    ⟦ t2 : σ_int ⟧(Σ, A, θ) ⇓ w2 ->
    ⟦ times_ t1 t2 : σ_int ⟧(Σ, A, θ)
      ⇓ interp_apply A.(domain)
         (A.(interp) f_times [σ_int; σ_int] σ_int)
         (HCons σ_int [σ_int] w1 (HCons σ_int [] w2 HNil)).
Proof.
  intros Σ A θ t1 t2 w1 w2 Hsub Ht1 Ht2.
  unfold times_. eapply E_TApp with (σs := [σ_int; σ_int])
    (vs := HCons σ_int [σ_int] w1 (HCons σ_int [] w2 HNil)).
  - repeat constructor; [exact Ht1 | exact Ht2].
  - constructor.
  - apply rank_monomorphic;
      [ apply (rank_extends Hsub); constructor
      | repeat constructor | repeat constructor ].
  - reflexivity.
Qed.


Theorem idiv_has_sort : forall Σ t1 t2,
    Σ_reals_ints ⊑ Σ ->
    (Σ ⊢ t1 : σ_int) ->
    (Σ ⊢ t2 : σ_int) ->
    Σ ⊢ idiv_ t1 t2 : σ_int.
Proof.
  intros * Hsub Ht.
  econstructor.
  - exists ∅, [σ_int; σ_int], σ_int. sauto qb:on dep:on.
  - intros * Hrank.
    eapply monomorphic_rank_conservative in Hrank; eauto.
    sauto. set_solver.
  - reflexivity.
  - intros * Ht_i Hσ_i.
    destruct i; simpl in *.
    + simplify_eq. assumption.
    + rewrite list_lookup_singleton in Ht_i.
      destruct i; try congruence. simpl in *.
      simplify_eq. assumption.
Qed.

Theorem mod_has_sort : forall Σ t1 t2,
    Σ_reals_ints ⊑ Σ ->
    (Σ ⊢ t1 : σ_int) ->
    (Σ ⊢ t2 : σ_int) ->
    Σ ⊢ mod_ t1 t2 : σ_int.
Proof.
  intros * Hsub Ht.
  econstructor.
  - exists ∅, [σ_int; σ_int], σ_int. sauto qb:on dep:on.
  - intros * Hrank.
    eapply monomorphic_rank_conservative in Hrank; eauto.
    sauto. set_solver.
  - reflexivity.
  - intros * Ht_i Hσ_i.
    destruct i; simpl in *.
    + simplify_eq. assumption.
    + rewrite list_lookup_singleton in Ht_i.
      destruct i; try congruence. simpl in *.
      simplify_eq. assumption.
Qed.

Theorem abs_has_sort : forall Σ t,
    Σ_reals_ints ⊑ Σ ->
    (Σ ⊢ t : σ_int) ->
    Σ ⊢ abs_ t : σ_int.
Proof.
  intros * Hsub Ht.
  econstructor.
  - exists ∅, [σ_int], σ_int. sauto q:on dep:on.
  - intros * Hrank.
    eapply monomorphic_rank_conservative in Hrank; eauto.
    sauto. set_solver.
  - reflexivity.
  - intros * Ht_i Hσ_i.
    rewrite list_lookup_singleton in Ht_i.
    destruct i; try congruence. simpl in *.
    simplify_eq. assumption.
Qed.

Theorem leq_has_sort_int : forall Σ t1 t2,
    Σ_reals_ints ⊑ Σ ->
    (Σ ⊢ t1 : σ_int) ->
    (Σ ⊢ t2 : σ_int) ->
    Σ ⊢ leq_ t1 t2 : σ_bool.
Proof.
  intros * Hsub Ht.
  econstructor.
  - exists ∅, [σ_int; σ_int], σ_bool. sauto q:on dep:on.
  - intros * Hrank.
    eapply monomorphic_rank_conservative in Hrank; eauto.
    sauto. set_solver.
  - reflexivity.
  - intros * Ht_i Hσ_i.
    destruct i; simpl in *.
    + simplify_eq. assumption.
    + rewrite list_lookup_singleton in Ht_i.
      destruct i; try congruence. simpl in *.
      simplify_eq. assumption.
Qed.

Theorem lt_has_sort_int : forall Σ t1 t2,
    Σ_reals_ints ⊑ Σ ->
    (Σ ⊢ t1 : σ_int) ->
    (Σ ⊢ t2 : σ_int) ->
    Σ ⊢ lt_ t1 t2 : σ_bool.
Proof.
  intros * Hsub Ht.
  econstructor.
  - exists ∅, [σ_int; σ_int], σ_bool. sauto q:on dep:on.
  - intros * Hrank.
    eapply monomorphic_rank_conservative in Hrank; eauto.
    sauto. set_solver.
  - reflexivity.
  - intros * Ht_i Hσ_i.
    destruct i; simpl in *.
    + simplify_eq. assumption.
    + rewrite list_lookup_singleton in Ht_i.
      destruct i; try congruence. simpl in *.
      simplify_eq. assumption.
Qed.

Lemma eval_lt_int :
  forall Σ A θ t1 t2 (w1 w2 : A.(domain) σ_int)
         HZ HR (Hri : models_reals_ints A HZ HR),
    Σ_reals_ints ⊑ Σ ->
    ⟦ t1 : σ_int ⟧(Σ, A, θ) ⇓ w1 ->
    ⟦ t2 : σ_int ⟧(Σ, A, θ) ⇓ w2 ->
    exists b : bool,
      ⟦ lt_ t1 t2 : σ_bool ⟧(Σ, A, θ) ⇓ cast_sym A.(domain_σ_bool) b /\
      b = Z.ltb (cast HZ w1) (cast HZ w2).
Proof.
  intros Σ A θ t1 t2 w1 w2 HZ HR Hri Hsub Ht1 Ht2.
  exists (Z.ltb (cast HZ w1) (cast HZ w2)).
  split; [|reflexivity].
  unfold lt_. eapply E_TApp with (σs := [σ_int; σ_int])
    (vs := HCons σ_int [σ_int] w1 (HCons σ_int [] w2 HNil)).
  - repeat constructor; [exact Ht1 | exact Ht2].
  - constructor.
  - apply rank_monomorphic;
      [ apply (rank_extends Hsub); constructor
      | repeat constructor | repeat constructor ].
  - apply (proj1 (cast_eq_iff_eq_cast_sym A.(domain_σ_bool)
      (interp_apply A.(domain)
        (A.(interp) f_lt [σ_int; σ_int] σ_bool)
        (HCons σ_int [σ_int] w1 (HCons σ_int [] w2 HNil)))
      (Z.ltb (cast HZ w1) (cast HZ w2)))).
    autorewrite with interp_apply.
    change (cast A.(domain_σ_bool)
      (A.(interp) f_lt [σ_int; σ_int] σ_bool w1 w2)
      = Z.ltb (cast HZ w1) (cast HZ w2)).
    exact (mri_lt_int Hri w1 w2).
Qed.

Lemma eval_leq_int :
  forall Σ A θ t1 t2 (w1 w2 : A.(domain) σ_int)
         HZ HR (Hri : models_reals_ints A HZ HR),
    Σ_reals_ints ⊑ Σ ->
    ⟦ t1 : σ_int ⟧(Σ, A, θ) ⇓ w1 ->
    ⟦ t2 : σ_int ⟧(Σ, A, θ) ⇓ w2 ->
    exists b : bool,
      ⟦ leq_ t1 t2 : σ_bool ⟧(Σ, A, θ) ⇓ cast_sym A.(domain_σ_bool) b /\
      b = Z.leb (cast HZ w1) (cast HZ w2).
Proof.
  intros Σ A θ t1 t2 w1 w2 HZ HR Hri Hsub Ht1 Ht2.
  exists (Z.leb (cast HZ w1) (cast HZ w2)).
  split; [|reflexivity].
  unfold leq_. eapply E_TApp with (σs := [σ_int; σ_int])
    (vs := HCons σ_int [σ_int] w1 (HCons σ_int [] w2 HNil)).
  - repeat constructor; [exact Ht1 | exact Ht2].
  - constructor.
  - apply rank_monomorphic;
      [ apply (rank_extends Hsub); constructor
      | repeat constructor | repeat constructor ].
  - apply (proj1 (cast_eq_iff_eq_cast_sym A.(domain_σ_bool)
      (interp_apply A.(domain)
        (A.(interp) f_leq [σ_int; σ_int] σ_bool)
        (HCons σ_int [σ_int] w1 (HCons σ_int [] w2 HNil)))
      (Z.leb (cast HZ w1) (cast HZ w2)))).
    autorewrite with interp_apply.
    change (cast A.(domain_σ_bool)
      (A.(interp) f_leq [σ_int; σ_int] σ_bool w1 w2)
      = Z.leb (cast HZ w1) (cast HZ w2)).
    exact (mri_leq_int Hri w1 w2).
Qed.


Theorem geq_has_sort_int : forall Σ t1 t2,
    Σ_reals_ints ⊑ Σ ->
    (Σ ⊢ t1 : σ_int) ->
    (Σ ⊢ t2 : σ_int) ->
    Σ ⊢ geq_ t1 t2 : σ_bool.
Proof.
  intros * Hsub Ht.
  econstructor.
  - exists ∅, [σ_int; σ_int], σ_bool. sauto q:on dep:on.
  - intros * Hrank.
    eapply monomorphic_rank_conservative in Hrank; eauto.
    sauto. set_solver.
  - reflexivity.
  - intros * Ht_i Hσ_i.
    destruct i; simpl in *.
    + simplify_eq. assumption.
    + rewrite list_lookup_singleton in Ht_i.
      destruct i; try congruence. simpl in *.
      simplify_eq. assumption.
Qed.

Lemma eval_geq_int_interp :
  forall Σ A θ t1 t2 (w1 w2 : A.(domain) σ_int),
    Σ_reals_ints ⊑ Σ ->
    ⟦ t1 : σ_int ⟧(Σ, A, θ) ⇓ w1 ->
    ⟦ t2 : σ_int ⟧(Σ, A, θ) ⇓ w2 ->
    ⟦ geq_ t1 t2 : σ_bool ⟧(Σ, A, θ)
      ⇓ interp_apply A.(domain)
         (A.(interp) f_geq [σ_int; σ_int] σ_bool)
         (HCons σ_int [σ_int] w1 (HCons σ_int [] w2 HNil)).
Proof.
  intros Σ A θ t1 t2 w1 w2 Hsub Ht1 Ht2.
  unfold geq_. eapply E_TApp with (σs := [σ_int; σ_int])
    (vs := HCons σ_int [σ_int] w1 (HCons σ_int [] w2 HNil)).
  - repeat constructor; [exact Ht1 | exact Ht2].
  - constructor.
  - apply rank_monomorphic;
      [ apply (rank_extends Hsub); constructor
      | repeat constructor | repeat constructor ].
  - reflexivity.
Qed.


Lemma eval_geq_int :
  forall Σ A θ t1 t2 (w1 w2 : A.(domain) σ_int)
         HZ HR (Hri : models_reals_ints A HZ HR),
    Σ_reals_ints ⊑ Σ ->
    ⟦ t1 : σ_int ⟧(Σ, A, θ) ⇓ w1 ->
    ⟦ t2 : σ_int ⟧(Σ, A, θ) ⇓ w2 ->
    exists b : bool,
      ⟦ geq_ t1 t2 : σ_bool ⟧(Σ, A, θ) ⇓ cast_sym A.(domain_σ_bool) b /\
      b = Z.geb (cast HZ w1) (cast HZ w2).
Proof.
  intros Σ A θ t1 t2 w1 w2 HZ HR Hri Hsub Ht1 Ht2.
  exists (Z.geb (cast HZ w1) (cast HZ w2)).
  split; [|reflexivity].
  pose proof (eval_geq_int_interp Σ A θ t1 t2 w1 w2 Hsub Ht1 Ht2) as Hge.
  replace (cast_sym A.(domain_σ_bool) (Z.geb (cast HZ w1) (cast HZ w2)))
    with (interp_apply A.(domain)
      (A.(interp) f_geq [σ_int; σ_int] σ_bool)
      (HCons σ_int [σ_int] w1 (HCons σ_int [] w2 HNil))).
  - exact Hge.
  - apply (proj1 (cast_eq_iff_eq_cast_sym A.(domain_σ_bool)
      (interp_apply A.(domain)
        (A.(interp) f_geq [σ_int; σ_int] σ_bool)
        (HCons σ_int [σ_int] w1 (HCons σ_int [] w2 HNil)))
      (Z.geb (cast HZ w1) (cast HZ w2)))).
    autorewrite with interp_apply.
    change (cast A.(domain_σ_bool)
      (A.(interp) f_geq [σ_int; σ_int] σ_bool w1 w2)
      = Z.geb (cast HZ w1) (cast HZ w2)).
    exact (mri_geq_int Hri w1 w2).
Qed.


Theorem gt_has_sort_int : forall Σ t1 t2,
    Σ_reals_ints ⊑ Σ ->
    (Σ ⊢ t1 : σ_int) ->
    (Σ ⊢ t2 : σ_int) ->
    Σ ⊢ gt_ t1 t2 : σ_bool.
Proof.
  intros * Hsub Ht.
  econstructor.
  - exists ∅, [σ_int; σ_int], σ_bool. sauto q:on dep:on.
  - intros * Hrank.
    eapply monomorphic_rank_conservative in Hrank; eauto.
    sauto. set_solver.
  - reflexivity.
  - intros * Ht_i Hσ_i.
    destruct i; simpl in *.
    + simplify_eq. assumption.
    + rewrite list_lookup_singleton in Ht_i.
      destruct i; try congruence. simpl in *.
      simplify_eq. assumption.
Qed.

Theorem neg_has_sort_real : forall Σ t,
    Σ_reals_ints ⊑ Σ ->
    (Σ ⊢ t : σ_real) ->
    Σ ⊢ neg_ t : σ_real.
Proof.
  intros * Hsub Ht.
  econstructor.
  - exists ∅, [σ_real], σ_real. sauto q:on dep:on.
  - intros * Hrank.
    eapply monomorphic_rank_conservative in Hrank; eauto.
    fcrush. set_solver.
  - reflexivity.
  - intros * Ht_i Hσ_i.
    rewrite list_lookup_singleton in Ht_i.
    destruct i; try congruence. simpl in *.
    simplify_eq. assumption.
Qed.

Theorem minus_has_sort_real : forall Σ t1 t2,
    Σ_reals_ints ⊑ Σ ->
    (Σ ⊢ t1 : σ_real) ->
    (Σ ⊢ t2 : σ_real) ->
    Σ ⊢ minus_ t1 t2 : σ_real.
Proof.
  intros * Hsub Ht.
  econstructor.
  - exists ∅, [σ_real; σ_real], σ_real. sauto q:on dep:on.
  - intros * Hrank.
    eapply monomorphic_rank_conservative in Hrank; eauto.
    fcrush. set_solver.
  - reflexivity.
  - intros * Ht_i Hσ_i.
    destruct i; simpl in *.
    + simplify_eq. assumption.
    + rewrite list_lookup_singleton in Ht_i.
      destruct i; try congruence. simpl in *.
      simplify_eq. assumption.
Qed.

Theorem plus_has_sort_real : forall Σ t1 t2,
    Σ_reals_ints ⊑ Σ ->
    (Σ ⊢ t1 : σ_real) ->
    (Σ ⊢ t2 : σ_real) ->
    Σ ⊢ plus_ t1 t2 : σ_real.
Proof.
  intros * Hsub Ht.
  econstructor.
  - exists ∅, [σ_real; σ_real], σ_real. sauto q:on dep:on.
  - intros * Hrank.
    eapply monomorphic_rank_conservative in Hrank; eauto.
    fcrush. set_solver.
  - reflexivity.
  - intros * Ht_i Hσ_i.
    destruct i; simpl in *.
    + simplify_eq. assumption.
    + rewrite list_lookup_singleton in Ht_i.
      destruct i; try congruence. simpl in *.
      simplify_eq. assumption.
Qed.

Theorem times_has_sort_real : forall Σ t1 t2,
    Σ_reals_ints ⊑ Σ ->
    (Σ ⊢ t1 : σ_real) ->
    (Σ ⊢ t2 : σ_real) ->
    Σ ⊢ times_ t1 t2 : σ_real.
Proof.
  intros * Hsub Ht.
  econstructor.
  - exists ∅, [σ_real; σ_real], σ_real. sauto q:on dep:on.
  - intros * Hrank.
    eapply monomorphic_rank_conservative in Hrank; eauto.
    fcrush. set_solver.
  - reflexivity.
  - intros * Ht_i Hσ_i.
    destruct i; simpl in *.
    + simplify_eq. assumption.
    + rewrite list_lookup_singleton in Ht_i.
      destruct i; try congruence. simpl in *.
      simplify_eq. assumption.
Qed.

Lemma eval_times_real :
  forall Σ A θ t1 t2 (w1 w2 : A.(domain) σ_real),
    Σ_reals_ints ⊑ Σ ->
    ⟦ t1 : σ_real ⟧(Σ, A, θ) ⇓ w1 ->
    ⟦ t2 : σ_real ⟧(Σ, A, θ) ⇓ w2 ->
    ⟦ times_ t1 t2 : σ_real ⟧(Σ, A, θ)
      ⇓ interp_apply A.(domain)
         (A.(interp) f_times [σ_real; σ_real] σ_real)
         (HCons σ_real [σ_real] w1 (HCons σ_real [] w2 HNil)).
Proof.
  intros Σ A θ t1 t2 w1 w2 Hsub Ht1 Ht2.
  unfold times_. eapply E_TApp with (σs := [σ_real; σ_real])
    (vs := HCons σ_real [σ_real] w1 (HCons σ_real [] w2 HNil)).
  - repeat constructor; [exact Ht1 | exact Ht2].
  - constructor.
  - apply rank_monomorphic;
      [ apply (rank_extends Hsub); constructor
      | repeat constructor | repeat constructor ].
  - reflexivity.
Qed.


Theorem div_has_sort : forall Σ t1 t2,
    Σ_reals_ints ⊑ Σ ->
    (Σ ⊢ t1 : σ_real) ->
    (Σ ⊢ t2 : σ_real) ->
    Σ ⊢ div_ t1 t2 : σ_real.
Proof.
  intros * Hsub Ht.
  econstructor.
  - exists ∅, [σ_real; σ_real], σ_real. sauto q:on dep:on.
  - intros * Hrank.
    eapply monomorphic_rank_conservative in Hrank; eauto.
    sauto. set_solver.
  - reflexivity.
  - intros * Ht_i Hσ_i.
    destruct i; simpl in *.
    + simplify_eq. assumption.
    + rewrite list_lookup_singleton in Ht_i.
      destruct i; try congruence. simpl in *.
      simplify_eq. assumption.
Qed.

Lemma eval_div_real :
  forall Σ A θ t1 t2 (w1 w2 : A.(domain) σ_real),
    Σ_reals_ints ⊑ Σ ->
    ⟦ t1 : σ_real ⟧(Σ, A, θ) ⇓ w1 ->
    ⟦ t2 : σ_real ⟧(Σ, A, θ) ⇓ w2 ->
    ⟦ div_ t1 t2 : σ_real ⟧(Σ, A, θ)
      ⇓ interp_apply A.(domain)
         (A.(interp) f_div [σ_real; σ_real] σ_real)
         (HCons σ_real [σ_real] w1 (HCons σ_real [] w2 HNil)).
Proof.
  intros Σ A θ t1 t2 w1 w2 Hsub Ht1 Ht2.
  unfold div_. eapply E_TApp with (σs := [σ_real; σ_real])
    (vs := HCons σ_real [σ_real] w1 (HCons σ_real [] w2 HNil)).
  - repeat constructor; [exact Ht1 | exact Ht2].
  - constructor.
  - apply rank_monomorphic;
      [ apply (rank_extends Hsub); constructor
      | repeat constructor | repeat constructor ].
  - reflexivity.
Qed.

Theorem leq_has_sort_real : forall Σ t1 t2,
    Σ_reals_ints ⊑ Σ ->
    (Σ ⊢ t1 : σ_real) ->
    (Σ ⊢ t2 : σ_real) ->
    Σ ⊢ leq_ t1 t2 : σ_bool.
Proof.
  intros * Hsub Ht.
  econstructor.
  - exists ∅, [σ_real; σ_real], σ_bool. sauto q:on dep:on.
  - intros * Hrank.
    eapply monomorphic_rank_conservative in Hrank; eauto.
    sauto. set_solver.
  - reflexivity.
  - intros * Ht_i Hσ_i.
    destruct i; simpl in *.
    + simplify_eq. assumption.
    + rewrite list_lookup_singleton in Ht_i.
      destruct i; try congruence. simpl in *.
      simplify_eq. assumption.
Qed.

Theorem lt_has_sort_real : forall Σ t1 t2,
    Σ_reals_ints ⊑ Σ ->
    (Σ ⊢ t1 : σ_real) ->
    (Σ ⊢ t2 : σ_real) ->
    Σ ⊢ lt_ t1 t2 : σ_bool.
Proof.
  intros * Hsub Ht.
  econstructor.
  - exists ∅, [σ_real; σ_real], σ_bool. sauto q:on dep:on.
  - intros * Hrank.
    eapply monomorphic_rank_conservative in Hrank; eauto.
    sauto. set_solver.
  - reflexivity.
  - intros * Ht_i Hσ_i.
    destruct i; simpl in *.
    + simplify_eq. assumption.
    + rewrite list_lookup_singleton in Ht_i.
      destruct i; try congruence. simpl in *.
      simplify_eq. assumption.
Qed.

Theorem geq_has_sort_real : forall Σ t1 t2,
    Σ_reals_ints ⊑ Σ ->
    (Σ ⊢ t1 : σ_real) ->
    (Σ ⊢ t2 : σ_real) ->
    Σ ⊢ geq_ t1 t2 : σ_bool.
Proof.
  intros * Hsub Ht.
  econstructor.
  - exists ∅, [σ_real; σ_real], σ_bool. sauto q:on dep:on.
  - intros * Hrank.
    eapply monomorphic_rank_conservative in Hrank; eauto.
    sauto. set_solver.
  - reflexivity.
  - intros * Ht_i Hσ_i.
    destruct i; simpl in *.
    + simplify_eq. assumption.
    + rewrite list_lookup_singleton in Ht_i.
      destruct i; try congruence. simpl in *.
      simplify_eq. assumption.
Qed.

Lemma eval_geq_real :
  forall Σ A θ t1 t2 (w1 w2 : A.(domain) σ_real),
    Σ_reals_ints ⊑ Σ ->
    ⟦ t1 : σ_real ⟧(Σ, A, θ) ⇓ w1 ->
    ⟦ t2 : σ_real ⟧(Σ, A, θ) ⇓ w2 ->
    ⟦ geq_ t1 t2 : σ_bool ⟧(Σ, A, θ)
      ⇓ interp_apply A.(domain)
         (A.(interp) f_geq [σ_real; σ_real] σ_bool)
         (HCons σ_real [σ_real] w1 (HCons σ_real [] w2 HNil)).
Proof.
  intros Σ A θ t1 t2 w1 w2 Hsub Ht1 Ht2.
  unfold geq_. eapply E_TApp with (σs := [σ_real; σ_real])
    (vs := HCons σ_real [σ_real] w1 (HCons σ_real [] w2 HNil)).
  - repeat constructor; [exact Ht1 | exact Ht2].
  - constructor.
  - apply rank_monomorphic;
      [ apply (rank_extends Hsub); constructor
      | repeat constructor | repeat constructor ].
  - reflexivity.
Qed.

(* [gt_] at the reals, in the shape a proof reading a guard back wants: the
   application's value is the model's comparison, so a true [gt_] is a strict
   inequality on the domains. *)
Lemma eval_gt_real_interp :
  forall Σ A θ t1 t2 (w1 w2 : A.(domain) σ_real),
    Σ_reals_ints ⊑ Σ ->
    ⟦ t1 : σ_real ⟧(Σ, A, θ) ⇓ w1 ->
    ⟦ t2 : σ_real ⟧(Σ, A, θ) ⇓ w2 ->
    ⟦ gt_ t1 t2 : σ_bool ⟧(Σ, A, θ)
      ⇓ interp_apply A.(domain)
         (A.(interp) f_gt [σ_real; σ_real] σ_bool)
         (HCons σ_real [σ_real] w1 (HCons σ_real [] w2 HNil)).
Proof.
  intros Σ A θ t1 t2 w1 w2 Hsub Ht1 Ht2.
  unfold gt_. eapply E_TApp with (σs := [σ_real; σ_real])
    (vs := HCons σ_real [σ_real] w1 (HCons σ_real [] w2 HNil)).
  - repeat constructor; [exact Ht1 | exact Ht2].
  - constructor.
  - apply rank_monomorphic;
      [ apply (rank_extends Hsub); constructor
      | repeat constructor | repeat constructor ].
  - reflexivity.
Qed.

Lemma eval_gt_real_true_inv :
  forall Σ A θ t1 t2 (w1 w2 : A.(domain) σ_real) HZ HR
         (Hri : models_reals_ints A HZ HR),
    Σ_reals_ints ⊑ Σ ->
    (Σ ⊢ gt_ t1 t2 : σ_bool) ->
    valuation_well_sorted Σ.(sorts) θ ->
    ⟦ t1 : σ_real ⟧(Σ, A, θ) ⇓ w1 ->
    ⟦ t2 : σ_real ⟧(Σ, A, θ) ⇓ w2 ->
    ⟦ gt_ t1 t2 : σ_bool ⟧(Σ, A, θ) ⇓ cast_sym A.(domain_σ_bool) true ->
    (cast HR w1 > cast HR w2)%R.
Proof.
  intros Σ A θ t1 t2 w1 w2 HZ HR Hri Hsub Hsort Hθ Ht1 Ht2 Htrue.
  pose proof (eval_gt_real_interp Σ A θ t1 t2 w1 w2 Hsub Ht1 Ht2) as Hgt.
  assert (Heq : interp_apply A.(domain)
                  (A.(interp) f_gt [σ_real; σ_real] σ_bool)
                  (HCons σ_real [σ_real] w1 (HCons σ_real [] w2 HNil))
                = cast_sym A.(domain_σ_bool) true)
    by (eapply eval_deterministic; [exact Hsort | exact Hθ | exact Hgt | exact Htrue]).
  pose proof (mri_gt_real Hri w1 w2
                (cast A.(domain_σ_bool)
                   (A.(interp) f_gt [σ_real; σ_real] σ_bool w1 w2))
                eq_refl) as Hsem.
  apply (proj1 Hsem).
  autorewrite with interp_apply in Heq.
  rewrite Heq. apply cast_cast_sym.
Qed.

(** The introduction form, for a proof building a guard. *)
Lemma eval_gt_real_true :
  forall Σ A θ t1 t2 (w1 w2 : A.(domain) σ_real) HZ HR
         (Hri : models_reals_ints A HZ HR),
    Σ_reals_ints ⊑ Σ ->
    ⟦ t1 : σ_real ⟧(Σ, A, θ) ⇓ w1 ->
    ⟦ t2 : σ_real ⟧(Σ, A, θ) ⇓ w2 ->
    (cast HR w1 > cast HR w2)%R ->
    ⟦ gt_ t1 t2 : σ_bool ⟧(Σ, A, θ) ⇓ cast_sym A.(domain_σ_bool) true.
Proof.
  intros Σ A θ t1 t2 w1 w2 HZ HR Hri Hsub Ht1 Ht2 Hgt.
  pose proof (eval_gt_real_interp Σ A θ t1 t2 w1 w2 Hsub Ht1 Ht2) as Hev.
  replace (cast_sym A.(domain_σ_bool) true)
    with (interp_apply A.(domain)
            (A.(interp) f_gt [σ_real; σ_real] σ_bool)
            (HCons σ_real [σ_real] w1 (HCons σ_real [] w2 HNil)));
    [exact Hev|].
  apply (proj1 (cast_eq_iff_eq_cast_sym A.(domain_σ_bool) _ true)).
  autorewrite with interp_apply.
  exact (proj2 (mri_gt_real Hri w1 w2
                  (cast A.(domain_σ_bool)
                     (A.(interp) f_gt [σ_real; σ_real] σ_bool w1 w2))
                  eq_refl) Hgt).
Qed.

Theorem gt_has_sort_real : forall Σ t1 t2,
    Σ_reals_ints ⊑ Σ ->
    (Σ ⊢ t1 : σ_real) ->
    (Σ ⊢ t2 : σ_real) ->
    Σ ⊢ gt_ t1 t2 : σ_bool.
Proof.
  intros * Hsub Ht.
  econstructor.
  - exists ∅, [σ_real; σ_real], σ_bool. sauto q:on dep:on.
  - intros * Hrank.
    eapply monomorphic_rank_conservative in Hrank; eauto.
    sauto. set_solver.
  - reflexivity.
  - intros * Ht_i Hσ_i.
    destruct i; simpl in *.
    + simplify_eq. assumption.
    + rewrite list_lookup_singleton in Ht_i.
      destruct i; try congruence. simpl in *.
      simplify_eq. assumption.
Qed.

Theorem to_real_has_sort : forall Σ t,
    Σ_reals_ints ⊑ Σ ->
    (Σ ⊢ t : σ_int) ->
    Σ ⊢ to_real t : σ_real.
Proof.
  intros * Hsub Ht.
  econstructor.
  - exists ∅, [σ_int], σ_real. sauto q:on dep:on.
  - intros * Hrank.
    eapply monomorphic_rank_conservative in Hrank; eauto.
    sauto. set_solver.
  - reflexivity.
  - intros * Ht_i Hσ_i.
    rewrite list_lookup_singleton in Ht_i.
    destruct i; try congruence. simpl in *.
    simplify_eq. assumption.
Qed.

Lemma eval_to_real :
  forall Σ A θ t (w : A.(domain) σ_int),
    Σ_reals_ints ⊑ Σ ->
    ⟦ t : σ_int ⟧(Σ, A, θ) ⇓ w ->
    ⟦ to_real t : σ_real ⟧(Σ, A, θ)
      ⇓ interp_apply A.(domain)
         (A.(interp) f_to_real [σ_int] σ_real)
         (HCons σ_int [] w HNil).
Proof.
  intros Σ A θ t w Hsub Ht.
  unfold to_real. eapply E_TApp with (σs := [σ_int])
    (vs := HCons σ_int [] w HNil).
  - repeat constructor. exact Ht.
  - constructor.
  - apply rank_monomorphic;
      [ apply (rank_extends Hsub); constructor
      | repeat constructor | repeat constructor ].
  - reflexivity.
Qed.

Theorem to_int_has_sort : forall Σ t,
    Σ_reals_ints ⊑ Σ ->
    (Σ ⊢ t : σ_real) ->
    Σ ⊢ to_int t : σ_int.
Proof.
  intros * Hsub Ht.
  econstructor.
  - exists ∅, [σ_real], σ_int. sauto q:on dep:on.
  - intros * Hrank.
    eapply monomorphic_rank_conservative in Hrank; eauto.
    sauto. set_solver.
  - reflexivity.
  - intros * Ht_i Hσ_i.
    rewrite list_lookup_singleton in Ht_i.
    destruct i; try congruence. simpl in *.
    simplify_eq. assumption.
Qed.

Lemma eval_to_int :
  forall Σ A θ t (w : A.(domain) σ_real),
    Σ_reals_ints ⊑ Σ ->
    ⟦ t : σ_real ⟧(Σ, A, θ) ⇓ w ->
    ⟦ to_int t : σ_int ⟧(Σ, A, θ)
      ⇓ interp_apply A.(domain)
         (A.(interp) f_to_int [σ_real] σ_int)
         (HCons σ_real [] w HNil).
Proof.
  intros Σ A θ t w Hsub Ht.
  unfold to_int. eapply E_TApp with (σs := [σ_real])
    (vs := HCons σ_real [] w HNil).
  - repeat constructor. exact Ht.
  - constructor.
  - apply rank_monomorphic;
      [ apply (rank_extends Hsub); constructor
      | repeat constructor | repeat constructor ].
  - reflexivity.
Qed.


Theorem is_int_has_sort : forall Σ t,
    Σ_reals_ints ⊑ Σ ->
    (Σ ⊢ t : σ_real) ->
    Σ ⊢ is_int t : σ_bool.
Proof.
  intros * Hsub Ht.
  econstructor.
  - exists ∅, [σ_real], σ_bool. sauto q:on dep:on.
  - intros * Hrank.
    eapply monomorphic_rank_conservative in Hrank; eauto.
    sauto. set_solver.
  - reflexivity.
  - intros * Ht_i Hσ_i.
    rewrite list_lookup_singleton in Ht_i.
    destruct i; try congruence. simpl in *.
    simplify_eq. assumption.
Qed.

Lemma eval_is_int :
  forall Σ A θ t (w : A.(domain) σ_real),
    Σ_reals_ints ⊑ Σ ->
    ⟦ t : σ_real ⟧(Σ, A, θ) ⇓ w ->
    ⟦ is_int t : σ_bool ⟧(Σ, A, θ)
      ⇓ interp_apply A.(domain)
         (A.(interp) f_is_int [σ_real] σ_bool)
         (HCons σ_real [] w HNil).
Proof.
  intros Σ A θ t w Hsub Ht.
  unfold is_int. eapply E_TApp with (σs := [σ_real])
    (vs := HCons σ_real [] w HNil).
  - repeat constructor. exact Ht.
  - constructor.
  - apply rank_monomorphic;
      [ apply (rank_extends Hsub); constructor
      | repeat constructor | repeat constructor ].
  - reflexivity.
Qed.


Theorem divisible_has_sort : forall Σ t1 n,
    Σ_reals_ints ⊑ Σ ->
    (Σ ⊢ t1 : σ_int) ->
    n <> 0 ->
    Σ ⊢ divisible t1 n : σ_bool.
Proof.
  intros * Hsub.
  econstructor.
  - exists ∅, [σ_int], σ_bool. sauto q:on dep:on.
  - intros * Hrank.
    eapply monomorphic_rank_conservative in Hrank; eauto; sauto.
  - reflexivity.
  - intros * Ht_i Hσ_i.
    rewrite list_lookup_singleton in Ht_i.
    destruct i; try congruence. simpl in *.
    simplify_eq. assumption.
Qed.

Theorem int_literal_has_sort : forall Σ i,
    Σ_reals_ints ⊑ Σ ->
    Σ ⊢ int_literal i : σ_int.
Proof.
  intros * Hsub.
  econstructor.
  - exists ∅, [], σ_int. sauto q:on dep:on.
  - intros * Hrank.
    eapply monomorphic_rank_conservative in Hrank; eauto; sauto.
  - reflexivity.
  - intros * Ht_i Hσ_i. inversion Ht_i.
Qed.

Theorem decimal_literal_has_sort : forall Σ x,
    Σ_reals_ints ⊑ Σ ->
    Σ ⊢ decimal_literal x : σ_real.
Proof.
  intros * Hsub.
  econstructor.
  - exists ∅, [], σ_real. sauto q:on dep:on.
  - intros * Hrank.
    eapply monomorphic_rank_conservative in Hrank; eauto; sauto.
  - reflexivity.
  - intros * Ht_i Hσ_i. inversion Ht_i.
Qed.

Lemma eval_int_literal :
  forall Σ A θ HZ HR (Hri : models_reals_ints A HZ HR) i,
    Σ_reals_ints ⊑ Σ ->
    ⟦ int_literal i : σ_int ⟧(Σ, A, θ) ⇓ cast_sym HZ i.
Proof.
  intros Σ A θ HZ HR Hri i Hsub.
  assert (Heval :
    ⟦ int_literal i : σ_int ⟧(Σ, A, θ)
      ⇓ interp_apply A.(domain)
         (A.(interp) (f_int_literal i) [] σ_int) HNil).
  { unfold int_literal. eapply E_TApp;
      [ constructor | constructor
      | apply rank_monomorphic;
          [ apply (rank_extends Hsub); constructor
          | constructor | repeat constructor ]
      | reflexivity ]. }
  replace (cast_sym HZ i) with
    (interp_apply A.(domain) (A.(interp) (f_int_literal i) [] σ_int) HNil);
    [exact Heval|].
  apply (proj1 (cast_eq_iff_eq_cast_sym HZ _ i)).
  autorewrite with interp_apply.
  exact (mri_int_literal Hri i).
Qed.

Lemma eval_zero_int :
  forall Σ A θ HZ HR (Hri : models_reals_ints A HZ HR),
    Σ_reals_ints ⊑ Σ ->
    ⟦ zero_int : σ_int ⟧(Σ, A, θ) ⇓ (cast_sym HZ 0%Z).
Proof.
  intros Σ A θ HZ HR Hri Hsub.
  exact (eval_int_literal Σ A θ HZ HR Hri 0%Z Hsub).
Qed.

Lemma eval_decimal_literal :
  forall Σ A θ HZ HR (Hri : models_reals_ints A HZ HR) q,
    Σ_reals_ints ⊑ Σ ->
    ⟦ decimal_literal q : σ_real ⟧(Σ, A, θ) ⇓ cast_sym HR (Q2R (Qcanon.this q)).
Proof.
  intros Σ A θ HZ HR Hri q Hsub.
  assert (Heval :
    ⟦ decimal_literal q : σ_real ⟧(Σ, A, θ)
      ⇓ interp_apply A.(domain)
         (A.(interp) (f_decimal_literal q) [] σ_real) HNil).
  { unfold decimal_literal. eapply E_TApp;
      [ constructor | constructor
      | apply rank_monomorphic;
          [ apply (rank_extends Hsub); constructor
          | constructor | repeat constructor ]
      | reflexivity ]. }
  replace (cast_sym HR (Q2R (Qcanon.this q))) with
    (interp_apply A.(domain) (A.(interp) (f_decimal_literal q) [] σ_real) HNil);
    [exact Heval|].
  apply (proj1 (cast_eq_iff_eq_cast_sym HR _ _)).
  autorewrite with interp_apply.
  exact (mri_decimal_literal Hri q).
Qed.

Lemma eval_zero_real :
  forall Σ A θ HZ HR (Hri : models_reals_ints A HZ HR),
    Σ_reals_ints ⊑ Σ ->
    ⟦ zero_real : σ_real ⟧(Σ, A, θ) ⇓ (cast_sym HR 0%R).
Proof.
  intros Σ A θ HZ HR Hri Hsub.
  replace 0%R with (Q2R (Qcanon.this 0%Qc)) by (unfold Q2R; simpl; ring).
  exact (eval_decimal_literal Σ A θ HZ HR Hri 0%Qc Hsub).
Qed.
