From SMTLIB Require Import Utils Symbols Term Signature Theory Sorting.
From SMTLIB.Theory Require Import Reals_Ints.
From Stdlib Require Import Strings.Ascii Strings.String.
From stdpp Require Import base gmap.

Open Scope smt_scope.

(* https://smt-lib.org/theories-UnicodeStrings.shtml *)

(* NOTE: The official theory is over Unicode code points 0 to 0x2FFFF.  We
         use Rocq's [string], a sequence of bytes, and identify a byte with
         the code point of the same number.  The function symbols below are
         modelled by their official semantics restricted to words over the
         sub-alphabet 0 to 255: [String.ltb] is the lexicographic extension
         of the numerical order on bytes, as [str.<] is of that on code
         points, and a string constant denotes one code point per byte.

         The *domain* is not restricted by this file.  [T_strings] requires
         a model's String domain to be [string], i.e. bytes, while a stock
         solver reasons over all of UC*; a query satisfiable only by a
         string with a code point above 255 is SAT for the solver and has
         no model here.  A solver agrees with this theory only once its
         alphabet is the bytes, as with z3's [(set-option :encoding ascii)]
         (cvc5: [--strings-alpha-card=256]). *)

(* NOTE: We only include the "core functions" for strings,
         not "Additional functions" and "Maps to and from integers" *)

(* NOTE: We do not include regular expressions. *)

Definition s_string : sortsymb := "String".
Definition σ_string : sort := SApp s_string [].

Definition f_str_concat : func := "str.++".
Definition f_str_len : func := "str.len".
Definition f_str_lt : func := "str.<".
Definition strings_funcs : gset func :=
  {[ f_str_concat; f_str_len; f_str_lt ]}.

(** ** String constants

    A string constant of the official theory is a double-quote-delimited
    sequence of printable US ASCII characters (code points 0x20 to 0x7E).
    Any other character is written with an escape sequence; [\u{HH}] is one.
    Inside the quotes the only other special character is the backslash,
    which starts such a sequence.

    [f_string_literal s] is the constant denoting [s].  A byte is written as
    itself when it is printable US ASCII and neither the quote nor the
    backslash, and as [\u{HH}] otherwise.  The text is therefore exactly a
    string constant of the official theory ([escape_string_wf]), it
    determines [s] ([f_string_literal_inj]), and [models_f_string_literal]
    below is the official semantics of that constant: one code point per
    byte.

    The escaping is part of the theory rather than left to a renderer
    because getting it wrong is unsound and silent: an unescaped [\u{41}]
    between quotes is read by every compliant solver as the one-character
    string [A].  Only a backslash that would start an escape sequence needs
    escaping, but escaping every backslash keeps the rule byte-local;
    [\u{5c}] denotes the backslash. *)

Definition quote_char : ascii := Ascii.ascii_of_nat 34.
Definition quote_string : string := String quote_char EmptyString.

(** The lower-case hexadecimal digit for [n < 16]. *)
Definition hex_digit (n : nat) : ascii :=
  ascii_of_nat (if n <? 10 then 48 + n else 87 + n).

Definition is_hex_digit (c : ascii) : Prop :=
  exists n, n < 16 /\ c = hex_digit n.

(** Whether the byte with code [n] stands for itself inside a constant. *)
Definition plain_char (n : nat) : bool :=
  (32 <=? n) && (n <=? 126) && negb (n =? 34) && negb (n =? 92).

Definition escape_ascii (c : ascii) : string :=
  let n := nat_of_ascii c in
  if plain_char n then String c EmptyString
  else "\u{" ++ String (hex_digit (n / 16)) (String (hex_digit (n mod 16)) "}").

Fixpoint escape_string (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c s' => escape_ascii c ++ escape_string s'
  end.

Definition f_string_literal (s : string) :=
  (quote_string ++ escape_string s ++ quote_string)%string.

(** The text between the quotes of a constant we produce: the official
    grammar of string constants, restricted to the escape [\u{HH}].  Each
    constructor is one character of the denoted word. *)
Inductive constant_body : string -> Prop :=
| cb_empty : constant_body ""
| cb_plain c s :
    plain_char (nat_of_ascii c) = true ->
    constant_body s ->
    constant_body (String c s)
| cb_escape d1 d2 s :
    is_hex_digit d1 ->
    is_hex_digit d2 ->
    constant_body s ->
    constant_body (String "\" (String "u" (String "{" (String d1 (String d2 (String "}" s)))))).

Lemma hex_digit_code : forall n,
    n < 16 -> nat_of_ascii (hex_digit n) = if n <? 10 then 48 + n else 87 + n.
Proof.
  intros n Hn. unfold hex_digit.
  apply nat_ascii_embedding. destruct (n <? 10); lia.
Qed.

Lemma hex_digit_inj : forall m n,
    m < 16 -> n < 16 -> hex_digit m = hex_digit n -> m = n.
Proof.
  intros m n Hm Hn H.
  apply (f_equal nat_of_ascii) in H.
  rewrite !hex_digit_code in H by assumption.
  destruct (m <? 10) eqn:Em, (n <? 10) eqn:En;
    rewrite ?Nat.ltb_lt, ?Nat.ltb_ge in Em, En; lia.
Qed.

(** The two shapes of [escape_ascii c ++ s], stated so that no reduction of
    [String.append] (which stdpp marks [simpl never]) is needed. *)
Lemma escape_ascii_plain : forall c s,
    plain_char (nat_of_ascii c) = true ->
    (escape_ascii c ++ s)%string = String c s.
Proof. intros c s Hp. unfold escape_ascii. rewrite Hp. reflexivity. Qed.

Lemma escape_ascii_escaped : forall c s,
    plain_char (nat_of_ascii c) = false ->
    (escape_ascii c ++ s)%string =
      String "\" (String "u" (String "{"
        (String (hex_digit (nat_of_ascii c / 16))
          (String (hex_digit (nat_of_ascii c mod 16)) (String "}" s))))).
Proof. intros c s Hp. unfold escape_ascii. rewrite Hp. reflexivity. Qed.

Theorem escape_string_wf : forall s, constant_body (escape_string s).
Proof.
  induction s as [| c s IH]; cbn [escape_string].
  - constructor.
  - pose proof (nat_ascii_bounded c).
    destruct (plain_char (nat_of_ascii c)) eqn:Hp.
    + rewrite escape_ascii_plain by assumption. apply cb_plain; assumption.
    + rewrite escape_ascii_escaped by assumption.
      apply cb_escape; [| | assumption].
      * exists (nat_of_ascii c / 16). split; [| reflexivity].
        apply Nat.Div0.div_lt_upper_bound. lia.
      * exists (nat_of_ascii c mod 16). split; [| reflexivity].
        apply Nat.mod_upper_bound. lia.
Qed.

(** Lexically, a constant body is printable US ASCII without a quote, so the
    whole constant is a well-formed SMT-LIB string literal. *)
Lemma constant_body_printable : forall s,
    constant_body s ->
    Forall (fun c => 32 <= nat_of_ascii c <= 126 /\ nat_of_ascii c <> 34)
      (list_ascii_of_string s).
Proof.
  intros s H.
  assert (Hhex : forall d, is_hex_digit d ->
            32 <= nat_of_ascii d <= 126 /\ nat_of_ascii d <> 34).
  { intros d (n & Hn & ->). rewrite hex_digit_code by assumption.
    destruct (n <? 10) eqn:E; rewrite ?Nat.ltb_lt, ?Nat.ltb_ge in E; lia. }
  induction H; simpl.
  - constructor.
  - constructor; [| assumption].
    unfold plain_char in H.
    rewrite !andb_true_iff, !negb_true_iff, !Nat.leb_le, !Nat.eqb_neq in H.
    lia.
  - repeat (constructor; [cbv; split; lia |]).
    constructor; [apply Hhex; assumption |].
    constructor; [apply Hhex; assumption |].
    constructor; [cbv; split; lia |].
    assumption.
Qed.

Lemma escape_ascii_nonempty : forall c, escape_ascii c <> "".
Proof.
  intros c. unfold escape_ascii. destruct (plain_char _); discriminate.
Qed.

Lemma escape_ascii_head : forall c1 c2 s1 s2,
    (escape_ascii c1 ++ s1)%string = (escape_ascii c2 ++ s2)%string -> c1 = c2 /\ s1 = s2.
Proof.
  intros c1 c2 s1 s2 H.
  pose proof (nat_ascii_bounded c1) as Hb1. pose proof (nat_ascii_bounded c2) as Hb2.
  destruct (plain_char (nat_of_ascii c1)) eqn:Hp1,
      (plain_char (nat_of_ascii c2)) eqn:Hp2;
    rewrite ?(escape_ascii_plain c1), ?(escape_ascii_plain c2),
      ?(escape_ascii_escaped c1), ?(escape_ascii_escaped c2) in H by assumption.
  - injection H as -> ->. auto.
  - injection H as Hc _. subst c1. vm_compute in Hp1. discriminate.
  - injection H as Hc _. subst c2. vm_compute in Hp2. discriminate.
  - (* [injection] simplifies [/] and [mod] on the way, so name them first. *)
    remember (nat_of_ascii c1 / 16) as q1 eqn:Eq1.
    remember (nat_of_ascii c2 / 16) as q2 eqn:Eq2.
    remember (nat_of_ascii c1 mod 16) as r1 eqn:Er1.
    remember (nat_of_ascii c2 mod 16) as r2 eqn:Er2.
    injection H as Hd Hm ->.
    apply hex_digit_inj in Hd;
      [| subst; apply Nat.Div0.div_lt_upper_bound; lia ..].
    apply hex_digit_inj in Hm;
      [| subst; apply Nat.mod_upper_bound; lia ..].
    split; [| reflexivity].
    rewrite <- (ascii_nat_embedding c1), <- (ascii_nat_embedding c2).
    f_equal.
    rewrite (Nat.div_mod_eq (nat_of_ascii c1) 16), (Nat.div_mod_eq (nat_of_ascii c2) 16).
    lia.
Qed.

Theorem escape_string_inj : forall s1 s2,
    escape_string s1 = escape_string s2 -> s1 = s2.
Proof.
  induction s1 as [| c1 s1 IH]; intros [| c2 s2] H; simpl in H.
  - reflexivity.
  - destruct (escape_ascii c2) eqn:E; [exact (False_ind _ (escape_ascii_nonempty _ E)) | discriminate].
  - destruct (escape_ascii c1) eqn:E; [exact (False_ind _ (escape_ascii_nonempty _ E)) | discriminate].
  - apply escape_ascii_head in H as [-> H]. f_equal. auto.
Qed.

Theorem f_string_literal_inj : forall s1 s2,
    f_string_literal s1 = f_string_literal s2 -> s1 = s2.
Proof.
  unfold f_string_literal, quote_string. intros s1 s2 H.
  injection H as H.
  change (("" ++ ?x)%string) with x in H.
  apply string_app_inj_tail in H.
  apply escape_string_inj in H. exact H.
Qed.

Definition string_literal s :=
  TApp (f_string_literal s) None [].
Definition string_literals (f : func) :=
  exists s, f = f_string_literal s.

(** ** Reading a Constant Back

    [f_string_literal] renders, and a signature has to decide whether a
    symbol is one of its renderings; that needs the inverse.  Only agreement
    on the image is proved, which is what [string_literals_dec] below asks
    for. *)

(** The value of a lower-case hexadecimal digit. *)
Definition hex_value (c : ascii) : option nat :=
  let n := nat_of_ascii c in
  if (48 <=? n) && (n <=? 57) then Some (n - 48)
  else if (97 <=? n) && (n <=? 102) then Some (n - 87)
  else None.

Lemma hex_value_digit : forall n, n < 16 -> hex_value (hex_digit n) = Some n.
Proof.
  intros n Hn. unfold hex_value. rewrite hex_digit_code by assumption.
  destruct (n <? 10) eqn:E; rewrite ?Nat.ltb_lt, ?Nat.ltb_ge in E.
  - rewrite (proj2 (Nat.leb_le 48 (48 + n))) by lia.
    rewrite (proj2 (Nat.leb_le (48 + n) 57)) by lia.
    simpl. f_equal. lia.
  - rewrite (proj2 (Nat.leb_gt (87 + n) 57)) by lia.
    rewrite andb_false_r.
    rewrite (proj2 (Nat.leb_le 97 (87 + n))) by lia.
    rewrite (proj2 (Nat.leb_le (87 + n) 102)) by lia.
    f_equal. lia.
Qed.

Fixpoint unescape_string (s : string) : option string :=
  match s with
  | EmptyString => Some EmptyString
  | String c1 s1 =>
      if plain_char (nat_of_ascii c1)
      then match unescape_string s1 with
           | Some r => Some (String c1 r)
           | None => None
           end
      else
        match s1 with
        | String c2 (String c3 (String d1 (String d2 (String c6 s2)))) =>
            if bool_decide (c1 = "\"%char) && bool_decide (c2 = "u"%char)
               && bool_decide (c3 = "{"%char) && bool_decide (c6 = "}"%char)
            then match hex_value d1, hex_value d2, unescape_string s2 with
                 | Some h, Some l, Some r =>
                     Some (String (ascii_of_nat (h * 16 + l)) r)
                 | _, _, _ => None
                 end
            else None
        | _ => None
        end
  end.

Lemma unescape_escape_string : forall s,
    unescape_string (escape_string s) = Some s.
Proof.
  induction s as [|c s IH]; [reflexivity|].
  cbn [escape_string].
  pose proof (nat_ascii_bounded c) as Hb.
  destruct (plain_char (nat_of_ascii c)) eqn:Hp.
  - rewrite escape_ascii_plain by assumption.
    cbn [unescape_string]. rewrite Hp, IH. reflexivity.
  - rewrite escape_ascii_escaped by assumption.
    cbn [unescape_string].
    assert (Hbs : plain_char (nat_of_ascii "\"%char) = false) by reflexivity.
    rewrite Hbs.
    rewrite !bool_decide_eq_true_2 by reflexivity. cbn [andb].
    rewrite (hex_value_digit (nat_of_ascii c / 16))
      by (apply Nat.Div0.div_lt_upper_bound; lia).
    rewrite (hex_value_digit (nat_of_ascii c mod 16))
      by (apply Nat.mod_upper_bound; lia).
    rewrite IH. do 2 f_equal.
    replace (nat_of_ascii c / 16 * 16 + nat_of_ascii c mod 16)
      with (nat_of_ascii c)
      by (pose proof (Nat.div_mod_eq (nat_of_ascii c) 16); lia).
    apply ascii_nat_embedding.
Qed.

(** The quote is what closes the constant, so it must not occur inside: a
    plain character is not one and an escape is six characters none of which
    is one. *)
Lemma string_occurs_quote_escape_ascii : forall c s,
    string_occurs quote_char (escape_ascii c ++ s)%string = string_occurs quote_char s.
Proof.
  intros c s. pose proof (nat_ascii_bounded c) as Hb.
  destruct (plain_char (nat_of_ascii c)) eqn:Hp.
  - rewrite escape_ascii_plain by assumption. cbn [string_occurs].
    rewrite decide_False; [reflexivity|]. intros ->.
    unfold plain_char, quote_char in Hp.
    rewrite nat_ascii_embedding in Hp by lia. by simpl in Hp.
  - assert (Hhex : forall n, n < 16 -> hex_digit n <> quote_char).
    { intros n Hn Hq. apply (f_equal nat_of_ascii) in Hq.
      rewrite hex_digit_code in Hq by assumption.
      unfold quote_char in Hq. rewrite nat_ascii_embedding in Hq by lia.
      destruct (n <? 10); lia. }
    assert (Hd1 : hex_digit (nat_of_ascii c / 16) <> quote_char)
      by (apply Hhex, Nat.Div0.div_lt_upper_bound; lia).
    assert (Hd2 : hex_digit (nat_of_ascii c mod 16) <> quote_char)
      by (apply Hhex, Nat.mod_upper_bound; lia).
    rewrite escape_ascii_escaped by assumption. cbn [string_occurs].
    by rewrite !decide_False by (first [exact Hd1 | exact Hd2 | done]).
Qed.

Lemma string_occurs_quote_escape_string : forall s,
    string_occurs quote_char (escape_string s) = false.
Proof.
  induction s as [|c s IH]; [reflexivity|].
  cbn [escape_string]. by rewrite string_occurs_quote_escape_ascii, IH.
Qed.

Definition parse_string_literal (f : func) : option string :=
  match f with
  | IdSimple s =>
      match string_strip_prefix quote_string s with
      | Some r =>
          match string_split_at quote_char r with
          | Some (body, EmptyString) => unescape_string body
          | _ => None
          end
      | None => None
      end
  | _ => None
  end.

Lemma parse_string_literal_eq : forall s,
    parse_string_literal (f_string_literal s) = Some s.
Proof.
  intros s. unfold parse_string_literal, f_string_literal.
  rewrite (string_strip_prefix_app quote_string (escape_string s ++ quote_string)).
  unfold quote_string.
  rewrite (string_split_at_app quote_char (escape_string s) EmptyString
             (string_occurs_quote_escape_string s)).
  apply unescape_escape_string.
Qed.

(** A symbol is a constant exactly when reading it back gives one that
    renders to it. *)
Global Instance string_literals_dec (f : func) : Decision (string_literals f).
Proof.
  unfold string_literals.
  destruct (parse_string_literal f) as [s|] eqn:Hp.
  - destruct (decide (f = f_string_literal s)) as [->|Hne].
    + left. by exists s.
    + right. intros [s' ->]. apply Hne.
      rewrite parse_string_literal_eq in Hp. by injection Hp as <-.
  - right. intros [s' ->]. by rewrite parse_string_literal_eq in Hp.
Defined.

Inductive rank_strings : func -> list sort -> sort -> Prop :=
| rank_f_str_concat : rank_strings f_str_concat [σ_string; σ_string] σ_string
| rank_f_str_len : rank_strings f_str_len [σ_string] σ_int
| rank_f_str_lt : rank_strings f_str_lt [σ_string; σ_string] σ_bool
| rank_f_string_literal : forall s, rank_strings (f_string_literal s) [] σ_string.

Program Definition Σ_strings : signature :=
  {|
    sort_symbols := {[ s_bool; s_map; s_string; s_int ]};

    funcs f := f ∈ strings_funcs \/ string_literals f;
    funcs_dec f := decide (f ∈ strings_funcs \/ string_literals f);

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

    rank := rank_strings;
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
  inversion Hf; split; repeat constructor.
Qed.
Next Obligation. Proof. sauto. Qed.
Next Obligation.
Proof.
  intros f H. destruct H as [H | H].
  - assert (H': f = f_str_concat \/ f = f_str_len \/ f = f_str_lt) by set_solver.
    destruct_or! H'; subst f; do 2 eexists; constructor.
  - destruct H as [s H]. subst f. do 2 eexists. constructor.
Qed.
Next Obligation. Proof. set_solver. Qed.
Next Obligation. Proof. set_solver. Qed.
Next Obligation. Proof. set_solver. Qed.
Next Obligation. Proof. set_solver. Qed.

Section StringsModels.

  Variable A : structure.
  Variable domain_σ_string : A.(domain) σ_string = string.
  Variable domain_σ_int : A.(domain) σ_int = Z.

  Definition cast_to_string := cast domain_σ_string.
  Definition cast_to_Z := cast domain_σ_int.
  Definition cast_to_bool := cast A.(domain_σ_bool).

  Definition models_f_str_concat : Prop :=
    let F := A.(interp) f_str_concat [σ_string; σ_string] σ_string in
    forall s1 s2, cast_to_string (F s1 s2) = (cast_to_string s1 ++ cast_to_string s2)%string.

  Definition models_f_str_len : Prop :=
    let F := A.(interp) f_str_len [σ_string] σ_int in
    forall s, cast_to_Z (F s) = Z.of_nat (String.length (cast_to_string s)).

  Definition models_f_str_lt : Prop :=
    let F := A.(interp) f_str_lt [σ_string; σ_string] σ_bool in
    forall s1 s2, cast_to_bool (F s1 s2) = String.ltb (cast_to_string s1) (cast_to_string s2).

  Definition models_f_string_literal : Prop := forall s,
    let F := A.(interp) (f_string_literal s) [] σ_string in
    cast_to_string F = s.

  Record models_strings : Prop :=
    {
      ms_str_concat : models_f_str_concat;
      ms_str_len : models_f_str_len;
      ms_str_lt : models_f_str_lt;
      ms_string_literal : models_f_string_literal
    }.

End StringsModels.

Arguments ms_str_concat {_} {_} {_}.
Arguments ms_str_len {_} {_} {_}.
Arguments ms_str_lt {_} {_} {_}.
Arguments ms_string_literal {_} {_} {_}.

Definition T_strings : pretheory :=
  {|
    pΣ := Σ_strings;
    pmodels A :=
      {Hstring : A.(domain) σ_string = string &
                 {Hint : A.(domain) σ_int = Z &
                         models_strings A Hstring Hint}};
  |}.

(* The symbol is one of [Σ_strings]'s.  The literal family is tried first: it
   fails immediately on a symbol from the finite set, whereas [set_solver] on a
   non-member of that set is slower than it looks. *)
Local Ltac str_func :=
  cbn [funcs Σ_strings];
  first [ right; eexists; reflexivity | left; set_solver ].

(** Every condition names one symbol, and all of them are declared by
    [Σ_strings]. *)
Theorem T_strings_local : pretheory_local T_strings.
Proof.
  intros D Hbool Hmap i j Hagree [Hstring [Hint Hm]].
  exists Hstring, Hint.
  assert (Hrw : forall f, Σ_strings.(funcs) f ->
                  forall σs σ, j f σs σ = i f σs σ)
    by (intros f Hf σs σ; symmetry; exact (Hagree f Hf σs σ)).
  destruct Hm as [A1 A2 A3 A4].
  constructor.
  - unfold models_f_str_concat in A1 |- *; cbv zeta in A1 |- *;
    cbn [interp structure_of] in A1 |- *;
    intros; rewrite Hrw by str_func; eapply A1; eauto.
  - unfold models_f_str_len in A2 |- *; cbv zeta in A2 |- *;
    cbn [interp structure_of] in A2 |- *;
    intros; rewrite Hrw by str_func; eapply A2; eauto.
  - unfold models_f_str_lt in A3 |- *; cbv zeta in A3 |- *;
    cbn [interp structure_of] in A3 |- *;
    intros; rewrite Hrw by str_func; eapply A3; eauto.
  - unfold models_f_string_literal in A4 |- *; cbv zeta in A4 |- *;
    cbn [interp structure_of] in A4 |- *;
    intros; rewrite Hrw by str_func; eapply A4; eauto.
Qed.

(** The three operations are computed on the canonical domains; a literal's
    symbol carries its own payload, recovered by [literal_payload]. *)
Section StringsInterpretable.

  Context (D : sort -> Type).
  Context (witness : forall σ, D σ).
  Context (Hbool : D σ_bool = bool).
  Context (Hmap : forall σ1 σ2, D (τ_map σ1 σ2) = (D σ1 -> D σ2)).
  Context (Hstring : D σ_string = string).
  Context (Hint : D σ_int = Z).

  Local Notation base := (interp_const D witness).

  (* Recovering a literal's payload from its symbol.  The symbol's text is
     the payload *escaped*, so reading it back takes the parser for
     [\u{HH}] that [parse_string_literal] is; the candidate it returns is
     checked by escaping it again, which is what makes the empty string the
     answer off the family rather than some other member's payload. *)
  Local Definition literal_payload (f : func) : string :=
    match parse_string_literal f with
    | Some s => if decide ((f_string_literal s : func) = f) then s else EmptyString
    | None => EmptyString
    end.

  Local Lemma literal_payload_f_string_literal : forall s,
      literal_payload (f_string_literal s) = s.
  Proof.
    intros s. unfold literal_payload.
    rewrite parse_string_literal_eq. by rewrite decide_True.
  Qed.

  (* A literal's symbol begins with a quote; none of the three operations
     does. *)
  Local Lemma f_string_literal_ne_op : forall (s : string) (f : func),
      f ∈ strings_funcs -> (f_string_literal s : func) <> f.
  Proof.
    intros s f Hf Heq.
    unfold strings_funcs in Hf.
    rewrite !elem_of_union, !elem_of_singleton in Hf.
    unfold f_string_literal, quote_string, f_str_concat, f_str_len, f_str_lt
      in *.
    destruct_or! Hf; subst f; injection Heq as Heq; vm_compute in Heq;
      discriminate Heq.
  Qed.

  Definition strings_interp : forall f σs σ, interpretation D σs σ :=
    interp_insert_func D f_str_concat
      (interp_insert_rank D [σ_string; σ_string] σ_string
         (fun s1 s2 : D σ_string =>
            cast_sym Hstring ((cast Hstring s1 ++ cast Hstring s2)%string))
         base)
   (interp_insert_func D f_str_len
      (interp_insert_rank D [σ_string] σ_int
         (fun s : D σ_string =>
            cast_sym Hint (Z.of_nat (String.length (cast Hstring s))))
         base)
   (interp_insert_func D f_str_lt
      (interp_insert_rank D [σ_string; σ_string] σ_bool
         (fun s1 s2 : D σ_string =>
            cast_sym Hbool (String.ltb (cast Hstring s1) (cast Hstring s2)))
         base)
   (fun f => interp_insert_rank D [] σ_string
               (cast_sym Hstring (literal_payload f)) base))).

  Theorem T_strings_interpretable :
    pretheory_interpretable T_strings D Hbool Hmap.
  Proof.
    exists strings_interp. exists Hstring, Hint.
    constructor;
      unfold models_f_str_concat, models_f_str_len, models_f_str_lt,
        models_f_string_literal, cast_to_string, cast_to_Z, cast_to_bool;
      cbv zeta; cbn [interp structure_of].
    - intros s1 s2. unfold strings_interp.
      rewrite interp_insert_func_eq, interp_insert_rank_eq.
      apply cast_cast_sym.
    - intros s. unfold strings_interp.
      rewrite interp_insert_func_ne by discriminate.
      rewrite interp_insert_func_eq, interp_insert_rank_eq.
      apply cast_cast_sym.
    - intros s1 s2. unfold strings_interp.
      rewrite interp_insert_func_ne by discriminate.
      rewrite interp_insert_func_ne by discriminate.
      rewrite interp_insert_func_eq, interp_insert_rank_eq.
      apply cast_cast_sym.
    - intros s. unfold strings_interp.
      rewrite interp_insert_func_ne
        by (apply f_string_literal_ne_op; set_solver).
      rewrite interp_insert_func_ne
        by (apply f_string_literal_ne_op; set_solver).
      rewrite interp_insert_func_ne
        by (apply f_string_literal_ne_op; set_solver).
      cbv beta. rewrite interp_insert_rank_eq.
      rewrite literal_payload_f_string_literal. apply cast_cast_sym.
  Qed.

End StringsInterpretable.

Theorem str_concat_has_sort : forall Σ t1 t2,
    Σ_strings ⊑ Σ ->
    (Σ ⊢ t1 : σ_string) ->
    (Σ ⊢ t2 : σ_string) ->
    Σ ⊢ TApp f_str_concat None [t1; t2] : σ_string.
Proof.
  intros * Hsub Ht1 Ht2.
  econstructor.
  - exists ∅, [σ_string; σ_string], σ_string. sauto.
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

Theorem str_len_has_sort : forall Σ t,
    Σ_strings ⊑ Σ ->
    (Σ ⊢ t : σ_string) ->
    Σ ⊢ TApp f_str_len None [t] : σ_int.
Proof.
  intros * Hsub Ht.
  econstructor.
  - exists ∅, [σ_string], σ_int. sauto.
  - intros * Hrank.
    eapply monomorphic_rank_conservative in Hrank; eauto.
    ecrush. set_solver.
  - reflexivity.
  - intros * Ht_i Hσ_i.
    rewrite list_lookup_singleton in Ht_i.
    rewrite list_lookup_singleton in Hσ_i.
    case_match; simplify_eq.
    assumption.
Qed.

Theorem str_lt_has_sort : forall Σ t1 t2,
    Σ_strings ⊑ Σ ->
    (Σ ⊢ t1 : σ_string) ->
    (Σ ⊢ t2 : σ_string) ->
    Σ ⊢ TApp f_str_lt None [t1; t2] : σ_bool.
Proof.
  intros * Hsub Ht1 Ht2.
  econstructor.
  - exists ∅, [σ_string; σ_string], σ_bool. sauto.
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

Theorem string_literal_has_sort : forall Σ s,
    Σ_strings ⊑ Σ ->
    Σ ⊢ string_literal s : σ_string.
Proof.
  intros * Hsub.
  econstructor.
  - sauto q:on.
  - intros * Hrank.
    eapply monomorphic_rank_conservative in Hrank; eauto; sauto.
  - reflexivity.
  - intros * Ht_i Hσ_i. inversion Ht_i.
Qed.
