(** * SMTLIB.Utils : General-Purpose Helpers *)

(** Transport along a type equality, then small facts about stdpp's own
    datatypes: options, lists, lists read as finite maps and sets, strings
    and their renderings, and stdpp's fresh-string generator. *)

From stdpp Require Import list gmap stringmap pretty.
From Stdlib Require Import Ascii.
From Stdlib Require Import Logic.EqdepFacts Logic.Eqdep_dec.
From Hammer Require Import Tactics.

(** * Type Casts *)

(** Two types that are provably equal are not thereby definitionally equal, so
    a value of one is not accepted where the other is expected until it is
    transported across the proof. [cast] transports forwards along such an
    equality and [cast_sym] backwards; the facts below are what lets a proof
    move a goal between the two sides.

    The caller this exists for is a record field of the form [f x = T], which
    fixes a type propositionally rather than by definition and leaves every
    use of that type owing a transport. *)

Definition cast {A B : Type} (H : A = B) (x : A) : B :=
  eq_rect A (fun T => T) x B H.

Definition cast_sym {A B : Type} (H : A = B) (x : B) : A :=
  eq_rect B (fun T => T) x A (eq_sym H).

Theorem cast_eq_iff_eq_cast_sym : forall {A B : Type} (H : A = B) (x : A) (y : B),
    cast H x = y <-> x = cast_sym H y.
Proof. sauto lq:on. Qed.

Theorem cast_sym_cast : forall {A B : Type} (H : A = B) (x : A),
    cast_sym H (cast H x) = x.
Proof. sauto lq:on. Qed.

Theorem cast_cast_sym : forall {A B : Type} (H : A = B) (y : B),
    cast H (cast_sym H y) = y.
Proof. sauto lq:on. Qed.

Theorem cast_sym_true_or_false : forall {T : Type} (H : T = bool) (x : T),
    x = cast_sym H true \/ x = cast_sym H false.
Proof.
  intros T H x.
  destruct (cast H x) eqn:Hb; [left|right];
    rewrite <- Hb; symmetry; apply cast_sym_cast.
Qed.

Theorem cast_sym_true_neq_false : forall {T : Type} (H : T = bool),
    cast_sym H true <> cast_sym H false.
Proof.
  intros T H Heq.
  assert (Hc : cast H (cast_sym H true) = cast H (cast_sym H false))
    by (rewrite Heq; reflexivity).
  rewrite !cast_cast_sym in Hc. discriminate Hc.
Qed.

(** * Heterogeneous Equality *)

(** Two elements of a family at two indices, equal in the sense that carries
    the two indices.  [JMeq] states the same thing about their two *types*
    and forgets the indices, so recovering an equation from it is UIP at
    [Type], which is an axiom; [eq_dep] keeps them, and [eq_of_heq] below
    recovers an equation whenever the index type has decidable equality —
    which it does everywhere here, the indices being sorts.

    An equation between dependent pairs would say the same thing again, but
    it is an [eq], so [simplify_eq] takes it apart and, with an equation
    between the two indices also in context, loops; [set_solver] is then
    unusable in any proof that carries one. *)
Notation "x ≅ y" := (eq_dep _ _ _ x _ y)
  (at level 70, no associativity) : type_scope.

(** Transport along an equation of indices is heterogeneously the identity. *)
Lemma heq_eq_rect_l :
  forall {I} (P : I -> Type) (i j : I) (x : P i) (Heq : i = j),
    eq_rect i P x j Heq ≅ x.
Proof. intros. destruct Heq. reflexivity. Qed.

(** At one index, a heterogeneous equation is an equation.  [eq_dep_sym] and
    [eq_dep_trans] are the other two steps; [reflexivity] already closes a
    [≅] goal, but [symmetry] and [etransitivity] do not, the relation not
    being homogeneous. *)
Lemma eq_of_heq : forall {I} `{EqDecision I} (P : I -> Type) (i : I) (x y : P i),
    x ≅ y -> x = y.
Proof.
  intros I ? P i x y H.
  apply (Eqdep_dec.eq_dep_eq_dec (fun a b => decide (a = b))). exact H.
Qed.

(** The same for an equation of dependent pairs at one index, which is how a
    finite map of sort-tagged values hands back what it stores. *)
Lemma eq_of_existT : forall {I} `{EqDecision I} (P : I -> Type) (i : I) (x y : P i),
    existT i x = existT i y -> x = y.
Proof.
  intros I ? P i x y. apply inj_pair2_eq_dec. intros a b. apply (decide (a = b)).
Qed.

(** * Options *)

(** For the general characterisation of [option_Forall], see stdpp's
    [option_Forall_from_option]. *)

Lemma option_Forall_Some : forall {A} (R : A -> Prop) x,
 option_Forall R (Some x) <-> R x.
Proof. sauto lq: on. Qed.

Lemma option_Forall_None : forall {A} (R : A -> Prop),
 option_Forall R None.
Proof. sauto lq: on. Qed.

(** * Lists *)

(** [omap] never grows a list. *)
Theorem length_omap_le :
 forall {A B} (f : A -> option B) (l : list A),
 length (omap f l) <= length l.
Proof.
 intros A B f l. induction l as [|a l' IH]; simpl; [lia|].
 destruct (f a) eqn:E; simpl; [apply le_n_S; exact IH|].
 etrans; [exact IH | apply Nat.le_succ_diag_r].
Qed.

(** An element [omap] drops makes the shrinkage strict. *)
Theorem length_omap_lt :
 forall {A B} (f : A -> option B) (l : list A) (a : A),
 a ∈ l ->
 f a = None ->
 length (omap f l) < length l.
Proof.
 intros A B f l a Hin Hnone. induction l as [|b l' IH].
 - apply elem_of_nil in Hin. contradiction.
 - apply elem_of_cons in Hin. simpl. destruct (f b) eqn:E; simpl.
   + apply le_n_S. apply IH.
     destruct Hin as [->|Hin]; [rewrite Hnone in E; discriminate | exact Hin].
   + apply le_n_S. apply length_omap_le.
Qed.

(** Mapping over the second component of a list of pairs leaves the first
    projections alone. *)
Theorem map_fst_map_second :
 forall {A B C} (g : B -> C) (l : list (A * B)),
 map fst (map (fun '(a, b) => (a, g b)) l) = map fst l.
Proof.
 intros A B C g l. rewrite map_map. apply map_ext. intros [a b]. reflexivity.
Qed.

(** ** Contiguous Sublists *)

(** [l1] occurs in [l2] as one unbroken run.  stdpp's [sublist_of] allows
    gaps, and stdpp has [prefix_of] and [suffix_of] but nothing between them. *)
Definition infix {A} (l1 l2 : list A) : Prop := exists k1 k2, l2 = k1 ++ l1 ++ k2.

Infix "`infix_of`" := infix (at level 70) : stdpp_scope.

Theorem infix_of_singleton : forall {A} (x : A) (l : list A),
 [x] `infix_of` l <-> x ∈ l.
Proof.
 intros A x l. split.
 - intros (k1 & k2 & ->). set_solver.
 - intros Hin. apply list_elem_of_split in Hin as (k1 & k2 & ->).
   exists k1, k2. reflexivity.
Qed.

(** ** Type-Valued "Every Element" *)

(** stdpp's [Forall] is [Prop]-valued, so it cannot carry the induction
    hypotheses of a recursor whose motive is in [Type].  This is the [Type]
    analogue, a nested tuple, matching [hlist_ForallT] in [SMTLIB.Theory]. *)
Fixpoint list_ForallT {A : Type} (P : A -> Type) (l : list A) : Type :=
  match l with
  | [] => unit
  | x :: l' => (P x * list_ForallT P l')%type
  end.

(** The payload wants to be read positionally in a proof, as [hlist_ForallT]'s
    does. *)
Theorem list_ForallT_lookup :
  forall {A} (P : A -> Prop) (l : list A),
    list_ForallT P l -> forall i x, l !! i = Some x -> P x.
Proof.
  intros A P l. induction l as [|y l' IH]; simpl.
  - intros _ i x Hlk. destruct i; simpl in Hlk; discriminate.
  - intros [Hy Hall] i x Hlk. destruct i; simpl in Hlk.
    + injection Hlk as <-. exact Hy.
    + eapply IH; eassumption.
Qed.

(** ** Decidable List Equality *)

(** Boolean equality on lists, from a boolean equality on elements. *)
Fixpoint list_eqb {A : Type} (eqb : A -> A -> bool) (l1 l2 : list A) : bool :=
 match l1, l2 with
 | [], [] => true
 | x1 :: l1', x2 :: l2' => eqb x1 x2 && list_eqb eqb l1' l2'
 | _, _ => false
 end.

(** [list_eqb] decides equality exactly when the element test does. *)
Theorem list_eqb_iff : forall {A} (eqb : A -> A -> bool) (l1 l2 : list A),
 (forall x y, eqb x y = true <-> x = y) ->
 list_eqb eqb l1 l2 = true <-> l1 = l2.
Proof.
 intros A eqb l1. induction l1 as [ | x l1 IH ]; intros [ | y l2 ] Helem; simpl.
 - split; reflexivity.
 - split; intros H; discriminate.
 - split; intros H; discriminate.
 - rewrite andb_true_iff, Helem, (IH l2 Helem). split.
   + intros [ -> -> ]. reflexivity.
   + intros H. injection H as -> ->. split; reflexivity.
Qed.

(** Decide list equality from a decision that holds only at the elements the
    two lists actually contain.  [list_eq_dec] asks for a decision at every
    element of the type, which a nested inductive cannot supply: its induction
    hypothesis reaches its own subterms and nothing else. *)
Theorem list_eq_dec_elem_of : forall {A} (xs ys : list A),
 (forall x y, x ∈ xs -> y ∈ ys -> { x = y } + { x <> y }) ->
 { xs = ys } + { xs <> ys }.
Proof.
 induction xs as [ | x xs IH ]; intros * Helem.
 - destruct ys; now auto.
 - destruct ys as [ | y ys ]; [ now right | ].
   specialize (IH ys). assert (Htail: {xs = ys} + {xs <> ys}).
   { apply IH. intros. apply Helem; set_solver. }
   specialize (Helem x y). assert (Hhead: {x = y} + {x <> y}).
   { apply Helem; set_solver. }
   destruct Hhead, Htail; subst; sfirstorder.
Qed.

(** ** Deciding [Forall] From Elementwise Decisions *)

(** stdpp's [Forall_dec] wants a decision at *every* element of the carrier,
    which a recursion over a nested inductive cannot supply: [sort_rect]'s
    induction hypothesis decides only the immediate arguments.  This is the
    version that asks no more than that. *)
Lemma Forall_dec_elem :
  forall {A} (P : A -> Prop) (l : list A),
    (forall x, x ∈ l -> Decision (P x)) -> Decision (Forall P l).
Proof.
  intros A P l. induction l as [| x l' IH]; intros Hdec.
  - left. constructor.
  - destruct (Hdec x ltac:(set_solver)) as [Hx | Hx].
    + destruct (IH ltac:(intros y Hy; apply Hdec; set_solver)) as [Hl | Hl].
      * left. by constructor.
      * right. intros Hwf. inversion Hwf. contradiction.
    + right. intros Hwf. inversion Hwf. contradiction.
Defined.

(** ** Projecting [Forall] *)

(** [Forall]'s two projections at a cons, as transparent terms.  [Stdlib]'s
    [Forall_inv] and [Forall_inv_tail] are opaque, which matters to a
    [Type]-valued recursion that threads a [Forall] through: a [cbn] that
    cannot step the projection stops with the premise unread, and a proof that
    passed a particular premise in cannot see it come back out. *)
Definition Forall_cons_head {A} {P : A -> Prop} {x xs}
  (H : Forall P (x :: xs)) : P x :=
  match H in Forall _ l
        return match l with [] => True | y :: _ => P y end with
  | ListDef.Forall_nil _ => I
  | ListDef.Forall_cons _ _ _ h _ => h
  end.

Definition Forall_cons_tail {A} {P : A -> Prop} {x xs}
  (H : Forall P (x :: xs)) : Forall P xs :=
  match H in Forall _ l
        return match l with [] => True | _ :: l' => Forall P l' end with
  | ListDef.Forall_nil _ => I
  | ListDef.Forall_cons _ _ _ _ t => t
  end.

(** * Lists into Finite Maps and Sets *)

(** A key outside the key list is absent from the map the list zips into.

    Stated one-directionally: the converse needs [length ks = length vs], since
    a key can otherwise sit in [ks] beyond the point where [zip] truncates. *)
Theorem lookup_list_to_map_zip_None :
 forall {A B} `{Countable A} (ks : list A) (vs : list B) (k : A),
 k ∉ ks ->
 (list_to_map (zip ks vs) : gmap A B) !! k = None.
Proof.
 intros A B ?? ks vs k Hk. apply not_elem_of_list_to_map_1.
 intro Hin. apply list_elem_of_fmap in Hin as ([a b] & Heq & Hp).
 simpl in Heq. subst a. apply elem_of_zip_l in Hp. contradiction.
Qed.

(** Mapping over the values of a zipped map is mapping over the value list. *)
Theorem fmap_list_to_map_zip :
 forall {A B C} `{Countable A} (f : B -> C) (ks : list A) (vs : list B),
 f <$> (list_to_map (zip ks vs) : gmap A B) = list_to_map (zip ks (f <$> vs)).
Proof.
 intros A B C ?? f ks vs. rewrite <- list_to_map_fmap. f_equal.
 revert vs. induction ks as [|k ks IH]; intros [|v vs]; simpl; [done..|].
 by rewrite IH.
Qed.

(** A one-binder list extension is an insertion. *)
Theorem list_to_map_zip_singleton_union :
 forall {K A} `{Countable K} (m : gmap K A) (k : K) (v : A),
 list_to_map (zip [k] [v]) ∪ m = <[k := v]> m.
Proof.
 intros K A ?? m k v. simpl. rewrite <- insert_union_l. f_equal. apply (left_id_L ∅ (∪)).
Qed.

(** Two maps agreeing at [j] away from a common extension still agree at [j]
    once both are extended the same way: an insert at [i] decides [j = i], a
    common left operand of [∪] decides every key it defines. *)
Theorem lookup_insert_agree :
 forall {K A} `{Countable K} (m1 m2 : gmap K A) (i j : K) (x : A),
 (j <> i -> m1 !! j = m2 !! j) ->
 <[i := x]> m1 !! j = <[i := x]> m2 !! j.
Proof.
 intros K A ?? m1 m2 i j x Hag. destruct (decide (j = i)) as [->|Hji].
 - by rewrite !lookup_insert_eq.
 - rewrite !lookup_insert_ne by congruence. by apply Hag.
Qed.

Theorem lookup_union_agree :
 forall {K A} `{Countable K} (m m1 m2 : gmap K A) (j : K),
 (m !! j = None -> m1 !! j = m2 !! j) ->
 (m ∪ m1) !! j = (m ∪ m2) !! j.
Proof.
 intros K A ?? m m1 m2 j Hag. destruct (m !! j) as [a|] eqn:Hj.
 - by rewrite !(lookup_union_Some_l _ _ _ _ Hj).
 - rewrite !(lookup_union_r _ _ _ Hj). by apply Hag.
Qed.

(** [list_to_set] can only lose elements, never gain them.  stdpp's
    [size_list_to_set] gives the exact size but assumes [NoDup]; this bound
    holds unconditionally. *)
Theorem size_list_to_set_le :
 forall {A} `{Countable A} (l : list A),
 size (list_to_set l : gset A) <= length l.
Proof.
 intros A ?? l. induction l as [|a l' IH]; simpl.
 - apply Nat.le_0_l.
 - rewrite size_union_alt, size_singleton.
   assert (Hd : size ((list_to_set l' : gset A) ∖ {[a]})
                <= size (list_to_set l' : gset A))
     by (apply subseteq_size; set_solver).
   lia.
Qed.

(** Looking a key up by its first position in the key list agrees with looking
    it up in the map the keys zip into. *)
Theorem list_find_eq_list_to_map_zip {K A} `{Countable K} :
  forall (xs : list K) (us : list A) x (d : A),
    length xs = length us ->
    match list_find (fun y => x = y) xs with
    | Some (j,_) => nth j us d
    | None => d
    end
    = match (list_to_map (zip xs us) : gmap K A) !! x with
      | Some u => u
      | None => d
      end.
Proof.
  induction xs as [|a xs IH]; intros us x d Hlen.
  - destruct us; simpl in *; [reflexivity| discriminate].
  - destruct us as [|u us]; simpl in Hlen; [discriminate|].
    injection Hlen as Hlen.
    simpl list_find. simpl zip. rewrite list_to_map_cons.
    destruct (decide (x = a)) as [->|Hne].
    + simpl. rewrite lookup_insert_eq. reflexivity.
    + rewrite lookup_insert_ne by auto.
      specialize (IH us x d Hlen).
      destruct (list_find (fun y => x = y) xs) as [[j w]|] eqn:Hf; simpl.
      * exact IH.
      * exact IH.
Qed.

(** * Strings *)

Theorem string_length_append : forall s t,
  String.length (s +:+ t) = String.length s + String.length t.
Proof. induction s; simpl; auto. Qed.

(** stdpp's [String.app_inj] cancels a common prefix; this cancels a common
    suffix. *)
Theorem string_app_inj_tail : forall s1 s2 t : string,
  s1 +:+ t = s2 +:+ t -> s1 = s2.
Proof.
  induction s1 as [| c1 s1 IH]; intros [| c2 s2] t H.
  - reflexivity.
  - apply (f_equal String.length) in H.
    rewrite !string_length_append in H. cbn [String.length] in H. lia.
  - apply (f_equal String.length) in H.
    rewrite !string_length_append in H. cbn [String.length] in H. lia.
  - injection H as -> H. f_equal. eauto.
Qed.

(** * Reading Back a Rendering *)

(** A symbol that carries a number carries it as text, through stdpp's
    [pretty].  Deciding whether a symbol is one of those, or recovering the
    number it carries, therefore needs a partial inverse: a [parse] that
    agrees with [pretty] on [pretty]'s image.  Soundness on the rest of the
    strings is not needed and is not claimed — a caller that wants it checks
    the candidate by rendering it again. *)

Definition parse_N_char (c : ascii) : option N :=
  match c with
  | "0"%char => Some 0 | "1"%char => Some 1 | "2"%char => Some 2
  | "3"%char => Some 3 | "4"%char => Some 4 | "5"%char => Some 5
  | "6"%char => Some 6 | "7"%char => Some 7 | "8"%char => Some 8
  | "9"%char => Some 9 | _ => None
  end%N.

Lemma parse_N_char_pretty : forall x,
    (x < 10)%N -> parse_N_char (pretty_N_char x) = Some x.
Proof.
  intros x Hx.
  assert (x = 0 \/ x = 1 \/ x = 2 \/ x = 3 \/ x = 4 \/
          x = 5 \/ x = 6 \/ x = 7 \/ x = 8 \/ x = 9)%N as Hx10 by lia.
  by repeat (destruct Hx10 as [->|Hx10]; [reflexivity|]); subst x.
Qed.

(** Read the digits of [s] onto [acc], left to right. *)
Fixpoint parse_N_go (s : string) (acc : N) : option N :=
  match s with
  | EmptyString => Some acc
  | String c s' =>
      match parse_N_char c with
      | Some d => parse_N_go s' (acc * 10 + d)
      | None => None
      end
  end%N.

(** [k] is the power of ten [x] was rendered at; the digit count is not
    needed anywhere else, so it stays existential. *)
Lemma parse_N_go_pretty : forall x s acc,
    exists k, (x < k)%N /\
      parse_N_go (pretty_N_go x s) acc = parse_N_go s (acc * k + x)%N.
Proof.
  intros x. induction x as [x IH] using (well_founded_ind N.lt_wf_0);
    intros s acc.
  destruct (decide (0 < x)%N) as [Hpos|Hz].
  - rewrite pretty_N_go_step by done.
    destruct (IH (x `div` 10)%N (N.div_lt x 10 Hpos eq_refl)
                (String (pretty_N_char (x `mod` 10)) s) acc)
      as (k & Hlt & Heq).
    exists (10 * k)%N.
    pose proof (N.div_mod' x 10) as Hdm.
    assert (x `mod` 10 < 10)%N as Hmod by (apply N.mod_lt; done).
    split; [lia|].
    rewrite Heq. simpl.
    rewrite parse_N_char_pretty by (apply N.mod_lt; done).
    f_equal. lia.
  - assert (x = 0)%N as -> by lia.
    rewrite pretty_N_go_0. exists 1%N. split; [lia|]. f_equal; lia.
Qed.

Definition parse_N (s : string) : option N := parse_N_go s 0.

Lemma parse_N_pretty : forall n : N, parse_N (pretty n) = Some n.
Proof.
  intros n. unfold parse_N, pretty, pretty_N.
  destruct (decide (n = 0)%N) as [->|Hn]; [reflexivity|].
  destruct (parse_N_go_pretty n "" 0) as (k & _ & Heq).
  rewrite Heq. simpl. f_equal; lia.
Qed.

Definition parse_positive (s : string) : option positive :=
  match parse_N s with Some (Npos p) => Some p | _ => None end.

Lemma parse_positive_pretty : forall p, parse_positive (pretty p) = Some p.
Proof.
  intros p. unfold parse_positive, pretty at 1, pretty_positive.
  by rewrite parse_N_pretty.
Qed.

(** A leading minus is what [pretty] puts on a negative, and it is not a
    digit, so the unsigned read fails on exactly those. *)
Definition parse_Z (s : string) : option Z :=
  match parse_N s with
  | Some n => Some (Z.of_N n)
  | None =>
      match s with
      | String "-"%char s' =>
          match parse_positive s' with Some p => Some (Zneg p) | None => None end
      | _ => None
      end
  end.

Lemma parse_Z_pretty : forall z : Z, parse_Z (pretty z) = Some z.
Proof.
  intros [|p|p]; unfold pretty at 1, pretty_Z; unfold parse_Z.
  - reflexivity.
  - change (pretty p) with (pretty (N.pos p)).
    by rewrite parse_N_pretty.
  - change (pretty p) with (pretty (N.pos p)). simpl.
    change (String.app "" (pretty (N.pos p))) with (pretty (N.pos p)).
    unfold parse_positive. by rewrite parse_N_pretty.
Qed.

(** ** Taking a Rendering Apart *)

(** Read a known prefix off the front of a string. *)
Fixpoint string_strip_prefix (p s : string) : option string :=
  match p, s with
  | EmptyString, _ => Some s
  | String c p', String d s' =>
      if decide (c = d) then string_strip_prefix p' s' else None
  | String _ _, EmptyString => None
  end.

Lemma string_strip_prefix_app : forall p s, string_strip_prefix p (p +:+ s) = Some s.
Proof.
  induction p as [|c p IH]; intros s; simpl; [reflexivity|].
  by rewrite decide_True.
Qed.

Fixpoint string_occurs (c : ascii) (s : string) : bool :=
  match s with
  | EmptyString => false
  | String d s' => if decide (d = c) then true else string_occurs c s'
  end.

(** Split at the first occurrence of [c], which is dropped. *)
Fixpoint string_split_at (c : ascii) (s : string) : option (string * string) :=
  match s with
  | EmptyString => None
  | String d s' =>
      if decide (d = c) then Some (EmptyString, s')
      else match string_split_at c s' with
           | Some (a, b) => Some (String d a, b)
           | None => None
           end
  end.

Lemma string_split_at_app : forall c a b,
    string_occurs c a = false -> string_split_at c (a +:+ String c b) = Some (a, b).
Proof.
  intros c a. induction a as [|d a IH]; intros b Hocc; simpl.
  - by rewrite decide_True.
  - simpl in Hocc. destruct (decide (d = c)) as [->|Hne]; [discriminate|].
    by rewrite (IH b Hocc).
Qed.

(** A rendered number is digits, so a separator that is not one survives the
    split above. *)
Lemma string_occurs_pretty_N_go : forall c x s,
    (forall n, (n < 10)%N -> pretty_N_char n <> c) ->
    string_occurs c (pretty_N_go x s) = string_occurs c s.
Proof.
  intros c x. induction x as [x IH] using (well_founded_ind N.lt_wf_0);
    intros s Hc.
  destruct (decide (0 < x)%N) as [Hpos|Hz].
  - rewrite pretty_N_go_step by done.
    rewrite (IH (x `div` 10)%N (N.div_lt x 10 Hpos eq_refl) _ Hc). simpl.
    rewrite decide_False; [reflexivity|].
    apply Hc, N.mod_lt; done.
  - assert (x = 0)%N as -> by lia. by rewrite pretty_N_go_0.
Qed.

Lemma string_occurs_pretty_N : forall c (n : N),
    (forall m, (m < 10)%N -> pretty_N_char m <> c) -> string_occurs c (pretty n) = false.
Proof.
  intros c n Hc. unfold pretty, pretty_N.
  destruct (decide (n = 0)%N) as [->|Hn].
  - simpl. rewrite decide_False; [reflexivity|]. apply (Hc 0%N); lia.
  - by rewrite string_occurs_pretty_N_go.
Qed.

Lemma string_occurs_pretty_Z : forall c (z : Z),
    c <> "-"%char ->
    (forall m, (m < 10)%N -> pretty_N_char m <> c) -> string_occurs c (pretty z) = false.
Proof.
  intros c z Hdash Hc. unfold pretty at 1, pretty_Z.
  destruct z as [|p|p].
  - simpl. rewrite decide_False; [reflexivity|]. apply (Hc 0%N); lia.
  - change (pretty p) with (pretty (N.pos p)). by apply string_occurs_pretty_N.
  - change (pretty p) with (pretty (N.pos p)). simpl.
    rewrite decide_False by (intros Heq; by apply Hdash).
    change (String.app "" (pretty (N.pos p))) with (pretty (N.pos p)).
    by apply string_occurs_pretty_N.
Qed.

(** * Fresh Strings *)

(** [fresh_string_of_set] and [fresh_strings_of_set] are stdpp's, from
    [stringmap]: the second draws [n] names avoiding a given [stringset], each
    draw also avoiding the ones before it.

    Three facts make such a list usable as a run of binder names: there are [n]
    of them, they are pairwise distinct, and they avoid the set. *)

Lemma not_elem_of_fresh_strings_of_set : forall s n y Y,
 y ∈ Y -> y ∉ fresh_strings_of_set s n Y.
Proof.
 induction n.
 - simpl. intros. apply not_elem_of_nil.
 - intros. simpl. rewrite not_elem_of_cons. split.
   { pose proof fresh_string_of_set_fresh. set_solver. }
   { apply IHn. set_solver. }
Qed.

Theorem length_fresh_strings_of_set : forall s n X,
 length (fresh_strings_of_set s n X) = n.
Proof. induction n; sauto. Qed.

Theorem NoDup_fresh_strings_of_set : forall s n X,
 NoDup (fresh_strings_of_set s n X).
Proof.
 induction n; intros.
 - constructor.
 - simpl. constructor.
   + apply not_elem_of_fresh_strings_of_set. set_solver.
   + sauto.
Qed.

(** The names drawn avoid the set, and so avoid any subset of it.  The subset
    [X'] is what makes this usable: a caller draws against a union of several
    sets and then needs disjointness from one of them. *)
Theorem fresh_strings_of_set_fresh : forall s n X X',
 X' ⊆ X ->
 list_to_set (fresh_strings_of_set s n X) ## X'.
Proof.
 setoid_rewrite elem_of_disjoint. setoid_rewrite elem_of_list_to_set.
 hauto l: on use: not_elem_of_fresh_strings_of_set.
Qed.
