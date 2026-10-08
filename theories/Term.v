(** * SMTLIB.Term : Syntax of SMT-LIB Terms *)

(** Corresponding to Sec. 5.2, _the language of terms_.
    Binders use the locally nameless representation. *)

From SMTLIB Require Import Utils Symbols.
From stdpp Require Import base gmap stringmap.

(** * Patterns *)

(** Patterns act as binders for match cases.
    [PVar] binds values constructed by an arbitrary constructor.
    [PApp c n] binds values constructed by the constructor [c]. *)

Inductive pattern : Type :=
| PVar
| PApp (c : func) (arity : nat).

Global Instance pattern_eq_dec : EqDecision pattern.
Proof. solve_decision. Qed.

Global Instance pattern_countable : Countable pattern :=
  inj_countable
    (λ p, match p with
          | PVar => inl ()
          | PApp c a => inr (c, a)
          end)
    (λ code, match code with
             | inl () => Some PVar
             | inr (c, a) => Some (PApp c a)
             end)
    (λ p, match p with
          | PVar => eq_refl
          | PApp c a => eq_refl
          end).

Definition pattern_constructor (p : pattern) : option func :=
  match p with
  | PVar => None
  | PApp c _ =>  Some c
  end.

Definition pattern_binders (p : pattern) : nat :=
  match p with
  | PVar => 1
  | PApp _ n => n
  end.

(** Exact coverage leaves no room for a default arm.  [omap
    pattern_constructor] drops a [PVar], so if the constructors it names are as
    many as the patterns themselves, none of them was a [PVar]. *)
Lemma exact_coverage_no_PVar :
  forall (ps : list pattern),
    size (list_to_set (omap pattern_constructor ps) : gset func) = length ps ->
    PVar ∉ ps.
Proof.
  intros ps Hsize Hin.
  pose proof (length_omap_lt pattern_constructor ps PVar Hin eq_refl) as Hlt.
  pose proof (size_list_to_set_le (omap pattern_constructor ps)) as Hle.
  lia.
Qed.

(** * Terms *)

(** Terms use the #<a href="https://www.chargueraud.org/softs/ln/">locally
    nameless representation</a># of quantifiers.
    [TFVar] represents a free variable, whereas
    [TBVar] represents a bound variable with its de Bruijn index. *)

Unset Elimination Schemes.

Inductive term : Type :=
| TFVar (x : var) (* Free variable *)
| TBVar (i : nat) (j : nat) (* Bound variable *)
| TApp (f : func) (σ : option sort) (ts : list term)
| TLambda (σ : sort) (t : term)
| TExists (σ : sort) (t : term)
| TForall (σ : sort) (t : term)
| TLet (binds : list (term)) (t : term)
| TMatch (t : term) (cases: list (pattern * term)).

Set Elimination Schemes.

Definition TExistss (σs : list sort) (t : term) :=
  foldr (fun σ t => TExists σ t) t σs.

(** The automatically generated inductive principle does not
    give inductive hypotheses for subterms within lists.
    E.g. for [TApp f σ ts], no inductive hypothesis is generated
    for each [t ∈ ts]. Below, we manually formulate a stronger
    inductive principle.*)

Section term_ind.

  Variables
    (P : term -> Prop)
    (HP_FVar : ∀ x, P (TFVar x))
    (HP_BVar : ∀ i j, P (TBVar i j))
    (HP_Fun : ∀ σ t, P t -> P (TLambda σ t))
    (HP_App : ∀ f σ ts, (forall t, t ∈ ts -> P t) -> P (TApp f σ ts))
    (HP_Exists : ∀ σ t, P t -> P (TExists σ t))
    (HP_Forall : ∀ σ t, P t -> P (TForall σ t))
    (HP_Let : forall ts t,
        (forall t, t ∈ ts -> P t) ->
        P t ->
        P (TLet ts t))
    (HP_Match : forall t pts,
        P t ->
        (forall p t, (p, t) ∈ pts -> P t) ->
        P (TMatch t pts)).

Fixpoint term_ind t : P t.
Proof.
  destruct t.
  - apply HP_FVar.
  - apply HP_BVar.
  - apply HP_App. induction ts; intros * Helem.
    + inversion Helem.
    + rewrite elem_of_cons in Helem. destruct Helem as [->|Helem].
      * apply term_ind.
      * apply IHts. apply Helem.
  - apply HP_Fun. apply term_ind.
  - apply HP_Exists. apply term_ind.
  - apply HP_Forall. apply term_ind.
  - apply HP_Let.
    + induction binds; intros * Helem.
      * inversion Helem.
      * rewrite elem_of_cons in Helem. destruct Helem as [->|Helem].
        -- apply term_ind.
        -- apply IHbinds. apply Helem.
    + apply term_ind.
  - apply HP_Match.
    + apply term_ind.
    + induction cases; intros * Helem.
      * inversion Helem.
      * rewrite elem_of_cons in Helem. destruct Helem as [Helem|Helem].
        -- destruct a. inversion Helem. apply term_ind.
        -- eapply IHcases. apply Helem.
Qed.

End term_ind.

Definition sub_term t1 t2 :=
 match t2 with
 | TApp f σ ts => t1 ∈ ts
 | TLambda σ t => t1 = t
 | TExists σ t => t1 = t
 | TForall σ t => t1 = t
 | TLet ts t => t1 ∈ ts \/ t1 = t
 | TMatch t pts => t1 = t \/ exists p, (p, t1) ∈ pts
 | _ => False
 end.

Theorem wf_sub_term : well_founded sub_term.
Proof.
  intros t. induction t; constructor;
  intros * Hsub; hauto q:on.
Qed.

Section term_rect.

  Variables
    (P : term -> Type)
    (HP_FVar : ∀ x, P (TFVar x))
    (HP_BVar : ∀ i j, P (TBVar i j))
    (HP_App : ∀ f σ ts, (forall t, t ∈ ts -> P t) -> P (TApp f σ ts))
    (HP_Fun : ∀ σ t, P t -> P (TLambda σ t))
    (HP_Exists : ∀ σ t, P t -> P (TExists σ t))
    (HP_Forall : ∀ σ t, P t -> P (TForall σ t))
    (HP_Let : forall ts t,
        (forall t, t ∈ ts -> P t) ->
        P t ->
        P (TLet ts t))
    (HP_Match : forall t pts,
        P t ->
        (forall p t, (p, t) ∈ pts -> P t) ->
        P (TMatch t pts)).

  Definition term_rect t : P t.
  Proof.
    induction t
      as [ ? IH ]
      using (well_founded_induction_type wf_sub_term).
    destruct t; hauto lq:on.
  Qed.

End term_rect.

Definition term_rec (P : _ -> Set) := term_rect P.

(** [EqDecision] and [Countable] instances for terms. *)

Global Instance term_eq_decision : EqDecision term.
Proof.
  unfold EqDecision, Decision; intros; decide equality;
  simplify_eq; try solve_trivial_decision;
  apply list_eq_dec_elem_of; try naive_solver.
  intros pt1 pt2 Helem1 Helem2.
  destruct pt1 as [p1 t1].
  destruct pt2 as [p2 t2].
  destruct (decide (p1 = p2)), (H0 p1 t1 Helem1 t2);
  first [left; congruence | right; congruence].
Qed.

Fixpoint term_encode (t : term)
  : list (var + (nat * nat) + ((nat * func * option sort) + sort)
          + (sort + sort + (nat + (list pattern)))) :=
  match t with
  | TFVar x => [ inl $ inl $ inl x ]
  | TBVar i j => [ inl $ inl $ inr (i, j) ]
  | TApp f σ ts => (ts ≫= term_encode) ++ [ inl $ inr $ inl (length ts, f, σ) ]
  | TLambda σ t => term_encode t ++ [ inl $ inr $ inr σ ]
  | TExists σ t => term_encode t ++ [ inr $ inl $ inl σ ]
  | TForall σ t => term_encode t ++ [ inr $ inl $ inr σ ]
  | TLet ts t =>
      (ts ≫= term_encode) ++
        (term_encode t) ++
        [ inr $ inr $ inl $ length ts ]
  | TMatch t pts =>
      let ps := map fst pts in
      (term_encode t)
        ++ (pts ≫= term_encode ∘ snd)
        ++ [ inr $ inr $ inr ps ]
  end.

Fixpoint term_decode
  (stack : list term)
  (code : list (var + (nat * nat) + ((nat * func * option sort) + sort)
                + (sort + sort + (nat + (list pattern)))))
  : option term :=
  match code with
  | [] => head stack
  | (inl (inl (inl x))) :: code' =>
      term_decode (TFVar x :: stack) code'
  | (inl (inl (inr (i, j)))) :: code' =>
      term_decode (TBVar i j :: stack) code'
  | (inl (inr (inl (n, f, σ)))) :: code' =>
      let ts := reverse (take n stack) in
      let stack' := drop n stack in
      term_decode (TApp f σ ts :: stack') code'
  | (inl (inr (inr σ))) :: code' =>
      t ← head stack;
      let stack' := tail stack in
      term_decode (TLambda σ t :: stack') code'
  | (inr (inl (inl σ))) :: code' =>
      t ← head stack;
      let stack' := tail stack in
      term_decode (TExists σ t :: stack') code'
  | (inr (inl (inr σ))) :: code' =>
      t ← head stack;
      let stack' := tail stack in
      term_decode (TForall σ t :: stack') code'
  | (inr (inr (inl n))) :: code' =>
      t ← head stack;
      let stack' := tail stack in
      let ts := reverse (take n stack') in
      let stack'' := drop n stack' in
      term_decode (TLet ts t :: stack'') code'
  | (inr (inr (inr ps))) :: code' =>
      let n := length ps in
      let ts := reverse (take n stack) in
      let stack' := drop n stack in
      t ← head stack';
      let stack'' := tail stack' in
      term_decode (TMatch t (zip ps ts) :: stack'') code'
  end.

(* The branch-body segment of a [TMatch] encoding is the concatenation of
   the encodings of the branch bodies. *)
Local Lemma term_encode_bind_snd : forall (pts : list (pattern * term)),
  (pts ≫= (term_encode ∘ snd)) = ((map snd pts) ≫= term_encode).
Proof.
  induction pts as [|[p t] pts IH].
  - reflexivity.
  - simpl. f_equal. apply IH.
Qed.

(* Decoding a concatenation of encoded subterms pushes them, in order,
   onto the stack: the residual code is decoded against [reverse ts ++
   stack].  The per-element hypothesis is supplied by [term_ind].        *)
Local Lemma term_decode_encode_list : forall ts,
  (forall t, t ∈ ts ->
     forall stack code,
       term_decode stack (term_encode t ++ code) = term_decode (t :: stack) code) ->
  forall stack code,
    term_decode stack ((ts ≫= term_encode) ++ code)
      = term_decode (reverse ts ++ stack) code.
Proof.
  induction ts as [|t0 ts IH]; intros Hsub stack code; simpl.
  - reflexivity.
  - rewrite <- app_assoc.
    rewrite Hsub by apply list_elem_of_here.
    rewrite IH.
    + rewrite reverse_cons, <- app_assoc. reflexivity.
    + intros t Ht stack' code'. apply Hsub, list_elem_of_further, Ht.
Qed.

(* Stack-machine invariant: decoding [term_encode t ++ code] is the same
   as decoding [code] with [t] already pushed.  Each binder marker pops
   exactly the elements its subterms pushed (the [reverse]/[take]/[drop]
   bookkeeping cancels), so this is proved by structural induction on t. *)
Local Lemma term_decode_encode_app : forall t stack code,
  term_decode stack (term_encode t ++ code) = term_decode (t :: stack) code.
Proof.
  induction t using term_ind; intros stack code; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite <- app_assoc. rewrite IHt. reflexivity.
  - rewrite <- app_assoc.
    rewrite term_decode_encode_list by assumption. simpl.
    rewrite <- (length_reverse ts).
    rewrite take_app_length, drop_app_length, reverse_involutive.
    reflexivity.
  - rewrite <- app_assoc. rewrite IHt. reflexivity.
  - rewrite <- app_assoc. rewrite IHt. reflexivity.
  - rewrite <- !app_assoc.
    rewrite term_decode_encode_list by assumption.
    rewrite IHt. simpl.
    rewrite <- (length_reverse ts).
    rewrite take_app_length, drop_app_length, reverse_involutive.
    reflexivity.
  - rewrite <- !app_assoc.
    rewrite IHt.
    rewrite term_encode_bind_snd.
    rewrite term_decode_encode_list
      by (intros tt Htt ? ?;
          rewrite list_elem_of_In, in_map_iff in Htt;
          destruct Htt as ([p t0] & Hsnd & Hin); simpl in Hsnd; subst tt;
          rewrite <- list_elem_of_In in Hin; eapply H; eassumption).
    simpl.
    assert (Hn : length (map fst pts) = length (reverse (map snd pts))).
    { rewrite length_reverse, !length_map. reflexivity. }
    rewrite Hn, take_app_length, drop_app_length, reverse_involutive.
    simpl. rewrite zip_fst_snd. reflexivity.
Qed.

Local Lemma term_encode_decode : ∀ t, term_decode [] (term_encode t) = Some t.
Proof.
  intros t. rewrite <- (app_nil_r (term_encode t)).
  rewrite term_decode_encode_app. reflexivity.
Qed.

Global Instance term_countable : Countable term :=
  inj_countable term_encode (term_decode []) term_encode_decode.

(** * Size *)

Fixpoint term_size (t : term) : nat :=
  match t with
  | TApp _ _ ts => 1 + sum_list (map term_size ts)
  | TLambda _ t => 1 + term_size t
  | TExists _ t => 1 + term_size t
  | TForall _ t => 1 + term_size t
  | TLet ts t => 1 + term_size t + sum_list (map term_size ts)
  | TMatch t pts => 1 + term_size t + sum_list (map (term_size ∘ snd) pts)
  | _ => 1
  end.

Lemma term_size_list : forall t ts,
    t ∈ ts -> term_size t < S (sum_list (map term_size ts)).
Proof. induction 1; simpl; lia. Qed.

Lemma term_size_cases : forall (pts : list (pattern * term)) p t,
    (p, t) ∈ pts -> term_size t < S (sum_list (map (term_size ∘ snd) pts)).
Proof.
  intros pts p t H. induction pts as [|a pts IHpts]; [inversion H|].
  rewrite elem_of_cons in H. simpl. unfold compose. simpl.
  destruct H as [Heq | Htl].
  - rewrite <- Heq. simpl. lia.
  - specialize (IHpts Htl). unfold compose in IHpts. lia.
Qed.

(** * Free Variables *)

(** Closed terms contain no free variables,
    and open terms are not closed. *)

Fixpoint fv (t : term) : gset var :=
  match t with
  | TFVar x => {[ x ]}
  | TBVar _ _ => ∅
  | TApp _ _ ts => ⋃ (map fv ts)
  | TLambda _ t => fv t
  | TExists _ t | TForall _ t => fv t
  | TLet ts t => fv t ∪ ⋃ (map fv ts)
  | TMatch t pts => fv t ∪ ⋃ (map (fv ∘ snd) pts)
  end.

Definition closed (t : term) : Prop := fv t = ∅.

Definition open (t : term) : Prop := ~ closed t.

(** A [TLet] binding selectors applied to [t] has no free variables beyond
    those of [t] and of its body: the selector symbols contribute none.  This
    is the shape of the body that evaluating a constructor pattern opens. *)
Lemma fv_TLet_selectors_subseteq :
  forall gs σs t t',
    fv (TLet
          (map (fun '(g, σ_i) => TApp g (Some σ_i) [t]) (zip gs σs))
          t') ⊆ fv t' ∪ fv t.
Proof.
  intros gs σs t t' z Hz.
  simpl in Hz.
  apply elem_of_union in Hz as [Hz|Hz]; [set_solver|].
  apply elem_of_union_list in Hz as (fv_ti & Hfv_ti & Hz).
  apply list_elem_of_fmap in Hfv_ti as (ti & -> & Hti).
  apply list_elem_of_fmap in Hti as ([g σ_i] & -> & _).
  simpl in Hz. set_solver.
Qed.

(** * Opening, Closing, Substitution & Local Closure *)

(** The opening and closing operations of the
    locally nameless representation are given below.
    Opening with [term_open k us t] substitutes
    parallel binders for the terms in [us].
    Closing with [term_close ys k t] replaces
    free variables [ys] with parallely bound variables. *)

(** Substitution with [term_subst subst t] acts on
    free variables as opposed to bound variables:
    if [subst !! x = Some u], then [x] is substituted
    for [u] in [t]. *)

Fixpoint term_open (k : nat) (us : list term) (t : term) : term :=
  match t with
  | TFVar x => TFVar x
  | TBVar i j => if decide (i = k) then nth j us t else t
  | TApp f σ ts => TApp f σ (map (term_open k us) ts)
  | TLambda τ t => TLambda τ (term_open (S k) us t)
  | TExists τ t => TExists τ (term_open (S k) us t)
  | TForall τ t => TForall τ (term_open (S k) us t)
  | TLet ts t =>
      let ts' := map (term_open k us) ts in
      TLet ts' (term_open (S k) us t)
  | TMatch t pts =>
      let t' := term_open k us t in
      let pts' :=
        map (fun '(p, t) => (p, term_open (S k) us t)) pts in
      TMatch t' pts'
  end.

Fixpoint term_close (ys : list var) (k : nat) (t : term) : term :=
  match t with
  | TFVar x =>
      match list_find (fun y => x = y) ys with
      | None   => TFVar x
      | Some (j, _) => TBVar k j
      end
  | TBVar i j => TBVar i j
  | TApp f σ ts => TApp f σ (map (term_close ys k) ts)
  | TLambda τ t => TLambda τ (term_close ys (S k) t)
  | TExists τ t => TExists τ (term_close ys (S k) t)
  | TForall τ t => TForall τ (term_close ys (S k) t)
  | TLet ts t =>
      let ts' := map (term_close ys k) ts in
      TLet ts' (term_close ys (S k) t)
  | TMatch t pts =>
      let t' := term_close ys k t in
      let match_case_open :=
        (fun '(p, t) => (p, term_close ys (S k) t)) in
      TMatch t' (map match_case_open pts)
  end.

Fixpoint term_subst (subst : gmap var term) (t : term) : term :=
  match t with
  | TFVar x =>
      match subst !! x with
      | None   => TFVar x
      | Some t' => t'
      end
  | TBVar i j => TBVar i j
  | TApp f σ ts => TApp f σ (map (term_subst subst) ts)
  | TLambda τ t => TLambda τ (term_subst subst t)
  | TExists τ t => TExists τ (term_subst subst t)
  | TForall τ t => TForall τ (term_subst subst t)
  | TLet ts t =>
      let ts' := map (term_subst subst) ts in
      TLet ts' (term_subst subst t)
  | TMatch t pts =>
      let t' := term_subst subst t in
      let match_case_subst :=
        (fun '(p, t) => (p, term_subst subst t)) in
      TMatch t' (map match_case_subst pts)
  end.

(** Not every [term] is meaningful: nothing stops a [TBVar] from pointing past
    every enclosing binder. [lc] ("locally closed") carves out those that do
    not, with the usual cofinite quantification — each binder rule asks for the
    body, opened with fresh names drawn from outside some finite [L], to be
    locally closed. Opening a locally closed term is the identity
    ([lc_term_open]).

    [lc_at ks t] is the structural counterpart, and is the easier of the two to
    use under a binder. Binders here bind a whole list of variables at once —
    [TLet], and each [TMatch] case — so [ks] is the list of arities of the
    enclosing binders, innermost first, and [TBVar i j] is well formed exactly
    when [ks !! i = Some a] with [j < a]. The two agree at the top level
    ([lc_lc_at]). *)

Inductive lc : term -> Prop :=
| LCT_TFVar : forall x, lc (TFVar x)
| LCT_TApp : forall f σ ts,
    (forall t, t ∈ ts -> lc t) ->
    lc (TApp f σ ts)
| LCT_TLambda : forall σ t (L : gset var),
    (forall x, x ∉ L -> lc (term_open 0 [TFVar x] t)) ->
    lc (TLambda σ t)
| LCT_TExists : forall σ t (L : gset var),
    (forall x, x ∉ L -> lc (term_open 0 [TFVar x] t)) ->
    lc (TExists σ t)
| LCT_TForall : forall σ t (L : gset var),
    (forall x, x ∉ L -> lc (term_open 0 [TFVar x] t)) ->
    lc (TForall σ t)
| LCT_TLet : forall ts t (L : gset var),
    (forall t, t ∈ ts -> lc t) ->
    (forall xs : list var,
        length xs = length ts ->
        list_to_set xs ## L ->
        lc (term_open 0 (map TFVar xs) t)) ->
    lc (TLet ts t)
| LCT_TMatch : forall t pts (L : gset var),
    lc t ->
    (forall p t xs,
        (p, t) ∈ pts ->
        length xs = pattern_binders p ->
        list_to_set xs ## L ->
        lc (term_open 0 (map TFVar xs) t)) ->
    lc (TMatch t pts).

(** Only the leaf rule is a hint: the binder rules would send [auto] hunting
    for a cofinite [L]. *)
Global Hint Resolve LCT_TFVar : core.

Inductive lc_at : list nat -> term -> Prop :=
| LCA_TFVar : forall ks x, lc_at ks (TFVar x)
| LCA_TBVar : forall ks i j a, ks !! i = Some a -> j < a -> lc_at ks (TBVar i j)
| LCA_TApp : forall ks f σ ts,
    (forall t, t ∈ ts -> lc_at ks t) ->
    lc_at ks (TApp f σ ts)
| LCA_TLambda : forall ks σ t,
    lc_at (1 :: ks) t -> lc_at ks (TLambda σ t)
| LCA_TExists : forall ks σ t,
    lc_at (1 :: ks) t -> lc_at ks (TExists σ t)
| LCA_TForall : forall ks σ t,
    lc_at (1 :: ks) t -> lc_at ks (TForall σ t)
| LCA_TLet : forall ks ts t,
    (forall t', t' ∈ ts -> lc_at ks t') ->
    lc_at (length ts :: ks) t ->
    lc_at ks (TLet ts t)
| LCA_TMatch : forall ks t pts,
    lc_at ks t ->
    (forall p t', (p, t') ∈ pts -> lc_at (pattern_binders p :: ks) t') ->
    lc_at ks (TMatch t pts).

(** ** Facts about [term_open] *)

Local Lemma term_open_nth_TFVar : forall k (a c : list var) (i j : nat),
  i <> k ->
  term_open k (map TFVar a) (nth j (map TFVar c) (TBVar i j))
   = nth j (map TFVar c) (TBVar i j).
Proof.
  intros k a c i j Hik.
  rewrite !nth_lookup.
  destruct (map TFVar c !! j) as [u|] eqn:Hu; simpl.
  - rewrite list_lookup_fmap in Hu.
    destruct (c !! j) as [y|] eqn:Hcj; simpl in Hu; [|discriminate].
    injection Hu as <-. reflexivity.
  - simpl. rewrite decide_False by auto. reflexivity.
Qed.

Local Lemma term_open_lem : forall t i us j vs,
    i <> j ->
    term_open i us (term_open j vs t) = term_open j vs t ->
    term_open i us t = t.
Proof.
  induction t; intros * Hneq Heq; simpl in *.
  - reflexivity.
  - hauto q:on.
  - sauto lq:on rew:off.
  - rewrite map_map in Heq.
    rewrite map_ext_in with (g := id).
    { rewrite map_id. reflexivity. }
    intros t Ht. simpl.
    rewrite <- list_elem_of_In in Ht.
    eapply H; eauto. inversion Heq.
    rewrite list_eq_Forall2 in H1.
    apply list_elem_of_lookup_1 in Ht.
    destruct Ht as [k Ht].
    eapply Forall2_lookup_lr
      with (i := k) in H1; revgoals.
    { rewrite list_lookup_fmap, Ht. reflexivity. }
    { rewrite list_lookup_fmap, Ht. reflexivity. }
    eassumption.
  - sauto lq:on rew:off.
  - sauto lq:on rew:off.
  - inversion Heq.
    erewrite IHt; revgoals.
    { apply H2. } { lia. } clear IHt H2.
    enough (map (term_open i us) ts = ts)
      by congruence.
    rewrite map_map in H1.
    rewrite map_ext_in with (g := id).
    { rewrite map_id. reflexivity. }
    intros t_i Ht_i. simpl.
    rewrite <- list_elem_of_In in Ht_i.
    eapply H; eauto.
    rewrite list_eq_Forall2 in H1.
    apply list_elem_of_lookup_1 in Ht_i.
    destruct Ht_i as [k Ht_i].
    eapply Forall2_lookup_lr
      with (i := k) in H1; revgoals.
    { rewrite list_lookup_fmap, Ht_i. reflexivity. }
    { rewrite list_lookup_fmap, Ht_i. reflexivity. }
    eassumption.
  - inversion Heq. clear Heq.
    erewrite IHt; eauto. clear IHt H1.
    enough (map (fun '(p_i, t_i) => (p_i, term_open (S i) us t_i)) pts = pts)
      by congruence.
    rewrite map_map in H2.
    rewrite map_ext_in with (g := id).
    { rewrite map_id. reflexivity. }
    intros pt Hpt.
    destruct pt as [p_i t_i]. simpl.
    rewrite <- list_elem_of_In in Hpt.
    erewrite H with (j := S j); eauto.
    rewrite list_eq_Forall2 in H2.
    apply list_elem_of_lookup_1 in Hpt.
    destruct Hpt as [k Ht_i].
    eapply Forall2_lookup_lr
      with (i := k) in H2; revgoals.
    { rewrite list_lookup_fmap, Ht_i. reflexivity. }
    { rewrite list_lookup_fmap, Ht_i. reflexivity. }
    hauto lq:on.
Qed.

(** Two openings at distinct levels by free-variable lists commute:
    neither substituent contains the bound variables filled by the other. *)
Theorem term_open_comm : forall t m n (a b : list var),
  m <> n ->
  term_open m (map TFVar a) (term_open n (map TFVar b) t)
   = term_open n (map TFVar b) (term_open m (map TFVar a) t).
Proof.
  induction t using term_ind; intros m n a b Hmn; simpl.
  - reflexivity.
  - destruct (decide (i = n)) as [Hin|Hin], (decide (i = m)) as [Him|Him];
      simpl; try (exfalso; lia).
    + case_decide; [|contradiction]. apply term_open_nth_TFVar; auto.
    + case_decide; [|contradiction]. symmetry. apply term_open_nth_TFVar; auto.
    + repeat case_decide; try contradiction; reflexivity.
  - f_equal. apply IHt. lia.
  - f_equal. rewrite !map_map. apply map_ext_in.
    intros tt Htt. rewrite <- list_elem_of_In in Htt. apply H; auto.
  - f_equal. apply IHt. lia.
  - f_equal. apply IHt. lia.
  - f_equal.
    + rewrite !map_map. apply map_ext_in.
      intros tt Htt. rewrite <- list_elem_of_In in Htt. apply H; auto.
    + apply IHt. lia.
  - f_equal.
    + apply IHt. auto.
    + rewrite !map_map. apply map_ext_in.
      intros pt Hpt. destruct pt as [p_i t_i].
      rewrite <- list_elem_of_In in Hpt. f_equal. eapply H; eauto; lia.
Qed.

(** Opening adds at most the free variables of what it opens with.  Stated over
    an arbitrary list of terms; [fv_term_open_TFVar_subseteq] below is the
    [map TFVar xs] case. *)
Theorem fv_term_open_subseteq :
  forall t k us, fv (term_open k us t) ⊆ fv t ∪ ⋃ (map fv us).
Proof.
  induction t using term_ind; intros k us; simpl.
  - (* TFVar *) set_solver.
  - (* TBVar *)
    destruct (decide (i = k)) as [->|Hne]; cycle 1.
    + simpl. set_solver.
    + rewrite nth_lookup. destruct (us !! j) eqn:Hlook; simpl.
      * apply list_elem_of_lookup_2 in Hlook.
        intros y Hy. apply elem_of_union_r.
        apply elem_of_union_list. exists (fv t).
        split; [|exact Hy].
        apply list_elem_of_fmap. exists t. split; [reflexivity|auto].
      * set_solver.
  - (* TLambda *) apply IHt.
  - (* TApp *)
    intros y Hy. apply elem_of_union_list in Hy.
    destruct Hy as (fv_ti & Hfv & Hy).
    apply list_elem_of_fmap in Hfv.
    destruct Hfv as (ti' & Heq & Hin). subst fv_ti.
    apply list_elem_of_fmap in Hin.
    destruct Hin as (ti & Heq & Hin). subst ti'.
    specialize (H ti Hin k us).
    pose proof (H y Hy) as Hy'.
    apply elem_of_union in Hy'. destruct Hy' as [Hy'|Hy'].
    + apply elem_of_union_l. apply elem_of_union_list.
      exists (fv ti). split; [|exact Hy'].
      apply list_elem_of_fmap. exists ti. split; [reflexivity|auto].
    + apply elem_of_union_r. exact Hy'.
  - (* TExists *) apply IHt.
  - (* TForall *) apply IHt.
  - (* TLet *)
    intros y Hy.
    apply elem_of_union in Hy. destruct Hy as [Hy|Hy].
    + specialize (IHt (S k) us). apply IHt in Hy.
      apply elem_of_union in Hy. destruct Hy as [Hy|Hy].
      * apply elem_of_union_l. set_solver.
      * apply elem_of_union_r. exact Hy.
    + apply elem_of_union_list in Hy.
      destruct Hy as (fv_ti & Hfv & Hy).
      apply list_elem_of_fmap in Hfv.
      destruct Hfv as (ti' & Heq & Hin). subst fv_ti.
      apply list_elem_of_fmap in Hin.
      destruct Hin as (ti & Heq & Hin). subst ti'.
      specialize (H ti Hin k us).
      pose proof (H y Hy) as Hy'.
      apply elem_of_union in Hy'. destruct Hy' as [Hy'|Hy'].
      * apply elem_of_union_l. apply elem_of_union_r.
        apply elem_of_union_list. exists (fv ti).
        split; [|exact Hy'].
        apply list_elem_of_fmap. exists ti.
        split; [reflexivity|auto].
      * apply elem_of_union_r. exact Hy'.
  - (* TMatch *)
    intros y Hy.
    apply elem_of_union in Hy. destruct Hy as [Hy|Hy].
    + apply IHt in Hy.
      apply elem_of_union in Hy. destruct Hy as [Hy|Hy].
      * apply elem_of_union_l. set_solver.
      * apply elem_of_union_r. exact Hy.
    + apply elem_of_union_list in Hy.
      destruct Hy as (fv_pt & Hfv & Hy).
      apply list_elem_of_fmap in Hfv.
      destruct Hfv as (pt' & Heq & Hin).
      unfold compose in Heq. subst fv_pt.
      apply list_elem_of_fmap in Hin.
      destruct Hin as ([p ti] & Heq & Hin). subst pt'.
      simpl in Hy.
      specialize (H p ti Hin (S k) us).
      pose proof (H y Hy) as Hy'.
      apply elem_of_union in Hy'. destruct Hy' as [Hy'|Hy'].
      * apply elem_of_union_l. apply elem_of_union_r.
        apply elem_of_union_list. exists (fv ti).
        split; [|exact Hy'].
        apply list_elem_of_fmap. exists (p, ti).
        split; [reflexivity|auto].
      * apply elem_of_union_r. exact Hy'.
Qed.

(** Opening removes no free variable: it replaces bound variables only. *)
Theorem fv_subseteq_fv_term_open :
  forall t k us, fv t ⊆ fv (term_open k us t).
Proof.
  induction t using term_ind; intros k us; simpl.
  - (* TFVar *) reflexivity.
  - (* TBVar *) apply empty_subseteq.
  - (* TLambda *) apply IHt.
  - (* TApp *)
    intros y Hy. apply elem_of_union_list in Hy as (X & HX & Hy).
    apply list_elem_of_fmap in HX as (ti & -> & Hin).
    apply elem_of_union_list. exists (fv (term_open k us ti)). split.
    + apply list_elem_of_fmap. exists (term_open k us ti). split; [reflexivity|].
      apply list_elem_of_fmap. exists ti. split; [reflexivity|exact Hin].
    + exact (H ti Hin k us y Hy).
  - (* TExists *) apply IHt.
  - (* TForall *) apply IHt.
  - (* TLet *)
    apply union_mono; [apply IHt|].
    intros y Hy. apply elem_of_union_list in Hy as (X & HX & Hy).
    apply list_elem_of_fmap in HX as (ti & -> & Hin).
    apply elem_of_union_list. exists (fv (term_open k us ti)). split.
    + apply list_elem_of_fmap. exists (term_open k us ti). split; [reflexivity|].
      apply list_elem_of_fmap. exists ti. split; [reflexivity|exact Hin].
    + exact (H ti Hin k us y Hy).
  - (* TMatch *)
    apply union_mono; [apply IHt|].
    intros y Hy. apply elem_of_union_list in Hy as (X & HX & Hy).
    apply list_elem_of_fmap in HX as ([p ti] & -> & Hin).
    apply elem_of_union_list. exists (fv (term_open (S k) us ti)). split.
    + apply list_elem_of_fmap. exists (p, term_open (S k) us ti). split; [reflexivity|].
      apply list_elem_of_fmap. exists (p, ti). split; [reflexivity|exact Hin].
    + exact (H p ti Hin (S k) us y Hy).
Qed.

(** The free variables of a list of [TFVar]s are exactly those variables. *)
Lemma fv_map_TFVar_eq_list_to_set :
  forall (xs : list var), ⋃ map fv (map TFVar xs) = list_to_set xs.
Proof.
  induction xs as [|x xs' IH]; simpl; [set_solver|].
  rewrite IH. set_solver.
Qed.

(** Opening by [xs] adds at most the variables [xs] to the free variables. *)
Corollary fv_term_open_TFVar_subseteq : forall t k xs,
  fv (term_open k (map TFVar xs) t) ⊆ fv t ∪ list_to_set xs.
Proof.
  intros t k xs.
  rewrite <- fv_map_TFVar_eq_list_to_set.
  apply fv_term_open_subseteq.
Qed.

(** The single-variable case of [fv_term_open_TFVar_subseteq]. *)
Corollary fv_term_open_TFVar1_subseteq : forall t k y,
  fv (term_open k [TFVar y] t) ⊆ fv t ∪ {[y]}.
Proof.
  intros t k y.
  pose proof (fv_term_open_TFVar_subseteq t k [y]) as H.
  set_solver.
Qed.

(** The elementwise form of [fv_term_open_TFVar_subseteq]: a free variable of an
    opened body is either free in the body or one of the variables opened with. *)
Corollary elem_of_fv_term_open_TFVar : forall t k xs y,
  y ∈ fv (term_open k (map TFVar xs) t) ->
  y ∈ fv t \/ y ∈ xs.
Proof.
  intros t k xs y Hy.
  pose proof (fv_term_open_TFVar_subseteq t k xs) as Hsub.
  apply (elem_of_weaken _ _ _ Hy) in Hsub.
  rewrite elem_of_union in Hsub. destruct Hsub as [Hl|Hr]; [left; exact Hl|].
  right. apply elem_of_list_to_set in Hr. exact Hr.
Qed.

(** The single-variable case of [elem_of_fv_term_open_TFVar]. *)
Corollary elem_of_fv_term_open_TFVar1 : forall t k x y,
  y ∈ fv (term_open k [TFVar x] t) ->
  y ∈ fv t \/ y = x.
Proof.
  intros t k x y Hy.
  change [TFVar x] with (map TFVar [x]) in Hy.
  apply elem_of_fv_term_open_TFVar in Hy as [Hl|Hr]; [left; exact Hl|].
  right. apply list_elem_of_singleton in Hr. exact Hr.
Qed.

Theorem term_size_term_open_TFVar : forall t xs k,
    term_size (term_open k (map TFVar xs) t) = term_size t.
Proof.
  induction t using term_ind; intros xs k; simpl.
  - reflexivity.
  - destruct (decide (i = k)) as [->|Hne]; [|reflexivity].
    destruct (nth_in_or_default j (map TFVar xs) (TBVar k j)) as [Hnth|Hnth].
    + apply list_elem_of_In, list_elem_of_fmap in Hnth.
      destruct Hnth as (x & -> & _). reflexivity.
    + rewrite Hnth. reflexivity.
  - f_equal. apply IHt.
  - f_equal. f_equal. rewrite map_map. apply map_ext_in.
    intros tt Htt. rewrite <- list_elem_of_In in Htt. apply H; auto.
  - f_equal. apply IHt.
  - f_equal. apply IHt.
  - rewrite IHt. f_equal. f_equal. rewrite map_map. f_equal. apply map_ext_in.
    intros tt Htt. rewrite <- list_elem_of_In in Htt. apply H; auto.
  - rewrite IHt. f_equal. f_equal. rewrite map_map. f_equal. apply map_ext_in.
    intros pt Hpt. destruct pt as [p_i t_i].
    rewrite <- list_elem_of_In in Hpt. unfold compose; simpl.
    eapply H; eauto.
Qed.

(** ** Facts about [term_close] *)

Local Lemma term_close_nth_TFVar : forall n (a xs : list var) (m j : nat),
  (list_to_set a : gset var) ## list_to_set xs ->
  term_close xs n (nth j (map TFVar a) (TBVar m j))
   = nth j (map TFVar a) (TBVar m j).
Proof.
  intros n a xs m j Hdisj.
  rewrite !nth_lookup.
  destruct (map TFVar a !! j) as [u|] eqn:Hu; simpl.
  - rewrite list_lookup_fmap in Hu.
    destruct (a !! j) as [y|] eqn:Haj; simpl in Hu; [|discriminate].
    injection Hu as <-. simpl.
    destruct (list_find (fun z => y = z) xs) as [[k z]|] eqn:Hfind.
    + exfalso. rewrite list_find_Some in Hfind.
      destruct Hfind as (Hz & Hyz & _). subst z.
      apply list_elem_of_lookup_2 in Haj, Hz.
      apply (Hdisj y); apply elem_of_list_to_set; auto.
    + reflexivity.
  - reflexivity.
Qed.

(** Closing over variables that do not occur free is the identity. *)
Theorem term_close_fresh : forall t ys k,
    list_to_set ys ## fv t ->
    term_close ys k t = t.
Proof.
  induction t; intros * Hdisj; simpl.
  - simpl in Hdisj.
    destruct (list_find (fun y => x= y) ys)
      as [[j y]|] eqn:Hfind; auto.
    rewrite list_find_Some in Hfind.
    destruct Hfind as (Hy & Hx & _). simplify_eq.
    rewrite disjoint_singleton_r in Hdisj.
    contradict Hdisj.
    apply elem_of_list_to_set.
    eapply list_elem_of_lookup_2; eauto.
  - reflexivity.
  - rewrite IHt. reflexivity. set_solver.
  - rewrite map_ext_in with (g := id).
    { rewrite map_id. reflexivity. }
    intros t Ht. simpl.
    rewrite <- list_elem_of_In in Ht.
    apply H; auto. simpl in Hdisj.
    intros y Hy Hy'. apply Hdisj in Hy. apply Hy.
    apply elem_of_union_list.
    exists (fv t). split; auto.
    rewrite list_elem_of_fmap.
    eexists. split; eauto.
  - rewrite IHt; auto.
  - rewrite IHt; auto.
  - simpl in Hdisj.
    rewrite IHt. 2: { set_solver. }
    rewrite map_ext_in with (g := id).
    { rewrite map_id. reflexivity. }
    intros t_i Ht_i. simpl.
    rewrite <- list_elem_of_In in Ht_i.
    apply H; auto. intros y Hy Hy'.
    apply Hdisj in Hy. apply Hy.
    rewrite elem_of_union. right.
    apply elem_of_union_list.
    eexists. split; eauto.
    rewrite list_elem_of_fmap.
    eexists. split; eauto.
  - rewrite IHt; auto. 2: { set_solver. }
    rewrite map_ext_in with (g := id).
    { rewrite map_id. reflexivity. }
    intros pt Hpt. simpl.
    destruct pt as [p_i t_i].
    rewrite <- list_elem_of_In in Hpt.
    rewrite H with (p := p_i); auto.
    intros y Hy Hy'.
    apply Hdisj in Hy. apply Hy. simpl.
    rewrite elem_of_union. right.
    apply elem_of_union_list.
    eexists. split; eauto.
    rewrite list_elem_of_fmap.
    eexists; split; eauto. reflexivity.
Qed.

(** Closing over [ys] removes exactly [ys] from the free variables. *)
Theorem fv_term_close : forall t ys k,
    fv (term_close ys k t) = fv t ∖ list_to_set ys.
Proof.
  induction t; intros *; simpl.
  - destruct (list_find (fun y => x = y))
      as [[j y]|] eqn: Hfind; simpl.
    + rewrite list_find_Some in Hfind.
      destruct Hfind as (Hfind & ? & _). simplify_eq.
      apply list_elem_of_lookup_2 in Hfind. set_solver.
    + rewrite list_find_None in Hfind.
      rewrite Forall_forall in Hfind.
      set_solver.
  - set_solver.
  - rewrite IHt. reflexivity.
  - rewrite map_map. apply set_eq.
    intro x. split; intro Hx.
    + rewrite elem_of_union_list in Hx.
      destruct Hx as (fv_t_i & Hfv_t_i & Hx).
      apply list_elem_of_fmap in Hfv_t_i.
      destruct Hfv_t_i as (t & Hfv_t_i & Ht). simplify_eq.
      rewrite H in Hx; auto.
      rewrite elem_of_difference. split.
      * rewrite elem_of_union_list. set_solver.
      * set_solver.
    + rewrite elem_of_difference in Hx.
      destruct Hx as [Hx Hx'].
      rewrite elem_of_union_list in Hx.
      destruct Hx as (fv_t & Hfv_t & Hx).
      rewrite list_elem_of_fmap in Hfv_t.
      destruct Hfv_t as (t & Hfv_t & Ht). simplify_eq.
      rewrite elem_of_union_list.
      exists (fv (term_close ys k t)). set_solver.
  - rewrite IHt. reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt. rewrite map_map.
    enough (⋃ map (fun x => fv (term_close ys k x)) ts
            = ⋃ map fv ts ∖ list_to_set ys) by set_solver.
    apply set_eq.
    intro x. split; intro Hx.
    + rewrite elem_of_union_list in Hx.
      destruct Hx as (fv_t_i & Hfv_t_i & Hx).
      apply list_elem_of_fmap in Hfv_t_i.
      destruct Hfv_t_i as (t_i & Hfv_t_i & Ht). simplify_eq.
      rewrite H in Hx; auto.
      rewrite elem_of_difference. split.
      * rewrite elem_of_union_list. set_solver.
      * set_solver.
    + rewrite elem_of_difference in Hx.
      destruct Hx as [Hx Hx'].
      rewrite elem_of_union_list in Hx.
      destruct Hx as (fv_t & Hfv_t & Hx).
      rewrite list_elem_of_fmap in Hfv_t.
      destruct Hfv_t as (t_i & Hfv_t_i & Ht_i). simplify_eq.
      rewrite elem_of_union_list.
      exists (fv (term_close ys k t_i)). set_solver.
  - rewrite IHt. rewrite map_map.
    enough (⋃ map (fun x => (fv ∘ snd) (let '(p, t0) := x in (p, term_close ys (S k) t0))) pts
            = ⋃ map (fv ∘ snd) pts ∖ list_to_set ys) by set_solver.
    apply set_eq.
    intro x. split; intro Hx.
    + rewrite elem_of_union_list in Hx.
      destruct Hx as (fv_t_i & Hfv_t_i & Hx).
      apply list_elem_of_fmap in Hfv_t_i.
      destruct Hfv_t_i as (pt & Hfv_t_i & Hpt).
      destruct pt as [p_i t_i]. simplify_eq.
      simpl in Hx. rewrite H with (p := p_i) in Hx; auto.
      rewrite elem_of_difference. split.
      * rewrite elem_of_union_list. set_solver.
      * set_solver.
    + rewrite elem_of_difference in Hx.
      destruct Hx as [Hx Hx'].
      rewrite elem_of_union_list in Hx.
      destruct Hx as (fv_t & Hfv_t & Hx).
      rewrite list_elem_of_fmap in Hfv_t.
      destruct Hfv_t as (pt & Hfv_t_i & Hpt).
      destruct pt as [p_i t_i]. simplify_eq.
      rewrite elem_of_union_list. simpl in Hx.
      exists (fv (term_close ys k t_i)). split.
      * simpl. rewrite list_elem_of_fmap.
        exists (p_i, t_i). set_solver.
      * set_solver.
Qed.

(** Closing never introduces free variables. *)
Corollary fv_term_close_subseteq : forall ys k t,
    fv (term_close ys k t) ⊆ fv t.
Proof.
  intros * x Hx.
  rewrite fv_term_close in Hx.
  set_solver.
Qed.

(** ** Interaction of [term_open] and [term_close] *)

(** An opening and a closing at distinct levels commute, provided the
    opening variables [a] are disjoint from the closing variables [xs]
    (otherwise [term_close] could recapture a variable introduced by
    [term_open]). *)
Theorem term_open_close_comm : forall t m n (a xs : list var),
  m <> n ->
  (list_to_set a : gset var) ## list_to_set xs ->
  term_open m (map TFVar a) (term_close xs n t)
   = term_close xs n (term_open m (map TFVar a) t).
Proof.
  induction t using term_ind; intros m n a xs Hmn Hdisj; simpl.
  - destruct (list_find (fun y => x = y) xs) as [[j y]|]; simpl;
      [rewrite decide_False by lia|]; reflexivity.
  - destruct (decide (i = m)) as [->|Hne]; simpl.
    + symmetry. apply term_close_nth_TFVar. auto.
    + reflexivity.
  - f_equal. apply IHt; auto; lia.
  - f_equal. rewrite !map_map. apply map_ext_in.
    intros tt Htt. rewrite <- list_elem_of_In in Htt. apply H; auto.
  - f_equal. apply IHt; auto; lia.
  - f_equal. apply IHt; auto; lia.
  - f_equal.
    + rewrite !map_map. apply map_ext_in.
      intros tt Htt. rewrite <- list_elem_of_In in Htt. apply H; auto.
    + apply IHt; auto; lia.
  - f_equal.
    + apply IHt; auto.
    + rewrite !map_map. apply map_ext_in.
      intros pt Hpt. destruct pt as [p_i t_i].
      rewrite <- list_elem_of_In in Hpt. f_equal. eapply H; eauto; lia.
Qed.

(** ** Facts about [term_subst] *)

(** [θ] fixes every free variable of [t], so substituting changes nothing.
    This is the root of the identity-substitution family below. *)
Theorem term_subst_id : forall (θ : gmap var term) t,
    (forall x u, x ∈ fv t -> θ !! x = Some u -> u = TFVar x) ->
    term_subst θ t = t.
Proof.
  intros θ t. revert θ.
  induction t using term_ind; intros θ Hid; simpl.
  - destruct (θ !! x) as [u|] eqn:Hx; [|reflexivity].
    apply (Hid x u); [simpl; set_solver| exact Hx].
  - reflexivity.
  - f_equal. apply IHt. intros y u Hy Hu. eapply Hid; eauto.
  - f_equal. rewrite <- (map_id ts) at 2. apply map_ext_in.
    intros tt Htt. rewrite <- list_elem_of_In in Htt.
    apply H; auto. intros y u Hy Hu. eapply Hid; [|exact Hu]. simpl.
    rewrite elem_of_union_list. exists (fv tt). split; [|exact Hy].
    apply list_elem_of_fmap. exists tt. split; [reflexivity| exact Htt].
  - f_equal. apply IHt. intros y u Hy Hu. eapply Hid; eauto.
  - f_equal. apply IHt. intros y u Hy Hu. eapply Hid; eauto.
  - f_equal.
    + rewrite <- (map_id ts) at 2. apply map_ext_in.
      intros tt Htt. rewrite <- list_elem_of_In in Htt.
      apply H; auto. intros y u Hy Hu. eapply Hid; [|exact Hu]. simpl.
      apply elem_of_union_r. rewrite elem_of_union_list.
      exists (fv tt). split; [|exact Hy].
      apply list_elem_of_fmap. exists tt. split; [reflexivity| exact Htt].
    + apply IHt. intros y u Hy Hu. eapply Hid; [|exact Hu]. simpl.
      apply elem_of_union_l. exact Hy.
  - f_equal.
    + apply IHt. intros y u Hy Hu. eapply Hid; [|exact Hu]. simpl.
      apply elem_of_union_l. exact Hy.
    + rewrite <- (map_id pts) at 2. apply map_ext_in.
      intros pt Hpt. destruct pt as [p_i t_i].
      rewrite <- list_elem_of_In in Hpt. unfold id. f_equal.
      eapply H; eauto. intros y u Hy Hu. eapply Hid; [|exact Hu]. simpl.
      apply elem_of_union_r. rewrite elem_of_union_list.
      exists (fv t_i). split; [|exact Hy].
      apply list_elem_of_fmap. exists (p_i, t_i). split; [reflexivity| exact Hpt].
Qed.

(** The identity renaming built from a list of variables. *)
Corollary term_subst_id_zip : forall (xs : list var) t,
    term_subst (list_to_map (zip xs (map TFVar xs)) : gmap var term) t = t.
Proof.
  intros xs t. apply term_subst_id. intros x u _ Hx.
  apply elem_of_list_to_map_2 in Hx.
  apply elem_of_lookup_zip_with in Hx as (i & a & b & Heq & Hxa & Hxb).
  injection Heq as -> ->. rewrite list_lookup_fmap in Hxb.
  destruct (xs !! i) eqn:Hxi; simpl in Hxb; [|discriminate].
  injection Hxb as <-. injection Hxa as <-. reflexivity.
Qed.

(** Renaming a single variable to itself. *)
Corollary term_subst_id_singleton : forall (x : var) (t : term),
    term_subst {[ x := TFVar x ]} t = t.
Proof.
  intros x t. apply term_subst_id. intros y u _ Hy.
  rewrite lookup_singleton_Some in Hy.
  destruct Hy as [Heq1 Heq2]. subst. reflexivity.
Qed.

(** Substituting variables that do not occur free is the identity: the
    premise of [term_subst_id] holds vacuously. The counterpart of
    [term_close_fresh] for substitution. *)
Corollary term_subst_fresh : forall (θ : gmap var term) t,
    dom θ ## fv t ->
    term_subst θ t = t.
Proof.
  intros θ t Hdisj. apply term_subst_id.
  intros x u Hx Hu. exfalso.
  apply (Hdisj x); [apply elem_of_dom; eauto| exact Hx].
Qed.

(** Singleton substitution. *)
Corollary term_subst_fresh_singleton : forall (x : var) (u t : term),
    x ∉ fv t -> term_subst {[ x := u ]} t = t.
Proof.
  intros x u t Hx. apply term_subst_fresh.
  rewrite dom_singleton_L. set_solver.
Qed.

(** Substitution depends only on the map's values at the free variables of
    the term: two substitutions agreeing on [fv t] act identically. *)
Theorem term_subst_ext : forall (θ1 θ2 : gmap var term) t,
    (forall x, x ∈ fv t -> θ1 !! x = θ2 !! x) ->
    term_subst θ1 t = term_subst θ2 t.
Proof.
  intros θ1 θ2 t. revert θ1 θ2.
  induction t using term_ind; intros θ1 θ2 Hagree; simpl.
  - rewrite (Hagree x). reflexivity. simpl. set_solver.
  - reflexivity.
  - f_equal. apply IHt. intros y Hy. apply Hagree. exact Hy.
  - f_equal. apply map_ext_in. intros tt Htt. rewrite <- list_elem_of_In in Htt.
    apply H; auto. intros y Hy. apply Hagree. simpl.
    rewrite elem_of_union_list. exists (fv tt). split; [|exact Hy].
    apply list_elem_of_fmap. exists tt. split; [reflexivity| exact Htt].
  - f_equal. apply IHt. intros y Hy. apply Hagree. exact Hy.
  - f_equal. apply IHt. intros y Hy. apply Hagree. exact Hy.
  - f_equal.
    + apply map_ext_in. intros tt Htt. rewrite <- list_elem_of_In in Htt.
      apply H; auto. intros y Hy. apply Hagree. simpl. apply elem_of_union_r.
      rewrite elem_of_union_list. exists (fv tt). split; [|exact Hy].
      apply list_elem_of_fmap. exists tt. split; [reflexivity| exact Htt].
    + apply IHt. intros y Hy. apply Hagree. simpl. apply elem_of_union_l. exact Hy.
  - f_equal.
    + apply IHt. intros y Hy. apply Hagree. simpl. apply elem_of_union_l. exact Hy.
    + apply map_ext_in. intros pt Hpt. destruct pt as [p_i t_i].
      rewrite <- list_elem_of_In in Hpt. f_equal.
      eapply H; eauto. intros y Hy. apply Hagree. simpl. apply elem_of_union_r.
      rewrite elem_of_union_list. exists (fv t_i). split; [|exact Hy].
      apply list_elem_of_fmap. exists (p_i, t_i). split; [reflexivity| exact Hpt].
Qed.

(** Substitution composition. [term_subst] replaces free variables and
    recurses structurally, with no level to track, so composing two
    substitutions needs no side conditions at all. The union is left-biased:
    variables in [dom θ1] take the composed value, the rest fall through to
    [θ2]. *)
Theorem term_subst_subst : forall (θ1 θ2 : gmap var term) t,
    term_subst θ2 (term_subst θ1 t)
      = term_subst ((term_subst θ2 <$> θ1) ∪ θ2) t.
Proof.
  intros θ1 θ2 t.
  induction t; simpl.
  - destruct (θ1 !! x) as [u|] eqn:H1; simpl.
    + erewrite lookup_union_Some_l; [reflexivity|].
      rewrite lookup_fmap, H1. reflexivity.
    + rewrite lookup_union_r by (rewrite lookup_fmap, H1; reflexivity).
      reflexivity.
  - reflexivity.
  - f_equal. apply IHt.
  - f_equal. rewrite !map_map. apply map_ext_in.
    intros t' Ht'. rewrite <- list_elem_of_In in Ht'. apply H; auto.
  - f_equal. apply IHt.
  - f_equal. apply IHt.
  - f_equal.
    + rewrite !map_map. apply map_ext_in.
      intros t' Ht'. rewrite <- list_elem_of_In in Ht'. apply H; auto.
    + apply IHt.
  - f_equal.
    + apply IHt.
    + rewrite !map_map. apply map_ext_in.
      intros pt Hpt. destruct pt as [p_i t_i].
      rewrite <- list_elem_of_In in Hpt. f_equal. eapply H; eauto.
Qed.

(** When the variables introduced by [θ2] are fresh for [t], nothing survives
    to fall through to [θ2] and the union drops away. *)
Corollary term_subst_subst_fresh : forall (θ1 θ2 : gmap var term) t,
    dom θ2 ## fv t ->
    term_subst θ2 (term_subst θ1 t) = term_subst (term_subst θ2 <$> θ1) t.
Proof.
  intros θ1 θ2 t Hdisj.
  rewrite term_subst_subst. apply term_subst_ext.
  intros x Hx.
  destruct ((term_subst θ2 <$> θ1) !! x) as [u|] eqn:H1.
  - apply lookup_union_Some_l. exact H1.
  - rewrite lookup_union_r by exact H1.
    apply not_elem_of_dom. intros Hd. exact (Hdisj x Hd Hx).
Qed.

(** Renaming [x] to a fresh [w] and then substituting [w] is one substitution
    of [x]. Only the intermediate [w] need be a variable; the final value [u]
    is arbitrary, and [w <> x] is not required, since [w ∉ fv t] already makes
    both sides [t] when they coincide. *)
Corollary term_subst_subst_fresh_singleton :
  forall (x w : var) (u t : term),
    w ∉ fv t ->
    term_subst {[ w := u ]} (term_subst {[ x := TFVar w ]} t)
      = term_subst {[ x := u ]} t.
Proof.
  intros x w u t Hw.
  rewrite term_subst_subst_fresh by (rewrite dom_singleton_L; set_solver).
  rewrite map_fmap_singleton.
  simpl. rewrite lookup_singleton_eq. reflexivity.
Qed.

(** An inserted binding can be peeled off as an outer substitution, provided
    [x] is neither in the domain of [θ] nor free in any of its values. A case
    of [term_subst_subst]: the composed map collapses back to the insert. *)
Corollary term_subst_insert : forall (θ : gmap var term) (x : var) (u t : term),
    x ∉ dom θ ->
    (forall y v, θ !! y = Some v -> x ∉ fv v) ->
    term_subst (<[ x := u ]> θ) t
      = term_subst {[ x := u ]} (term_subst θ t).
Proof.
  intros θ x u t Hdom Hcod.
  apply not_elem_of_dom in Hdom.
  rewrite term_subst_subst. f_equal.
  apply map_eq. intros y. symmetry.
  destruct (decide (y = x)) as [->|Hne].
  - rewrite lookup_insert_eq.
    rewrite lookup_union_r by (rewrite lookup_fmap, Hdom; reflexivity).
    apply lookup_singleton_eq.
  - rewrite lookup_insert_ne by auto.
    destruct (θ !! y) as [v|] eqn:Hy.
    + apply lookup_union_Some_l.
      rewrite lookup_fmap, Hy. simpl. f_equal.
      apply term_subst_fresh. rewrite dom_singleton_L.
      apply disjoint_singleton_l. exact (Hcod y v Hy).
    + rewrite lookup_union_r by (rewrite lookup_fmap, Hy; reflexivity).
      apply lookup_singleton_ne. auto.
Qed.

(** The renaming case: [θ] is the identity-shaped map sending [xs] to [ys]. *)
Corollary term_subst_insert_zip_TFVar :
  forall (x y : var) (xs ys : list var) t,
    x ∉ xs ->
    x ∉ ys ->
    term_subst
      (<[x := TFVar y]>
         (list_to_map (zip xs (map TFVar ys)) : gmap var term)) t =
    term_subst {[x := TFVar y]}
      (term_subst (list_to_map (zip xs (map TFVar ys)) : gmap var term) t).
Proof.
  intros x y xs ys t Hxdom Hxcod.
  apply term_subst_insert.
  - apply not_elem_of_dom.
    destruct ((list_to_map (zip xs (map TFVar ys)) : gmap var term) !! x)
      as [v|] eqn:Hx; [|reflexivity].
    exfalso. apply elem_of_list_to_map_2 in Hx.
    apply elem_of_lookup_zip_with in Hx as (i & a & b & Heq & Hxs & _).
    injection Heq as -> ->. apply Hxdom. apply list_elem_of_lookup. eauto.
  - intros z v Hz. apply elem_of_list_to_map_2 in Hz.
    apply elem_of_lookup_zip_with in Hz as (i & a & b & Heq & _ & Hys).
    injection Heq as -> ->. rewrite list_lookup_fmap in Hys.
    destruct (ys !! i) as [yi|] eqn:Hyi; simpl in Hys; [|discriminate].
    injection Hys as <-. simpl. intros Hin.
    rewrite elem_of_singleton in Hin. subst yi.
    apply Hxcod. apply list_elem_of_lookup. eauto.
Qed.

Theorem fv_term_subst_subseteq :
  forall (m : gmap var term) (V : gset var) (t : term),
    (forall x u, m !! x = Some u -> fv u ⊆ V) ->
    fv (term_subst m t) ⊆ (fv t ∖ dom m) ∪ V.
Proof.
  intros m V t Hbound. induction t using term_ind; simpl.
  - destruct (m !! x) as [u|] eqn:Hx.
    + apply Hbound in Hx. set_solver.
    + apply not_elem_of_dom in Hx. simpl. set_solver.
  - set_solver.
  - exact IHt.
  - (* TApp *) intros y Hy.
    rewrite elem_of_union_list in Hy.
    destruct Hy as (S0 & HS0 & Hy).
    rewrite map_map in HS0.
    rewrite list_elem_of_In in HS0.
    apply in_map_iff in HS0.
    destruct HS0 as (t1 & <- & Ht1).
    rewrite <- list_elem_of_In in Ht1.
    specialize (H _ Ht1 _ Hy).
    rewrite elem_of_union in H. destruct H as [H|H].
    + apply elem_of_union_l.
      rewrite elem_of_difference in H |- *.
      destruct H as [H Hne]. split; [|exact Hne].
      apply elem_of_union_list. exists (fv t1). split; [|exact H].
      rewrite list_elem_of_fmap. exists t1.
      split; [reflexivity|exact Ht1].
    + apply elem_of_union_r. exact H.
  - exact IHt.
  - exact IHt.
  - (* TLet *) intros y Hy.
    rewrite elem_of_union in Hy. destruct Hy as [Hy|Hy].
    + apply IHt in Hy.
      rewrite elem_of_union in Hy. destruct Hy as [Hy|Hy].
      * apply elem_of_union_l.
        rewrite elem_of_difference in Hy |- *.
        destruct Hy as [Hy Hne]. split; auto. set_solver.
      * apply elem_of_union_r. exact Hy.
    + rewrite elem_of_union_list in Hy.
      destruct Hy as (S0 & HS0 & Hy).
      rewrite map_map in HS0.
      rewrite list_elem_of_In in HS0.
      apply in_map_iff in HS0.
      destruct HS0 as (t1 & <- & Ht1).
      rewrite <- list_elem_of_In in Ht1.
      specialize (H _ Ht1 _ Hy).
      rewrite elem_of_union in H. destruct H as [H|H].
      * apply elem_of_union_l.
        rewrite elem_of_difference in H |- *.
        destruct H as [H Hne]. split; auto.
        apply elem_of_union_r.
        apply elem_of_union_list. exists (fv t1). split; [|exact H].
        rewrite list_elem_of_fmap. exists t1.
        split; [reflexivity|exact Ht1].
      * apply elem_of_union_r. exact H.
  - (* TMatch *) intros y Hy.
    rewrite elem_of_union in Hy. destruct Hy as [Hy|Hy].
    + apply IHt in Hy.
      rewrite elem_of_union in Hy. destruct Hy as [Hy|Hy].
      * apply elem_of_union_l.
        rewrite elem_of_difference in Hy |- *.
        destruct Hy as [Hy Hne]. split; auto. set_solver.
      * apply elem_of_union_r. exact Hy.
    + rewrite elem_of_union_list in Hy.
      destruct Hy as (S0 & HS0 & Hy).
      rewrite map_map in HS0.
      rewrite list_elem_of_In in HS0.
      apply in_map_iff in HS0.
      destruct HS0 as ([p1 t1] & <- & Hpt1).
      rewrite <- list_elem_of_In in Hpt1.
      simpl in Hy.
      specialize (H _ _ Hpt1 _ Hy).
      rewrite elem_of_union in H. destruct H as [H|H].
      * apply elem_of_union_l.
        rewrite elem_of_difference in H |- *.
        destruct H as [H Hne]. split; auto.
        apply elem_of_union_r.
        apply elem_of_union_list. exists (fv t1). split; [|exact H].
        rewrite list_elem_of_fmap. exists (p1, t1).
        split; [reflexivity|exact Hpt1].
      * apply elem_of_union_r. exact H.
Qed.

Lemma fv_term_subst_zip_TFVar_subseteq :
  forall (xs ys : list var) t,
    fv (term_subst (list_to_map (zip xs (map TFVar ys)) : gmap var term) t)
      ⊆ fv t ∪ (list_to_set ys : gset var).
Proof.
  intros xs ys t. etrans.
  - apply (fv_term_subst_subseteq _ (list_to_set ys : gset var)).
    intros z u Hu.
    apply elem_of_list_to_map_2 in Hu.
    apply elem_of_lookup_zip_with in Hu as (i & a & b & Heq & _ & Hu).
    injection Heq as -> ->.
    rewrite list_lookup_fmap in Hu.
    destruct (ys !! i) as [yi|] eqn:Hyi; simpl in Hu; [|discriminate].
    injection Hu as <-. simpl. intros q Hq.
    rewrite elem_of_singleton in Hq. subst q.
    rewrite elem_of_list_to_set. apply list_elem_of_lookup. eauto.
  - set_solver.
Qed.

Lemma not_elem_of_fv_term_subst_zip :
  forall (y : var) (xs ys : list var) t (Φ : gset term),
    y ∉ (list_to_set ys : gset var) ->
    y ∉ fv t ∪ set_bind fv Φ ->
    y ∉ fv (term_subst (list_to_map (zip xs (map TFVar ys)) : gmap var term) t)
         ∪ set_bind fv
             (set_map
                (term_subst (list_to_map (zip xs (map TFVar ys)) : gmap var term))
                Φ : gset term).
Proof.
  intros y xs ys t Φ Hy_ys Hy Hin.
  rewrite elem_of_union in Hin. destruct Hin as [Hin | Hin].
  - apply fv_term_subst_zip_TFVar_subseteq in Hin. set_solver.
  - rewrite elem_of_set_bind in Hin. destruct Hin as (ψ & Hψ & Hy_ψ).
    rewrite elem_of_map in Hψ. destruct Hψ as (ϕ & -> & Hϕ).
    apply fv_term_subst_zip_TFVar_subseteq in Hy_ψ.
    rewrite elem_of_union in Hy_ψ. destruct Hy_ψ as [Hy_ψ | Hy_ψ]; [| set_solver].
    apply Hy. apply elem_of_union_r. rewrite elem_of_set_bind.
    exists ϕ. split; assumption.
Qed.

Lemma set_map_term_subst_TFVar_id : forall (x : var) (Φ : gset term),
    set_map (term_subst {[x := TFVar x]}) Φ = Φ.
Proof.
  intros x Φ. apply set_eq. intros ψ.
  rewrite elem_of_map. split.
  - intros (ϕ & -> & Hϕ). rewrite term_subst_id_singleton. exact Hϕ.
  - intros Hψ. exists ψ. rewrite term_subst_id_singleton.
    split; [reflexivity | exact Hψ].
Qed.

Lemma set_map_term_subst_zip_id : forall (xs : list var) (Φ : gset term),
    (set_map (term_subst (list_to_map (zip xs (map TFVar xs)) : gmap var term)) Φ
     : gset term) = Φ.
Proof.
  intros xs Φ. apply set_eq. intros ψ.
  rewrite elem_of_map. split.
  - intros (ϕ & -> & Hϕ). rewrite term_subst_id_zip. exact Hϕ.
  - intros Hψ. exists ψ. rewrite term_subst_id_zip.
    split; [reflexivity | exact Hψ].
Qed.

Lemma set_map_term_subst_insert_zip_TFVar :
  forall (x y : var) (xs ys : list var) (Φ : gset term),
    x ∉ xs ->
    x ∉ ys ->
    (set_map
      (term_subst
         (<[x := TFVar y]>
            (list_to_map (zip xs (map TFVar ys)) : gmap var term))) Φ
     : gset term)
    = set_map (term_subst {[x := TFVar y]})
        (set_map
           (term_subst (list_to_map (zip xs (map TFVar ys)) : gmap var term))
           Φ : gset term).
Proof.
  intros x y xs ys Φ Hx1 Hx2.
  apply set_eq. intros ψ. rewrite !elem_of_map. split.
  - intros (ϕ & -> & Hϕ).
    exists (term_subst (list_to_map (zip xs (map TFVar ys)) : gmap var term) ϕ).
    split.
    + apply term_subst_insert_zip_TFVar; assumption.
    + apply elem_of_map_2. exact Hϕ.
  - intros (ψ' & -> & Hψ'). rewrite elem_of_map in Hψ'.
    destruct Hψ' as (ϕ & -> & Hϕ).
    exists ϕ. split; [| exact Hϕ].
    symmetry. apply term_subst_insert_zip_TFVar; assumption.
Qed.

Corollary fv_term_subst_singleton_TFVar_subseteq :
  forall (x w : var) (t : term),
    fv (term_subst {[ x := TFVar w ]} t) ⊆ (fv t ∖ {[ x ]}) ∪ {[ w ]}.
Proof.
  intros x w t.
  transitivity ((fv t ∖ dom ({[ x := TFVar w ]} : gmap var term)) ∪ {[ w ]}).
  - eapply fv_term_subst_subseteq.
    intros y u Hyu.
    rewrite lookup_singleton_Some in Hyu.
    destruct Hyu as [_ <-]. set_solver.
  - rewrite dom_singleton. reflexivity.
Qed.

(** ** Facts about [lc] *)

(** Opening a locally closed term acts as the identity function. *)
Theorem lc_term_open : forall t,
    lc t ->
    forall k us, term_open k us t = t.
Proof.
  induction 1; intros *; try reflexivity; simpl.
  - rewrite map_ext_in with (g := id).
    { rewrite map_id. reflexivity. }
    intros t Ht.
    apply list_elem_of_In in Ht.
    apply H0; auto.
  - set (x := fresh L).
    assert (Hx: x ∉ L) by apply is_fresh.
    apply H0 with (k := S k) (us := us) in Hx.
    apply term_open_lem in Hx; auto.
    rewrite Hx. reflexivity.
  - set (x := fresh L).
    assert (Hx: x ∉ L) by apply is_fresh.
    apply H0 with (k := S k) (us := us) in Hx.
    apply term_open_lem in Hx; auto.
    rewrite Hx. reflexivity.
  - set (x := fresh L).
    assert (Hx: x ∉ L) by apply is_fresh.
    apply H0 with (k := S k) (us := us) in Hx.
    apply term_open_lem in Hx; auto.
    rewrite Hx. reflexivity.
  - rewrite map_ext_in with (g := id); revgoals.
    { intros t_i Ht_i. simpl.
      rewrite <- list_elem_of_In in Ht_i.
      apply H0; auto. }
    rewrite map_id.
    set (xs := fresh_strings_of_set "" (length ts) L).
    assert (Hxs: list_to_set xs ## L).
    { apply fresh_strings_of_set_fresh. set_solver. }
    eapply H2 with (k := S k) in Hxs; revgoals.
    { subst xs. rewrite length_fresh_strings_of_set.
      reflexivity. }
    apply term_open_lem in Hxs; auto.
    rewrite Hxs. reflexivity.
  - rewrite IHlc.
    rewrite map_ext_in with (g := id).
    { rewrite map_id. reflexivity. }
    intros pt Hpt. destruct pt as [p_i t_i]. simpl.
    rewrite <- list_elem_of_In in Hpt.
    set (xs := fresh_strings_of_set "" (pattern_binders p_i) L).
    assert (Hxs: list_to_set xs ## L).
    { apply fresh_strings_of_set_fresh. set_solver. }
    eapply H1 with (k := S k) in Hxs; eauto; revgoals.
    { subst xs. rewrite length_fresh_strings_of_set. reflexivity. }
    apply term_open_lem in Hxs; auto.
    rewrite Hxs. reflexivity.
Qed.

(** Local closure of an all-[TFVar] opening depends only on how many
    variables are used, not which: opening by free variables merely discharges
    the level-[k] bound variables. *)
Theorem lc_term_open_rename : forall t k xs xs',
    length xs = length xs' ->
    lc (term_open k (map TFVar xs) t) ->
    lc (term_open k (map TFVar xs') t).
Proof.
  intros t k xs xs' Hlen Hlc.
  (* Induct on the [lc] derivation, so its subject must be a variable: hide
     the opening behind [u] and re-equate with [Heq]. Generalising [t], [k]
     and the variable lists keeps the induction hypothesis strong enough to
     push a cofinite level-0 opening under the level-[S k] one. *)
  remember (term_open k (map TFVar xs) t) as u eqn:Heq.
  revert t k xs xs' Hlen Heq.
  induction Hlc; intros t0 k xs xs' Hlen Heq;
    destruct t0; simpl in Heq; try discriminate Heq.
  - (* TFVar / TBVar leaves mapping to TFVar *)
    inversion Heq; subst. apply LCT_TFVar.
  - (* TBVar opened to TFVar at level k *)
    simpl. destruct (decide (i = k)) as [->|HneTBV].
    + destruct (decide (j < length xs)) as [Hlt|Hge].
      * rewrite (nth_indep (map TFVar xs') (TBVar k j) (TFVar ""))
          by (rewrite length_map; lia). rewrite map_nth. apply LCT_TFVar.
      * exfalso. rewrite nth_overflow in Heq by (rewrite length_map; lia).
        inversion Heq.
    + exfalso. inversion Heq.
  - (* A [TApp] subject against a [TBVar] term. Opening a bound
       variable yields a free variable or leaves it bound, never a [TApp]. *)
    case_decide.
    + rewrite nth_lookup, list_lookup_fmap in Heq.
      destruct (xs !! j); discriminate.
    + discriminate.
  - (* TApp *)
    simpl in Heq. inversion Heq; subst. simpl.
    apply LCT_TApp. intros t' Ht'.
    apply list_elem_of_fmap in Ht' as (t_i & -> & Hin).
    assert (Hin' : term_open k (map TFVar xs) t_i
                   ∈ map (term_open k (map TFVar xs)) ts0)
      by (apply list_elem_of_fmap; exists t_i; split; [reflexivity|exact Hin]).
    apply (H0 _ Hin') with (t := t_i) (xs := xs); auto.
  - (* A [TLambda] subject against a [TBVar] term. Opening a bound
       variable yields a free variable or leaves it bound, never a [TLambda]. *)
    case_decide.
    + rewrite nth_lookup, list_lookup_fmap in Heq.
      destruct (xs !! j); discriminate.
    + discriminate.
  - (* TLambda *)
    simpl in Heq. inversion Heq; subst. simpl.
    apply LCT_TLambda with (L := L). intros x Hx.
    change [TFVar x] with (map TFVar [x]).
    rewrite term_open_comm by lia.
    apply (H0 x Hx) with
      (t := term_open 0 (map TFVar [x]) t0) (xs := xs); auto.
    rewrite <- term_open_comm by lia. reflexivity.
  - (* A [TExists] subject against a [TBVar] term. Opening a bound
       variable yields a free variable or leaves it bound, never a [TExists]. *)
    case_decide.
    + rewrite nth_lookup, list_lookup_fmap in Heq.
      destruct (xs !! j); discriminate.
    + discriminate.
  - (* TExists *)
    simpl in Heq. inversion Heq; subst. simpl.
    apply LCT_TExists with (L := L). intros x Hx.
    change [TFVar x] with (map TFVar [x]).
    rewrite term_open_comm by lia.
    apply (H0 x Hx) with
      (t := term_open 0 (map TFVar [x]) t0) (xs := xs); auto.
    rewrite <- term_open_comm by lia. reflexivity.
  - (* A [TForall] subject against a [TBVar] term. Opening a bound
       variable yields a free variable or leaves it bound, never a [TForall]. *)
    case_decide.
    + rewrite nth_lookup, list_lookup_fmap in Heq.
      destruct (xs !! j); discriminate.
    + discriminate.
  - (* TForall *)
    simpl in Heq. inversion Heq; subst. simpl.
    apply LCT_TForall with (L := L). intros x Hx.
    change [TFVar x] with (map TFVar [x]).
    rewrite term_open_comm by lia.
    apply (H0 x Hx) with
      (t := term_open 0 (map TFVar [x]) t0) (xs := xs); auto.
    rewrite <- term_open_comm by lia. reflexivity.
  - (* A [TLet] subject against a [TBVar] term. Opening a bound
       variable yields a free variable or leaves it bound, never a [TLet]. *)
    case_decide.
    + rewrite nth_lookup, list_lookup_fmap in Heq.
      destruct (xs !! j); discriminate.
    + discriminate.
  - (* TLet *)
    simpl in Heq. inversion Heq; subst. simpl.
    apply LCT_TLet with (L := L).
    + intros t' Ht'.
      apply list_elem_of_fmap in Ht' as (t_i & -> & Hin).
      assert (Hin' : term_open k (map TFVar xs) t_i
                     ∈ map (term_open k (map TFVar xs)) binds)
        by (apply list_elem_of_fmap; exists t_i; split; [reflexivity|exact Hin]).
      apply (H0 _ Hin') with (t := t_i) (xs := xs); auto.
    + intros ys Hys Hdisj.
      rewrite length_map in Hys.
      rewrite term_open_comm by lia.
      match goal with
      | [ |- lc (term_open (S k) (map TFVar xs')
                   (term_open 0 (map TFVar ys) ?body)) ] =>
          apply (H2 ys) with
            (t := term_open 0 (map TFVar ys) body) (xs := xs)
      end; auto.
      * rewrite length_map. exact Hys.
      * rewrite <- term_open_comm by lia. reflexivity.
  - (* A [TMatch] subject against a [TBVar] term. Opening a bound
       variable yields a free variable or leaves it bound, never a [TMatch]. *)
    case_decide.
    + rewrite nth_lookup, list_lookup_fmap in Heq.
      destruct (xs !! j); discriminate.
    + discriminate.
  - (* TMatch *)
    simpl in Heq. inversion Heq; subst. simpl.
    apply LCT_TMatch with (L := L).
    + apply IHHlc with (t := t0) (xs := xs); auto.
    + intros p t' ys Hpt' Hys Hdisj.
      apply list_elem_of_fmap in Hpt' as ([p0 t_i] & Heqpt & Hin).
      inversion Heqpt; subst p t'. clear Heqpt.
      rewrite term_open_comm by lia.
      assert (Hmem : (p0, term_open (S k) (map TFVar xs) t_i)
                     ∈ map (fun '(p1, t1) => (p1, term_open (S k) (map TFVar xs) t1)) cases).
      { apply list_elem_of_fmap. exists (p0, t_i).
        split; [reflexivity|exact Hin]. }
      apply (H0 p0 (term_open (S k) (map TFVar xs) t_i) ys Hmem
               Hys Hdisj (term_open 0 (map TFVar ys) t_i) (S k) xs xs' Hlen).
      rewrite term_open_comm by lia. reflexivity.
Qed.

Theorem lc_term_open_term_close : forall t,
    lc t ->
    forall k xs ys,
      length xs = length ys ->
      lc $ term_open k (map TFVar ys) (term_close xs k t).
Proof.
  induction 1; intros * Hlength; simpl.
  - case_match; simpl.
    + destruct p as [j x']; simpl.
      rewrite decide_True; auto.
      rewrite list_find_Some in H.
      destruct H as (Hx & Hx'' & _). subst x'.
      apply mk_is_Some in Hx as Hx'.
      apply lookup_lt_is_Some_1 in Hx'.
      rewrite Hlength in Hx'.
      apply lookup_lt_is_Some_2 in Hx'.
      destruct Hx' as (y & Hy).
      rewrite nth_lookup.
      destruct (map TFVar ys !! j) eqn:Hlook.
      * rewrite list_lookup_fmap_Some in Hlook.
        destruct Hlook as (y' & Ht & Hy'). simplify_eq.
        simpl. constructor.
      * rewrite list_lookup_fmap in Hlook.
        rewrite Hy in Hlook. simpl.
        rewrite fmap_None in Hlook. congruence.
    + constructor.
  - apply LCT_TApp. intros t' Ht'.
    rewrite map_map in Ht'. rewrite list_elem_of_fmap in Ht'.
    destruct Ht' as (t0 & -> & Ht0). apply H0; auto.
  - apply LCT_TLambda with (L := L ∪ list_to_set xs). intros x Hx.
    replace [TFVar x] with (map TFVar [x]) by reflexivity.
    rewrite term_open_comm by lia.
    rewrite term_open_close_comm by (try lia; set_solver).
    apply H0; [ set_solver | exact Hlength ].
  - apply LCT_TExists with (L := L ∪ list_to_set xs). intros x Hx.
    replace [TFVar x] with (map TFVar [x]) by reflexivity.
    rewrite term_open_comm by lia.
    rewrite term_open_close_comm by (try lia; set_solver).
    apply H0; [ set_solver | exact Hlength ].
  - apply LCT_TForall with (L := L ∪ list_to_set xs). intros x Hx.
    replace [TFVar x] with (map TFVar [x]) by reflexivity.
    rewrite term_open_comm by lia.
    rewrite term_open_close_comm by (try lia; set_solver).
    apply H0; [ set_solver | exact Hlength ].
  - apply LCT_TLet with (L := L ∪ list_to_set xs).
    + intros t' Ht'.
      rewrite map_map in Ht'. rewrite list_elem_of_fmap in Ht'.
      destruct Ht' as (t0 & -> & Ht0). apply H0; auto.
    + intros zs Hzs_len Hzs_disj.
      rewrite !length_map in Hzs_len.
      rewrite term_open_comm by lia.
      rewrite term_open_close_comm by (try lia; set_solver).
      apply H2; [ exact Hzs_len | set_solver | exact Hlength ].
  - apply LCT_TMatch with (L := L ∪ list_to_set xs).
    + apply IHlc; auto.
    + intros p t' zs Hmem Hlen Hzs.
      rewrite map_map in Hmem. rewrite list_elem_of_fmap in Hmem.
      destruct Hmem as ([p0 t0] & Heq & Hpt0). simpl in Heq.
      injection Heq as -> ->.
      rewrite term_open_comm by lia.
      rewrite term_open_close_comm by (try lia; set_solver).
      apply H1 with (p := p0); [ exact Hpt0 | exact Hlen | set_solver | exact Hlength ].
Qed.

(** ** Facts about [lc_at] *)

Lemma lc_at_TApp_cons : forall ks f σ t ts,
    lc_at ks (TApp f σ (t :: ts)) <-> lc_at ks t /\ lc_at ks (TApp f σ ts).
Proof.
  split.
  - inversion 1; subst. split.
    + apply H2. apply elem_of_cons. left. reflexivity.
    + apply LCA_TApp. intros t' Ht'. apply H2. apply elem_of_cons. right. exact Ht'.
  - intros [Ht Hts]. inversion Hts; subst. apply LCA_TApp.
    intros t' Ht'. apply elem_of_cons in Ht'. destruct Ht' as [->|Ht']; auto.
Qed.

Lemma lc_at_TLet_cons : forall ks u us t,
    lc_at ks (TLet (u :: us) t) <->
    lc_at ks u /\ lc_at (S (length us) :: ks) t /\
    (forall u', u' ∈ us -> lc_at ks u').
Proof.
  split.
  - inversion 1; subst. split; [|split].
    + apply H3. apply elem_of_cons. left. reflexivity.
    + simpl in H4. exact H4.
    + intros u' Hu'. apply H3. apply elem_of_cons. right. exact Hu'.
  - intros (Hu & Ht & Hus). apply LCA_TLet.
    + intros u' Hu'. apply elem_of_cons in Hu'. destruct Hu' as [->|Hu']; auto.
    + simpl. exact Ht.
Qed.

Lemma lc_at_TMatch_cons : forall ks t p u pts,
    lc_at ks (TMatch t ((p, u) :: pts)) <->
    lc_at (pattern_binders p :: ks) u /\ lc_at ks (TMatch t pts).
Proof.
  split.
  - inversion 1; subst. split.
    + apply (H4 p u). apply elem_of_cons. left. reflexivity.
    + apply LCA_TMatch; [assumption|].
      intros p' u' Hu'. apply H4. apply elem_of_cons. right. exact Hu'.
  - intros [Hu Hrest]. inversion Hrest; subst. apply LCA_TMatch; [assumption|].
    intros p' u' Hu'. apply elem_of_cons in Hu'.
    destruct Hu' as [Heq|Hu'].
    + injection Heq as -> ->. exact Hu.
    + auto.
Qed.

(** Weakening: since [ks] lists the enclosing binders innermost first,
    appending [ks'] on the right adds binders _outside_ the existing ones.
    Every [TBVar i j] in [t] already indexes into [ks], so its index is
    undisturbed and [t] stays locally closed. *)
Theorem lc_at_app_r : forall t ks ks', lc_at ks t -> lc_at (ks ++ ks') t.
Proof.
  induction t using term_ind; intros ks ks' Hlc; inversion Hlc; subst.
  - constructor.
  - apply LCA_TBVar with (a := a); [|assumption].
    rewrite lookup_app_l; [assumption|].
    apply lookup_lt_Some in H2. exact H2.
  - apply LCA_TLambda. apply (IHt (1 :: ks) ks'); auto.
  - apply LCA_TApp. intros t' Ht'. apply H; auto.
  - apply LCA_TExists. apply (IHt (1 :: ks) ks'); auto.
  - apply LCA_TForall. apply (IHt (1 :: ks) ks'); auto.
  - apply LCA_TLet.
    + intros t' Ht'. apply H; auto.
    + apply (IHt (length ts :: ks) ks'); auto.
  - apply LCA_TMatch.
    + apply IHt; auto.
    + intros p t' Ht'. apply (H p t' Ht' (pattern_binders p :: ks) ks'); auto.
Qed.

(** Opening at the outermost level reflects local closure: [t] is closed under
    the enclosing binders [ks] extended by one more of arity [length us] exactly
    when its opening by [us] is closed under [ks] alone.

    The premise is [Forall (lc_at []) us] rather than [Forall (lc_at ks) us]
    because [ks] grows in the binder cases; asking for closure at the empty
    stack keeps the hypothesis usable there. *)
Theorem lc_at_term_open : forall t ks us,
    Forall (lc_at []) us ->
    (lc_at ks (term_open (length ks) us t) <->
     lc_at (ks ++ [length us]) t).
Proof.
  induction t using term_ind; intros ks us Hus; simpl.
  - (* TFVar *) split; intros _; constructor.
  - (* TBVar *)
    case_decide as Hik.
    + subst i. split.
      * intros Hlc.
        apply LCA_TBVar with (a := length us).
        -- rewrite lookup_app_r by lia.
           rewrite Nat.sub_diag. reflexivity.
        -- destruct (decide (j < length us)) as [Hjlt|Hjge]; [exact Hjlt|].
           rewrite nth_overflow in Hlc by lia.
           inversion Hlc; subst.
           exfalso. apply lookup_lt_Some in H2. lia.
      * intros Hlc. inversion Hlc; subst.
        rewrite lookup_app_r in H2 by lia.
        rewrite Nat.sub_diag in H2. simpl in H2. injection H2 as <-.
        rewrite nth_lookup.
        destruct (us !! j) as [u|] eqn:Hu.
        -- rewrite Forall_forall in Hus.
           assert (Hu' : u ∈ us) by (apply list_elem_of_lookup_2 in Hu; exact Hu).
           specialize (Hus u Hu').
           apply (lc_at_app_r u [] ks) in Hus. exact Hus.
        -- apply lookup_ge_None in Hu. lia.
    + split.
      * intros Hlc. inversion Hlc; subst.
        apply LCA_TBVar with (a := a); [|assumption].
        apply lookup_lt_Some in H2 as Hlt.
        rewrite lookup_app_l by lia. exact H2.
      * intros Hlc. inversion Hlc; subst.
        apply lookup_lt_Some in H2 as Hlt.
        rewrite length_app in Hlt. simpl in Hlt.
        apply LCA_TBVar with (a := a); [|assumption].
        rewrite lookup_app_l in H2 by lia. exact H2.
  - (* TLambda *)
    split; inversion 1; subst; constructor;
      change (S (length ks)) with (length (1 :: ks));
      apply (IHt (1 :: ks) us); auto.
  - (* TApp *)
    induction ts as [|t0 ts0 IHts].
    + split; intros _; constructor; intros t' Ht';
        apply elem_of_nil in Ht'; contradiction.
    + simpl. rewrite !lc_at_TApp_cons.
      setoid_rewrite elem_of_cons in H.
      rewrite IHts by (intros; apply H; auto).
      rewrite (H t0) by auto. reflexivity.
  - (* TExists *)
    split; inversion 1; subst; constructor;
      change (S (length ks)) with (length (1 :: ks));
      apply (IHt (1 :: ks) us); auto.
  - (* TForall *)
    split; inversion 1; subst; constructor;
      change (S (length ks)) with (length (1 :: ks));
      apply (IHt (1 :: ks) us); auto.
  - (* TLet *)
    split.
    + inversion 1; subst. apply LCA_TLet.
      * intros t' Ht'.
        apply (H t' Ht' ks us); auto.
        apply H4. apply list_elem_of_fmap.
        exists t'. split; [reflexivity| exact Ht'].
      * rewrite length_map in H5.
        change (S (length ks)) with (length (length ts :: ks)) in H5.
        apply (IHt (length ts :: ks) us) in H5; auto.
    + inversion 1; subst. apply LCA_TLet.
      * intros t' Ht'. rewrite list_elem_of_fmap in Ht'.
        destruct Ht' as (t0 & -> & Ht0).
        apply (H t0 Ht0 ks us); auto.
      * rewrite length_map.
        change (S (length ks)) with (length (length ts :: ks)).
        apply (IHt (length ts :: ks) us); auto.
  - (* TMatch *)
    split; intros Hlc; inversion Hlc; subst.
    + apply LCA_TMatch.
      * apply (IHt ks us); auto.
      * intros p t' Ht'.
        assert (Hin : (p, term_open (S (length ks)) us t')
                       ∈ map (fun '(p0, t0) =>
                            (p0, term_open (S (length ks)) us t0)) pts).
        { rewrite list_elem_of_fmap. exists (p, t').
          split; [reflexivity| exact Ht']. }
        specialize (H4 p _ Hin).
        change (S (length ks)) with (length (pattern_binders p :: ks)) in H4.
        apply (H p t' Ht' (pattern_binders p :: ks) us) in H4; auto.
    + apply LCA_TMatch.
      * apply (IHt ks us); auto.
      * intros p t' Ht'. rewrite list_elem_of_fmap in Ht'.
        destruct Ht' as ([p0 t0] & Heq & Hpt0).
        injection Heq as -> ->.
        change (S (length ks)) with (length (pattern_binders p0 :: ks)).
        apply (H p0 t0 Hpt0 (pattern_binders p0 :: ks) us); auto.
        apply (H4 p0 t0). exact Hpt0.
Qed.

(** The empty-stack case, used in the binder cases of [lc_lc_at]. *)
Corollary lc_at_term_open_nil : forall t us,
    Forall (lc_at []) us ->
    (lc_at [] (term_open 0 us t) <-> lc_at [length us] t).
Proof.
  intros t us Hus.
  apply (lc_at_term_open t [] us). exact Hus.
Qed.

(** Bridge between the cofinite [lc] and the stack-indexed [lc_at]: the two
    agree at the empty stack. The backward direction goes by well-founded
    induction on [term_size], since opening by free variables preserves it. *)
Theorem lc_lc_at : forall t, lc t <-> lc_at [] t.
Proof.
  split.
  (* lc t -> lc_at [] t *)
  - induction 1.
    + constructor.
    + apply LCA_TApp. exact H0.
    + apply LCA_TLambda.
      set (x := fresh L). assert (Hx : x ∉ L) by apply is_fresh.
      specialize (H0 x Hx).
      apply (lc_at_term_open_nil t [TFVar x]) in H0.
      * exact H0.
      * apply Forall_singleton. constructor.
    + apply LCA_TExists.
      set (x := fresh L). assert (Hx : x ∉ L) by apply is_fresh.
      specialize (H0 x Hx).
      apply (lc_at_term_open_nil t [TFVar x]) in H0.
      * exact H0.
      * apply Forall_singleton. constructor.
    + apply LCA_TForall.
      set (x := fresh L). assert (Hx : x ∉ L) by apply is_fresh.
      specialize (H0 x Hx).
      apply (lc_at_term_open_nil t [TFVar x]) in H0.
      * exact H0.
      * apply Forall_singleton. constructor.
    + apply LCA_TLet.
      * exact H0.
      * set (xs := fresh_strings_of_set "" (length ts) L).
        assert (Hxs : list_to_set xs ## L)
          by (apply fresh_strings_of_set_fresh; set_solver).
        assert (Hlen : length xs = length ts)
          by (subst xs; apply length_fresh_strings_of_set).
        specialize (H2 xs Hlen Hxs).
        apply (lc_at_term_open_nil t (map TFVar xs)) in H2.
        -- rewrite length_map in H2. rewrite Hlen in H2. exact H2.
        -- apply Forall_forall. intros u Hu.
           rewrite list_elem_of_fmap in Hu.
           destruct Hu as (y & -> & _). constructor.
    + apply LCA_TMatch.
      * exact IHlc.
      * intros p t' Hpt'.
        set (xs := fresh_strings_of_set "" (pattern_binders p) L).
        assert (Hxs : list_to_set xs ## L)
          by (apply fresh_strings_of_set_fresh; set_solver).
        assert (Hlen : length xs = pattern_binders p)
          by (subst xs; apply length_fresh_strings_of_set).
        specialize (H1 p t' xs Hpt' Hlen Hxs).
        apply (lc_at_term_open_nil t' (map TFVar xs)) in H1.
        -- rewrite length_map in H1. rewrite Hlen in H1. exact H1.
        -- apply Forall_forall. intros u Hu.
           rewrite list_elem_of_fmap in Hu.
           destruct Hu as (y & -> & _). constructor.
  (* lc_at [] t -> lc t *)
  - revert t.
    induction t as [t IH]
      using (well_founded_induction (well_founded_ltof term term_size)).
    intros Hlc. destruct t; inversion Hlc; subst.
    + constructor.
    + (* TBVar: impossible, [] !! i = None *)
      rewrite lookup_nil in H2. discriminate.
    + apply LCT_TApp. intros t' Ht'. apply IH.
      * unfold ltof. simpl. apply term_size_list. exact Ht'.
      * apply H1. exact Ht'.
    + apply LCT_TLambda with (L := ∅). intros x _.
      apply IH.
      * unfold ltof. change [TFVar x] with (map TFVar [x]).
        rewrite term_size_term_open_TFVar. simpl. lia.
      * apply (lc_at_term_open_nil t [TFVar x]).
        -- apply Forall_singleton. constructor.
        -- exact H1.
    + apply LCT_TExists with (L := ∅). intros x _.
      apply IH.
      * unfold ltof. change [TFVar x] with (map TFVar [x]).
        rewrite term_size_term_open_TFVar. simpl. lia.
      * apply (lc_at_term_open_nil t [TFVar x]).
        -- apply Forall_singleton. constructor.
        -- exact H1.
    + apply LCT_TForall with (L := ∅). intros x _.
      apply IH.
      * unfold ltof. change [TFVar x] with (map TFVar [x]).
        rewrite term_size_term_open_TFVar. simpl. lia.
      * apply (lc_at_term_open_nil t [TFVar x]).
        -- apply Forall_singleton. constructor.
        -- exact H1.
    + apply LCT_TLet with (L := ∅).
      * intros u Hu. apply IH.
        -- unfold ltof. simpl. apply term_size_list in Hu. lia.
        -- apply H2. exact Hu.
      * intros xs Hlen _. apply IH.
        -- unfold ltof. rewrite term_size_term_open_TFVar. simpl. lia.
        -- apply (lc_at_term_open_nil t (map TFVar xs)).
           ++ apply Forall_forall. intros u Hu.
              rewrite list_elem_of_fmap in Hu.
              destruct Hu as (y & -> & _). constructor.
           ++ rewrite length_map. rewrite Hlen. exact H3.
    + apply LCT_TMatch with (L := ∅).
      * apply IH.
        -- unfold ltof. simpl. lia.
        -- exact H2.
      * intros p t' xs Hpt' Hlen _. apply IH.
        -- unfold ltof. rewrite term_size_term_open_TFVar.
           apply term_size_cases in Hpt'. simpl. lia.
        -- apply (lc_at_term_open_nil t' (map TFVar xs)).
           ++ apply Forall_forall. intros u Hu.
              rewrite list_elem_of_fmap in Hu.
              destruct Hu as (y & -> & _). constructor.
           ++ rewrite length_map. rewrite Hlen.
              apply (H3 p t'). exact Hpt'.
Qed.

(** Reading a body's local closure back off its opening. The binder rules of
    [term_has_sort] and of [eval] present a body already opened at a run of
    free variables; this is what recovers [lc_at] for the body itself. *)
Corollary lc_at_of_lc_term_open_TFVar : forall t xs,
    lc (term_open 0 (map TFVar xs) t) -> lc_at [length xs] t.
Proof.
  intros t xs Hlc.
  rewrite <- (length_map TFVar xs).
  apply (lc_at_term_open_nil t (map TFVar xs)).
  - apply Forall_forall. intros u Hu.
    rewrite list_elem_of_fmap in Hu. destruct Hu as (y & -> & _). constructor.
  - apply lc_lc_at. exact Hlc.
Qed.

(** Substitution preserves local closure, provided every value of [θ] is
    closed at the empty stack. That is the stable premise: [ks] grows in the
    binder cases, and [lc_at_app_r] lifts [lc_at []] to any [ks]. *)
Theorem lc_at_term_subst : forall (θ : gmap var term) t ks,
    (forall x u, θ !! x = Some u -> lc_at [] u) ->
    lc_at ks t ->
    lc_at ks (term_subst θ t).
Proof.
  intros θ t.
  induction t using term_ind; intros ks Hθ Hlc; simpl.
  - destruct (θ !! x) as [u|] eqn:Hu.
    + apply (lc_at_app_r u [] ks). apply (Hθ x u Hu).
    + constructor.
  - exact Hlc.
  - inversion Hlc; subst. constructor. apply IHt; auto.
  - inversion Hlc; subst. constructor. intros u Hu.
    rewrite list_elem_of_fmap in Hu. destruct Hu as (t0 & -> & Ht0).
    apply H; auto.
  - inversion Hlc; subst. constructor. apply IHt; auto.
  - inversion Hlc; subst. constructor. apply IHt; auto.
  - inversion Hlc; subst. constructor.
    + intros u Hu. rewrite list_elem_of_fmap in Hu.
      destruct Hu as (t0 & -> & Ht0). apply H; auto.
    + rewrite length_map. apply IHt; auto.
  - inversion Hlc; subst. constructor.
    + apply IHt; auto.
    + intros p u Hu. rewrite list_elem_of_fmap in Hu.
      destruct Hu as ([p0 t0] & Heq & Hpt). simpl in Heq.
      injection Heq as -> ->. apply (H p0 t0 Hpt); auto.
Qed.

(** The renaming case: a substitution whose values are all free variables. *)
Corollary lc_at_term_subst_TFVar : forall (θ : gmap var term) t ks,
    (forall x u, θ !! x = Some u -> exists y, u = TFVar y) ->
    lc_at ks t ->
    lc_at ks (term_subst θ t).
Proof.
  intros θ t ks Hθ Hlc. apply lc_at_term_subst; [|exact Hlc].
  intros x u Hu. destruct (Hθ x u Hu) as [y ->]. constructor.
Qed.

Theorem lc_at_term_close :
  forall t (xs : list var) (ks : list nat),
    lc_at ks t ->
    lc_at (ks ++ [length xs]) (term_close xs (length ks) t).
Proof.
  induction t using term_ind; intros xs ks Hlc; simpl.
  - destruct (list_find (fun y => x = y) xs) as [[j y]|] eqn:Hfind.
    + apply list_find_Some in Hfind.
      destruct Hfind as (Hxs & _ & _).
      apply lookup_lt_Some in Hxs.
      apply LCA_TBVar with (a := length xs); [|exact Hxs].
      rewrite lookup_app_r by lia.
      rewrite Nat.sub_diag. reflexivity.
    + apply LCA_TFVar.
  - inversion Hlc; subst. apply LCA_TBVar with (a := a); [|assumption].
    apply lookup_lt_Some in H2 as Hlt.
    rewrite lookup_app_l by lia. assumption.
  - inversion Hlc; subst. apply LCA_TLambda.
    apply (IHt xs (1 :: ks)); auto.
  - inversion Hlc; subst. apply LCA_TApp.
    intros t' Ht'. rewrite list_elem_of_fmap in Ht'.
    destruct Ht' as (t0 & -> & Ht0). apply (H t0 Ht0 xs ks); auto.
  - inversion Hlc; subst. apply LCA_TExists.
    apply (IHt xs (1 :: ks)); auto.
  - inversion Hlc; subst. apply LCA_TForall.
    apply (IHt xs (1 :: ks)); auto.
  - inversion Hlc; subst. apply LCA_TLet.
    + intros t' Ht'. rewrite list_elem_of_fmap in Ht'.
      destruct Ht' as (t0 & -> & Ht0). apply (H t0 Ht0 xs ks); auto.
    + rewrite length_map.
      apply (IHt xs (length ts :: ks)); auto.
  - inversion Hlc as [| | | | | | | ks0 t1 pts0 Hlc_t Hlc_branches];
      subst.
    apply LCA_TMatch.
    + apply (IHt xs ks); auto.
    + intros p t' Ht'. rewrite list_elem_of_fmap in Ht'.
      destruct Ht' as (pt & Heq & Hpt).
      destruct pt as [p0 t0]. simpl in Heq.
      injection Heq as -> ->.
      apply (H p0 t0 Hpt xs (pattern_binders p0 :: ks)); eauto.
Qed.

Corollary lc_at_term_close1 :
  forall (x : var) t,
    lc_at [] t ->
    lc_at [1] (term_close [x] 0 t).
Proof.
  intros x t Hlc.
  apply (lc_at_term_close t [x] []) in Hlc.
  exact Hlc.
Qed.

(** ** Substitution under opening *)

(** Substitution pushes through an opening, carrying [θ] into the
    substituents. The [lc] premise on the values of [θ] is what stops the
    opening from capturing bound variables inside a substituted term. *)
Theorem term_subst_open :
  forall (θ : gmap var term) t k (us : list term),
    (forall x u, θ !! x = Some u -> lc u) ->
    term_subst θ (term_open k us t)
      = term_open k (map (term_subst θ) us) (term_subst θ t).
Proof.
  induction t using term_ind; intros k us Hlc; simpl.
  - (* TFVar *)
    destruct (θ !! x) as [u|] eqn:Hx; simpl.
    + symmetry. apply (lc_term_open u (Hlc x u Hx)).
    + reflexivity.
  - (* TBVar *)
    destruct (decide (i = k)) as [->|Hne]; cycle 1.
    + reflexivity.
    + rewrite !nth_lookup, list_lookup_fmap.
      destruct (us !! j); simpl; reflexivity.
  - (* TLambda *) f_equal. apply IHt; auto.
  - (* TApp *) f_equal. rewrite !map_map. apply map_ext_in.
    intros tt Ht. rewrite <- list_elem_of_In in Ht. apply H; auto.
  - (* TExists *) f_equal. apply IHt; auto.
  - (* TForall *) f_equal. apply IHt; auto.
  - (* TLet *) f_equal.
    + rewrite !map_map. apply map_ext_in.
      intros t' Ht'. rewrite <- list_elem_of_In in Ht'. apply H; auto.
    + apply IHt; auto.
  - (* TMatch *) f_equal.
    + apply IHt; auto.
    + rewrite !map_map. apply map_ext_in.
      intros pt Hpt. destruct pt as [p_i t_i].
      rewrite <- list_elem_of_In in Hpt. f_equal. eapply H; eauto.
Qed.

(** Opening by free variables outside the domain of [θ]: [θ] fixes the
    substituents, so the two operations commute outright. *)
Corollary term_subst_open_TFVar_comm :
  forall (θ : gmap var term) t k (xs : list var),
    (forall x u, θ !! x = Some u -> lc u) ->
    (forall x, x ∈ xs -> θ !! x = None) ->
    term_subst θ (term_open k (map TFVar xs) t)
      = term_open k (map TFVar xs) (term_subst θ t).
Proof.
  intros θ t k xs Hlc Hfresh.
  rewrite term_subst_open by assumption.
  f_equal. rewrite map_map. apply map_ext_in.
  intros x Hx. rewrite <- list_elem_of_In in Hx.
  simpl. rewrite (Hfresh x Hx). reflexivity.
Qed.

(** The renaming case: [θ] is exactly the map sending the opening variables
    [ys] to [xs], so the opening comes out re-indexed by [xs]. Compare
    [term_subst_open_TFVar_comm], where [θ] misses the opening variables
    entirely and slides past unchanged. *)
Corollary term_subst_open_TFVar_rename : forall (ys xs : list var) c k,
    length ys = length xs ->
    NoDup ys ->
    list_to_set ys ## fv c ->
    term_subst (list_to_map (zip ys (map TFVar xs)) : gmap var term)
      (term_open k (map TFVar ys) c)
    = term_open k (map TFVar xs) c.
Proof.
  intros ys xs c k Hlen Hnodup Hdisj.
  rewrite term_subst_open.
  2: { intros z u Hz.
       apply elem_of_list_to_map_2, elem_of_lookup_zip_with in Hz
         as (i & a & b & Heq & _ & Hb).
       injection Heq as -> ->. rewrite list_lookup_fmap in Hb.
       destruct (xs !! i); simpl in Hb; [|discriminate].
       injection Hb as <-. constructor. }
  rewrite term_subst_fresh.
  2: { rewrite dom_list_to_map_L, fst_zip by (rewrite length_map; lia).
       exact Hdisj. }
  f_equal. rewrite map_map. apply list_eq. intros j.
  rewrite !list_lookup_fmap.
  destruct (ys !! j) as [yj|] eqn:Hyj; simpl.
  - assert (Hjlt : j < length xs) by (apply lookup_lt_Some in Hyj; lia).
    assert (Hxj : xs !! j = Some (xs !!! j))
      by (apply list_lookup_lookup_total_lt; lia).
    rewrite Hxj. simpl.
    assert (Hlk : (list_to_map (zip ys (map TFVar xs)) : gmap var term) !! yj
                  = Some (TFVar (xs !!! j))).
    { apply elem_of_list_to_map_1.
      - rewrite fst_zip by (rewrite length_map; lia). exact Hnodup.
      - apply elem_of_lookup_zip_with. exists j, yj, (TFVar (xs !!! j)).
        split; [reflexivity|]. split; [exact Hyj|].
        rewrite list_lookup_fmap, Hxj. reflexivity. }
    rewrite Hlk. reflexivity.
  - assert (Hxn : xs !! j = None).
    { apply lookup_ge_None. apply lookup_ge_None in Hyj. lia. }
    rewrite Hxn. reflexivity.
Qed.

(** Singleton substitution. *)
Corollary term_subst_singleton_open_TFVar_comm :
  forall t k (a : var) (u : term) (xs : list var),
    lc u ->
    a ∉ xs ->
    term_subst {[ a := u ]} (term_open k (map TFVar xs) t)
      = term_open k (map TFVar xs) (term_subst {[ a := u ]} t).
Proof.
  intros t k a u xs Hlc Ha.
  apply term_subst_open_TFVar_comm.
  - intros x u' Hx. rewrite lookup_singleton_Some in Hx.
    destruct Hx as [_ <-]. exact Hlc.
  - intros x Hx. rewrite lookup_singleton_None.
    intros ->. contradiction.
Qed.

(** Singleton substitution, single opening variable. *)
Corollary term_subst_singleton_open_TFVar1_comm :
  forall t k (a : var) (u : term) (y : var),
    lc u ->
    y <> a ->
    term_subst {[ a := u ]} (term_open k [TFVar y] t)
      = term_open k [TFVar y] (term_subst {[ a := u ]} t).
Proof.
  intros t k a u y Hlc Hya.
  change [TFVar y] with (map TFVar [y]).
  apply term_subst_singleton_open_TFVar_comm; [exact Hlc|].
  intros Ha. apply list_elem_of_singleton in Ha. subst. contradiction.
Qed.

(** ** Opening and closing round-trips *)

(** Closing over [xs] and then opening by [us] performs the substitution
    [xs ↦ us] outright. The [lc_at ks] premise is what licenses dropping the
    outer opening from the right-hand side: it says [t] has no bound variables
    of its own at level [length ks], so the only ones the opening can fill are
    those [term_close] has just introduced. *)
Theorem term_open_close_subst :
  forall t (xs : list var) (us : list term) ks,
    length xs = length us ->
    lc_at ks t ->
    term_open (length ks) us (term_close xs (length ks) t)
      = term_subst (list_to_map (zip xs us)) t.
Proof.
  intros t. induction t using term_ind; intros xs us ks Hlen Hlc; simpl.
  - destruct (list_find (fun y => x = y) xs) as [[j w]|] eqn:Hf.
    + simpl. rewrite decide_True by reflexivity.
      pose proof Hf as Hf'. rewrite list_find_Some in Hf'.
      destruct Hf' as (Hxs & _ & _).
      assert (Hjlt : j < length us).
      { rewrite <- Hlen. apply lookup_lt_Some in Hxs. exact Hxs. }
      rewrite (nth_indep us (TBVar (length ks) j) (TFVar x) Hjlt).
      pose proof (list_find_eq_list_to_map_zip xs us x (TFVar x) Hlen) as Heq.
      rewrite Hf in Heq. exact Heq.
    + simpl.
      pose proof (list_find_eq_list_to_map_zip xs us x (TFVar x) Hlen) as Heq.
      rewrite Hf in Heq. exact Heq.
  - inversion Hlc; subst. rewrite decide_False.
    + reflexivity.
    + apply lookup_lt_Some in H2. lia.
  - inversion Hlc; subst. f_equal. apply (IHt xs us (1 :: ks)); auto.
  - inversion Hlc; subst. f_equal. rewrite map_map. apply map_ext_in.
    intros tt Htt. rewrite <- list_elem_of_In in Htt.
    apply (H tt Htt xs us ks); auto.
  - inversion Hlc; subst. f_equal. apply (IHt xs us (1 :: ks)); auto.
  - inversion Hlc; subst. f_equal. apply (IHt xs us (1 :: ks)); auto.
  - inversion Hlc; subst. f_equal.
    + rewrite map_map. apply map_ext_in.
      intros tt Htt. rewrite <- list_elem_of_In in Htt.
      apply (H tt Htt xs us ks); auto.
    + apply (IHt xs us (length ts :: ks)); auto.
  - inversion Hlc; subst. f_equal.
    + apply (IHt xs us ks); auto.
    + rewrite map_map. apply map_ext_in.
      intros pt Hpt. destruct pt as [p_i t_i].
      rewrite <- list_elem_of_In in Hpt. f_equal.
      apply (H p_i t_i Hpt xs us (pattern_binders p_i :: ks)); eauto.
Qed.

(** At the top level, where there are no enclosing binders. *)
Corollary term_open_close_subst_nil :
  forall t (xs : list var) (us : list term),
    length xs = length us ->
    lc_at [] t ->
    term_open 0 us (term_close xs 0 t)
      = term_subst (list_to_map (zip xs us)) t.
Proof. intros t xs us. apply (term_open_close_subst t xs us []). Qed.

(** Closing and reopening a single variable renames it. *)
Corollary term_open_close_subst1 :
  forall t (x x' : var) (ks : list nat),
    lc_at ks t ->
    term_open (length ks) [TFVar x'] (term_close [x] (length ks) t)
      = term_subst {[ x := TFVar x' ]} t.
Proof.
  intros t x x' ks Hlc.
  rewrite (term_open_close_subst t [x] [TFVar x'] ks eq_refl Hlc).
  simpl. rewrite insert_empty. reflexivity.
Qed.

(** Renaming a single variable at the top level. *)
Corollary term_open_close_subst1_nil :
  forall t (x x' : var),
    lc_at [] t ->
    term_open 0 [TFVar x'] (term_close [x] 0 t)
      = term_subst {[ x := TFVar x' ]} t.
Proof. intros t x x'. apply (term_open_close_subst1 t x x' []). Qed.

(** Closing and substituting agree once an opening is applied, with no
    local-closure premise at all: the outer [term_open] fills the [TBVar] that
    [term_close] introduced, arriving at what [term_subst] wrote there
    directly. Compare [term_open_close_subst], which drops the opening from the
    right-hand side but must assume [lc_at] to do so. *)
Theorem term_open_close_as_open_subst :
  forall t x' y' k,
    term_open k [TFVar x'] (term_close [y'] k t) =
    term_open k [TFVar x'] (term_subst {[y' := TFVar x']} t).
Proof.
  intros t. induction t; intros x' y' k; simpl.
  - destruct (decide (x = y')) as [->|Hne].
    + rewrite lookup_singleton_eq.
      simpl.
      destruct (decide (k = k)) as [_|Hbad]; [reflexivity|contradiction].
    + rewrite lookup_singleton_ne by (intros Heq; apply Hne; symmetry; exact Heq).
      simpl.
      reflexivity.
  - reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite !map_map. f_equal.
    apply map_ext_in. intros t Ht. apply H.
    rewrite list_elem_of_In. exact Ht.
  - rewrite IHt. reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite !map_map. f_equal.
    + apply map_ext_in. intros u Hu. apply H.
      rewrite list_elem_of_In. exact Hu.
    + apply IHt.
  - rewrite IHt.
    rewrite !map_map. f_equal.
    apply map_ext_in. intros [p u] Hpt. simpl. f_equal.
    apply (H p u).
    rewrite list_elem_of_In. exact Hpt.
Qed.

(** Reopening under a different name does not bring the closed variable back:
    [term_close] removed every free [y], and the reopening only introduces [x].
    No local-closure premise is needed, since this is a statement about free
    variables only. *)
Corollary not_elem_of_fv_term_open_close1 :
  forall t x y,
    x <> y ->
    y ∉ fv (term_open 0 [TFVar x] (term_close [y] 0 t)).
Proof.
  intros t x y Hxy Hy.
  pose proof (fv_term_open_TFVar1_subseteq (term_close [y] 0 t) 0 x) as Hsub.
  apply Hsub in Hy. clear Hsub.
  rewrite fv_term_close in Hy.
  rewrite elem_of_union in Hy.
  destruct Hy as [Hy|Hy].
  - rewrite elem_of_difference in Hy. destruct Hy as [_ Hy].
    apply Hy. rewrite list_to_set_singleton. apply elem_of_singleton. reflexivity.
  - rewrite elem_of_singleton in Hy. apply Hxy. symmetry. exact Hy.
Qed.

(** Where a reopened free variable came from. If [z] is one of the opening
    variables [ys] and is free in [term_open ys (term_close xs t)], then [z] is
    the [j]th of [ys] for some [j] that [term_close] actually used: [j] is the
    index of the _first_ occurrence of [xs !!! j] in [xs], which is the one
    both [list_find] and [list_to_map] select. This pins down which closed
    variable an occurrence corresponds to, and hence the sort an inverse
    renaming must give it. *)
Theorem fv_term_open_close_image :
  forall t xs ys ks z,
    length xs = length ys ->
    NoDup ys ->
    lc_at ks t ->
    (list_to_set ys : gset var) ## fv t ->
    z ∈ ys ->
    z ∈ fv (term_open (length ks) (map TFVar ys)
              (term_close xs (length ks) t)) ->
    exists j, j < length xs /\ ys !! j = Some z /\
      list_find (fun y => xs !!! j = y) xs = Some (j, xs !!! j).
Proof.
  induction t using term_ind; intros xs ys ks z Hlen Hnodup Hlc Hdisj Hzys Hz; simpl in *.
  - destruct (list_find (fun y => x = y) xs) as [[j w]|] eqn:Hf; simpl in Hz.
    + rewrite decide_True in Hz by reflexivity. rewrite nth_lookup in Hz.
      destruct (map TFVar ys !! j) as [u|] eqn:Hu; simpl in Hz.
      * rewrite list_lookup_fmap in Hu.
        destruct (ys !! j) as [yj|] eqn:Hyj; simpl in Hu; [|discriminate].
        injection Hu as <-. simpl in Hz. rewrite elem_of_singleton in Hz. subst z.
        exists j. assert (Hjlt : j < length xs).
        { rewrite list_find_Some in Hf. destruct Hf as (Hxsj & _).
          apply lookup_lt_Some in Hxsj. exact Hxsj. }
        split; [exact Hjlt|]. split; [exact Hyj|].
        rewrite list_find_Some in Hf. destruct Hf as (Hxsj & <- & Hmin).
        assert (Hxxj : xs !!! j = x) by (apply list_lookup_total_correct; exact Hxsj).
        rewrite Hxxj. rewrite list_find_Some. split; [exact Hxsj|]. split; [reflexivity|].
        exact Hmin.
      * simpl in Hz. rewrite elem_of_empty in Hz. contradiction.
    + simpl in Hz. rewrite elem_of_singleton in Hz. subst z.
      exfalso. apply (Hdisj x); [apply elem_of_list_to_set; exact Hzys| set_solver].
  - inversion Hlc; subst. rewrite decide_False in Hz.
    + simpl in Hz. rewrite elem_of_empty in Hz. contradiction.
    + apply lookup_lt_Some in H2. lia.
  - inversion Hlc; subst. eapply (IHt xs ys (1 :: ks) z); eauto.
  - inversion Hlc; subst.
    rewrite !map_map in Hz.
    apply elem_of_union_list in Hz as (X & HX & HzX).
    apply list_elem_of_fmap in HX as (tt & -> & Htt).
    eapply (H tt Htt xs ys ks z); eauto.
    simpl in Hdisj. intros w Hw Hw'. apply (Hdisj w Hw).
    rewrite elem_of_union_list. exists (fv tt). split; [|exact Hw'].
    apply list_elem_of_fmap. exists tt. split; [reflexivity| exact Htt].
  - inversion Hlc; subst. eapply (IHt xs ys (1 :: ks) z); eauto.
  - inversion Hlc; subst. eapply (IHt xs ys (1 :: ks) z); eauto.
  - inversion Hlc; subst.
    rewrite elem_of_union in Hz. destruct Hz as [Hz | Hz].
    + eapply (IHt xs ys (length ts :: ks) z); eauto. simpl in Hdisj. set_solver.
    + rewrite !map_map in Hz.
      apply elem_of_union_list in Hz as (X & HX & HzX).
      apply list_elem_of_fmap in HX as (tt & -> & Htt).
      eapply (H tt Htt xs ys ks z); eauto.
      simpl in Hdisj. intros w Hw Hw'. apply (Hdisj w Hw). apply elem_of_union_r.
      rewrite elem_of_union_list. exists (fv tt). split; [|exact Hw'].
      apply list_elem_of_fmap. exists tt. split; [reflexivity| exact Htt].
  - inversion Hlc; subst.
    rewrite elem_of_union in Hz. destruct Hz as [Hz | Hz].
    + eapply (IHt xs ys ks z); eauto. simpl in Hdisj. set_solver.
    + rewrite !map_map in Hz.
      apply elem_of_union_list in Hz as (X & HX & HzX).
      apply list_elem_of_fmap in HX as (pt & HXeq & Hpt).
      destruct pt as [p_i t_i]. simpl in HXeq. subst X.
      eapply (H p_i t_i Hpt xs ys (pattern_binders p_i :: ks) z); eauto.
      simpl in Hdisj. intros w Hw Hw'. apply (Hdisj w Hw). apply elem_of_union_r.
      rewrite elem_of_union_list. exists (fv t_i). split; [|exact Hw'].
      apply list_elem_of_fmap. exists (p_i, t_i). split; [reflexivity| exact Hpt].
Qed.

(** At the top level, where there are no enclosing binders. *)
Corollary fv_term_open_close_image_nil :
  forall t xs ys z,
    length xs = length ys ->
    NoDup ys ->
    lc_at [] t ->
    (list_to_set ys : gset var) ## fv t ->
    z ∈ ys ->
    z ∈ fv (term_open 0 (map TFVar ys) (term_close xs 0 t)) ->
    exists j, j < length xs /\ ys !! j = Some z /\
      list_find (fun y => xs !!! j = y) xs = Some (j, xs !!! j).
Proof. intros t xs ys z. apply (fv_term_open_close_image t xs ys []). Qed.

(** * Sort Parameters and Sort Substitution *)

(** The sort parameters a term writes: §5.2.2's [pars(t)], those in a
    binder's sort or in an application's annotation.  A free variable's sort
    lives in the sorting, not in the term, so it does not count. *)
Fixpoint pars (t : term) : gset sortparam :=
  match t with
  | TFVar _ | TBVar _ _ => ∅
  | TApp _ σ ts => from_option sort_params ∅ σ ∪ ⋃ (map pars ts)
  | TLambda σ t | TExists σ t | TForall σ t => sort_params σ ∪ pars t
  | TLet ts t => pars t ∪ ⋃ (map pars ts)
  | TMatch t pts => pars t ∪ ⋃ (map (pars ∘ snd) pts)
  end.

(** Definition 3's application [θ(t)] of a sort substitution to a term: every
    sort the term writes is substituted, and nothing else changes. *)
Fixpoint term_sort_subst (θ : sort_subst_map) (t : term) : term :=
  match t with
  | TFVar x => TFVar x
  | TBVar i j => TBVar i j
  | TApp f σ ts => TApp f (sort_subst θ <$> σ) (map (term_sort_subst θ) ts)
  | TLambda σ t => TLambda (sort_subst θ σ) (term_sort_subst θ t)
  | TExists σ t => TExists (sort_subst θ σ) (term_sort_subst θ t)
  | TForall σ t => TForall (sort_subst θ σ) (term_sort_subst θ t)
  | TLet ts t => TLet (map (term_sort_subst θ) ts) (term_sort_subst θ t)
  | TMatch t pts =>
      TMatch (term_sort_subst θ t)
        (map (fun '(p, t) => (p, term_sort_subst θ t)) pts)
  end.

Theorem term_sort_subst_empty : forall t, term_sort_subst ∅ t = t.
Proof.
  induction t using term_ind; simpl; rewrite ?sort_subst_empty; f_equal;
    try assumption.
  - (* an application's annotation *)
    destruct σ; simpl; [rewrite sort_subst_empty |]; reflexivity.
  - (* an application's arguments *)
    rewrite <- (map_id ts) at 2. apply map_ext_in. intros t Ht.
    apply H. by apply list_elem_of_In.
  - (* a let's bindings *)
    rewrite <- (map_id ts) at 2. apply map_ext_in. intros t' Ht'.
    apply H. by apply list_elem_of_In.
  - (* a match's cases *)
    rewrite <- (map_id pts) at 2. apply map_ext_in. intros [p t'] Hpt.
    simpl. f_equal. apply (H p). by apply list_elem_of_In.
Qed.

(** Opening only replaces bound variables, which write no sort. *)
Lemma pars_subseteq_pars_term_open :
  forall t k us, pars t ⊆ pars (term_open k us t).
Proof.
  (* the variables and the one-body binders go by the induction hypothesis *)
  induction t using term_ind; intros k us; simpl; try set_solver.
  - (* TApp *)
    apply union_mono_l. intros u Hu.
    apply elem_of_union_list in Hu as (X & HX & Hu).
    apply list_elem_of_fmap in HX as (t & -> & Ht).
    apply elem_of_union_list. exists (pars (term_open k us t)). split.
    + rewrite map_map. apply list_elem_of_fmap. by exists t.
    + by apply (H t Ht).
  - (* TLet *)
    apply union_mono; [apply IHt |]. intros u Hu.
    apply elem_of_union_list in Hu as (X & HX & Hu).
    apply list_elem_of_fmap in HX as (t' & -> & Ht').
    apply elem_of_union_list. exists (pars (term_open k us t')). split.
    + rewrite map_map. apply list_elem_of_fmap. by exists t'.
    + by apply (H t' Ht').
  - (* TMatch *)
    apply union_mono; [apply IHt |]. intros u Hu.
    apply elem_of_union_list in Hu as (X & HX & Hu).
    apply list_elem_of_fmap in HX as ([p t'] & -> & Hpt).
    apply elem_of_union_list. exists (pars (term_open (S k) us t')). split.
    + rewrite map_map. apply list_elem_of_fmap. by exists (p, t').
    + by apply (H p t' Hpt).
Qed.
