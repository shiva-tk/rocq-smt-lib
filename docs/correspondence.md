# Correspondence between the standard and our mechanisation

This file gives the correspondence between version 2.7 of the SMT-LIB standard and our mechanisation, section by section of the standard. All references below (sections, definitions, etc.) are references to the standard.

All relevant definitions are from chapter 5, except symbols (§3.1) and identifiers (§3.3), which are defined in chapter 3.

# Correspondence

## 3.1 Lexicon and 3.3 Identifiers

Symbols and identifiers are defined in `Symbols.v`. The rest of chapter 3 is either re-defined in chapter 5 or not relevant.

## 5.1 The language of sorts

**Definition 1** (Sorts) is `sort` in `Symbols.v`. `sort_wf_base` defines membership in $\mathit{Sort}(S, \mathcal{U})$ for a set of sort symbols and arity function; `sort_wf` is the same predicate specialised to a `signature`.

## 5.2 The language of terms

The syntax of terms, defined in Fig. 5.2 (Abstract syntax for unsorted terms), is `term` in `Term.v`. Binders use the locally nameless representation ([Charguéraud, 2012](https://doi.org/10.1007/s10817-011-9225-2)).

### 5.2.1 Signatures

**Definition 2** (SMT-LIB Signature) is `signature` in `Signature.v`. 

One of its ranking conditions differs from the standard's. Ranking condition 4 of Definition 2 compares a constructor's ranks. Transcribed into Rocq, it reads:

```coq
forall c τs τs' τ,
  c ∈ constructors -> rank c τs τ -> rank c τs' τ -> τs = τs'
```

Note 59 in the standard gives the reason for condition 4: a constructor's result sort uniquely determines its argument sorts, so the variables of a match pattern need no sort annotation. Condition 4 does not achieve this once ranks are polymorphic. Consider when $`(c, u\;\delta)`$ is the only rank for constructor $c$, sort parameter $u$ and monomorphic datatype sort $\delta$ in the signature's ranking relation $R$. Condition 4 holds in this case, yet the rank can be instantiated monomorphically to both $`c \, : \, \mathbf{Int} \; \delta \in \Sigma`$ and $`c \, : \, \mathbf{Bool} \; \delta \in \Sigma`$.

The mechanisation therefore states Note 59's property directly, on monomorphic instances, as the field `rank_constructor_args_determined` of `signature`:

```coq
rank_constructor_args_determined :
  forall c σs σs' σ,
    c ∈ constructors ->
    monomorphic_rank_base rank c σs σ ->
    monomorphic_rank_base rank c σs' σ ->
    σs = σs';
```

Here `monomorphic_rank_base rank c σs σ` says that `σs` and `σ` are a monomorphic instance of one of `c`'s ranks. Entry 3 of [the discrepancy list](standard-discrepancies.md#3-ranking-condition-4-does-not-deliver-note-59) sets out the gap in condition 4 against the standard's text.

**Definition 3** (Sort substitution and instance) is in `Symbols.v` for sorts, grouped with the definition of sorts, and is `term_sort_subst` in `Term.v` for terms: the application $\theta(t)$ that substitutes every sort a term writes. Notation 2's judgement $`f \, : \, \sigma_1 \; \cdots \; \sigma_n \; \sigma \in \Sigma`$, that $f$ has a rank of which $`\sigma_1 \cdots \sigma_n \; \sigma`$ is an instance, is `monomorphic_rank` in `Signature.v`, for monomorphic $`\sigma_1, \ldots, \sigma_n, \sigma`$.

**Definition 4** (Signature expansions) is `signature_expansion` in `Signature.v`, clause for clause. It has one clause more, `signature_expansion_constructors`, which Definition 4's clause on selectors and testers presupposes: only a constructor of the larger signature has selectors and a tester there.

* `signature_compose` in `Signature.v`, guarded by `signatures_composable`, is the combination $\Sigma_1 + \Sigma_2$ of §5.4.1, written in our mechanisation with notation `Σ₁ ⊕[ C ] Σ₂` for `C` a proof of composability. Its ranks are exactly the components' ranks, and it is an expansion of both (`signature_compose_signature_expansion_left` and `_right`). `signatures_composable` generalises the standard's compatibility. Compatibility asks for exactly the same sort symbols, constructors, selectors and testers to be defined in both signatures, with the same arities and the same variable sorts. Composability asks only that the two signatures agree on the symbols defined across both signatures. The standard gets that sameness by instantiating every theory declaration at one common signature (§5.4.2, used by §5.5.1), whereas here each component is built over its own sort symbols.
* `extends_rank` is the relation the consumers use, written in our mechanisation with notation `Σ₁ ⊑ Σ₂` in `smt_scope`. It is a *conservative* expansion, one that gives the smaller signature's symbols no new ranks. Definition 4 does not ask for conservativity, but a consumer needs it to evaluate one of a component's symbols in a larger signature: the symbol must have no ranks there that the component's interpretation does not cover. So the composite of two signatures is a rank extension of each part only under `rank_consistent` (`signature_compose_extends_rank_left` and `_right`).

The variable component of Definition 2, a partial mapping from variables to sorts, is `sorts`, a `sorting`: a finite map `gmap var sort`. It is finite where the standard's need not be, since a signature here declares only the free variables of a query, and a query has finitely many. Definition 2 assigns some of the variables a sort in $`\mathit{Sort}(\Sigma^{\mathrm{S}}, \mathcal{U})`$, which may be polymorphic (entry 5 of [the discrepancy list](standard-discrepancies.md#5-variables-with-polymorphic-sorts-have-no-meaning)); here there is no restriction on `signature` which stipulates that a declared variable's sort must be monomorphic and well formed under the signature. Instead, the sorting judgment checks that the sort of a free variable is monomorphic and well formed in the signature (`S_TFVar`). §5.2.2's $\Sigma[x_1{:}\tau_1, \ldots, x_n{:}\tau_n]$ is `m ⊍ Σ` (`signature_add_sorts`) for `m` the map from each $x_i$ to $\tau_i$, and a signature is read and extended at one variable through stdpp's `Lookup` and `Insert` classes, as `Σ !! x` and `<[x := σ]> Σ`.

### 5.2.2 Well-sorted terms

**Definition 5** (Well-sorted Terms) is `term_has_sort` in `Sorting.v`, written `Σ ⊢ t : σ` in `smt_scope`. 

The judgment is monomorphic. A binder's sort must be monomorphic, and an application's rank is a monomorphic instance of one of the symbol's ranks (`monomorphic_rank`), so a term never has a polymorphic sort. A well-sorted term therefore writes no sort parameter: 
its `pars` (the $\mathit{pars}(t)$ set of parameters in term $t$'s binders and annotations from §5.2.2) is empty (`term_has_sort_pars_empty`). A term that does write parameters gets its meaning through its instances instead; see the notes on Definition 11.

**Definition 6** (SMT-LIB formulas) is not represented as a separate type. A formula is a `term` well sorted at `σ_bool`.

## 5.3 Structures and Satisfiability

**Definition 7** (Σ-structure) is `structure` in `Theory.v`. A structure $\mathbf{A}$'s universe $A$ and the subset $\sigma^{\mathbf{A}} \subseteq A$ it assigns to each monomorphic sort $\sigma$ appear together as one sort-indexed family, the field `domain : sort -> Type`. For a structure `A`, `A.(domain) σ` represents the standard's $\sigma^{\mathbf{A}}$, and the structure's universe is implicitly the union of all sort domains.

**Definition 8** (Absolutely free structure), which Definition 9(3) applies to the constructors, is what pins down the domain of a datatype sort (we use $\delta$ here and in the code to distinguish datatype sorts). It asks that the domain of a datatype sort is the term algebra freely generated by the constructors over the domains of the *generator* sorts — the sorts whose elements a term may hold without analysing them further — and that each constructor be interpreted as the term former it names.

The mechanisation names that algebra. `ground_term` is an inductive with two cases: a generator, held opaquely, and a constructor applied to further ground terms. `adt_axioms` then has one field equating each datatype sort's domain with `ground_term` at that sort (`adt_domain`), and one saying that applying a constructor's interpretation builds exactly the ground term its arguments name (`adt_interp_constructor`).

Which sorts are generators is where the mechanisation deliberately departs from the standard, because the standard's choice is circular. Definition 9(3) takes as generators the domains of all the sorts of $\mathit{Sort}(\Sigma)$ that are not datatypes. For every datatype $\delta$, $\delta \boldsymbol{\to} \delta$ is such a sort, since $\boldsymbol{\to}$ belongs to every signature yet is not a datatype sort, so 9(3) makes its domain $(\delta \boldsymbol{\to} \delta)^{\mathbf{A}}$ a generator of the algebra defining $\delta$'s domain $\delta^{\mathbf{A}}$. Simultaneously 9(2) defines $(\delta \boldsymbol{\to} \delta)^{\mathbf{A}}$ as the set of total maps $\delta^{\mathbf{A}} \to \delta^{\mathbf{A}}$. Neither the definition of $\delta^{\mathbf{A}}$ nor of $(\delta \boldsymbol{\to} \delta)^{\mathbf{A}}$ is prior to the other: the definition of one depends on the definition of the other ([discrepancy list](standard-discrepancies.md#7-definition-93-is-circular-as-a-definition), entry 7). A theory can add more of the same: the `Seq` theory fixes the domain of $`\mathbf{Seq}\;\delta`$ to be the sequences over $\delta$'s. 

The circle does not make Definition 9 inconsistent. A datatype's domain depends only on the generators at the sorts its constructors' fields actually have. For example, if no constructor has a field of sort $\delta \boldsymbol{\to} \delta$, then the above circle is broken. So where §4.2.3(iv) and declaration order keep $\delta$ out of those sorts below their top symbol, a structure satisfying 9(2) and 9(3) exists. 

What the circle does is stop 9(3) being a definition. It is a condition that a structure built some other way can be checked against: build $\delta$'s domain from the generators at the sorts its constructors' fields have, then check that the remaining generators, $\delta \boldsymbol{\to} \delta$'s among them, add no ground terms of sort $\delta$. That check does not carry over to Rocq. A domain equation such as `adt_domain` is an equality of types, and the type `ground_term` builds depends on the generator family at every generator sort, whether or not a constructor field reaches it. Ground terms over two families that differ only at sorts no field reaches are isomorphic types, not equal ones. So under 9(3) the domains cannot be built in two passes, as `Domain.v` builds them, because the first pass would have to supply $\delta \boldsymbol{\to} \delta$'s domain before $\delta$'s exists.

Taking instead the sorts that mention no datatype anywhere breaks the circle, at a price: it also drops generators the standard's algebra uses. §4.2.3(iv) forbids burying a datatype under another sort constructor only within the datatype's own `declare-datatypes` group, so a later group may bury an earlier datatype. Two examples recur below. In the first, a cache is either cold, or warm with a lookup from keys to cached values, and $\mathbf{Option}$ is declared in an earlier group than $\mathbf{Cache}$:

```smt2
(declare-datatypes ((Option 0)) (((none) (some (val Int)))))
(declare-datatypes ((Cache 0)) (((cold) (warm (lookup (-> Int Option))))))
```

$\mathrm{warm}$'s field buries $\mathbf{Option}$ under $\boldsymbol{\to}$, and keeps to (iv) because the two datatypes are declared by separate `declare-datatypes` commands, so are in different groups. 9(3) makes $\mathbf{Int} \boldsymbol{\to} \mathbf{Option}$ a generator, and `adt_free` does not, so here $\mathrm{warm}$ builds no ground terms. In the second, a tree is a leaf, or a node with any number of subtrees:

```smt2
(declare-datatypes ((Tree 0)) (((leaf) (node (children (Seq Tree))))))
```

$\mathrm{node}$'s field buries $\mathbf{Tree}$ under $\mathbf{Seq}$ within its own group, which breaks (iv), though solvers accept it (see ["Datatypes nested under `Seq`"](#datatypes-nested-under-seq)).

The two readings give every datatype the same ground terms exactly when no constructor field buries a datatype (`constructor_args_embeddable`). What the difference costs is in the notes on Definition 9 below.

**Definition 9** (SMT-LIB Σ-structure) is distributed as follows:

* the Bool and map-sort requirements, 9(1) and 9(2), are fields of `structure`, namely `domain_σ_bool` and `domain_σ_map`;
* the ADT requirement, 9(3), is `adt_domain` and `adt_interp_constructor`, with the generators read as in the notes on Definition 8 above. `adt_interp_constructor` says that applying a constructor's interpretation to some arguments gives the ground term built from those arguments. To build that term, each argument, a domain element, has to become a ground term of its sort. That is possible exactly at the sorts `embeddable_sort` admits:

  ```coq
  Definition embeddable_sort (Σ : signature) (τ : sort) : Prop :=
    adt Σ τ \/ adt_free Σ τ.
  ```

  At a datatype sort the element already is a ground term, by `adt_domain`. At a datatype-free sort it becomes a generator. The condition is therefore stated only at the constructor ranks whose argument sorts are all embeddable. A field that buries a datatype under another sort constructor is neither: $\mathbf{Int} \boldsymbol{\to} \mathbf{Option}$ is not a datatype sort, but it mentions one. That holds whether the field keeps to §4.2.3(iv), as $\mathrm{warm}$'s does, or breaks it, as $\mathrm{node}$'s does. Such a constructor is left *uninterpreted* rather than modelless: it must still denote some function into its datatype's domain, but the mechanisation constrains nothing about which. This is the one point at which the mechanisation constrains less than the standard. `Theory/Seq.v` reads the same requirement through sequences, and so does constrain $\mathrm{node}$; see ["Datatypes nested under `Seq`"](#datatypes-nested-under-seq);
* the selector and tester requirements, 9(4) and 9(5), are `adt_interp_selector` and `adt_interp_tester`.

Rather than packaging all of Definition 9 into one large record, the mechanisation keeps the core structure record small and adds `adt_axioms Σ A` to the model predicate, imposing Definition 9(3)–(5), with the generators and constructor ranks read as above. It is added once, at the finished signature, by `theory_init`, or by `theory_init_seq` for the extension that datatypes nested under `Seq` need — see the notes on Definition 13 and ["Datatypes nested under `Seq`"](#datatypes-nested-under-seq).

**Definition 10** (Isomorphism) is not mechanised: Definition 13 combines theories up to isomorphism, but the mechanisation's combination does not need it. See the notes on Definition 13.

### 5.3.1 The meaning of terms

**Definition 11** (Interpretation of terms) is `eval` in `Eval.v`. It is indexed by the structure and the valuation, as $`[\![t]\!]^{\mathcal{I}}`$ is by $\mathcal{I} = (\mathbf{A}, v)$, and a variable's sort is read from the valuation. A `valuation` is partial, as §5.3.1's valuations are, and also finite. A variable it leaves undefined evaluates to nothing, as Definition 11's rule 2 gives it no value either. The condition that rule 2 needs at every declared variable is `valuation_well_sorted Σ.(sorts) V`: `V` is defined, at the declared sort, at every variable the signature `Σ` declares. `eval_total` proves that every well-sorted term evaluates under such a valuation. See further discussion in entry 1 of [the discrepancy list](standard-discrepancies.md#1-valuations-are-partial-but-definition-11-is-claimed-total).

Rule 1 of Definition 11, the one rule for terms writing sort parameters, is `holds` in `Eval.v`: a formula holds when every instance `term_sort_subst θ ϕ` evaluates to true, for `θ` assigning a monomorphic sort of the signature to each parameter in `pars ϕ` (`monomorphic_sort_subst`). A parameter-free formula is its own only instance, so for it `holds` is evaluation to true (`holds_iff_eval`). The standard also asks the formula itself to be well sorted at $\mathbf{Bool}$, under the sorting rules read at polymorphic sorts. Here an instance that is not well sorted has no value, so a formula holds only if every instance is well sorted, which is `polymorphic_term_has_sort` in `Sorting.v`, written `Σ ⊢p t : σ` in `smt_scope`.

One deviation is in how a valuation is keyed. A valuation maps each variable to a sort and a value of that sort, rather than mapping variable–sort pairs to values. The two agree on everything a term can observe: restricted to the variable-sort pairs a signature's sorting declares, the standard's valuations and these are in bijection. Storing the sort with the value makes a valuation a single finite map with ordinary equality, makes a binder's shadowing an overwrite, and lets evaluation read a variable's sort from the valuation, rather than from the interpretation's signature as Definition 11's rule 2 does.

Rule 9 is read with each selector sort-annotated, $g_i^{\sigma_i}$ (in concrete syntax, `(as g_i σ_i)`), for $\sigma_i$ the constructor's $i$-th argument sort at the scrutinee's sort, which `rank_constructor_args_determined` makes unique; a $\mathbf{match}$ then has exactly one value even where a selector is overloaded, and a pattern must bind exactly as many variables as the constructor has arguments. Entry 2 of [the discrepancy list](standard-discrepancies.md#2-rule-9-does-not-determine-a-value-for-match-reported-to-the-maintainers) says why the standard's rule gives it none.

## 5.4 Theories

**Definition 12** (Theory) is `theory` in `Theory.v`: a signature together with a class of structures satisfying the theory's model predicate. A theory is built from a `pretheory`, the same pair minus the datatype condition; see the notes on Definition 13.

See also the theories we have mechanised in the directory `Theory`.

### 5.4.1 Combined Theories

**Definition 13** (Theory Combination) is represented by `pretheory_compose` in `Theory.v`. The standard defines combination up to isomorphism: $\mathcal{T}_1 + \mathcal{T}_2$ consists of all $(\Sigma_1 + \Sigma_2)$-structures whose reduct to $\Sigma_i$ is isomorphic to a model of $\mathcal{T}_i$, for $i = 1, 2$. The mechanisation's combination is a conjunction of the two model predicates over one shared structure:

```coq
Definition pretheory_compose (pT1 pT2 : pretheory)
  (C : pretheories_composable pT1 pT2) : pretheory :=
  {| pΣ := pT1.(pΣ) ⊕[ C.(ptc_signatures_composable) ] pT2.(pΣ);
     pmodels A := pT1.(pmodels) A /\ pT2.(pmodels) A |}.
```

There is no isomorphism. The interpreted theories fix their domains to the Rocq types they mean, so there is no second presentation of a model for an isomorphism to identify, and proofs can use the ordinary computational meaning of these types directly:

| Sort | Domain |
|---|---|
| $\mathbf{Bool}$ | `bool` |
| $\mathbf{Int}$ | `Z` |
| $\mathbf{Real}$ | `R` |
| $\mathbf{String}$ | `string` |
| $`\mathbf{Seq}\,\sigma`$ | `list` over $\sigma$'s domain |
| a datatype $\delta$ | its ground terms |

Combination is an operation on `pretheory`, not on `theory`. A component is a `pretheory`, a signature and a model predicate with no datatype condition, and `theory_init` closes a finished composition into a `theory` by conjoining `adt_axioms` at the signature reached:

```coq
Definition theory_init (pT : pretheory) : theory :=
  {| Σ := pT.(pΣ);
     models A := pT.(pmodels) A /\ adt_axioms (Σ := pT.(pΣ)) A |}.
```

`tests/TestTheory.v` builds its test theory this way, composing first and closing once, with `C_arith` and `C_test` the composability proofs:

```coq
Definition T_arith : pretheory := T_core ⊕[ C_arith ] T_reals_ints.
Definition T_test  : theory    := theory_init (T_arith ⊕[ C_test ] T_uninterp).
```

The datatype condition waits for the finished signature because it is a condition on the *combined* structure. `ground_term Σ` is indexed by `Σ`, so asserting the domain equation at a component's own signature constrains a different type from the one the combined signature is about, with no transport between them. Since `⊕` takes pretheories and `theory_init` returns a `theory`, composing after closing does not typecheck, which is the point of the split. A composition with datatypes nested under `Seq` closes with `theory_init_seq` instead; see ["Datatypes nested under `Seq`"](#datatypes-nested-under-seq).

**Definition 14** (Satisfiability and Entailment Modulo a Theory) is `sat` and `entails` in `Eval.v`; `entails T Γ ϕ` is written `Γ ⊨[ T ] ϕ` in `smt_scope`. Both are stated with `holds`, under which a formula writing sort parameters stands for all its instances. On parameter-free formulae, which include the well-sorted ones, `holds` is evaluation to true, so `sat` and `entails` agree with `monomorphic_sat` and `monomorphic_entails` (`sat_iff_monomorphic_sat`, `entails_iff_monomorphic_entails`). Both depart from the standard in two ways:

* *Finite sets, not single sentences.* `sat` takes a finite set of formulae, satisfied together, where the standard takes one sentence. `entails` takes a finite set of premises `Γ`, where the standard allows any set.
* *Valuations.* Terms here may have free variables, where the standard's are sentences, so each model is paired with a valuation: `sat` asks for some model `A` and valuation `V`, and `entails` quantifies over all of them. Both range over valuations well sorted for `Σ.(sorts)`, which is the only place the signature's variable sorts enter.

Validity, which §2.1 describes as being satisfied by every model of the theory, is the `Γ = ∅` case of `entails`; Definition 14 does not define it separately, and neither does the mechanisation.

For a parameter-free `ϕ`, `entails T Γ ϕ` and `~ sat T ({[not_ ϕ]} ∪ Γ)` are equivalent in the standard's classical reading but are not interchangeable here. The first gives the second by `eval_not` and `eval_deterministic`; the converse needs `ϕ` to evaluate to something at all, which is `eval_total`: that needs `ϕ` well sorted, beyond the well-sorted valuation `entails` supplies, and is classical (see the notes on Definition 11). `entails_sat` and `not_sat_not_entails` relate the two notions relative to `Γ` being satisfiable, `sat T ∅` being the case that says `T` has a model. For a `ϕ` writing sort parameters the two are not equivalent even classically, in the standard or here, which contradicts the standard's §2.1 claim that validity reduces to unsatisfiability of the negation for any class of formulae closed under negation ([discrepancy list](standard-discrepancies.md#15-validity-does-not-reduce-to-unsatisfiability-with-sort-parameters), entry 15). Asserting `not_ ϕ` asserts every instance of `not_ ϕ`, which is not the negation of asserting every instance of `ϕ`. "Every sort has at most two elements" is neither valid nor refuted, because its instance at $\mathbf{Int}$ is false while its negation's instance at $\mathbf{Bool}$ is false too (`not_valid_at_most_two` and `not_sat_not_at_most_two` in `tests/UnitTests.v`).

### 5.4.2 Theory declarations

Theory declarations (Fig. 5.4) are not mechanised as syntax. The theories they declare are written directly as `pretheory` values in the `Theory/` directory.

## 5.5 Logics

Logics are out of scope of the mechanisation.

# Extensions

We only have one extension.

## Datatypes nested under `Seq`

SMT-LIB (§4.2.3, restriction (iv)) lets a datatype's field have that same datatype as its sort, but not bury it inside another sort constructor. $\mathbf{Tree}$ from [the notes on Definition 8](#53-structures-and-satisfiability) breaks it, since $\mathrm{node}$'s field has sort $`\mathbf{Seq}\,\mathbf{Tree}`$. Giving $\mathrm{node}$ two fields of sort $\mathbf{Tree}$ instead, for a binary tree, would keep to it.

z3 nonetheless accepts the nesting and returns models for it (see below), so the mechanisation extends the standard to give such datatypes a meaning too. To nest a datatype under $\mathbf{Seq}$, close the theory with `theory_init_seq` instead of `theory_init` (see [the notes on Definition 13](#541-combined-theories)). Under `theory_init`, a constructor whose field nests a datatype under $\mathbf{Seq}$, such as $\mathrm{node}$, is left uninterpreted. Under `theory_init_seq`, it is interpreted as the term former it names, like any other constructor.

The difference is the term algebra each conjoins. `theory_init` conjoins `adt_axioms`, whose `ground_term` is the standard's reading: a term is a constructor applied to further terms, and anything at a generator sort is an opaque leaf. `theory_init_seq` conjoins `Theory/Seq.v`'s `seq_adt_axioms`, whose `seq_ground_term` has one extra case: a term at a sequence sort is a list of further terms. Both are ordinary Rocq inductives, so either way a datatype domain is still a well-founded set of finite terms, which is what Definition 8 asks for.

The extension is the solvers' own: they do not enforce restriction (iv) either. z3 4.15.4 and cvc5 1.3.4 and 1.4.1 all accept this declaration, though it puts `D1` under `Seq` in a field of `D2`, in the same group:

```smt2
(declare-datatypes ((D1 0) (D2 0))
  (((a) (b (gb Int)))
   ((c (gc (Seq D1))))))
```

What cvc5 rejects is a datatype that recurses through another sort constructor:

```smt2
(declare-datatypes ((D 0)) (((leaf) (node (kids (Seq D))))))
```

It reports `Cannot handle nested-recursive datatype D`, and does the same for `Array Int D`, `Set D`, or a parametric datatype applied to `D`. However, cvc5 does implement the nesting, behind the expert option `--dt-nested-rec`: with it, cvc5 accepts `D` and returns models for it. z3 accepts `D` by default, and returns models for it. Both solvers thus support the nesting, as an extension the standard does not describe. Entries 9 and 10 of [the discrepancy list](standard-discrepancies.md#9-neither-z3-nor-cvc5-enforces-restriction-iv) tabulate both solvers' answers across nestings, and say which nestings no semantics can admit.

`Theory/Seq.v` is already not a standard SMT-LIB theory — it is mechanised from the z3 and cvc5 documentation — so the extension sits with the rest of the non-standard material, and a theory must ask for it by name. Nor does `signature` enforce restriction (iv), and it could not faithfully do so: the restriction constrains the datatypes of a single `declare-datatypes` group, and `signature` records no declaration groups.

# Design choices

The mechanisation follows the standard closely, while using a few choices that are natural in Rocq:

* A signature declares finitely many variables, as every script does, so a sorting is a finite map.
* The sorting judgment is monomorphic, and a formula writing sort parameters is given meaning through its instances, each checked by that judgment, rather than by a sorting judgment at polymorphic sorts (see the notes on [Definition 5](#522-well-sorted-terms) and [Definition 11](#531-the-meaning-of-terms)). The meaning is the standard's, and the reading of well-sortedness is the one the script in §3.6.1 uses.
* The universe of a structure is represented as a sort-indexed family `domain : sort -> Type`. This is the usual type-theoretic presentation of many-sorted semantics: each sort has its own domain, and in Rocq this is naturally written as a family of types indexed by sort codes. This is closely related to the Tarski-style [universe design pattern](https://leanprover.github.io/functional_programming_in_lean/dependent-types/universe-pattern.html) of using codes together with a decoding function.
* The generators of a datatype's free algebra are the domains of the datatype-free sorts, rather than of every non-datatype sort as in Definition 9(3), which is circular for every datatype $\delta$, at $\delta \boldsymbol{\to} \delta$ (see [the notes on Definition 8](#53-structures-and-satisfiability)). The two agree wherever no constructor field buries a datatype under another sort constructor, which §4.2.3(iv) guarantees only within a declaration group. Where they differ, the mechanisation leaves a constructor at an offending field uninterpreted, its selectors included, rather than ruling the theory out; the alternatives were to make such theories modelless, or to give the offending sort a trivial generator, which would silently identify distinct values. `Theory/Seq.v` constrains one shape of nesting beyond this, a datatype nested under `Seq` (see [Datatypes nested under `Seq`](#datatypes-nested-under-seq)). A general treatment — a theory registering the sort constructors a datatype may nest under, so that any strictly positive nesting is constrained — is not implemented.
* A valuation stores each variable's sort with its value, rather than being keyed on variable–sort pairs (see [the notes on Definition 11](#531-the-meaning-of-terms)).
* Interpreted sorts use canonical domains, which keeps domains connected to the intended computational types.
* Theory combination uses a shared structure rather than explicit reducts up to isomorphism; for the canonical domains used here, this is the direct form of the same combined-model requirement.
