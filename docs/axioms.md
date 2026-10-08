# Axioms

This formalisation is not designed to be constructive, but it is conservative about where it is not. SMT-LIB is a classical logic: a structure gives every formula one of two truth values, and $\mathbf{Bool}$ is an ordinary sort whose domain is that two-element type. Rocq's logic is constructive, so mechanising that semantics means supplying classical strength rather than deriving it. Most of the theory uses no axioms at all; what does has six sources, plus what the tests add on their own account. Each source is listed below, with the constants that use it and why.

* **Map sorts and the lambda binder.** A structure's `domain_σ_map` makes the domain at `τ_map σ1 σ2` Rocq's own function type `domain σ1 -> domain σ2`. Three steps then need axioms.

  * *Constructing a model of Core.* `models_f_eq` constrains `f_eq` at every sort, so every model of Core must decide equality on every domain — the map sorts included, where no term decides equality on Rocq functions. `core_interp` therefore uses `excluded_middle_informative`, that is `classic` with `constructive_indefinite_description`. It is built over an arbitrary domain family, where nothing is decidable at any sort, but a concrete family would still not escape the map-sort case. `seq_interp` decides `infix` the same way.

  * *Proving evaluation deterministic.* `eval_deterministic`'s lambda case has two values at a map sort that agree pointwise, and they are literal Rocq functions, so it uses `functional_extensionality_dep`.

  * *Proving evaluation total.* `eval_total`'s lambda case must exhibit a Rocq function, assembling one body value per argument, which is choice: `constructive_indefinite_description`.

  `excluded_middle_informative` is not merely a convenience — being inconsistent with Church's thesis, it stops a model reading `->` as the computable function space.

* **Quantifiers over an arbitrary domain.** Whether $`\exists\,(x{:}\sigma)\; t`$ denotes true is whether some witness satisfies the body, and no structural recursion answers that, so `eval_total`'s quantifier cases use `classic`, and only `classic`: the witness goes into the proof, not into the value, and reaching it costs no choice.

* **Classifying entailment.** `entails_trichotomy` applies `classic` to `entails T Γ ϕ` and `sat T ({[ ϕ ]} ∪ Γ)` themselves, to know that a formula falls into one of its three cases. It needs nothing about whether the formula evaluates.

* **Stdlib's `R`.** `Rdefinitions` builds `R` from `ClassicalDedekindReals`, whose `sig_forall_dec` is an axiom, so every fact about the reals carries it and `functional_extensionality_dep`. `Theory/Reals_Ints.v` pins the Real domain to `R`, and `tests/TestTheory.v` does the same through `test_base`. It makes a useful marker: a constant carrying funext without it traces to another source.

* **Generator families.** `Domain.v`'s `sort_domain_adt` equates two generator families that agree pointwise, and needs `functional_extensionality_dep`.

* **Datatypes nested under `Seq`.** `Theory/Seq.v`'s `seq_constructor_interp` interprets a constructor as its term former only at the ranks it can build a term at, and decides which those are with `excluded_middle_informative`. `seq_constructor_interp_apply` then reconciles the proofs that decision returns with the ones a caller supplies, using proof irrelevance derived from `classic`.

* **The tests.** `A_free_models_reals_ints` reconciles two proofs of the same domain equation with proof irrelevance derived from `classic`. `valid_fun_ext` and `valid_ho_ext` prove two lambdas equal outright, which is the first source's funext again; `base_interp` and `div_by_zero` decide with `excluded_middle_informative` where a `Decision` instance would serve, and `eval_at_most_two_body` decides equality at an arbitrary sort with `classic`.
