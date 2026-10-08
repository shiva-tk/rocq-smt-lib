# Discrepancies with the SMT-LIB standard

Problems found, mostly in chapter 5, in *SMT-LIB 2.7*, release 2026-09-09
(<https://smt-lib.org/papers/smt-lib-reference-v2.7-r2026-09-09.pdf>), while
mechanising it in Rocq. The only change from the 2026-03-27 release is
syntactic sugar for applying a monomorphic map, which no entry concerns. Each
entry quotes the text at issue, says what goes wrong,
and suggests a fix; a last line says what the mechanisation does, which
[`correspondence.md`](correspondence.md) describes in full.

Entries 1 to 8 are defects. Entries 9 and 10 are observations about
restriction (iv) of §4.2.3 rather than defects. Entries 11 to 16 are minor
corrections.

## Valuations and totality

### 1. Valuations are partial, but Definition 11 is claimed total

§5.3.1 defines valuations as partial:

> A valuation into a $`\Sigma`$-structure $`\mathbf{A}`$ is a *partial* mapping
> $`v`$ from $`\mathcal{X} \times \mathit{Sort}(\Sigma)`$ to the set of all
> domain elements of $`\mathbf{A}`$ …

and then, before Definition 11, claims that

> A $`\Sigma`$-interpretation $`\mathcal{I}`$ assigns a meaning to well-sorted
> $`\Sigma`$-terms by means of a uniquely determined *(total)* mapping
> $`[\![\cdot]\!]^{\mathcal{I}}`$ …

**Problem.** Nothing requires $`v`$ to be defined at the variables $`\Sigma`$
declares. If $`x{:}\sigma \in \Sigma`$ but $`v(x{:}\sigma)`$ is undefined, then
$`x`$ is well sorted and Definition 11's rule 2 (variables) gives it no value,
so the claim is false for open terms.

The claim after Definition 11, that $`[\![\cdot]\!]^{\mathcal{I}}`$ "is
well-defined, and hence total, over *closed* terms", is true: a binder's rule
extends the valuation at exactly the variable it binds. But it cannot be proved
without the open case, since Definition 11's rules 4–7, and rules 9 and 11
through $`\mathbf{let}`$, descend through binders into open terms, and the open
case needs the missing premise.

**Suggested fix.** This could be explicitly clarified. 
Call $`v`$ *well sorted* for $`\Sigma`$ when $`v(x{:}\sigma)`$
is defined for every $`x{:}\sigma \in \Sigma`$. State the totality claim for
interpretations whose valuation is well sorted, and derive the closed-term claim
from it.

**In the mechanisation.** Valuations are partial, and being well sorted is a
premise of totality and determinism of evaluation.

## Ranks of constructors and selectors

### 2. Rule 9 does not determine a value for `match` (reported to the maintainers)

Definition 11, rule 9:

> 9. $`[\![\mathbf{match}\ t\ \mathbf{with}\ (c\,x_1 \cdots x_{k+1}) \to t_0\ \ p_1 \to t_1 \cdots p_n \to t_n]\!]^{\mathcal{I}} = [\![\mathbf{let}\ x_1 = g_1(t) \cdots x_{k+1} = g_{k+1}(t)\ \mathbf{in}\ t_0]\!]^{\mathcal{I}}`$
>
>    if … $`[\![t]\!]^{\mathcal{I}}`$ is in the range of $`c^{\mathbf{A}}`$, and
>    $`\mathrm{sel}_\Sigma(c) = g_1 \cdots g_{k+1}`$

**Problem.** Definition 2 does not stop a selector from being overloaded. If
$`g_i`$ has two ranks at the datatype sort, the unannotated $`g_i(t)`$ is ill
sorted, so the right-hand side of rule 9 is outside the domain of
$`[\![\cdot]\!]^{\mathcal{I}}`$. The desugaring (3.7) in §3.6.1 has the same
problem with its unqualified selectors and testers.

Scripts do not reach the case in 2.7: selectors are fresh (§4.2.3) and
user-declared symbols cannot be overloaded (§4.1.5). But chapter 5 does not
distinguish user-declared from theory-declared symbols, and Remark 18 says only
that every script gives a Definition 2 signature, not that every Definition 2
signature comes from a script.

**The maintainers' reply** was that constructors cannot be overloaded in 2.7,
that 3.0 will allow overloading user-declared symbols but not constructors, and
a proposal to amend condition 1 on the ranking relation $`R`$ in Definition 2
(SMT-LIB Signature, §5.2.1) to

> each constructor $`c \in \Sigma^{\mathrm{C}}`$ has a *unique* rank of the form
> $`\tau_1 \ldots \tau_n\ \tau`$ …

This does not close the problem, which is in the *selector* ranks. Ranking
conditions 2 and 3 of Definition 2 say that a selector or tester *has* the rank
its constructor induces, not that it has no other. For a datatype sort
$`\delta`$, take $`\mathbf{Int}\;\delta`$ as $`c`$'s unique rank,
$`\mathrm{sel}_\Sigma(c) = g`$, and give $`g`$ the ranks
$`\delta\;\mathbf{Int}`$ and $`\delta\;\mathbf{Bool}`$. Definition 2 holds, and
the sorting rules of Fig. 5.3 sort
$`(\mathbf{match}\ t\ \mathbf{with}\ (c\,x) \to x)`$ at $`\mathbf{Int}`$, but
Definition 11's rule 9 rewrites it to
$`\mathbf{let}\ x = g(t)\ \mathbf{in}\ x`$, which is ill sorted. Under the 3.0
plan, a script can build this signature, since only constructors are
excluded from overloading. Will 3.0 exclude selector and tester overloading too?

**Suggested fix.** Unique constructor ranks, with entry 3's fix, make "$`c`$'s
$`i`$-th argument sort at the scrutinee's sort" well defined. Then either:

1. strengthen ranking conditions 2 and 3 from "if" to "iff", so that a
   selector's or tester's only ranks are those its constructor induces, which
   forbids overloading them. Definition 2's conditions 2 and 3 would read:

   > 2. for all constructors $`c \in \Sigma^{\mathrm{C}}`$, selectors
   >    $`g_1 \cdots g_n = \mathrm{sel}_\Sigma(c)`$, $`i = 1, \ldots, n`$, and
   >    $`\rho \in \mathit{Sort}(\Sigma^{\mathrm{S}}, \mathcal{U})^+`$,
   >    $`(g_i, \rho) \in R`$ iff $`\rho = \tau\;\tau_i`$ for some
   >    $`\tau_1, \ldots, \tau_n, \tau`$ with
   >    $`(c, \tau_1 \cdots \tau_n\;\tau) \in R`$;
   > 
   > 3. for all constructors $`c \in \Sigma^{\mathrm{C}}`$, testers
   >    $`p = \mathrm{tes}_\Sigma(c)`$, and
   >    $`\rho \in \mathit{Sort}(\Sigma^{\mathrm{S}}, \mathcal{U})^+`$,
   >    $`(p, \rho) \in R`$ iff $`\rho = \tau\;\mathbf{Bool}`$ for some
   >    $`\tau_1, \ldots, \tau_n, \tau`$ with
   >    $`(c, \tau_1 \cdots \tau_n\;\tau) \in R`$;

   or
2. annotate the selectors in Definition 11's rule 9,
   $`\mathbf{let}\ x_1 = g_1^{\sigma_1}(t) \cdots`$ with $`\sigma_i`$ $`c`$'s
   $`i`$-th argument sort, and likewise in (3.7), which keeps overloading.

**In the mechanisation.** The second: rule 9 annotates each selector.

### 3. Ranking condition 4 does not deliver Note 59

Definition 2's ranking condition 4 and its Note 59:

> 4. there is no constructor $`c \in \Sigma^{\mathrm{C}}`$ such that
>    $`(c, \overline{\tau}_1\ \tau), (c, \overline{\tau}_2\ \tau) \in R`$ for
>    distinct $`\overline{\tau}_1`$ and $`\overline{\tau}_2`$.

> Because of this constraint, the return sort of a constructor uniquely
> determines the sort of its arguments.

**Problem.** Condition 4 compares ranks, not their monomorphic instances. Let
$`(c, u\;\delta)`$, for a sort parameter $`u`$ and a monomorphic datatype sort
$`\delta`$, be $`c`$'s only rank in $`R`$. It satisfies condition 4, yet has the
instances $`c \, : \, \mathbf{Int} \; \delta \in \Sigma`$ and
$`c \, : \, \mathbf{Bool} \; \delta \in \Sigma`$. Then
$`(\mathbf{match}\ t\ \mathbf{with}\ (c\,x) \to x)`$ has both sorts
$`\mathbf{Int}`$ and $`\mathbf{Bool}`$, against §5.2.2's "every closed term has
at most one sort". Scripts do not reach the case, because §4.2.3 confines a
constructor's argument sorts to its datatype's parameters, but chapter 5 states
no such condition. The unique ranks proposed under entry 2 do not help: this
rank is unique.

**Suggested fix.** State condition 4 on monomorphic instances, which is Note 59
itself; or require, as §4.2.3 does, that every sort parameter of a constructor's
argument sorts occur in its result sort.

**In the mechanisation.** Condition 4 is stated on monomorphic instances.

### 4. The combination of two signatures need not be a signature

§5.4.1:

> Two signatures $`\Sigma_1`$ and $`\Sigma_2`$ are compatible if they have the
> same sort symbols, have the same datatype constructors, selectors and testers,
> and they agree on both the arity they assign to sort symbols and the sorts they
> assign to variables. … The combination $`\Sigma_1 + \Sigma_2`$ … [is] the
> unique signature $`\Sigma`$ compatible with $`\Sigma_1`$ and $`\Sigma_2`$ such
> that, for all $`f \in \mathcal{F}`$ and $`\tau \in \mathit{Sort}(\Sigma)^+`$,
> $`f \, : \, \tau \in \Sigma`$ iff $`f \, : \, \tau \in \Sigma_1`$ or
> $`f \, : \, \tau \in \Sigma_2`$.

**Problem.** Compatibility asks for the same constructors, not the same ranks
for them. If $`\Sigma_1`$ gives $`c`$ the rank $`\mathbf{Int}\;\delta`$ and
$`\Sigma_2`$ the rank $`\mathbf{Bool}\;\delta`$, the union of ranks violates
Definition 2's ranking condition 4, so "the unique signature" does not exist.
Either side can likewise give a selector an extra rank (entry 2).

**Suggested fix.** Require compatible signatures to give each constructor,
selector and tester the same ranks.

**In the mechanisation.** Composable signatures give each shared constructor
the same ranks.

## Sort parameters

### 5. Variables with polymorphic sorts have no meaning

Definition 2 gives variables sorts that may contain sort parameters ("a partial
mapping from $`\mathcal{X}`$ to $`\mathit{Sort}(\Sigma^{\mathrm{S}}, \mathcal{U})`$"),
but valuations are defined only on $`\mathcal{X} \times \mathit{Sort}(\Sigma)`$,
the monomorphic sorts, and §5.2.2 defines

> the set $`\mathit{pars}(t)`$ of all sort parameters that explicitly occur in
> $`t`$, that is, in a binder in $`t`$ or in the annotation of a function symbol
> in $`t`$.

**Problem.** Let $`x{:}u \in \Sigma`$ for a sort parameter $`u`$. Then
$`\mathit{pars}(x \approx x)`$ is empty, so Definition 11's rule 1, which
instantiates the sort parameters in $`\mathit{pars}(t)`$, does not instantiate
$`u`$. Definition 11's rule 2, for variables, then needs $`v(x{:}u)`$, which no
valuation defines. So the formula has no value.

**Suggested fix.** Either give variables monomorphic sorts only, or count the
parameters of free variables' sorts in $`\mathit{pars}(t)`$.

**In the mechanisation.** Variables have monomorphic sorts.

### 6. Sort substitution does not preserve well-sortedness

After Definition 3:

> It can be shown that $`\theta(t)`$ is well-sorted if $`t`$ is.

**Problem.** Overloading breaks this. Let $`u`$ and $`u'`$ be sort parameters,
and give $`f`$ the ranks $`u\;u`$ and $`\mathbf{Int}\;\mathbf{Bool}`$, which
Definition 2 allows. In the formula $`\forall\,(x{:}u')\; f(x) \approx f(x)`$, the only
instance of one of $`f`$'s ranks with argument sort $`u'`$ is $`u'\;u'`$, so
Fig. 5.3's sorting rule for unannotated application accepts $`f(x)`$. Under
$`\{u' \mapsto \mathbf{Int}\}`$, $`f(x)`$ has the instances
$`\mathbf{Int}\;\mathbf{Int}`$ and $`\mathbf{Int}\;\mathbf{Bool}`$, so it is ill
sorted, and Definition 11's rule 1 asks for the value of a term Definition 11
does not interpret.

**Suggested fix.** §3.6.1 already reads a polymorphic assertion as well sorted
only if all its instances are:

> In contrast, the formula in the third assert command is ill sorted. The reason
> is that the assertion again stands for a family of assertions for each
> possible monomorphic instance of `X`, in particular, one in which `X` is
> replaced by `Bool`, giving `b` rank `(Array Int Bool)`.

State that reading in Definition 11's rule 1, or forbid ranks whose instances
overlap.

**In the mechanisation.** We take the former solution: the sorting judgement is 
monomorphic, and a term with sort parameters is well sorted when every monomorphic 
instance of it is.

## Datatype domains

### 7. Definition 9(3) is circular as a definition

Definition 9, items 2 and 3:

> 2. for all monomorphic sorts $`\sigma_1`$ and $`\sigma_2`$,
>    $`(\sigma_1 \boldsymbol{\to} \sigma_2)^{\mathbf{A}}`$ is the set of all total maps from
>    $`\sigma_1^{\mathbf{A}}`$ to $`\sigma_2^{\mathbf{A}}`$;
>
> 3. … the $`\Omega`$-reduct of $`\mathbf{A}`$ is an absolutely free algebra
>    with generators $`\bigcup_{\sigma \in S} \sigma^{\mathbf{A}}`$ where $`S`$
>    collects the sorts of $`\mathit{Sort}(\Sigma)`$ that are *not datatypes*;

**Problem.** For a datatype $`\delta`$, $`\delta \boldsymbol{\to} \delta`$ is
not a datatype, so 9(3) makes $`(\delta \boldsymbol{\to} \delta)^{\mathbf{A}}`$
a generator of the algebra defining $`\delta^{\mathbf{A}}`$, while 9(2) defines
$`(\delta \boldsymbol{\to} \delta)^{\mathbf{A}}`$ from $`\delta^{\mathbf{A}}`$.
The same holds for $`\mathbf{Array}\;\mathbf{Int}\;\delta`$, and for
$`\mathbf{Seq}\;\delta`$ in solver extensions. This is not an inconsistency:
$`\delta^{\mathbf{A}}`$ depends only on the generators at its constructors'
argument sorts, so a structure exists. But 9(3) cannot be read as a definition,
since building the domains by recursion on sorts needs each of
$`\delta^{\mathbf{A}}`$ and $`(\delta \boldsymbol{\to} \delta)^{\mathbf{A}}`$
before the other.

Restriction (iv) on the `declare-datatypes` command, in §4.2.3, does not remove
the circularity. For a command declaring the datatypes
$`\delta_1, \ldots, \delta_n`$, it asks of each constructor field
$`(s_j\ \tau_j)`$ that

> (iv) $`\tau_j`$ is a sort term that contains no occurrences of
> $`\delta_1, \ldots, \delta_n`$ below its top symbol.

It constrains one declaration group, while 9(3) ranges over all of
$`\mathit{Sort}(\Sigma)`$, which contains
$`\mathbf{Array}\;\mathbf{Int}\;\delta`$ however (iv) is enforced. What makes
the domains well founded is (iv) together with declaration order, since a later
group may nest an earlier datatype, and Definition 2's signature records neither
groups nor order.

**Suggested fix.** Define the domains group by group, in declaration order,
taking as a group's generators the non-datatype sorts that mention none of its
datatypes and no later one. This needs the signature to record declaration
order.

**In the mechanisation.** While 9(3) takes the domains of the sorts that are not
datatypes as generators, the mechanisation takes only those of the sorts that
mention no datatype at all. This removes the circularity, but drops generators
that 9(3) keeps. For example, in

```smt2
(declare-datatypes ((Option 0)) (((none) (some (val Int)))))
(declare-datatypes ((Cache 0)) (((cold) (warm (lookup (-> Int Option))))))
```

$`\mathbf{Option}`$ and $`\mathbf{Cache}`$ are declared by separate commands,
so $`\mathrm{warm}`$'s field keeps to (iv). 9(3) makes
$`\mathbf{Int} \boldsymbol{\to} \mathbf{Option}`$ a generator, but it mentions
$`\mathbf{Option}`$, so the mechanisation does not, and leaves $`\mathrm{warm}`$
uninterpreted: it denotes some function into $`\mathbf{Cache}`$'s domain, its
selector is unconstrained, and only its tester is still tied to it, holding
exactly on its range.

### 8. Definition 8's generators have no sort

Definition 8, and Note 61:

> Let $`\mathbf{A}`$ be a $`\Sigma`$-structure with universe $`A`$ and let
> $`G \subseteq A`$. Let $`\Sigma_G`$ be the expansion of $`\Sigma`$ obtained by
> adding to $`\Sigma`$ a constant symbol $`c_a`$ of sort $`\sigma`$ for every
> $`a \in G`$ and monomorphic sort $`\sigma \in \Sigma^{\mathrm{S}}`$ such that
> $`a \in \sigma^{\mathbf{A}}`$.

> Distinct sorts can have non-disjoint domain in a structure. However, whether
> they do that or not is irrelevant in SMT-LIB logic.

**Problem.** A generator's sorts are recovered by membership, and Note 61 lets
domains overlap. A generator $`a \in \mathbf{Int}^{\mathbf{A}}`$ that is also in
$`\delta^{\mathbf{A}}`$, for a datatype $`\delta`$, gets a constant $`c_a`$ of
sort $`\delta`$, which puts into $`\delta^{\mathbf{A}}`$ a value no constructor
builds. Every tester is false on it, and a `match` whose patterns are all
constructors cycles through Definition 11's rule 10 forever, so has no value.
Remark 21's claim that "sorts with constructors indeed denote algebraic
datatypes" fails, and so does Note 61's: `match` and the testers can observe
the overlap.

**Suggested fix.** Index the generators by sort, with $`c_a`$ of sort
$`\sigma`$ only for $`a \in G_\sigma`$, and in Definition 9(3) take
$`G_\sigma = \sigma^{\mathbf{A}}`$ for each $`\sigma \in S`$.

**In the mechanisation.** Domains are a sort-indexed family, and each generator
builds a ground term at its own sort only.

### 9. Neither z3 nor cvc5 enforces restriction (iv)

§4.2.3 requires that

> A compliant solver must return an error in response to invocations of this
> command that do not satisfy all of the restrictions above.

Measured 2026-10-01 with z3 4.15.4, and cvc5 1.3.4 and 1.4.1, which agree. Each
declaration is run alone, and again with a term of the datatype asserted, on
which z3 answers alike and cvc5 does not. `Seq` is a solver extension, not
standard SMT-LIB.

| declaration | z3 | cvc5, declaration only | cvc5, with a term of the datatype |
|---|---|---|---|
| `(declare-datatypes ((D 0)) (((mk (kids (Seq D))))))` | error: not well-founded | error: not well-founded | error: not well-founded |
| `(declare-datatypes ((D 0)) (((leaf) (node (kids (Seq D))))))` | *sat*, with a model | *sat* | error: nested-recursive datatype |
| `(declare-datatypes ((D 0)) (((leaf) (node (kids (Array Int D))))))` | *sat*, with a model | *sat* | error: nested-recursive datatype |
| `(declare-datatypes ((D 0)) (((leaf) (node (kids (Set D))))))` | error: datatype is not co-variant | *sat* | error: nested-recursive datatype |
| `(declare-datatypes ((D 0)) (((leaf) (node (kids (Array D Int))))))` | error: datatype is not co-variant | *sat* | error: nested-recursive datatype |
| `(declare-datatypes ((P 2)) ((par (X Y) ((p (p1 X) (p2 Y))))))`<br>`(declare-datatypes ((D 0)) (((leaf) (node (kids (P D D))))))` | *sat*, with a model | *sat* | error: nested-recursive datatype |
| `(declare-datatypes ((D1 0) (D2 0)) (((a) (b (gb Int))) ((c (gc (Seq D1))))))` | *sat*, with a model | *sat* | *sat*, with a model |
| `(declare-datatypes ((D 0)) (((leaf) (node (n Int)))))`<br>`(declare-const x1 (Array D D))`<br>`(declare-const x2 (Seq D))`<br>`(declare-const x3 (-> D D))` | *sat*, with a model | *sat* | *sat*, with a model |

Every row but the last violates (iv); the last, outside any declaration, shows
the sorts entry 7 is about. None of the rejections enforces (iv):

- Row 1 fails well-foundedness, not (iv), in both solvers.
- cvc5's "nested-recursive" errors are a limit of its datatype solver, raised
  only once a term reaches it. Its expert option `--dt-nested-rec` lifts them.
- z3's "not co-variant" errors are a positivity check (entry 10).

Row 7 violates (iv) without recursion, and both solvers accept it in every
configuration.

### 10. Nesting to the left of an arrow

Since each constructor is injective, a datatype's domain must contain a copy of
each constructor's argument domains. A datatype may therefore nest itself
*strictly positively*, nowhere to the left of an arrow. Examples of strictly
positive nesting are fields of sort `(Seq D)`, `(Array Int D)`, `(P D D)` for
another datatype `P`, or `(-> Int D)`. Its domain is then the well-founded
trees, built in stages. It may never nest itself to the left of an arrow. A
datatype $`\delta`$ with a field of sort
$`\delta \boldsymbol{\to} \delta`$, as in

```smt2
(declare-datatypes ((D 0)) (((leaf) (node (kids (-> D D))))))
```

needs an injection of all maps from $`\delta^{\mathbf{A}}`$ to itself, by
Definition 9(2), into $`\delta^{\mathbf{A}}`$, and by Cantor's theorem there is
none once $`\delta^{\mathbf{A}}`$ has two elements.

Covariance is not enough. $`\delta`$ is covariant in
$`(\delta \boldsymbol{\to} \mathbf{Bool}) \boldsymbol{\to} \mathbf{Bool}`$, but
that sort's domain is the power set of the power set of $`\delta^{\mathbf{A}}`$,
too large by Cantor's theorem twice.
Under the intended all-maps reading of `ArraysEx`, the index of `Array` is the
left of an arrow too, which rules out a field of sort `(Array D Int)`.

z3 rejects fields of sort `(Array D Int)`, `(Set D)` and the covariant
`(Array (Array D Bool) Bool)` in the declaration above, all as "not
co-variant", so its check is in fact strict positivity. cvc5 with
`--dt-nested-rec` accepts all three and returns models, which the all-maps
reading rules out.

**Suggested fix.** If (iv) is restated, state it as strict positivity: a
datatype of the group occurs nowhere to the left of an arrow, nor in a position
a theory reads as a map's domain, such as `Array`'s index, at any depth. A
blanket ban on nesting forbids too much, and a ban on contravariant positions
too little.

## Minor corrections

### 11. Definition 8 ranges over sort symbols

"monomorphic sort $`\sigma \in \Sigma^{\mathrm{S}}`$" should read
"$`\sigma \in \mathit{Sort}(\Sigma)`$": $`\Sigma^{\mathrm{S}}`$ is the set of
sort symbols.

### 12. Remark 23 names the old application symbol

> There is no rule above for higher-order function application \_, since \_ is a
> normal (interpreted) function symbol defined in the HO-Core theory (see
> Figure 3.6).

The 2025-04-09 release "Replaced \_ with @ as the map application operator in
theory HO-Core", and Fig. 3.6 uses `@`. Remark 23 should name `@`.

### 13. Rule 2 names the valuation where it means the variable

Definition 11, rule 2:

> 2. $`[\![x]\!]^{\mathcal{I}} = v(x{:}\sigma)`$ if $`\mathcal{I} = (\mathbf{A}, v)`$
>    and $`v`$ is of sort $`\sigma`$

A valuation has no sort. This should read "$`x`$ is of sort $`\sigma`$", that
is, $`x{:}\sigma \in \Sigma`$ for $`\mathcal{I}`$'s signature $`\Sigma`$.

### 14. Fig. 5.3 applies $`\mathrm{con}_\Sigma`$ to a sort

$`\mathrm{con}_\Sigma`$ is defined on sort symbols (Definition 2), but both
match rules of Fig. 5.3 apply it to the scrutinee's sort $`\delta`$, as in
$`\{c_1, \ldots, c_{k+1}\} = \mathrm{con}_\Sigma(\delta)`$. This should be
$`\mathrm{con}_\Sigma(s)`$ for $`s`$ the top symbol of $`\delta`$.

### 15. Validity does not reduce to unsatisfiability with sort parameters

§2.1:

> … at least for classes of formulas that are closed under logical negation,
> this is no restriction because the two problems are inter-reducible: a formula
> $`\varphi`$ is valid in a theory $`T`$ exactly when its negation is not
> satisfiable in the theory.

Formulas with sort parameters are closed under negation, but asserting
$`\neg\varphi`$ asserts every instance of $`\neg\varphi`$, which is not the
negation of asserting every instance of $`\varphi`$. Remark 15 in §4.2.4 says as
much. §2.1 should restrict the claim to formulas without sort parameters, or
refer to Remark 15. (Checked in the mechanisation: `not_valid_at_most_two` and
`not_sat_not_at_most_two` in `tests/UnitTests.v`.)

### 16. Remark 13's formula does not say what the remark says

Remark 13, in §4.2.4:

> ```smt2
> (declare-sort-parameter A)
> (assert (forall ((x A) (y A) (z A)) (or (= x y) (= x z))))
> ```
>
> The assertion states that the domain of every sort has cardinality at most
> two. … the formula is satisfiable if the only available sort is Bool …

The formula says every domain has at most one element: take $`y = z \neq x`$.
It is false at $`\mathbf{Bool}`$, so unsatisfiable when $`\mathbf{Bool}`$ is the
only sort. The intended formula needs the third disjunct `(= y z)`.
