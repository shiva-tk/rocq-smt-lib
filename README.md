# Rocq mechanisation of SMT-LIB

This is a mechanisation of [SMT-LIB](https://smt-lib.org), a standard language for Satisfiability Modulo Theories (SMT) solvers.

The mechanisation is based on version 2.7 of the standard and covers the logical semantics of the language, as described in chapter 5 of the standard.

The [generated documentation](https://smt-lib.shiva-tk.xyz) of the Rocq sources, built with `rocq doc`, is browsable online.

Additional documentation, located in `docs`:

- [`correspondence.md`](docs/correspondence.md) gives the correspondence between the standard and the mechanisation, section by section of the standard, followed by the mechanisation's extensions to the standard and its design choices. Where we believe the standard itself is inconsistent or imprecise, the mechanisation's way round it is described there.
- [`standard-discrepancies.md`](docs/standard-discrepancies.md) sets out each such problem in the standard, with the standard's text quoted.
- [`axioms.md`](docs/axioms.md) lists each axiom the formalisation uses, where, and why. The formalisation is not designed to be constructive, but it is conservative about where it is not.
