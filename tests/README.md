# Unit tests

| File | Holds |
|---|---|
| `TestTheory.v` | the shared setting: the signature `Σ_test`, the theory `T_test`, the domain, the interpretation, the model family `A_free` with its `T_test.(models)` proof, `T_test_consistent`, and the helper lemmas the tests use |
| `UnitTests.v` | the tests themselves, and nothing else |

`T_test` is Core and Reals_Ints composed, extended with one uninterpreted `f : Int Int`. It declares no datatype, so the datatype conditions are vacuous at it and nothing here exercises them.
