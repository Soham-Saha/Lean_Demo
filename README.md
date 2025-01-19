First successful attempt at formalizing a non-trivial theorem in Lean 4

The lemma and its proof are described [here](https://math.stackexchange.com/a/5015161)

[Link](https://live.lean-lang.org/#codez=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) to Lean4Web online viewer
