# NTIME(n) ⊊ DSPACE(n): partial Lean formalization (reference material)

This directory is a partial Lean formalization of Charlie Cruz's manuscript
"Nondeterministic Linear Time Is Strictly Contained in Deterministic Linear
Space". It is shared as reference material. It is not part of the Complexitylib
build, does not follow Complexitylib's module conventions, and is not intended
to be merged as is.

The final theorem `NTIME encBits (fun n => n) ⊂ DSPACE encBits (fun n => n)`
is not proved here. Everything that is present compiles, has no `sorry`, and the
checked theorems print only `propext`, `Classical.choice` and `Quot.sound`.

## What is proved

- Semantic reduction (`SemanticReduction.exists_networks_of_mem_NTIME`):
  membership in `NTIME[T]` is positivity of the contraction of some schedule's
  block-counting network (`blockNetworkOf`), and each network is a weighted
  constraint system (`NetworkSystem.count_toSystem`).
- Counting algebra for weighted constraint systems (`WeightedSystem` and the
  `W*` modules), including the grouped, measurement-decoupled expression and
  balanced hash placement (`WSchedulePlacement`).
- A verified first-order language `Prog` with bounded folds and its compiler to
  Complexitylib counter programs (`ProgLang.compile_correct`,
  `decidable_of_prog`, `ProgLength.decidable_of_prog_len`): a term whose
  intermediate values stay below `2^K` with `K ≤ c·S` decides its language in
  simultaneous time `2^(C·S)` and space `C·S`. This reuses Complexitylib's
  counter-program certificates.
- Local access to the block-counting network by terms, without storing it: a
  verified one-interval machine simulation (`Local*`,
  `LocalIntervalCount.intervalCountT_denote` = `localIntervalCount`), ports and
  port positions (`NetPortTerm`), and table entries
  (`NetTable.denote_tableEntryT` = `tableEntryNum`), tied to `blockNetworkOf`
  (`NetAccess`, `NetSystemSpec`).
- The arithmetic counter as a term: support codes via the verified gamma-code
  parser (`SupportQueryTerm`), the compressed Taylor loop
  (`TaylorLoopEq.taylorLoopT_eq`), and recovery
  (`CounterTerm.counterT_eq` = `WCompressedRecoveryLoop.evaluate`), for accessor
  terms meeting stated contracts.
- Some accessors: labels and tensor signs (`LabelTerm`) and parity
  interpolation (`DeformTerm`).

## What is missing

- The remaining accessor terms: bad-label test, `beta`, residual and matrix
  entries, spectral row indexing, incidence evaluation, grouped accessors, hash
  placement with seed search.
- Instantiating the parameters and checking every side condition of
  `WConcreteCountingLoop.countModP_correct` with `o(n)` space.
- The prime scan and the top-level decider (accept when some schedule's count
  is nonzero modulo some scanned prime).
- Value-bound (`Bnd`) lemmas for all terms, giving the `2^(C·κ)` register bound.
- The final theorem, which would combine the simulation with the space
  hierarchy (`ComplexityReuse.conditional_linear_separation`, which currently
  takes the simulation as a hypothesis).

`PROGRESS.md` is the working log, with the plan and the exact stopping point.

## Building

The sources are plain (non-`module`) Lean files in the `NtimeDspace` namespace,
using `lakefile.toml`, `lean-toolchain` and `lake-manifest.json` from this
directory: Lean `v4.36.0-rc2`, Complexitylib at
`a696d7b149f95e241251ed0f575645d6468a9ccc` (the base of this branch), with the
matching cslib and Mathlib pins. `NtimeDspace.lean` aggregates the original
148 checked modules; the newer modules (for example `CounterTerm`, `NetTable`,
`TaylorLoopEq`) were checked one at a time against a full build of that
Complexitylib closure. `NtimeDspace/Checks/` holds the `#print axioms` checks.

## Provenance

Written with substantial AI assistance (Claude Code), directed by the author of
the manuscript. No human has reviewed the Lean proofs line by
line; the evidence is that they compile with the axiom reports above.
