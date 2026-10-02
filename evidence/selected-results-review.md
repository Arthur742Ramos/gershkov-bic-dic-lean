# Independent review of selected mathematical results

Reviewed 2026-10-02 against public baseline commit
`cc7dd990edab0d29b02a751350446e11d2b9b9a4`. This independent review used
lightweight source reads, byte comparisons, hashing, and in-memory Python
generation. The reviewer changed only this report and its companion hash
record; no Lean build, proof job, kernel replay, rendering, or hosted job was
run by this reviewer.

**Verdict: pass for the selection and source-preservation checks.** The selected
mathematical results are finite Bayesian-to-dominant-strategy equivalence,
weighted monotone lifting, and optimizer monotonicity. The support
implementation and all library proofs are unchanged.

## Exact preservation

Every byte of `Gershkov.lean` and all nine `Gershkov/*.lean` files equals the
baseline. Their current SHA-256 values also equal the bindings in the existing
public final source review; the nine mathematical-library file hashes equal
the bindings in the existing public final mathematical review. The original
library reviews therefore still concern these same library contents. Their
historical wrapper and validation conclusions must be read with their original
snapshot bindings.

For both `Challenge.lean` and `Solution.lean`, the current file equals the
baseline prefix ending immediately before the three removed support-result
export blocks, with only the introductory selection wording updated. This
comparison covers every remaining namespace, universe, variable context,
definition, instance, theorem header, and proof body. Each retained Solution
proof is the identical application of its corresponding `Gershkov` theorem.
Each retained Challenge proof is its original isolated reference placeholder.
No retained theorem assumption or conclusion was changed.

| Selected public contract | Preserved assumptions and conclusions |
| --- | --- |
| `GGKMS.finite_bayesian_dominant_equivalence` | Arbitrary finite agents and alternatives; heterogeneous nonempty supports `Fin (n i + 1)`; strictly increasing real type maps; independent positive normalized real priors; nonnegative value slopes and arbitrary real constants; an arbitrary feasible BIC mechanism. Constructs feasible DIC, preserves every support type's truthful interim utility and ex ante social surplus, matches interim slopes and every alternative's ex ante probability, matches modified interim transfers, and attains the weighted quadratic minimum. |
| `GGKMS.weighted_monotone_lifting` | Arbitrary finite dependent type spaces with preorders, arbitrary positive normalized independent priors, real slopes, feasible initial allocation, and monotone prescribed interim slopes. Constructs a matching feasible allocation with pointwise monotone own-type slopes and actual weighted quadratic minimality. There is no assumed lifting or minimizer existence. |
| `GGKMS.minimizer_monotone` | A matching allocation, monotone prescribed interim slopes, and actual global weighted quadratic minimality over matching allocations. Concludes pointwise own-type monotonicity at every opponents' support profile. Monotonicity is a conclusion rather than a premise. |

`Matches` retains its genuine feasibility, slope-marginal, and alternative
ex ante probability constraints. All 26 selected definitions, abbreviations,
and named instances retain their exact baseline bodies and contexts. They are
also identical to the declarations extracted from the unchanged library by
the generator.

## Supporting library results remain available

Only these three names were removed from the selected Comparator result list
and the `GGKMS` wrapper exports:

- `GGKMS.Transfers.scalarIC_iff_monotone_adjacent`
- `GGKMS.expectation_on_support`
- `GGKMS.product_expectation_on_support`

Their original, complete proof bodies remain in
`Gershkov.Transfers.scalarIC_iff_monotone_adjacent`,
`Gershkov.expectation_on_support`, and
`Gershkov.product_expectation_on_support`. They remain public library
declarations available through `Gershkov` and Solution's public import.
The scalar characterization still covers all deviations through the unchanged
adjacent-bounds and telescoping development. The expectation identities still
allow arbitrary nonnegative finite masses and delete only zero-mass labels;
normalization, support nonemptiness, and opponents' expectation preservation
also remain proved in the library. This revision introduces no claim of
IC/IR at deleted ambient labels, preserved utility for null types, or an
individual-rationality refinement.

## Generation, audit coverage, and documentation

The generator was evaluated in memory with its file-write statements disabled.
Its generated Challenge, Solution, and Comparator JSON matched the current
files byte for byte. Comparator has exactly the three retained theorem names,
the identical ordered list of 26 definition/instance names, and the unchanged
module names and permitted axioms.

The current explicit declaration inventory contains 155 declarations.
`Audit.lean`, `ContractAudit.lean`, and
`evidence/authored-declarations.json` match their generator computations
exactly, including every recorded source hash. The full library declaration
inventory still contains all three supporting lemmas. Audit coverage lost
only the three deleted wrapper declarations; it did not lose their library
implementations. A comment-aware source scan found exactly the three selected
Challenge placeholders and no admissions/custom axioms or prohibited proof
shortcuts in Solution or the library. This textual scan does not replace
an environment-based axiom audit.

The ordered `formalization.yaml` alignment list equals Comparator's selected
theorem list. README and metadata accurately describe three selected results
and 26 genuine definitions/instances, distinguish the supporting library facts,
and preserve the positive-support, arbitrary-prior, heterogeneous-cardinality,
weighted-minimizer, telescoping-transfer, utility, and surplus scope. They
continue to disclose the constant modified base transfer and absence of the
source's additional ex post individual-rationality refinement. Verification
scripts and hosted workflows are unchanged apart from the authorized theorem
selection in the contract generator. The scoped whitespace check passed.

## Separate validation gates

This report certifies the inspected source selection and preservation checks.
It does not certify Lean elaboration, environment axiom auditing, Comparator
acceptance, default-kernel/NanoDa/con-ron replay, sanitizer/render output,
Linux confinement, hosted verification, or intake readiness for the revised
candidate. Baseline local logs and baseline local-render/local-validation
records are historical evidence wherever their hashes or counts identify the
older six-result package. Fresh validation must identify the revised files
and exact candidate commit before being treated as current success.

The companion `selected-results-review-hashes.json` binds the reviewed source,
configuration, scripts, workflows, public documentation, declaration inventory,
and this report. Validation logs and mutable validation manifests are kept
outside this source-review hash binding. Any later change to a bound file
requires rechecking the affected claim and refreshing the binding.
