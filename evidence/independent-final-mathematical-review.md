# Final mathematical binder and dependency review

Date: 2026-10-02. Reviewer: independent mathematical review agent. Scope: read-only review of the actual finite equivalence library, following the preimplementation review in `independent-mathematical-review.md`. This is a mathematical/source-alignment review, not human endorsement or certification of the separate publishing and kernel gates.

## Verdict

**Pass for the finite positive-support specialization of published GGKMS (2013), Theorem 2.** The actual `Gershkov.finite_bayesian_dominant_equivalence` binders match the intended finite theorem, and its proof constructs weighted monotone lifting rather than assuming it. There is no uniform-prior, equal-cardinality, auction-feasibility, rational-probability, nonnegative-type, fixed-agent-count, or fixed-alternative-count restriction. Monetary transfers and alternative constants are unrestricted real values. Each support type's interim utility and ex ante surplus are explicitly preserved.

The accurate scope is finite **support** reports/types. Extra ambient zero-mass reports and preservation of their utilities are not claimed. The transfers use a constant modified base with the same expectation as source equation (5), a valid existential variation. The source's particular proportional base and its individual-rationality refinement are not formalized by this theorem.

## Reviewed source binding

Published source: supplied `sources/2012004913OK.pdf`, SHA-256 `bbdfb4d6df83c7e979a48e809e32c52f36f2e8800b8b06fe2a30cb4029c9223c`; model pp. 199–200, discrete IC pp. 205–206, Theorem 2 p. 206, appendix proof pp. 217–218. The p. 206 image confirmed the nonzero-denominator coefficient case. The earlier report records the weighted finite perturbation derivation and source support caveat.

Reviewed Lean file hashes in `gershkov-equivalence-lean`:

| File | SHA-256 |
| --- | --- |
| `Gershkov/Smoothing.lean` | `7b1a4157bcb6b10023c10a008054dc3d2bbaab0992f1af24f32eaa1c8eef9b53` |
| `Gershkov/Model.lean` | `7f7b741a020d36bb4b8cb0084ee071da7dcd9c3b33f1a28b0597a70a56161523` |
| `Gershkov/Compactness.lean` | `8c4b0f7ef3766850d16e2da33fe3ae62af0d6bca77119a9cb4f6d14aba7a1397` |
| `Gershkov/Lifting.lean` | `8d6d4b877494de2e95c73432f9e11745b52f1d8f0a87cb460cfe59e851041c64` |
| `Gershkov/Transfers.lean` | `99ba8b78bf932b7ed0542fcc35ef4d5b4e92d7b7206d6879b4e56058ef2d1597` |
| `Gershkov/Mechanism.lean` | `e4c2d4456e5bd05063f96bd610561dfff81e5fc4dce680c28b781f2ba742bfa6` |
| `Gershkov/Equivalence.lean` | `a70f03add72cd0d56b84568460ed2a341ddb09695d7c42657cdb111a6d03b620` |
| `Gershkov/Support.lean` | `3f120dd8fada000d65ebf1f46fe9c97f86344d6e8974b10c8c19550f01798b50` |
| `Gershkov/Examples.lean` | `36826b0e0f064d91437039d358bbf4b95951f0b408b4625d5d1f654f60471813` |

The review is bound to these contents. Mathematical changes after this snapshot require renewed review; cosmetic/import changes should at least update the binding. The successful library build is recorded in `evidence/equivalence-build.log`, with `Built Gershkov.Equivalence` and successful completion. The reviewed files contain no textual `sorry`, `admit`, custom `axiom`, or `unsafe` declaration. A complete environment-based all-declaration transitive axiom audit is a separate required gate; textual inspection cannot replace it.

### Final-package revalidation

The packaged report was independently rebound on 2026-10-02 after inspection of two additive corollaries: `exAnte_transfers_match` in `Mechanism.lean` and `opponent_expectation_on_support` in `Support.lean`. Both corollaries pass mathematical review, as explained below. The other seven listed files retain exactly the reviewed hashes, including the unchanged `Equivalence.lean` main theorem. These additions neither change the main theorem's assumptions/conclusions nor introduce a lifting premise. No library file was edited during this revalidation and no additional Lean build was run. This revalidation concerns source correspondence; any subsequent release commit must obtain its own exact-commit hosted verification.

## Exact binder alignment

`I` and `K` are arbitrary types with `Fintype`, so arbitrary finite cardinalities are supported. `DecidableEq I` is a finite-representation requirement, not an economic restriction. Types are `Types n i = Fin (n i + 1)` for an arbitrary function `n : I → Nat`; each agent therefore has a nonempty finite support and cardinalities may differ. Any finite nonempty set of distinct real types admits such a strictly ordered enumeration. `hθ : ∀ i, StrictMono (θ i)` states precisely that distinct indices correspond to strictly ordered distinct real scalar values; negative values and singleton supports are included.

`p` has values in `Real`. `SupportPrior p` unfolds to strict positivity at every listed support atom and sum one for each agent. Product `joint p` and `opponentMass p` define the actual independent prior. There is no assumption of equal or rational masses. The final theorem takes `a,c : I→K→Real`, with `_ha : ∀ i k, 0≤a i k`; no restriction is imposed on `c`. The nonnegative-slope assumption is unused by the finite lifting/constant-base proof, which proves an extension, but it is correctly retained in the public source theorem contract.

`Feasible q₀` is nonnegativity and sum one over alternatives at every report profile. This is a full random social choice simplex, not a single-item or auction polytope. There is no fixed cardinality or deterministic-allocation premise. All transfer values are real and unrestricted. No ex post budget balance is assumed or concluded. A feasible initial allocation implicitly rules out an empty alternative set on the nonempty profile space.

The payoff definition correctly includes scalar private values and alternative constants: `θ_i(true) * Σ_k a_i^k q_k(report,opponents) + Σ_k c_i^k q_k(report,opponents) + pay_i(report,opponents)`. BIC compares every true support type to every support report against the opponents' product prior. DIC compares those same reports at every opponent support report profile. No truth condition is weakened to adjacent or averaged deviations in the final DIC definition.

## Constructed lifting and dependency check

The final theorem first derives marginal monotonicity from `bic_scalar` and `Transfers.monotone_of_ic`. It then calls `weighted_monotone_lifting`, whose apparent monotone-marginal premise is thus discharged from the actual BIC input. It does not receive any hypothesized allocation, minimizer, monotone lifting, separation oracle, or optimizer property from the final theorem's caller.

`exists_minimizer` constructs a minimizer on `Matches p a q q₀`. `Matches` genuinely contains simplex feasibility, all weighted own slope marginals, and every alternative's ex ante probability. The original allocation witnesses nonemptiness. Feasibility bounds every entry in `[0,1]`; closedness of the finite linear constraints and finite product compactness give compactness. The actual quadratic objective `energy (joint p) a q = Σ_profile jointMass * Σ_agent slope(profile)^2` is continuous and attains a minimum. No coercion has substituted a different objective or constraint set.

`minimizer_monotone` proves pointwise monotonicity from the explicit `improving_perturbation` contradiction. `crossing_context` extracts a strictly positive reverse context using all strictly positive opponent masses. Four profile distinctness is proved from different own types and contexts. `doubleMix` changes the two disjoint pairs by the actual joint-mass-scaled coefficients. The common perturbation masses are `δ=η/d` and `ε=η/e`, with `η` positive and below all four joint-mass-times-gap bounds. Hence every convex mixing coefficient is strictly between zero and one.

The weighted moment identity is proved algebraically, not assumed. For another agent, the two profile indicators agree within each pair and its conditioned moment change vanishes. For the selected agent, the two moment changes cancel because `δ*d=ε*e=η`. `fiber_moment` correctly converts this full joint weighted moment to own-mass times the conditioned slope; own-mass positivity permits cancellation. Every alternative's ex ante moment is preserved by the constant profile indicator. These steps use the product prior and do not inadvertently extend to correlated priors.

The weighted squared-norm identity in `mixPair_energy` has the correct unequal-mass factor `-δ*(2-δ/μ_l-δ/μ_r)`. The sum of squared slope differences is strictly positive because the selected agent's component differs. Both pair changes strictly improve the objective; disjointness permits sequential composition. Consequently optimizer monotonicity is an actual conclusion. These facts discharge the central mathematical obstacle identified before implementation.

## Transfers, utilities, and surplus

`Transfers.coefficient_bounds` derives the source's adjacent coefficient interval from full scalar BIC. `coefficient_transfer_delta` covers zero marginal differences by forcing the modified transfer difference to zero. `pair_bounds_of_adjacent` uses finite induction to telescope full report-to-report incentive inequalities, including negative scalar values. Thus `constructed_transfer_ic` proves full DIC, rather than silently invoking unproved adjacent sufficiency.

The finite prefix-sum transfer uses the constant base `T(0)`. `constructed_transfer_mean` proves expected transfer matching for arbitrary normalized finite opponent weights; it uses explicit expectation linearity and finite induction. `transfers_for_matching_allocation` selects this construction separately for every agent and defines actual payment by subtracting `value c q`. `pack_self`, `pack_other`, and the context identity recover the selected modified transfer at every own report/opponent profile. Full DIC then follows from the scalar certificate. Matched slope marginals and matched modified transfers give truthful interim utility equality for **every** listed support type.

`socialSurplus` is the expected sum of agents' private alternative values, excluding monetary transfers, exactly as in the source's utility-minus-transfers definition. `surplus_matches` splits the type-linear term into `Σ_i Σ_t p_i(t) θ_i(t) V_i(t)`, preserved by slope marginals, and the alternative-constant term into `Σ_i Σ_k c_i^k E q_k`, preserved by ex ante alternative probabilities. Arbitrary real `c` are handled; they are not discarded or assumed zero. The final conclusion additionally records `Matches`, every support type's modified transfer equality, and actual objective minimization.

The added `exAnte_transfers_match` explicitly proves preservation of each agent's ex ante **actual monetary transfer** from `Matches` and equality of every modified interim transfer. It first uses `exAnte_interim` to lift the modified interim equality to equality of modified ex ante transfers. It then uses `exAnte_value` and alternative-probability matching to prove equality of the expected constant-value terms. Finally, linearity gives `E(modified) = E(actual pay) + E(value c)`, and subtraction proves equality of expected actual payments. This is the source's transfer consequence with arbitrary nonzero constants and the correct plus/minus convention. It requires no budget-balance assumption or extra optimizer property. It is an additive corollary; the main theorem's exact contract remains unchanged and supplies its premises.

## Support and limits

`PositiveSupport`, `expectation_on_support`, and `support_normalized` explicitly remove zero-mass ambient labels while preserving weighted expectations and normalization. The reviewed `product_expectation_on_support` further proves exact preservation of the full joint expectation after independently restricting every agent's ambient domain: the positive-profile subtype is equivalent to the product of positive-atom subtypes; every omitted profile has a zero factor in its joint mass.

The added `opponent_expectation_on_support` applies that product identity to the finite subtype of agents distinct from a fixed agent `i`. Its left side sums over precisely the positive opponent atoms, and its right side uses the original `opponentMass p i` product. The hypothesis is only nonnegativity of the ambient masses; normalization is unnecessary for this weighted-sum identity. For a fixed own support true type/report, take `f` to be the corresponding payoff or allocation function to obtain interim expectation preservation after deleting opponent null labels. The corollary asserts an expectation identity, not IC at extra null reports or preservation of an ambient null own type's utility by the constructed mechanism. It is additive and does not change the main theorem's positive-support report domain.

The main report domain is the nonempty positive support itself. The library does not establish DIC against arbitrary ambient null reports or preserve utilities of every ambient null label. It also does not claim a result for infinite/countable discrete supports, correlated types, multidimensional types, nonlinear private utilities, all alternative-specific interim allocations, or ex post budget balance. These limits agree with the intended finite specialization and must remain clear in README and final claims.

The new `Gershkov/Examples.lean` provides independent explicit matrix regression certificates rather than hiding behind the equivalence theorem. Its unequal prior example proves feasibility, weighted marginals, original BIC and failure of DIC, lifted DIC, equal ex ante on probabilities, and equal surplus with nonzero constants. Flat adjacent coefficients, negative real types/coefficient, and singleton supports are also covered. The serial command `lake env lean Gershkov/Examples.lean` returned exit zero with no warnings; its empty development log remains outside the published package because successful compilation printed nothing. The example source has no admissions/custom axioms. These are scalar/matrix certificates, not an assertion that the full main mechanism representation has been instantiated by the examples.

## Remaining nonmathematical gates

This review does not certify Challenge/Solution Comparator correspondence, named declaration inventory, all-declaration standard-axiom audit, NanoDa/con-ron acceptance, pinned Verso/sanitizer HTML output, final archive hashes, public repository identity, or hosted Linux execution. They must be checked on the actual final package. No Palomar registration, human review, source-author endorsement, or novelty guarantee follows from this report.
