# Finite Bayesian-to-Dominant-Strategy Equivalence in Lean

This repository proves the finite support specialization of Theorem 2 of Gershkov, Goeree, Kushnir, Moldovanu, and Shi, “On the Equivalence of Bayesian and Dominant Strategy Implementation,” Econometrica 81 (2013), 197–220, [DOI 10.3982/ECTA10592](https://doi.org/10.3982/ECTA10592). The [published paper](https://opus.lib.uts.edu.au/bitstream/10453/27834/1/2012004913OK.pdf) states Theorem 2 on p.206.

Formalization authors and responsible maintainers: **Arthur Freitas Ramos, David Barros Hulak, and Ruy Jose Guerra Barretto de Queiroz**. The mathematical theorem belongs to the five paper authors. Independent AI reviews are documented; no human peer review, source-author endorsement, or novelty guarantee is claimed.

## Exact contract and binder alignment

`GGKMS.finite_bayesian_dominant_equivalence` constructs a feasible DIC mechanism from every feasible BIC mechanism, preserving every support type's truthful interim utility and ex ante social surplus. Its conclusion also records matched interim slopes, modified interim transfers, each alternative's ex ante probability, and actual minimization of the weighted quadratic objective.

| Binder | Meaning and source correspondence |
| --- | --- |
| `I`, `[Fintype I]` | Arbitrary finite agents; `DecidableEq I` supplies indexing. |
| `K`, `[Fintype K]` | Arbitrary finite social alternatives. Feasibility is nonnegative probabilities summing to one at every profile. |
| `n : I → Nat` | Agent `i` has `n i + 1` support types; arbitrary heterogeneous cardinalities. |
| `θ`, `hθ : ∀ i, StrictMono (θ i)` | Strictly ordered distinct real scalar types, as on p.205. Negative values and singleton supports are included. |
| `p`, `hp : SupportPrior p` | Arbitrary positive real support masses normalized separately for each agent. `joint` and `opponentMass` are the independent products. No uniformity or rationality requirement. |
| `a`, `_ha : ∀ i k, 0 ≤ a i k` | The nonnegative private-value slopes in the p.199 model. |
| `c : I → K → Real` | Arbitrary alternative-dependent constants, retained in utility and surplus. |
| `q₀`, `hfeasible` | Arbitrary randomized social choice with full simplex feasibility. |
| `pay₀` | Arbitrary real transfers received by agents. No budget constraint. |
| `hBIC` | Every true support type prefers truth to every support report in actual weighted interim utility. |
| Constructed `q`, `pay`, `DIC` | Every true support type prefers truth against every own support report at every opponents' support report profile. |

Any nonempty finite distinct scalar support admits the strictly ordered enumeration above. The endpoint assumes no monotone lifting, optimizer property, uniform prior, fixed cardinality, auction constraint, or zero constants.

## Proof and scope

`Compactness.lean` proves that the actual weighted marginal polytope is nonempty and compact and that the quadratic objective attains its minimum. `Smoothing.lean` and `Lifting.lean` prove a genuine four-profile improvement for every pointwise monotonicity violation. Different mixing rates for unequal masses preserve all weighted slope marginals and ex ante alternative probabilities while strictly decreasing the squared-norm objective. Optimizer monotonicity is a conclusion.

`Transfers.lean` proves adjacent coefficient bounds, the flat-marginal branch, finite telescoping for all deviations, and arbitrary-weight expected transfer matching. `Equivalence.lean` combines these with the minimizer. `Mechanism.lean` proves surplus preservation with arbitrary constants and preservation of each agent's ex ante actual transfer.

The modified base transfer is constant at the original lowest type's modified interim transfer. It has the same expectation as the source's ratio base in equation (5), giving the same existence, utility, and surplus result. We do not claim to reproduce that displayed ratio base or the additional ex post individual-rationality remark. The adjacent coefficients and telescoping construction follow equation (5).

The paper's `X_i` is a distribution support, so its finite atoms have positive masses. `Support.lean` separately proves normalization and expectation preservation after removing zero-mass ambient labels, for individual, joint, and opponents' interim expectations. Reports in the main theorem are support types. DIC against extra ambient null reports and utility preservation for deleted null types are not claimed.

The scope is finite supports. Infinite discrete/continuous supports, correlated types, multidimensional types, nonlinear private values, ex post budget balance, and preservation of every alternative-specific interim allocation are outside the theorem. Existing Myerson, Border, Rochet, and BCE repositories were not modified. Bounded duplicate searches found no existing target; this is not a novelty claim.

## Examples

`Examples.lean` supplies explicit scalar/matrix certificates independent of the existence theorem. Priors `(1/3,2/3)` and `(1/4,3/4)` give a feasible BIC allocation that fails DIC. The explicit feasible DIC replacement preserves weighted marginals, interim utilities, ex ante on-probability `21/40`, and surplus `83/60` with nonzero constants. Other certificates cover flat marginals, negative scalar types and coefficients, and singleton support. They certify the explicit scalar/matrix representation rather than instantiate the full mechanism API.

## Reproduction and evidence

Exact pin: Lean `v4.35.0-rc2`, Mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55`. Official policy: `65f0154ed776cd26c224254aa57b379137f28b0d`; Verso: `9f8096e40b31715b1d8d5997f15a0bd832f7e37d`.

```sh
lake update
lake exe cache get Mathlib.Tactic Mathlib.Topology.Order.Compact
lake build
PALOMAR_SUBMISSION_DIR=/path/to/pinned/PalomarSubmission ./scripts/verify.sh
```

`Challenge.lean` contains 26 genuine copied definitions/instances and three exact theorem contracts: finite Bayesian-to-dominant-strategy equivalence, weighted monotone lifting, and optimizer monotonicity. Only those three named reference theorem proofs have policy-permitted placeholders. The scalar IC characterization and the two support-restriction identities remain proved library facts used to support the construction; they are not selected as independent results. `Solution.lean` proves the selected contracts from the complete library, without admissions/custom axioms. The public comparison namespace is `GGKMS`; implementation proofs use `Gershkov`. Solution and the library do not import Challenge. `scripts/make_challenge.py` regenerates the exact exports and Comparator lists; package checks enforce byte parity.

The verification script validates metadata and selected names, audits all explicit declarations and every actual authored environment constant including generated helpers, and allows only `propext`, `Quot.sound`, and `Classical.choice`. Reference definitions and named placeholders are audited separately. Official Comparator replay uses Lean's default kernel, NanoDa, and con-ron. Local macOS replay discloses unsandboxed mode; hosted Linux verification separately checks confinement.

`evidence/` contains independent source/math reviews, build/axiom/contract/kernel logs, source hashes, and local pinned rendering evidence. The official rendering workflow uses the trusted core-notation audit and unchanged sanitizer and requires each HTML page below 8 MiB. Both hosted workflows must pass on the exact candidate commit before submission readiness. Their artifacts provide exact-SHA Linux proof and sanitized-render evidence. No Palomar intake or registration is performed.
