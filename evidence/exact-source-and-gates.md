# Independent exact-source and infrastructure review

Reviewed 2026-10-02 by a separate AI reviewing agent. This review did not author
Lean proofs or modify the existing BCE, Border, Rochet, or Palomar repositories.
It is source and mathematical review, not human peer review or kernel evidence.

## Primary source and exact scope

Gershkov, Goeree, Kushnir, Moldovanu, and Shi, *On the Equivalence of Bayesian
and Dominant Strategy Implementation*, Econometrica 81 (2013), 197–220,
DOI 10.3982/ECTA10592. Supplied published PDF:
https://opus.lib.uts.edu.au/bitstream/10453/27834/1/2012004913OK.pdf

Local source: `sources/2012004913OK.pdf`; SHA256:
`bbdfb4d6df83c7e979a48e809e32c52f36f2e8800b8b06fe2a30cb4029c9223c`.
Read the model on pp.199–200, quadratic program and Lemma 1 on pp.201–204,
discrete IC conditions on p.205, Theorem 2 and formula (5) on p.206, and its
appendix proof on pp.217–218. Visually inspected p.206 using Poppler because
text extraction loses the not-equal symbol in alpha's definition.

The source has finite agents and alternatives. Values are private, scalar,
linear, and quasilinear: `a_i^k x_i + c_i^k + t_i`, with `a_i^k >= 0`, arbitrary
real `c_i^k`, and unrestricted real transfers **received** by the agent.
Types are independent with arbitrary distributions. The finite/discrete theorem
uses heterogeneous lists `x_i^1 < ... < x_i^{N_i}`; there is no bound or equality
requirement on the cardinalities, no uniformity requirement, and no auction
restriction. Each `X_i` is explicitly the **support** of its distribution in
the model. For finite `X_i`, all its masses are positive and it is nonempty.

Definition 1 says equivalence preserves every type's interim truthful expected
utility and the ex ante social surplus. Theorem 2 actually constructs a stronger
equivalence: allocation slopes' interim marginals `V_i`, modified interim
transfers `T_i`, and every alternative's ex ante probability all match.
It does not generally preserve each alternative's interim allocation
probability (Section 4.1 explains this distinction).

## Allocation contract and the weighted perturbation

Let `v_i(x) = sum_k a_i^k q_k(x)` and let opponent expectation use the product
of the agents' actual masses. The quadratic minimizer is over feasible
pointwise lotteries with exact constraints

* `E_{-i} v_i(s,x_{-i}) = E_{-i} vtilde_i(s,x_{-i})` for every i and s;
* `E q_k = E qtilde_k` for every alternative k.

The objective is `E_x sum_i v_i(x)^2`. The original allocation is a feasible
witness; the finite polytope is closed and bounded. Continuity gives a minimum.
The critical theorem is that an actual minimum has every `v_i` pointwise
nondecreasing in its own type, provided its prescribed interim marginals are
nondecreasing. Existence of a lifting or monotone minimum cannot be an input.

The published Lemma 1 writes only the uniform perturbation, while Lemma 3
supplies arbitrary laws through a continuous quantile argument. A direct finite
weighted version avoids silently formalizing only Lemma 1:

Fix agent j, types a<b with masses p_a,p_b>0 and opponent profiles y,z with
weights r_y,r_z>0. Suppose `d_y=v_j(a,y)-v_j(b,y)>0`; monotone marginals force
some z with `d_z=v_j(b,z)-v_j(a,z)>0`. Hence y and z are distinct. Put
`rho=p_a/p_b`, `theta_y=epsilon/(r_y*d_y)` and
`theta_z=epsilon/(r_z*d_z)`, choosing epsilon>0 small enough that all four
coefficients `theta_y`, `rho*theta_y`, `theta_z`, `rho*theta_z` lie in (0,1).
At each pair (a,w),(b,w), w=y,z, replace

`q_a'=(1-theta_w)q_a+theta_w q_b`,
`q_b'=(1-rho*theta_w)q_b+rho*theta_w q_a`.

This preserves `p_a q_a+p_b q_b` separately for each opponent profile, so it
preserves all alternative ex ante probabilities and all other agents' interim
slopes. Agent j's a-type slope changes by `-epsilon` at y and `+epsilon` at z
after opponent weighting; its b-type changes cancel after scaling by rho.
Thus all required marginals are preserved. The pair's objective change is

`-p_a*r_w*theta_w*(2-(1+rho)*theta_w)*||v_a-v_b||^2`.

It is strictly negative, since `theta_w < min(1,1/rho)` implies
`(1+rho)*theta_w < 2`, and the j-coordinate difference is nonzero. This proves
the contradiction using actual arbitrary finite masses and feasible convex
mixing. Four distinct profile updates and dependent-function fibers need care
in Lean, especially when preserving another agent's interim marginal.

## Discrete transfers and all-report IC

The modified transfer is `tau_i=t_i+sum_k c_i^k q_k`. Write `Ttilde_i` for its
interim expectation. The adjacent Bayesian IC constraints are

`(Vtilde_n-Vtilde_{n-1}) x_{n-1} <= Ttilde_{n-1}-Ttilde_n`
`<= (Vtilde_n-Vtilde_{n-1}) x_n`.

The exact p.206 formula is

`alpha_n=(Ttilde_{n-1}-Ttilde_n)/(Vtilde_n-Vtilde_{n-1})`

when the denominator is **nonzero**, and `alpha_n=x_n` otherwise. BIC gives
`x_{n-1} <= alpha_n <= x_n`; when the denominator vanishes, BIC also gives
`Ttilde_{n-1}=Ttilde_n`.

`tau_n(y)=tau_1(y)-sum_{m=2}^n (v_m(y)-v_{m-1}(y))*alpha_m`.

The source base is `tau_1(y)=(v_1(y)/Vtilde_1)*Ttilde_1`, with the earlier
footnote's `0/0=1` convention. Because a>=0 and all opponent weights are
positive, `Vtilde_1=0` and matched marginals imply `v_1(y)=0` everywhere;
the convention yields the constant base `Ttilde_1` and the correct expectation.
Using the constant base `tau_1(y)=Ttilde_1` always is another mathematically
valid construction for the requested equivalence theorem. It does not reproduce
the source's extra ex post individual-rationality property. If that simpler
construction is used, document the alteration rather than claiming formula (5)
including its base is literally reproduced.

Adjacent DIC follows since `v_n-v_{n-1}>=0` and alpha is between its two types.
Full DIC must be proved by summing adjacent inequalities: for true type r and
report s>r, every intermediate alpha_m>=x_r, and for s<r every intermediate
alpha_m<=x_r. Telescoping v and tau gives the actual truthful-report payoff
inequality, not merely adjacent IC. Taking the opponent expectation of tau and
using the definition of alpha telescopes to `Ttilde_n`. This last equality in
the zero-denominator case uses `Ttilde_{n-1}=Ttilde_n`, without division by zero.

Ex ante surplus is `E sum_{i,k} q_k(x)(a_i^k x_i+c_i^k)`. Matching every
own-type slope marginal preserves its `a*x` term; matching every alternative's
ex ante probability preserves the `c` term. Matching interim utilities also
then implies matching each agent's ex ante original monetary transfers.

## Support and null types

The finite source theorem is naturally formalized on strictly positive support
types. Every arbitrary finite probability law can be restricted to its support
subtype with induced ordered real types; arbitrary real positive weights remain
allowed. This is an honest arbitrary-distribution theorem on source supports.
The source does not demand claims for extra, zero-mass labels outside support.
If the API retains such labels, spell out whether BIC and preserved utility are
support-only and whether DIC is asserted only on support report profiles.

Do not assert all-label monotonicity of every quadratic minimum when null labels
are present: the objective ignores zero-probability profiles, so a minimizing
allocation may be arbitrarily nonmonotone there. Preserving every interim slope
at an extra zero-mass own-type also adds constraints absent from the source.
An all-label theorem requires a genuine monotone extension proof and a separate
argument preserving that label's utility. The support reduction itself must not
be presented as proving the stronger off-support claim.

## Checked infrastructure and current pins

Read `/Users/arthur/.codex/AGENTS.md` (empty) and relevant memory entries. Memory
warns that proof/kernel/render passing alone does not justify mathematical
readiness, that immutable exact SHA evidence matters, and that toolchain drift
requires explicit repair. Inspected read-only reference trees:

* `/Users/arthur/Documents/Codex/2026-10-01/task-7/bayes-correlated-equilibrium-lean`
* `/Users/arthur/Documents/Codex/2026-10-01/task-3/border-auction-feasibility-lean`
* `/Users/arthur/Documents/Codex/2026-10-01/task-3/border-compact-challenge`
* `/Users/arthur/Documents/Codex/2026-10-01/task-2/rochet-cyclic-monotonicity-lean`
* `/Users/arthur/Documents/Codex/2026-10-01/task-7/review-sources/PalomarSubmission`

Live read-only `git ls-remote` confirmed on 2026-10-02:

| Component | Exact currently verified reference |
| --- | --- |
| PalomarSubmission main | `65f0154ed776cd26c224254aa57b379137f28b0d` |
| Mathlib v4.35.0-rc2 | `065356127b1dc0016f66b7283ce0ce2c4055aa55` |
| Verso v4.35.0-rc2 | `9f8096e40b31715b1d8d5997f15a0bd832f7e37d` |
| Lean | `leanprover/lean4:v4.35.0-rc2` |

Live official `toolchains.json` independently reads schema 2, minimum
`v4.35.0-rc2`:
https://raw.githubusercontent.com/PalomarRegistry/PalomarSubmission/main/toolchains.json
The policy imposes a minimum supported Lean, **not** one universally mandatory
Mathlib revision: selected authenticated Mathlib's `lean-toolchain` must exactly
match the project version. The reference Mathlib tag above supplies the correct
matching pinned revision for this build.

Reusable BCE infrastructure: `scripts/authored_declarations.py`,
`scripts/check_package.py`, `scripts/check_challenge_axioms.py`,
`scripts/verification_config.py`, `scripts/verify_metadata.py`,
`scripts/verify.sh`, `.github/workflows/verify.yml`, and
`.github/workflows/render.yml`. Adapt all namespace/file/name/count/hash claims.
An all-authored-declaration transitive audit must cover every actual definition,
theorem, instance, and helper, not only selected public theorems.

The reference Comparator JSON contains only challenge_module, solution_module,
theorem_names, definition_names, and permitted_axioms. Permitted solution axioms
are exactly propext, Quot.sound, Classical.choice. Execution-only kernel commands
are generated outside the submission, using the pinned policy's official config
validator and toolchain-bundled `nanoda_bin` and `con-ron`. The submission's
configuration must not invent submitter-controlled external kernels.
Challenge must be Mathlib-only and have genuine compared definitions; deliberate
reference theorem placeholders are documented and audited separately. Library
and Solution must have no admissions or custom axioms. Names and binders must
elaborate, with library implementation and comparison namespaces separated.

On macOS the reference comparator uses `--inadvisably-no-sandbox`; local evidence
must disclose that fact. Hosted exact-commit Linux bubblewrap and three-kernel
verification remain a later gate after authorized publication.

The exact renderer builds with pinned Verso, performs a trusted core-notation
audit, and runs the unchanged sanitizer. Its per-file cap is 8*1024*1024 bytes,
total bundle cap 25 MiB, and file-count cap 2,000. Keep each resulting HTML page
strictly below 8 MiB with margin. Border's original fully mirrored Challenge
passed mechanical proof checks but produced an oversized page rejected at
sanitize; proof-state rendering can be much larger than the Lean source.
Compact exact contracts avoid repeating long helper proofs. Rendering evidence
must record policy, Verso, source SHA, per-page sizes, and sanitizer success.
Local macOS reproduction does not prove production confinement or hosted success.

## Bounded existing-target search

Read-only local directory-name search of `/Users/arthur/Repos` to depth 2 and
`/Users/arthur/Documents/Codex` to depth 5 found no Gershkov/Goeree/dominant
project. Read-only public GitHub repository inventory for `Arthur742Ramos`
(paginated `gh api users/Arthur742Ramos/repos`) returned the existing AGV, BCE,
Border, Rochet, and VCG projects when filtered by target/relevant names, with no
Gershkov or Goeree repository. Bounded web searches for Gershkov Lean/GGKMS and
this owner yielded no relevant formalization. This is duplicate avoidance,
not a novelty guarantee; repository names do not exhaust code-level prior art.

## Review verdict and open gates

The requested finite support theorem and direct weighted minimizer proof plan
match the primary source's finite result. No uniform-prior, auction, fixed-size,
or optimizer-monotonicity restriction is justified. The mathematical work still
needs a complete checked weighted perturbation/minimum proof, all-report
telescoping IC, support handling and examples. Package, axiom, Comparator,
three-kernel, exact pinned rendering, and hosted Linux gates have not been run
for the new project by this reviewer and are not reported as passing.
