# Independent mathematical review: finite GGKMS Theorem 2

Reviewer: separate mathematical review agent, before implementation. Date: 2026-10-02.

This report reviews the published mathematical claim and a direct finite weighted proof. It does not certify a Lean development or submission gates that have not yet been run.

## Exact source and scope

The supplied source is Gershkov, Goeree, Kushnir, Moldovanu, and Shi, *On the Equivalence of Bayesian and Dominant Strategy Implementation*, Econometrica 81(1), January 2013, pp. 197–220, DOI 10.3982/ECTA10592. Local file: `sources/2012004913OK.pdf`. SHA-256: `bbdfb4d6df83c7e979a48e809e32c52f36f2e8800b8b06fe2a30cb4029c9223c`. Original URL: <https://opus.lib.uts.edu.au/bitstream/10453/27834/1/2012004913OK.pdf>. Theorem 2 is printed on p. 206 (PDF page 10); its proof is on pp. 217–218. The model is on pp. 199–200; discrete incentive constraints are on p. 205. A visual rendering of p. 206 is saved as `reviews/source-p206.png` to disambiguate the PDF's text extraction.

The finite specialization is as follows:

* There are finitely many agents and finitely many social alternatives. Each agent has a nonempty finite set of distinct scalar types, strictly ordered by their real values. Cardinalities may differ across agents and are not fixed constants.
* Types are private and independently distributed. Each marginal distribution is arbitrary; there is no equal-mass or rational-mass assumption.
* The source calls `X_i` the **support** of the distribution. On a finite support each listed type therefore has strictly positive mass. The probability vector sums to one. Positivity is a source-support condition, not a uniformity restriction.
* Utility at alternative `k` is `a_i^k t_i + c_i^k + transfer_i`, with real `c_i^k`, real `a_i^k ≥ 0`, and unrestricted real monetary transfers. The source uses `x_i` for the scalar type and `t_i` for the transfer; avoiding that clash in Lean is useful.
* At each report profile the alternative probabilities are nonnegative and sum to one. General random social choice is allowed. No auction-specific feasibility is assumed, and transfers need not balance ex post.
* BIC means truth maximizes expected utility against the independent distribution of other agents for every own support type and every own support report. DIC means truth maximizes utility for every own support type, own support report, and opponents' report profile in their support product.
* The conclusion preserves every support type's truthful interim expected utility and ex ante expected social surplus. The construction also preserves each agent's interim expected slope and modified transfer, each alternative's ex ante probability, and each agent's ex ante expected actual transfer. It does **not** promise preservation of every alternative's interim allocation probability; the paper expressly discusses failure of that stronger claim.

The exact theorem asserts that any solution of optimization problem (1), with the displayed transfers (5), provides an equivalent DIC mechanism. A formal existence theorem proved by constructing a minimizer and transfers is the intended finite equivalence claim. If the library additionally asserts that **every** minimizer is monotone, its hypotheses must include positive mass on every modeled support profile.

### Null types

A finite probability measure may be given on a larger ambient finite set with some zero masses. The faithful source domain is the subtype of positive-mass elements. Restricting to this subtype preserves all ex ante expectations, and all interim expectations for each support type, since omitted summands vanish. A support-restriction theorem should establish those identities explicitly.

Quantifying BIC/DIC over the support product is honest. It does not mean DIC has been established for extra zero-mass reports from a larger ambient domain, nor that every ambient null type's utility was preserved. The source's use of `L∞(λ)` identifies functions equal almost everywhere, so an arbitrary optimizer can be altered on null profiles without changing its objective or ex ante constraints. Consequently one must not claim pointwise monotonicity for all ambient null profiles from the positive-support minimizer proof alone. Either restrict the formal domain explicitly to support, as the paper does, or prove a separate extension theorem before making that stronger claim.

No assumption that agents' types are nonnegative is needed. Strict ordering suffices, and the adjacent IC algebra works with negative real type values.

## Direct arbitrary-weight lifting proof

Let `T = ∏_i T_i` be the support profile space and `w(t)=∏_i p_i(t_i)>0`. Set

`v_i(t) = Σ_k a_i^k q_k(t)`

and `V_i(r)=Σ_y w_{-i}(y) v_i(r,y)`. Optimize

`F(q) = Σ_t w(t) Σ_i v_i(t)^2`

subject to simplex feasibility at each profile, `V_i = Ṽ_i` at every type, and `Σ_t w(t) q_k(t)=Σ_t w(t) q̃_k(t)` for every alternative. These are finite linear equalities and inequalities. The original allocation is feasible, so the constraint set is nonempty. Every simplex coordinate lies in `[0,1]`; closedness plus finite dimension gives compactness. The quadratic polynomial is continuous and hence attains a minimum. No optimizer property may be assumed: monotonicity must follow from the following explicit contradiction.

Fix agent `j`, distinct ordered types `r<s`, and a context `y` with

`d = v_j(r,y)-v_j(s,y)>0`.

BIC gives `Ṽ_j(r)≤Ṽ_j(s)`, so the equality constraints imply `Σ_u w_{-j}(u)[v_j(s,u)-v_j(r,u)]≥0`. Since the summand at `y` is strictly negative and its weight is strictly positive, some context `z` has

`e=v_j(s,z)-v_j(r,z)>0`.

In particular `z≠y`. The four modified profiles are therefore distinct. Define

`p=p_j(r)>0`, `h=p_j(s)>0`, `μ=w_{-j}(y)>0`, `ν=w_{-j}(z)>0`.

Choose `η>0` smaller than each of `p μ d`, `h μ d`, `p ν e`, `h ν e`; for example half their finite minimum. Put

`α=η/(p μ d)`, `β=η/(h μ d)`, `γ=η/(p ν e)`, `δ=η/(h ν e)`.

Then all four coefficients lie strictly between zero and one. For allocation vectors `A=q(r,y)`, `B=q(s,y)`, `C=q(r,z)`, `D=q(s,z)`, set

```
A' = (1-α) A + α B
B' = (1-β) B + β A
C' = (1-γ) C + γ D
D' = (1-δ) D + δ C
```

Leave all other profiles unchanged. Each modified allocation is a convex combination of two feasible allocations, so feasibility holds. These mixing coefficients are different when the own-type masses differ: the uniform swap from Lemma 1 must not be reused unchanged.

The identities

`p α = h β`, `p γ = h δ`, and `μ α d = ν γ e`

are the complete marginal-preservation mechanism:

1. At each fixed context, the own-type-weighted allocation vector is unchanged: `p A'+h B'=p A+h B` and `p C'+h D'=p C+h D`. Thus every alternative's ex ante probability is unchanged.
2. For an agent `i≠j`, conditioning on its own type leaves both members of each `j`-pair in the same conditional fiber. Their opponents' weights differ by the factors `p` and `h`; the other coordinate weights are equal. The vector cancellations above therefore preserve that agent's slope marginal, even when `y` and `z` differ in several opponent coordinates or agree at `i`.
3. For agent `j` at own type `r`, the slope change is `-μ α d+ν γ e=0`. At own type `s`, it is `μ β d-ν δ e=0`, using `β=(p/h)α` and `δ=(p/h)γ`. All other own types are unchanged.

Let `u=A_slope-B_slope` denote the full agent-slope vector `A·q(r,y)-A·q(s,y)` (here the first `A` is the source's coefficient matrix), and similarly let `zvec=D_slope-C_slope`. Direct expansion of the weighted squared norms gives

```
F(q') - F(q)
 = -μ p α (2-α-β) Σ_i u_i²
   -ν p γ (2-γ-δ) Σ_i zvec_i².
```

For clarity, the first pair calculation is

`p||U-α(U-W)||²+h||W+β(U-W)||² - p||U||²-h||W||²`

`= [-2pα+pα²+hβ²]||U-W||²`

`= -pα(2-α-β)||U-W||²`, because `pα=hβ`.

Both factors `2-α-β` and `2-γ-δ` are positive; both squared-vector sums are strictly positive because their `j` components are respectively `d` and `e`, both positive. All weight factors are positive. Thus `F(q')<F(q)`, contradicting minimization. This proves pointwise monotonicity for arbitrary finite positive marginal weights.

The proof uses independence in the paired conditional-weight cancellations. It must not be generalized to arbitrary correlated joint measures.

## Incentive constraints and transfers

Absorb constants into modified transfers:

`τ_i(t)=transfer_i(t)+Σ_k c_i^k q_k(t)`.

The utility of true scalar type `r` reporting `s` is then `r v_i(s,y)+τ_i(s,y)`. Write `Ṫ_n` for the original BIC modified interim transfer at ordered type `x_n`, and `V_n` for its slope marginal. The full BIC inequalities at adjacent types imply

`x_{n-1}(V_n-V_{n-1}) ≤ Ṫ_{n-1}-Ṫ_n ≤ x_n(V_n-V_{n-1})`.

Adding the two relevant BIC inequalities yields `(x_n-x_{n-1})(V_n-V_{n-1})≥0`; strict ordering gives `V_n≥V_{n-1}`. For `ΔV_n>0`, define

`α_n=(Ṫ_{n-1}-Ṫ_n)/ΔV_n`.

For `ΔV_n=0`, the displayed adjacent inequalities force `Ṫ_{n-1}=Ṫ_n`; set `α_n=x_n`, as in the source. In both cases

`x_{n-1}≤α_n≤x_n` and `Ṫ_{n-1}-Ṫ_n=α_n ΔV_n`.

The source's PDF text extraction drops the slash on `≠` in the denominator case. The p. 206 image confirms the ratio is used for **unequal** marginals, and the fallback is used for equal marginals.

For the monotone lifted slopes, choose any base function `b_i(y)` with expected value `Ṫ_0`, then set

`τ_i(x_n,y)=b_i(y)-Σ_{m=1}^n α_m[v_i(x_m,y)-v_i(x_{m-1},y)]`.

The source uses `b_i(y)=(v_i(x_0,y)/V_0)Ṫ_0` with `0/0` interpreted as one. For positive `V_0`, marginal matching proves its expectation is `Ṫ_0`. For `V_0=0`, nonnegative coefficients imply each `v_i(x_0,y)≥0`; positive opponent weights and zero expectation force each slope to be zero, so the convention gives `b_i(y)=Ṫ_0`. A constant base `b_i(y)=Ṫ_0` gives the same existential utility/surplus theorem and avoids this auxiliary division. If using the constant base, documentation should state this harmless alternative rather than claim to reproduce the displayed source base. No individual-rationality enhancement is claimed by the basic constant-base proof.

Adjacent transfer differences are exactly `α_n Δv_n(y)`. Since `Δv_n(y)≥0` and `x_{n-1}≤α_n≤x_n`, they satisfy the two adjacent DIC inequalities. To prove full DIC, do not assume adjacent constraints suffice: telescope. For any `p<q`,

`τ_p(y)-τ_q(y)=Σ_{m=p+1}^q α_m Δv_m(y)`

and `v_q(y)-v_p(y)=Σ_{m=p+1}^q Δv_m(y)`.

Each `α_m` is between `x_p` and `x_q`, so

`x_p(v_q-v_p)≤τ_p-τ_q≤x_q(v_q-v_p)`.

These two bounds are exactly the low-to-high and high-to-low deviation inequalities. Equality of reports is immediate. Arbitrary negative type values cause no issue because the multiplied slope increments are nonnegative.

Taking expectations in the transfer formula and using `E b_i=Ṫ_0` and matched slope marginals gives

`E τ_i(x_n,·)=Ṫ_0-Σ_{m=1}^n α_m ΔV_m=Ṫ_0-Σ_{m=1}^n(Ṫ_{m-1}-Ṫ_m)=Ṫ_n`.

Thus truthful interim utilities are preserved. Finally define actual transfer by `transfer_i=τ_i-Σ_k c_i^k q_k`. Ex ante social surplus is

`Σ_i Σ_n p_i(x_n) x_n V_i(x_n) + Σ_k (Σ_i c_i^k) E q_k`.

Matched marginals preserve the first term and matched ex ante alternative probabilities preserve the second, including arbitrary nonzero constants. Equivalently, matched modified transfers and ex ante alternative probabilities preserve each agent's expected actual transfer.

## Meaningful unequal-weight example

Two agents have types `0<1`. Agent 1's low/high probabilities are `1/3,2/3`; agent 2's are `1/4,3/4`. There are two alternatives, on/off; each agent's on slope is one and off slope is zero. The original on-allocation matrix, with agent 1 on rows and agent 2 on columns, is

```
          low 2   high 2
low 1      4/5     1/10
high 1     1/5      4/5
```

Agent 1's marginals are `11/40,13/20`, a difference `3/8`; agent 2's are `2/5,17/30`, a difference `1/6`. Choose modified transfers zero for low reports and respectively `-3/16` and `-1/12` for high reports. The adjacent coefficients are both `1/2`, so the mechanism is BIC. It is not DIC: agent 1's slope falls from `4/5` to `1/5` when agent 2 reports low.

The lifted on matrix

```
           low 2   high 2
low 1      3/20    19/60
high 1     21/40   83/120
```

is feasible, monotone in both coordinates, and preserves both slope marginals. It is the additive marginal solution `q_on(r,y)=V_1(r)+V_2(y)-21/40`, which lies inside `[0,1]`; the original and lifted ex ante on probability is `21/40`. Own slope differences are constant (`3/8` for agent 1 and `1/6` for agent 2), so the same modified transfers are DIC for the lifted rule. Arbitrary alternative constants can be added with actual transfers adjusted by `-Σ c_i^k q_k`; for example on constants `2` and `-1`, off constants zero, give an example exercising the constants in surplus preservation.

Additional useful tests include a singleton-type agent, a zero coefficient row, flat adjacent marginals and transfers, negative type values, unequal numbers of types, and explicit removal of a zero-mass ambient label.

## Formal obligations that must remain theorem conclusions

The central proof obligations are: weighted feasible-polytope compactness and existence of a minimizer; BIC-to-marginal monotonicity; positive crossing-context extraction; four-profile distinctness; convex feasibility; every weighted marginal cancellation; exact weighted quadratic expansion and strict decrease; adjacent coefficient bounds including zero marginal difference; full telescoping IC; transfer expectation telescoping; and surplus identity with constants. None may be replaced by assumptions named `MonotoneLifting`, `OptimizerMonotone`, or equivalent. Positive-mass support restriction must appear visibly in the final binders or in an explicit support subtype.

The direct finite weighted proof above is mathematically valid and proves the requested finite support equivalence without a uniform-distribution restriction. It supplies a cleaner finite proof than the source's quantile passage: the appendix's discrete theorem proof cites Lemma 1 (the uniform lemma), while general distributions require its Lemma 3 or this weighted replacement. This citation mismatch should not be propagated as a proof assumption. The source's general `L∞` and quantile proof also must not be treated as a shortcut to arbitrary pointwise null-profile assertions.

This review is complete for the source statement and proposed finite mathematical proof. A later independent audit must compare the actual final Lean binders and theorem dependencies with these contracts; this report alone is not that audit.
