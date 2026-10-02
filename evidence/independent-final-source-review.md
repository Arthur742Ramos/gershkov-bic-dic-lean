# Independent core mathematical and exact-contract review

Reviewed 2026-10-02 by a separate AI agent. The reviewer did not author the
Gershkov library's mathematical proofs. It did prepare the compact contract
generator and comparison wrappers, so their construction is disclosed rather
than characterized as independently authored packaging. This is not human peer
review, original-author endorsement, or a novelty assessment. The reviewed
source files and hashes are in `independent-final-source-hashes.json`; any later
source change requires reconciling that snapshot and rerunning relevant checks.

## Actual main statement and source assumptions

`GGKMS.finite_bayesian_dominant_equivalence` copies the exact library header of
`Gershkov.finite_bayesian_dominant_equivalence`. Its implicit binders are arbitrary
finite agent and alternative types, decidable equality on agents, and an arbitrary
agent-dependent function `n : I → Nat`. Agent i's report carrier is
`Fin (n i + 1)`. This represents the source's arbitrary heterogeneous ordered
nonempty finite lists; no fixed common cardinality, two-type assumption, or
auction feasibility assumption occurs.

The explicit binders and their source meanings are:

| Binder | Source meaning |
| --- | --- |
| `p` | Agent-dependent real probability masses on each type support |
| `hp : SupportPrior p` | Strictly positive support masses and each marginal sum equal to one |
| `θ` | Scalar real values of the finite type labels |
| `hθ : ∀ i, StrictMono (θ i)` | Source's strictly increasing, distinct type lists |
| `a c` | Arbitrary agent/alternative real slope and constant matrices |
| `_ha` | Every slope is nonnegative, exactly as in the source model |
| `q₀`, `pay₀` | Original pointwise lottery and unrestricted real transfers received |
| `hfeasible` | Pointwise nonnegativity and lottery probabilities summing to one |
| `hBIC` | Every own-type misreport has no higher opponent-weighted expected utility |

Independence is expressed by genuine products of p in `joint` and
`opponentMass`, not by a supplied conditional-law oracle. `BIC` compares all
own reports. `DIC` compares all own reports against every opponent support
profile, so it is dominant-strategy IC rather than only interim or adjacent IC.
All values and transfers are real; c and θ may be negative. The assumption `_ha`
is retained, although this existential construction's constant base allows the
implementation proof to work more generally.

The conclusion gives an actual q and pay satisfying feasibility, full DIC,
every support type's exact interim truthful utility equality, and exact ex ante
social-surplus equality. It additionally preserves all weighted own-type slope
marginals, every alternative's ex ante probability, every modified interim
transfer, and attains the actual constrained quadratic minimum. No monotone
lifting, optimizer property, or transfer existence is assumed in this final
theorem. `Fin (n i + 1)` is an arbitrary finite support indexing convention;
no claim about incentive compatibility at extra zero-mass labels is made.

## Allocation proof checked against the source

`Gershkov.exists_minimizer` proves actual existence. Its feasible set is
closed; nonnegative pointwise lotteries have all entries at most one, yielding
a compact containing box. Exact weighted moment constraints are closed and the
original q is a nonempty witness. The finite quadratic objective is continuous,
so a minimum is attained. There is no assumed quadratic optimizer certificate.

`Gershkov.mixPair` uses real joint probability masses, with δ divided by the
two actual profile masses. Its feasibility lemma proves both convex coefficients
are in [0,1]. `mixPair_moment` explicitly computes changes of arbitrary linear
moments. `mixPair_energy` proves the exact objective difference
`-δ*(2-δ/μ_l-δ/μ_r)*sum_i (v_i(l)-v_i(r))²`; strict improvement requires δ>0,
δ<both profile masses and one nonzero value-coordinate difference.

`Gershkov.improving_perturbation` finds a positive-weight crossing opponent
context from matched nondecreasing interim slopes. It proves the four profiles
are distinct, chooses a sufficiently small positive η, and sets the two joint
mass perturbations to η divided by their respective nonzero slope differences.
The matched own-agent changes cancel; for other agents, the weighted own-type
pair preserves every fiber moment. Alternative moments are constant moments.
Both pair improvements are strict. `minimizer_monotone` contradicts true
minimality using this constructed feasible improving allocation.
`weighted_monotone_lifting` combines actual existence and proved monotonicity.
This is the required weighted finite argument, not the source's uniform Lemma 1
alone. Nonuniform probability masses are neither replaced by equal weights nor
duplicated into an implicitly rational uniform model.

## Transfers, utilities and surplus

`Transfers.coefficient` matches the published p.206 nonzero-denominator ratio
and chooses the upper type when adjacent marginals are equal. Bayesian adjacent
bounds prove the coefficient lies between adjacent types and that its slope
increment product equals the original modified transfer difference, including
the flat branch without division by zero.

`pair_bounds_of_adjacent` inducts along the finite type order to prove bounds
for every pair, and `ic_of_adjacent` covers both report directions.
`scalarIC_iff_monotone_adjacent` is the full finite scalar IC characterization.
The prefix-sum transfer has the exact adjacent increment and its opponent
expectation telescopes to the original modified transfer at every type.
The base modified transfer is the constant original lowest-type interim
modified transfer. This is a valid variation of the source's equation (5) base
with the same expectation. The project correctly makes no claim about the
source's additional ex post individual-rationality property.

`Gershkov.interimPayoff_modified` identifies the actual model payoff with its
scalar slope and modified transfer, so the scalar proof is connected to genuine
model BIC/DIC. `transfers_for_matching_allocation` constructs original monetary
transfers by subtracting the alternative-constant value. `surplus_matches`
preserves the θ*a part using own-type marginals and the c part using alternative
ex ante probabilities. The further `exAnte_transfers_match` corollary subtracts
matched c moments from matched ex ante modified transfers and correctly proves
each agent's actual ex ante monetary transfer also matches.

## Support and examples

`PositiveSupport` is a genuine positive-mass subtype. The named Fintype
instance uses `Subtype.fintype` under classical decidability, not an assumed
support enumeration. `expectation_on_support` proves deletion of null labels
preserves any finite expectation; `support_normalized` proves normalized
nonnegative laws become positive normalized support laws. The product identity
proves full independent expectations agree after deletion. The added
`opponent_expectation_on_support` instantiates that identity on opponents,
covering interim expectations at any fixed retained own type and report.
These theorems do not assert IC or utility preservation at deleted null labels.
This distinction matches the source model, where Xi is the distribution support.

Examples include unequal masses for both agents, explicit feasible original and
replacement matrices with the same weighted slope marginals, a certified BIC
original that fails a pointwise DIC deviation, certified DIC replacement,
interim utilities and surplus with nonzero alternative constants, flat adjacent
marginals, negative real types and negative coefficient, and one-point support.
They are explicit scalar/matrix certificates, not a claim that their displayed
replacement is the particular quadratic minimizer chosen by the main theorem.

## Exact comparison and audit coverage

`scripts/make_challenge.py` extracts genuine declaration bodies and exact
theorem headers from the actual library. Both exports use the separate `GGKMS`
namespace; implementation theorems remain under `Gershkov`. Solution's six
proofs apply complete library theorems, with definitionally equal copied model
definitions. The successful Solution build checks this connection.

Challenge has 26 genuine copied definitions, abbreviations and named instances.
Its only holes are the six selected reference theorem proof bodies, each
explicitly named in Comparator. The exact pinned official policy's
`docs/comparator-declaration-closure.md` allows named Challenge supporting
theorem holes. It does not justify placeholder model definitions; these are
genuine here. The full selected names elaborate, and Challenge's source
dependency output contains only core and Mathlib sources.

The source scanner inventories every explicit library and Solution declaration,
including examples and named instances, and rejects unsupported private or
generated declaration forms. A plain source scanner does not by itself certify
every environment-generated constant. The root's `scripts/EnvironmentAudit.lean`
uses `import all Solution` to include otherwise hidden imported constants and
correctly adds defining-module inventory for Solution, Gershkov and Gershkov.*,
regardless of generated helper naming. It checks every constant's transitive
axioms against propext, Quot.sound and Classical.choice. The final
`evidence/environment-axioms.log` reports an actual pass for 216 unique
constants. This reviewer independently parsed all 216 rows, confirmed permitted
modules and axiom sets, and confirmed that all 158 explicit authored declarations
are included. The other 58 constants include generated equations, proof helpers
and simplification congruences. The reviewed tooling source uses an explicit Nat
counter and a parenthesized quoted-name prefix check; its earlier syntax draft
is replaced in the recorded snapshot. Mathematical library and exact contract
hashes are unchanged from the preceding review.

The copied Lake manifest originally retained the reference project's root name
`bayes_correlated_equilibrium`. It was repaired to `gershkov_equivalence`, matching
the actual lakefile. This reviewer compared its parsed JSON against the original
reference manifest: the only differing top-level key is `name`, and the full
package list and every package field and revision are unchanged. Replacing that
one text value back reconstructs the exact earlier reviewed SHA256. The Mathlib
pin remains `065356127b1dc0016f66b7283ce0ce2c4055aa55`; all nine dependency
revisions are unchanged. This is a package identity repair with no mathematical
or contract-source change. The reviewed snapshot records its new manifest hash.
The normalized environment audit log was rechecked and its refreshed checksum
recorded: it still covers exactly 216 unique constants, all 158 explicit names,
and only the three permitted axioms.

The rewritten README's binder table agrees with the actual main statement,
including unbounded heterogeneous cardinalities, arbitrary real normalized
positive support masses, nonnegative slopes, arbitrary constants and unrestricted
transfers. Its disclosure of the constant modified base, source-support scope,
null-label limitation, and scalar/matrix example representation is accurate.
The formalization metadata gives the same source scope and all six selected
contract names, with the trio authors and maintainers and checked MSC codes.
The citation message now requests immutable-commit evidence without obsolete
work-in-progress wording. Documentation never establishes a gate without its
actual exact-candidate evidence.

## Review verdict and remaining evidence

No mathematical defect, weakened source assumption, hidden optimizer oracle,
uniform-prior restriction, fixed-cardinality restriction, auction restriction,
namespace collision, or off-support claim was found in this inspected snapshot.
The source's finite support theorem is represented accurately, with the disclosed
constant-base transfer variation. Positive support expectation reduction is
explicit; an all-label off-support mechanism theorem is not claimed.

This reviewer observed successful Challenge and Solution builds, selected-name
elaboration, metadata validation, and standard-axiom audit of the then-present
156 explicit authored declarations. Two later corollaries were source-reviewed
above; the final environment audit covers the resulting 158 explicit declarations
and 58 generated constants. The final local Comparator log was also inspected:
it exports all six theorem names and all 26 definition/instance names, reports
acceptance from Lean default, NanoDa and con-ron, and ends with the successful
Comparator verdict. It explicitly warns that sandboxing is disabled on macOS;
this is local kernel evidence, not Linux confinement evidence.

The local pinned rendering report identifies the unchanged Challenge hash,
official policy and Verso revisions, 32 trusted audited declarations, and
successful rendering with `Challenge/index.html` at 437,749 bytes (well below
8,388,608) and the search page at 31,467 bytes. Its own scope correctly excludes
Linux sandbox and hosted-workflow claims. The root has recorded the unchanged
official sanitizer's successful local execution separately.

These observations do not stand in for the final exact-source manifest and
archive, or exact-commit hosted Linux proof and sanitized rendering evidence.
Those are separate gates and must be supported by their actual logs. No
publication, actual Palomar intake, registration, human review or novelty
conclusion is asserted by this report.
