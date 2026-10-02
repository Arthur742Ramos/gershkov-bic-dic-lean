module
public import Gershkov.Mechanism

@[expose] public section

/-!
# Explicit finite regression certificates

The two-agent example has unequal probabilities on both agents' two-point
supports. Its original allocation is feasible and BIC, but not DIC. The
displayed replacement is feasible and DIC, with identical weighted slope
marginals, modified transfers, alternative probabilities, and surplus.
These are explicit matrix/scalar certificates using the library's `Feasible`
and `Transfers.ScalarIC`, rather than an invocation of the existence theorem.
On-alternative constants `2` and `-1` give the surplus term `+1` below.
-/

namespace Gershkov.Examples

open scoped BigOperators

noncomputable def types : Fin 2 → ℝ := ![0, 1]
noncomputable def firstPrior : Fin 2 → ℝ := ![1 / 3, 2 / 3]
noncomputable def secondPrior : Fin 2 → ℝ := ![1 / 4, 3 / 4]

noncomputable def original : Fin 2 → Fin 2 → ℝ :=
  ![![4 / 5, 1 / 10], ![1 / 5, 4 / 5]]

noncomputable def lifted : Fin 2 → Fin 2 → ℝ :=
  ![![3 / 20, 19 / 60], ![21 / 40, 83 / 120]]

noncomputable def firstSlope : Fin 2 → ℝ := ![11 / 40, 13 / 20]
noncomputable def secondSlope : Fin 2 → ℝ := ![2 / 5, 17 / 30]
noncomputable def firstTransfer : Fin 2 → ℝ := ![0, -(3 / 16)]
noncomputable def secondTransfer : Fin 2 → ℝ := ![0, -(1 / 12)]

noncomputable def allocation (Q : Fin 2 → Fin 2 → ℝ)
    (x : Fin 2 × Fin 2) (k : Fin 2) : ℝ :=
  if k = 0 then Q x.1 x.2 else 1 - Q x.1 x.2

theorem priors_positive_normalized :
    (∀ r, 0 < firstPrior r) ∧ (∀ s, 0 < secondPrior s) ∧
    (∑ r, firstPrior r = 1) ∧ (∑ s, secondPrior s = 1) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r; fin_cases r <;> norm_num [firstPrior]
  · intro s; fin_cases s <;> norm_num [secondPrior]
  · norm_num [firstPrior, Fin.sum_univ_two]
  · norm_num [secondPrior, Fin.sum_univ_two]

theorem types_strictMono : StrictMono types := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro k
  fin_cases k
  norm_num [types]

theorem allocations_feasible : Feasible (allocation original) ∧ Feasible (allocation lifted) := by
  constructor <;> constructor
  · rintro ⟨r, s⟩ k
    fin_cases r <;> fin_cases s <;> fin_cases k <;> norm_num [allocation, original]
  · rintro ⟨r, s⟩
    simp [allocation, Fin.sum_univ_two]
  · rintro ⟨r, s⟩ k
    fin_cases r <;> fin_cases s <;> fin_cases k <;> norm_num [allocation, lifted]
  · rintro ⟨r, s⟩
    simp [allocation, Fin.sum_univ_two]

theorem weighted_marginals :
    (∀ r, ∑ s, secondPrior s * original r s = firstSlope r) ∧
    (∀ s, ∑ r, firstPrior r * original r s = secondSlope s) ∧
    (∀ r, ∑ s, secondPrior s * lifted r s = firstSlope r) ∧
    (∀ s, ∑ r, firstPrior r * lifted r s = secondSlope s) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r; fin_cases r <;> norm_num [original, secondPrior, firstSlope, Fin.sum_univ_two]
  · intro s; fin_cases s <;> norm_num [original, firstPrior, secondSlope, Fin.sum_univ_two]
  · intro r; fin_cases r <;> norm_num [lifted, secondPrior, firstSlope, Fin.sum_univ_two]
  · intro s; fin_cases s <;> norm_num [lifted, firstPrior, secondSlope, Fin.sum_univ_two]

theorem original_bic :
    Transfers.ScalarIC types firstSlope firstTransfer ∧
    Transfers.ScalarIC types secondSlope secondTransfer := by
  constructor <;> intro r s <;> fin_cases r <;> fin_cases s <;>
    norm_num [types, firstSlope, secondSlope, firstTransfer, secondTransfer]

/-- A genuine pointwise deviation: high agent 1 wants to report low against low agent 2. -/
theorem original_not_dic :
    ¬ Transfers.ScalarIC types (fun r => original r 0) firstTransfer := by
  intro h
  have hh := h 1 0
  norm_num [types, original, firstTransfer] at hh

theorem lifted_dic :
    (∀ s, Transfers.ScalarIC types (fun r => lifted r s) firstTransfer) ∧
    (∀ r, Transfers.ScalarIC types (fun s => lifted r s) secondTransfer) := by
  constructor
  · intro s r r'
    fin_cases s <;> fin_cases r <;> fin_cases r' <;> norm_num [types, lifted, firstTransfer]
  · intro r s s'
    fin_cases r <;> fin_cases s <;> fin_cases s' <;> norm_num [types, lifted, secondTransfer]

theorem exAnte_on_probability :
    (∑ r, ∑ s, firstPrior r * secondPrior s * original r s) = 21 / 40 ∧
    (∑ r, ∑ s, firstPrior r * secondPrior s * lifted r s) = 21 / 40 := by
  norm_num [firstPrior, secondPrior, original, lifted, Fin.sum_univ_two]

/-- Both agents value the on alternative with slope one. On constants sum to one. -/
noncomputable def constantSurplus (Q : Fin 2 → Fin 2 → ℝ) : ℝ :=
  ∑ r, ∑ s, firstPrior r * secondPrior s * ((types r + types s + 1) * Q r s)

theorem nonzero_constants_surplus :
    constantSurplus original = 83 / 60 ∧ constantSurplus lifted = 83 / 60 := by
  norm_num [constantSurplus, firstPrior, secondPrior, types, original, lifted, Fin.sum_univ_two]

theorem interim_utilities_equal :
    (∀ r, types r * (∑ s, secondPrior s * original r s) + firstTransfer r =
      types r * (∑ s, secondPrior s * lifted r s) + firstTransfer r) ∧
    (∀ s, types s * (∑ r, firstPrior r * original r s) + secondTransfer s =
      types s * (∑ r, firstPrior r * lifted r s) + secondTransfer s) := by
  constructor
  · intro r; rw [weighted_marginals.1 r, weighted_marginals.2.2.1 r]
  · intro s; rw [weighted_marginals.2.1 s, weighted_marginals.2.2.2 s]

/-- Flat adjacent marginals force flat modified transfers; the upper-type fallback is defined. -/
theorem flat_coefficient :
    Transfers.ScalarIC types (![2, 2]) (![3, 3]) ∧
    Transfers.coefficient types (![2, 2]) (![3, 3]) (0 : Fin 1) = 1 := by
  constructor
  · intro r s; fin_cases r <;> fin_cases s <;> norm_num [types]
  · norm_num [Transfers.coefficient, types]

noncomputable def negativeTypes : Fin 2 → ℝ := ![-3, -1]

/-- The adjacent coefficient is allowed to be negative when both ordered scalar types are. -/
theorem negative_types_ic :
    StrictMono negativeTypes ∧
    Transfers.ScalarIC negativeTypes (![0, 1]) (![0, 2]) ∧
    Transfers.coefficient negativeTypes (![0, 1]) (![0, 2]) (0 : Fin 1) = -2 := by
  refine ⟨?_, ?_, ?_⟩
  · apply Fin.strictMono_iff_lt_succ.mpr
    intro k; fin_cases k; norm_num [negativeTypes]
  · intro r s; fin_cases r <;> fin_cases s <;> norm_num [negativeTypes]
  · norm_num [Transfers.coefficient, negativeTypes]

/-- A one-point support is included by `n = 0`; there are no adjacent edges. -/
theorem singleton_transfer (v : Fin 1 → ℝ) (b : ℝ) (r : Fin 1) :
    Transfers.transfer (fun k : Fin 0 => Fin.elim0 k) v b r = b := by
  have hr : r = 0 := Fin.eq_zero r
  subst r
  exact Transfers.transfer_zero _ _ _

end Gershkov.Examples
