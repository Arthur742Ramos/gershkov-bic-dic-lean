module
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Tactic

@[expose] public section
open scoped BigOperators
namespace Gershkov
universe uP uK uI
variable {P : Type uP} {K : Type uK} {I : Type uI}
variable [Fintype P] [DecidableEq P] [Fintype K] [Fintype I]

noncomputable def value (a : I → K → ℝ) (q : P → K → ℝ) (i : I) (x : P) : ℝ :=
  ∑ k, a i k * q x k

def Feasible (q : P → K → ℝ) : Prop :=
  (∀ x k, 0 ≤ q x k) ∧ (∀ x, ∑ k, q x k = 1)

noncomputable def energy (μ : P → ℝ) (a : I → K → ℝ) (q : P → K → ℝ) : ℝ :=
  ∑ x, μ x * ∑ i, (value a q i x) ^ 2

/-- A weighted two-cell averaging. The same joint probability mass δ moves in both directions. -/
noncomputable def mixPair (μ : P → ℝ) (q : P → K → ℝ) (l r : P) (δ : ℝ) : P → K → ℝ :=
  fun x k => if x = l then (1 - δ / μ l) * q l k + (δ / μ l) * q r k
    else if x = r then (1 - δ / μ r) * q r k + (δ / μ r) * q l k else q x k

theorem sum_change_two (l r : P) (hlr : l ≠ r) (f g : P → ℝ)
    (h : ∀ x, x ≠ l → x ≠ r → g x = f x) :
    (∑ x, g x) - ∑ x, f x = (g l - f l) + (g r - f r) := by
  rw [← Finset.sum_sub_distrib]
  calc
    _ = ∑ x, ((if x = l then g l - f l else 0) +
        (if x = r then g r - f r else 0)) := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : x = l
      · subst x; simp [hlr]
      · by_cases hy : x = r
        · subst x; simp [hx]
        · simp [hx, hy, h x hx hy]
    _ = _ := by simp [Finset.sum_add_distrib]

theorem mixPair_left (μ : P → ℝ) (q : P → K → ℝ) (l r : P) (δ : ℝ) (k : K) :
    mixPair μ q l r δ l k = (1 - δ / μ l) * q l k + (δ / μ l) * q r k := by
  simp [mixPair]

theorem mixPair_right (μ : P → ℝ) (q : P → K → ℝ) (l r : P) (hlr : l ≠ r)
    (δ : ℝ) (k : K) :
    mixPair μ q l r δ r k = (1 - δ / μ r) * q r k + (δ / μ r) * q l k := by
  simp [mixPair, Ne.symm hlr]

theorem mixPair_other (μ : P → ℝ) (q : P → K → ℝ) (l r x : P)
    (hxl : x ≠ l) (hxr : x ≠ r) (δ : ℝ) : mixPair μ q l r δ x = q x := by
  funext k; simp [mixPair, hxl, hxr]

theorem value_mixPair_left (μ : P → ℝ) (a : I → K → ℝ) (q : P → K → ℝ)
    (l r : P) (δ : ℝ) (i : I) :
    value a (mixPair μ q l r δ) i l =
      (1 - δ / μ l) * value a q i l + (δ / μ l) * value a q i r := by
  simp only [value, mixPair_left, mul_add, Finset.sum_add_distrib]
  simp_rw [← mul_assoc, mul_comm (a i _) (1 - δ / μ l),
    mul_comm (a i _) (δ / μ l), mul_assoc]
  rw [Finset.mul_sum, Finset.mul_sum]

theorem value_mixPair_right (μ : P → ℝ) (a : I → K → ℝ) (q : P → K → ℝ)
    (l r : P) (hlr : l ≠ r) (δ : ℝ) (i : I) :
    value a (mixPair μ q l r δ) i r =
      (1 - δ / μ r) * value a q i r + (δ / μ r) * value a q i l := by
  simp only [value, mixPair_right μ q l r hlr, mul_add, Finset.sum_add_distrib]
  simp_rw [← mul_assoc, mul_comm (a i _) (1 - δ / μ r),
    mul_comm (a i _) (δ / μ r), mul_assoc]
  rw [Finset.mul_sum, Finset.mul_sum]

theorem mixPair_feasible (μ : P → ℝ) (q : P → K → ℝ) (l r : P) (δ : ℝ)
    (hq : Feasible q) (hμl : 0 < μ l) (hμr : 0 < μ r)
    (hδ : 0 ≤ δ) (hδl : δ ≤ μ l) (hδr : δ ≤ μ r) :
    Feasible (mixPair μ q l r δ) := by
  have hu : 0 ≤ δ / μ l := div_nonneg hδ hμl.le
  have hv : 0 ≤ δ / μ r := div_nonneg hδ hμr.le
  have hu' : δ / μ l ≤ 1 := (div_le_one hμl).mpr hδl
  have hv' : δ / μ r ≤ 1 := (div_le_one hμr).mpr hδr
  constructor
  · intro x k
    unfold mixPair
    split_ifs <;> first
    | exact add_nonneg (mul_nonneg (by linarith) (hq.1 _ _))
        (mul_nonneg (by assumption) (hq.1 _ _))
    | exact hq.1 _ _
  · intro x
    unfold mixPair
    split_ifs <;> simp [Finset.sum_add_distrib, ← Finset.mul_sum, hq.2]

/-- The change of every weighted linear moment, including alternative and type marginals. -/
theorem mixPair_moment (μ : P → ℝ) (q : P → K → ℝ) (l r : P) (hlr : l ≠ r)
    (hμl : μ l ≠ 0) (hμr : μ r ≠ 0) (δ : ℝ) (C : P → ℝ) (b : K → ℝ) :
    (∑ x, μ x * C x * ∑ k, b k * mixPair μ q l r δ x k) -
      (∑ x, μ x * C x * ∑ k, b k * q x k) =
      δ * (C l - C r) * ((∑ k, b k * q r k) - ∑ k, b k * q l k) := by
  rw [sum_change_two l r hlr _ _ (by
    intro x hxl hxr; rw [mixPair_other μ q l r x hxl hxr])]
  have h₁ := value_mixPair_left μ (fun _ : Unit => b) q l r δ ()
  have h₂ := value_mixPair_right μ (fun _ : Unit => b) q l r hlr δ ()
  simp only [value] at h₁ h₂
  rw [h₁, h₂]
  field_simp
  <;> ring

theorem mixPair_energy (μ : P → ℝ) (a : I → K → ℝ) (q : P → K → ℝ)
    (l r : P) (hlr : l ≠ r) (hμl : μ l ≠ 0) (hμr : μ r ≠ 0) (δ : ℝ) :
    energy μ a (mixPair μ q l r δ) - energy μ a q =
      -(δ * (2 - δ / μ l - δ / μ r)) * ∑ i, (value a q i l - value a q i r)^2 := by
  unfold energy
  rw [sum_change_two l r hlr _ _ (by
    intro x hxl hxr; simp only [value, mixPair_other μ q l r x hxl hxr])]
  simp_rw [value_mixPair_left, value_mixPair_right μ a q l r hlr]
  simp_rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  field_simp
  <;> ring

theorem mixPair_energy_lt (μ : P → ℝ) (a : I → K → ℝ) (q : P → K → ℝ)
    (l r : P) (hlr : l ≠ r) (hμl : 0 < μ l) (hμr : 0 < μ r)
    (δ : ℝ) (hδ : 0 < δ) (hδl : δ < μ l) (hδr : δ < μ r)
    (j : I) (hj : value a q j l ≠ value a q j r) :
    energy μ a (mixPair μ q l r δ) < energy μ a q := by
  have hsq : 0 < ∑ i, (value a q i l - value a q i r)^2 := by
    apply Finset.sum_pos'
    · intro i _; positivity
    · exact ⟨j, Finset.mem_univ _, sq_pos_of_ne_zero (sub_ne_zero.mpr hj)⟩
  have hu : δ / μ l < 1 := (div_lt_one hμl).mpr hδl
  have hv : δ / μ r < 1 := (div_lt_one hμr).mpr hδr
  have hn : 0 < δ * (2 - δ / μ l - δ / μ r) := mul_pos hδ (by linarith)
  have he := mixPair_energy μ a q l r hlr hμl.ne' hμr.ne' δ
  have hp := mul_neg_of_neg_of_pos (neg_neg_of_pos hn) hsq
  linarith

noncomputable def doubleMix (μ : P → ℝ) (q : P → K → ℝ) (l r s t : P)
    (δ ε : ℝ) : P → K → ℝ := mixPair μ (mixPair μ q l r δ) s t ε

theorem doubleMix_moment (μ : P → ℝ) (q : P → K → ℝ) (l r s t : P)
    (hlr : l ≠ r) (hst : s ≠ t) (hsl : s ≠ l) (hsr : s ≠ r)
    (htl : t ≠ l) (htr : t ≠ r) (hμ : ∀ x, μ x ≠ 0) (δ ε : ℝ)
    (C : P → ℝ) (b : K → ℝ) :
    (∑ x, μ x * C x * ∑ k, b k * doubleMix μ q l r s t δ ε x k) -
      (∑ x, μ x * C x * ∑ k, b k * q x k) =
      δ * (C l - C r) * ((∑ k, b k * q r k) - ∑ k, b k * q l k) +
      ε * (C s - C t) * ((∑ k, b k * q t k) - ∑ k, b k * q s k) := by
  have h₁ := mixPair_moment μ q l r hlr (hμ l) (hμ r) δ C b
  have h₂ := mixPair_moment μ (mixPair μ q l r δ) s t hst (hμ s) (hμ t) ε C b
  rw [mixPair_other μ q l r t htl htr, mixPair_other μ q l r s hsl hsr] at h₂
  change _ at h₂
  unfold doubleMix
  linarith

theorem doubleMix_energy_lt (μ : P → ℝ) (a : I → K → ℝ) (q : P → K → ℝ)
    (l r s t : P) (hlr : l ≠ r) (hst : s ≠ t) (hsl : s ≠ l) (hsr : s ≠ r)
    (htl : t ≠ l) (htr : t ≠ r) (hμ : ∀ x, 0 < μ x) (δ ε : ℝ)
    (hδ : 0 < δ) (hδl : δ < μ l) (hδr : δ < μ r)
    (hε : 0 < ε) (hεs : ε < μ s) (hεt : ε < μ t)
    (j : I) (hj : value a q j l ≠ value a q j r)
    (hj' : value a q j s ≠ value a q j t) :
    energy μ a (doubleMix μ q l r s t δ ε) < energy μ a q := by
  have h₁ := mixPair_energy_lt μ a q l r hlr (hμ l) (hμ r) δ hδ hδl hδr j hj
  have h₂ := mixPair_energy_lt μ a (mixPair μ q l r δ) s t hst (hμ s) (hμ t)
    ε hε hεs hεt j (by
      simp only [value, mixPair_other μ q l r s hsl hsr,
        mixPair_other μ q l r t htl htr] at *
      exact hj')
  exact h₂.trans h₁

end Gershkov
