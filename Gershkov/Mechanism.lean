module
public import Gershkov.Model
public import Gershkov.Transfers

@[expose] public section
open scoped BigOperators
namespace Gershkov
universe uI uK
variable {I : Type uI} [Fintype I] [DecidableEq I]
variable {K : Type uK} [Fintype K]
variable {n : I → ℕ}
abbrev Types (n : I → ℕ) (i : I) := Fin (n i + 1)

noncomputable def modified (c : I → K → ℝ) (q : Profile (Types n) → K → ℝ)
    (pay : I → Profile (Types n) → ℝ) (i : I) (x : Profile (Types n)) : ℝ :=
  pay i x + value c q i x

/-- Expected private value plus monetary transfer when true type `t` reports `r`.
Opponent profiles range over the full finite support product. -/
noncomputable def payoff (θ : ∀ i, Types n i → ℝ) (a c : I → K → ℝ)
    (q : Profile (Types n) → K → ℝ) (pay : I → Profile (Types n) → ℝ)
    (i : I) (t r : Types n i) (y : Opponents (Types n) i) : ℝ :=
  θ i t * value a q i (pack i r y) + value c q i (pack i r y) + pay i (pack i r y)

noncomputable def interimPayoff (p θ : ∀ i, Types n i → ℝ) (a c : I → K → ℝ)
    (q : Profile (Types n) → K → ℝ) (pay : I → Profile (Types n) → ℝ)
    (i : I) (t r : Types n i) : ℝ :=
  ∑ y, opponentMass p i y * payoff θ a c q pay i t r y

def BIC (p θ : ∀ i, Types n i → ℝ) (a c : I → K → ℝ)
    (q : Profile (Types n) → K → ℝ) (pay : I → Profile (Types n) → ℝ) : Prop :=
  ∀ i t r, interimPayoff p θ a c q pay i t r ≤ interimPayoff p θ a c q pay i t t

def DIC (θ : ∀ i, Types n i → ℝ) (a c : I → K → ℝ)
    (q : Profile (Types n) → K → ℝ) (pay : I → Profile (Types n) → ℝ) : Prop :=
  ∀ i y t r, payoff θ a c q pay i t r y ≤ payoff θ a c q pay i t t y

noncomputable def modifiedInterim (p : ∀ i, Types n i → ℝ) (c : I → K → ℝ)
    (q : Profile (Types n) → K → ℝ) (pay : I → Profile (Types n) → ℝ)
    (i : I) (t : Types n i) : ℝ := interim p (modified c q pay i) i t

theorem payoff_modified (θ : ∀ i, Types n i → ℝ) (a c : I → K → ℝ)
    (q : Profile (Types n) → K → ℝ) (pay : I → Profile (Types n) → ℝ)
    (i : I) (t r : Types n i) (y : Opponents (Types n) i) :
    payoff θ a c q pay i t r y = θ i t * value a q i (pack i r y) +
      modified c q pay i (pack i r y) := by
  unfold payoff modified
  ring

theorem interimPayoff_modified (p θ : ∀ i, Types n i → ℝ) (a c : I → K → ℝ)
    (q : Profile (Types n) → K → ℝ) (pay : I → Profile (Types n) → ℝ)
    (i : I) (t r : Types n i) :
    interimPayoff p θ a c q pay i t r =
      θ i t * slope p a q i r + modifiedInterim p c q pay i r := by
  simp only [interimPayoff, payoff_modified, mul_add, Finset.sum_add_distrib,
    slope, modifiedInterim, interim, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro y _
  ring

theorem bic_scalar (p θ : ∀ i, Types n i → ℝ) (a c : I → K → ℝ)
    (q : Profile (Types n) → K → ℝ) (pay : I → Profile (Types n) → ℝ)
    (h : BIC p θ a c q pay) (i : I) :
    Transfers.ScalarIC (θ i) (slope p a q i) (modifiedInterim p c q pay i) := by
  intro t r
  simpa only [interimPayoff_modified] using h i t r

noncomputable def socialSurplus (p θ : ∀ i, Types n i → ℝ) (a c : I → K → ℝ)
    (q : Profile (Types n) → K → ℝ) : ℝ :=
  exAnte p (fun x => ∑ i, (θ i (x i) * value a q i x + value c q i x))

theorem exAnte_value (p : ∀ i, Types n i → ℝ) (b : I → K → ℝ)
    (q : Profile (Types n) → K → ℝ) (i : I) :
    exAnte p (value b q i) = ∑ k, b i k * exAnte p (fun x => q x k) := by
  unfold exAnte value
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem exAnte_typeValue (p θ : ∀ i, Types n i → ℝ) (a : I → K → ℝ)
    (q : Profile (Types n) → K → ℝ) (i : I) :
    exAnte p (fun x => θ i (x i) * value a q i x) =
      ∑ t, p i t * (θ i t * slope p a q i t) := by
  rw [exAnte_interim p _ i]
  simp only [interim, pack_self, slope]
  apply Finset.sum_congr rfl
  intro t _
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ring

theorem surplus_matches (p θ : ∀ i, Types n i → ℝ) (a c : I → K → ℝ)
    (q q₀ : Profile (Types n) → K → ℝ) (hq : Matches p a q q₀) :
    socialSurplus p θ a c q = socialSurplus p θ a c q₀ := by
  unfold socialSurplus exAnte
  simp_rw [Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp_rw [mul_add, Finset.sum_add_distrib]
  change exAnte p (fun x => θ i (x i) * value a q i x) + exAnte p (value c q i) =
    exAnte p (fun x => θ i (x i) * value a q₀ i x) + exAnte p (value c q₀ i)
  rw [exAnte_typeValue, exAnte_typeValue, exAnte_value, exAnte_value]
  simp only [hq.2.1, hq.2.2]

/-- Matching modified interim transfers and ex ante alternatives also matches every agent's
ex ante actual monetary transfer, even with nonzero alternative constants. -/
theorem exAnte_transfers_match (p : ∀ i, Types n i → ℝ) (a c : I → K → ℝ)
    (q q₀ : Profile (Types n) → K → ℝ) (pay pay₀ : I → Profile (Types n) → ℝ)
    (hq : Matches p a q q₀)
    (hm : ∀ i t, modifiedInterim p c q pay i t = modifiedInterim p c q₀ pay₀ i t)
    (i : I) : exAnte p (pay i) = exAnte p (pay₀ i) := by
  have hmod : exAnte p (modified c q pay i) = exAnte p (modified c q₀ pay₀ i) := by
    rw [exAnte_interim p _ i, exAnte_interim p _ i]
    change (∑ t, p i t * modifiedInterim p c q pay i t) =
      ∑ t, p i t * modifiedInterim p c q₀ pay₀ i t
    simp only [hm]
  have hc : exAnte p (value c q i) = exAnte p (value c q₀ i) := by
    rw [exAnte_value, exAnte_value]
    simp only [hq.2.2]
  have hsplit (q : Profile (Types n) → K → ℝ) (pay : I → Profile (Types n) → ℝ) :
      exAnte p (modified c q pay i) = exAnte p (pay i) + exAnte p (value c q i) := by
    simp [exAnte, modified, mul_add, Finset.sum_add_distrib]
  rw [hsplit, hsplit] at hmod
  linarith

end Gershkov
