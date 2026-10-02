module
public import Gershkov.Smoothing
public import Mathlib.Logic.Equiv.Prod
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section
open scoped BigOperators
namespace Gershkov
universe uI uT uK
variable {I : Type uI} [Fintype I] [DecidableEq I]
variable {T : I → Type uT} [∀ i, Fintype (T i)] [∀ i, DecidableEq (T i)]
variable {K : Type uK} [Fintype K]

abbrev Profile (T : I → Type uT) := ∀ i, T i
abbrev Opponents (T : I → Type uT) (i : I) := ∀ j : {j : I // j ≠ i}, T j

def pack (i : I) (t : T i) (y : Opponents T i) : Profile T :=
  (Equiv.piSplitAt i T).symm (t, y)

@[simp] theorem pack_self (i : I) (t : T i) (y : Opponents T i) : pack i t y i = t := by
  simp [pack, Equiv.piSplitAt]

@[simp] theorem pack_other (i j : I) (hji : j ≠ i) (t : T i) (y : Opponents T i) :
    pack i t y j = y ⟨j, hji⟩ := by
  simp [pack, Equiv.piSplitAt, hji]

@[simp] theorem pack_split (i : I) (x : Profile T) :
    pack i (x i) (fun j => x j) = x := (Equiv.piSplitAt i T).symm_apply_apply x

theorem pack_injective (i : I) : Function.Injective (fun z : T i × Opponents T i => pack i z.1 z.2) :=
  (Equiv.piSplitAt i T).symm.injective

noncomputable def joint (p : ∀ i, T i → ℝ) (x : Profile T) : ℝ := ∏ i, p i (x i)
noncomputable def opponentMass (p : ∀ i, T i → ℝ) (i : I) (y : Opponents T i) : ℝ :=
  ∏ j : {j : I // j ≠ i}, p j (y j)

def SupportPrior (p : ∀ i, T i → ℝ) : Prop :=
  (∀ i t, 0 < p i t) ∧ (∀ i, ∑ t, p i t = 1)

theorem joint_pos (p : ∀ i, T i → ℝ) (hp : SupportPrior p) (x : Profile T) : 0 < joint p x := by
  exact Finset.prod_pos (fun i _ => hp.1 i (x i))

theorem opponentMass_pos (p : ∀ i, T i → ℝ) (hp : SupportPrior p)
    (i : I) (y : Opponents T i) : 0 < opponentMass p i y := by
  exact Finset.prod_pos (fun j _ => hp.1 j (y j))

theorem joint_pack (p : ∀ i, T i → ℝ) (i : I) (t : T i) (y : Opponents T i) :
    joint p (pack i t y) = p i t * opponentMass p i y := by
  rw [joint, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  simp only [pack_self]
  congr 1
  rw [Finset.prod_subtype (p := fun j => j ≠ i) (Finset.univ.erase i) (by simp) (fun j => p j (pack i t y j))]
  unfold opponentMass
  apply Finset.prod_congr rfl
  intro j _
  rw [pack_other i j j.property]

theorem joint_sum (p : ∀ i, T i → ℝ) (hp : SupportPrior p) : ∑ x, joint p x = 1 := by
  simp only [joint]
  rw [← Fintype.prod_sum]
  simp [hp.2]

theorem opponentMass_sum (p : ∀ i, T i → ℝ) (hp : SupportPrior p) (i : I) :
    ∑ y, opponentMass p i y = 1 := by
  simp only [opponentMass]
  rw [← Fintype.prod_sum]
  simp [hp.2]

noncomputable def interim (p : ∀ i, T i → ℝ) (f : Profile T → ℝ) (i : I) (t : T i) : ℝ :=
  ∑ y, opponentMass p i y * f (pack i t y)

noncomputable def exAnte (p : ∀ i, T i → ℝ) (f : Profile T → ℝ) : ℝ := ∑ x, joint p x * f x

/-- Product independence converts a conditioned moment to a full joint weighted sum. -/
theorem fiber_moment (p : ∀ i, T i → ℝ) (f : Profile T → ℝ) (i : I) (t : T i) :
    (∑ x, joint p x * (if x i = t then 1 else 0) * f x) = p i t * interim p f i t := by
  rw [← (Equiv.piSplitAt i T).symm.sum_comp]
  rw [Fintype.sum_prod_type]
  change (∑ s : T i, ∑ y : Opponents T i, joint p (pack i s y) *
    (if pack i s y i = t then 1 else 0) * f (pack i s y)) = _
  simp [joint_pack, interim, ← Finset.mul_sum, mul_assoc]

theorem exAnte_interim (p : ∀ i, T i → ℝ) (f : Profile T → ℝ) (i : I) :
    exAnte p f = ∑ t, p i t * interim p f i t := by
  unfold exAnte
  rw [← (Equiv.piSplitAt i T).symm.sum_comp, Fintype.sum_prod_type]
  change (∑ t : T i, ∑ y : Opponents T i, joint p (pack i t y) * f (pack i t y)) = _
  simp only [joint_pack, mul_assoc, interim, Finset.mul_sum]

theorem interim_const (p : ∀ i, T i → ℝ) (hp : SupportPrior p) (i : I) (t : T i) (c : ℝ) :
    interim p (fun _ => c) i t = c := by
  simp [interim, ← Finset.sum_mul, opponentMass_sum p hp]

theorem interim_add (p : ∀ i, T i → ℝ) (f g : Profile T → ℝ) (i : I) (t : T i) :
    interim p (fun x => f x + g x) i t = interim p f i t + interim p g i t := by
  simp [interim, mul_add, Finset.sum_add_distrib]

theorem interim_sub (p : ∀ i, T i → ℝ) (f g : Profile T → ℝ) (i : I) (t : T i) :
    interim p (fun x => f x - g x) i t = interim p f i t - interim p g i t := by
  simp [interim, mul_sub, Finset.sum_sub_distrib]

theorem interim_mul (p : ∀ i, T i → ℝ) (f : Profile T → ℝ) (i : I) (t : T i) (c : ℝ) :
    interim p (fun x => c * f x) i t = c * interim p f i t := by
  simp [interim, Finset.mul_sum, mul_left_comm]

noncomputable def slope (p : ∀ i, T i → ℝ) (a : I → K → ℝ) (q : Profile T → K → ℝ)
    (i : I) (t : T i) : ℝ := interim p (value a q i) i t

def Matches (p : ∀ i, T i → ℝ) (a : I → K → ℝ) (q q₀ : Profile T → K → ℝ) : Prop :=
  Feasible q ∧ (∀ i t, slope p a q i t = slope p a q₀ i t) ∧
    (∀ k, exAnte p (fun x => q x k) = exAnte p (fun x => q₀ x k))

end Gershkov
