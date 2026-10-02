module
public import Gershkov.Model

@[expose] public section
open scoped BigOperators
namespace Gershkov
universe uA
variable {A : Type uA} [Fintype A] [DecidableEq A]

/-- Only positive-probability atoms are modeled reports in the published finite support theorem. -/
abbrev PositiveSupport (w : A → ℝ) := {a : A // 0 < w a}

noncomputable instance positiveSupportFintype (w : A → ℝ) : Fintype (PositiveSupport w) :=
  by classical exact Subtype.fintype _

instance positiveSupportDecidableEq (w : A → ℝ) : DecidableEq (PositiveSupport w) :=
  Subtype.instDecidableEq

/-- Deleting null labels preserves every weighted expectation, without any conditional division. -/
theorem expectation_on_support (w : A → ℝ) (hw : ∀ a, 0 ≤ w a) (f : A → ℝ) :
    (∑ a : PositiveSupport w, w a * f a) = ∑ a, w a * f a := by
  classical
  symm
  apply Finset.sum_congr_set {a | 0 < w a} (fun a => w a * f a) (fun a => w a * f a)
  · intro a ha; rfl
  · intro a ha
    have hz : w a = 0 := le_antisymm (le_of_not_gt ha) (hw a)
    simp [hz]

theorem support_normalized (w : A → ℝ) (hw : ∀ a, 0 ≤ w a) (hn : ∑ a, w a = 1) :
    (∀ a : PositiveSupport w, 0 < w a) ∧ (∑ a : PositiveSupport w, w a = 1) := by
  refine ⟨fun a => a.property, ?_⟩
  simpa using (expectation_on_support w hw (fun _ => 1)).trans (by simpa using hn)

theorem support_nonempty (w : A → ℝ) (hw : ∀ a, 0 ≤ w a) (hn : ∑ a, w a = 1) :
    Nonempty (PositiveSupport w) := by
  classical
  by_contra he
  haveI : IsEmpty (PositiveSupport w) := not_nonempty_iff.mp he
  have hs := (support_normalized w hw hn).2
  simp at hs

universe uI uT
variable {I : Type uI} [Fintype I] [DecidableEq I]
variable {T : I → Type uT} [∀ i, Fintype (T i)] [∀ i, DecidableEq (T i)]

/-- Restricting each independent distribution to its positive support leaves the full joint
expectation unchanged. It makes no assertion about IC at deleted zero-mass reports. -/
theorem product_expectation_on_support (p : ∀ i, T i → ℝ)
    (hp : ∀ i t, 0 ≤ p i t) (f : Profile T → ℝ) :
    (∑ z : ∀ i, PositiveSupport (p i), (∏ i, p i (z i).val) * f (fun i => (z i).val)) =
      exAnte p f := by
  classical
  let S := {x : Profile T // ∀ i, 0 < p i (x i)}
  letI : Fintype S := Subtype.fintype (fun x : Profile T => ∀ i, 0 < p i (x i))
  let e : S ≃ (∀ i, PositiveSupport (p i)) := Equiv.subtypePiEquivPi (β := T) (p := fun i t => 0 < p i t)
  have hsum : (∑ x : S, joint p x.val * f x.val) = exAnte p f := by
    symm
    unfold exAnte
    apply Finset.sum_congr_set {x : Profile T | ∀ i, 0 < p i (x i)}
      (fun x => joint p x * f x) (fun x => joint p x.val * f x.val)
    · intro x hx; rfl
    · intro x hx
      simp only [Set.mem_setOf_eq, not_forall, not_lt] at hx
      obtain ⟨i, hi⟩ := hx
      have hz : p i (x i) = 0 := le_antisymm hi (hp i (x i))
      have hj : joint p x = 0 := Finset.prod_eq_zero (Finset.mem_univ i) hz
      simp [hj]
  calc
    _ = ∑ x : S, joint p x.val * f x.val := e.symm.sum_comp _
    _ = exAnte p f := hsum

/-- The same restriction identity for opponents proves interim expectation preservation for
each fixed own support type and report, including payoff and allocation functions. -/
theorem opponent_expectation_on_support (p : ∀ i, T i → ℝ)
    (hp : ∀ i t, 0 ≤ p i t) (i : I) (f : Opponents T i → ℝ) :
    (∑ z : ∀ j : {j : I // j ≠ i}, PositiveSupport (p j),
      (∏ j : {j : I // j ≠ i}, p j (z j).val) * f (fun j => (z j).val)) =
      ∑ y, opponentMass p i y * f y := by
  exact product_expectation_on_support (fun j : {j : I // j ≠ i} => p j)
    (fun j t => hp j t) f

end Gershkov
