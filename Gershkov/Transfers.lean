module
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Order.Fin.Basic
public import Mathlib.Tactic

@[expose] public section

/-!
# Finite scalar incentive constraints and transfers

This module proves the transfer part of the finite GGKMS equivalence theorem.
Types are arbitrary strictly ordered real numbers indexed by `Fin (n + 1)`.
The modified transfer absorbs the alternative-dependent utility constants.
We use a constant modified base transfer, a valid existential variation of the
source's base with the same expected value. No individual-rationality claim
is made here.
-/

namespace Gershkov.Transfers

open scoped BigOperators

/-- Truthful reporting maximizes scalar linear utility over the finite report set. -/
def ScalarIC {n : ℕ} (x v t : Fin (n + 1) → ℝ) : Prop :=
  ∀ r s, x r * v s + t s ≤ x r * v r + t r

/-- The bounds on the difference of transfers at consecutive ordered types. -/
def AdjacentIC {n : ℕ} (x v t : Fin (n + 1) → ℝ) : Prop :=
  ∀ k : Fin n,
    x k.castSucc * (v k.succ - v k.castSucc) ≤ t k.castSucc - t k.succ ∧
    t k.castSucc - t k.succ ≤ x k.succ * (v k.succ - v k.castSucc)

theorem adjacent_of_ic {n : ℕ} {x v t : Fin (n + 1) → ℝ}
    (h : ScalarIC x v t) : AdjacentIC x v t := by
  intro k
  have hl := h k.castSucc k.succ
  have hh := h k.succ k.castSucc
  constructor <;> nlinarith

theorem monotone_of_ic {n : ℕ} {x v t : Fin (n + 1) → ℝ}
    (hx : StrictMono x) (h : ScalarIC x v t) : Monotone v := by
  intro r s hrs
  rcases eq_or_lt_of_le hrs with heq | hlt
  · simp [heq]
  have htype := hx hlt
  have hl := h r s
  have hh := h s r
  have hprod : 0 ≤ (x s - x r) * (v s - v r) := by nlinarith
  have : 0 ≤ v s - v r := nonneg_of_mul_nonneg_right hprod (sub_pos.mpr htype)
  linarith

/-- The adjacent coefficient in source equation (5); flat marginals use the upper type. -/
noncomputable def coefficient {n : ℕ} (x v t : Fin (n + 1) → ℝ) (k : Fin n) : ℝ :=
  if v k.succ = v k.castSucc then x k.succ
  else (t k.castSucc - t k.succ) / (v k.succ - v k.castSucc)

theorem coefficient_bounds {n : ℕ} {x v t : Fin (n + 1) → ℝ}
    (hx : StrictMono x) (h : ScalarIC x v t) (k : Fin n) :
    x k.castSucc ≤ coefficient x v t k ∧ coefficient x v t k ≤ x k.succ := by
  have hmono := monotone_of_ic hx h
  have hadj := adjacent_of_ic h k
  by_cases heq : v k.succ = v k.castSucc
  · simp only [coefficient, ite_eq_left heq]
    exact ⟨(hx k.castSucc_lt_succ).le, le_rfl⟩
  · have hdelta : 0 < v k.succ - v k.castSucc := by
      have hle := hmono k.castSucc_lt_succ.le
      exact sub_pos.mpr (lt_of_le_of_ne hle (Ne.symm heq))
    simp only [coefficient, ite_eq_right heq]
    exact ⟨(le_div_iff₀ hdelta).mpr hadj.1, (div_le_iff₀ hdelta).mpr hadj.2⟩

theorem coefficient_transfer_delta {n : ℕ} {x v t : Fin (n + 1) → ℝ}
    (h : ScalarIC x v t) (k : Fin n) :
    coefficient x v t k * (v k.succ - v k.castSucc) = t k.castSucc - t k.succ := by
  by_cases heq : v k.succ = v k.castSucc
  · have hb := adjacent_of_ic h k
    simp only [coefficient, heq, sub_self, mul_zero]
    have hb0 : 0 ≤ t k.castSucc - t k.succ ∧ t k.castSucc - t k.succ ≤ 0 := by
      simpa [heq] using hb
    have : t k.castSucc - t k.succ = 0 := le_antisymm hb0.2 hb0.1
    exact this.symm
  · simp only [coefficient, ite_eq_right heq]
    exact div_mul_cancel₀ _ (sub_ne_zero.mpr heq)

/-- Consecutive inequalities suffice for full scalar IC; this is a telescoping proof. -/
theorem pair_bounds_of_adjacent {n : ℕ} {x v t : Fin (n + 1) → ℝ}
    (hx : Monotone x) (hv : Monotone v) (h : AdjacentIC x v t) :
    ∀ r s, r ≤ s →
      x r * (v s - v r) ≤ t r - t s ∧
      t r - t s ≤ x s * (v s - v r) := by
  intro r s
  induction s using Fin.induction with
  | zero =>
      intro hr
      have heq : r = 0 := by apply Fin.ext; have := Fin.le_def.mp hr; simp at this; omega
      simp [heq]
  | succ k ih =>
      intro hr
      by_cases heq : r = k.succ
      · simp [heq]
      have hrk : r ≤ k.castSucc := by
        have hrv := Fin.le_def.mp hr
        have hne : r.val ≠ k.succ.val := by simpa [Fin.ext_iff] using heq
        apply Fin.le_def.mpr
        simp only [Fin.val_succ, Fin.val_castSucc] at *
        omega
      have hp := ih hrk
      have ha := h k
      have hxr := hx hrk
      have hxs := hx k.castSucc_lt_succ.le
      have hvr := hv hrk
      have hvs := hv k.castSucc_lt_succ.le
      have hlo := mul_nonneg (sub_nonneg.mpr hxr) (sub_nonneg.mpr hvs)
      have hhi := mul_nonneg (sub_nonneg.mpr hxs) (sub_nonneg.mpr hvr)
      constructor <;> nlinarith

theorem ic_of_adjacent {n : ℕ} {x v t : Fin (n + 1) → ℝ}
    (hx : Monotone x) (hv : Monotone v) (h : AdjacentIC x v t) : ScalarIC x v t := by
  intro r s
  rcases le_total r s with hrs | hsr
  · have hb := (pair_bounds_of_adjacent hx hv h r s hrs).1
    nlinarith
  · have hb := (pair_bounds_of_adjacent hx hv h s r hsr).2
    nlinarith

/-- Exact finite scalar IC characterization, including every nonadjacent deviation. -/
theorem scalarIC_iff_monotone_adjacent {n : ℕ} {x v t : Fin (n + 1) → ℝ}
    (hx : StrictMono x) : ScalarIC x v t ↔ Monotone v ∧ AdjacentIC x v t := by
  constructor
  · intro h
    exact ⟨monotone_of_ic hx h, adjacent_of_ic h⟩
  · rintro ⟨hv, h⟩
    exact ic_of_adjacent hx.monotone hv h

/-- Extend the adjacent edge amount by zero at the final type. -/
noncomputable def edge {n : ℕ} (a : Fin n → ℝ) (v : Fin (n + 1) → ℝ) :
    Fin (n + 1) → ℝ :=
  Fin.lastCases 0 (fun k => a k * (v k.succ - v k.castSucc))

/-- The finite telescoping modified transfer with a constant base. -/
noncomputable def transfer {n : ℕ} (a : Fin n → ℝ) (v : Fin (n + 1) → ℝ)
    (b : ℝ) (r : Fin (n + 1)) : ℝ :=
  b - ∑ k ∈ Finset.Iio r, edge a v k

theorem transfer_zero {n : ℕ} (a : Fin n → ℝ) (v : Fin (n + 1) → ℝ) (b : ℝ) :
    transfer a v b 0 = b := by
  have hi : Finset.Iio (0 : Fin (n + 1)) = ∅ := by
    ext k
    simp
  simp [transfer, hi]

theorem Iio_succ_eq_insert {n : ℕ} (k : Fin n) :
    Finset.Iio k.succ = insert k.castSucc (Finset.Iio k.castSucc) := by
  ext r
  simp only [Finset.mem_Iio, Finset.mem_insert, Fin.lt_def, Fin.val_succ, Fin.val_castSucc]
  constructor
  · intro hr
    by_cases heq : r.val = k.val
    · exact Or.inl (Fin.ext heq)
    · exact Or.inr (by omega)
  · rintro (hr | hr)
    · subst r; simp
    · omega

theorem transfer_adjacent_delta {n : ℕ} (a : Fin n → ℝ) (v : Fin (n + 1) → ℝ)
    (b : ℝ) (k : Fin n) :
    transfer a v b k.castSucc - transfer a v b k.succ =
      a k * (v k.succ - v k.castSucc) := by
  classical
  rw [transfer, transfer, Iio_succ_eq_insert, Finset.sum_insert]
  · simp [edge]
  · simp

theorem constructed_transfer_ic {n : ℕ} {x V T v : Fin (n + 1) → ℝ}
    (hx : StrictMono x) (hBIC : ScalarIC x V T) (hv : Monotone v) (b : ℝ) :
    ScalarIC x v (transfer (coefficient x V T) v b) := by
  apply ic_of_adjacent hx.monotone hv
  intro k
  rw [transfer_adjacent_delta]
  have hb := coefficient_bounds hx hBIC k
  have hd : 0 ≤ v k.succ - v k.castSucc := sub_nonneg.mpr (hv k.castSucc_lt_succ.le)
  exact ⟨mul_le_mul_of_nonneg_right hb.1 hd, mul_le_mul_of_nonneg_right hb.2 hd⟩

/-- Finite weighted expectation, used only through its linearity in this module. -/
def mean {Ω : Type*} [Fintype Ω] (w : Ω → ℝ) (f : Ω → ℝ) : ℝ := ∑ y, w y * f y

theorem mean_sub {Ω : Type*} [Fintype Ω] (w f g : Ω → ℝ) :
    mean w (fun y => f y - g y) = mean w f - mean w g := by
  simp [mean, mul_sub, Finset.sum_sub_distrib]

theorem mean_mul {Ω : Type*} [Fintype Ω] (w f : Ω → ℝ) (a : ℝ) :
    mean w (fun y => a * f y) = a * mean w f := by
  simp [mean, mul_left_comm, Finset.mul_sum]

theorem mean_const {Ω : Type*} [Fintype Ω] (w : Ω → ℝ)
    (hw : ∑ y, w y = 1) (b : ℝ) : mean w (fun _ => b) = b := by
  simp [mean, ← Finset.sum_mul, hw]

/-- The constructed transfer preserves all original modified interim transfers.
No uniformity of the opponents' weights is assumed. -/
theorem constructed_transfer_mean {n : ℕ} {Ω : Type*} [Fintype Ω]
    {x V T : Fin (n + 1) → ℝ} (hBIC : ScalarIC x V T)
    (w : Ω → ℝ) (hw : ∑ y, w y = 1) (v : Fin (n + 1) → Ω → ℝ)
    (hmarg : ∀ r, mean w (v r) = V r) (r : Fin (n + 1)) :
    mean w (fun y => transfer (coefficient x V T) (fun s => v s y) (T 0) r) = T r := by
  induction r using Fin.induction with
  | zero => simpa only [transfer_zero] using mean_const w hw (T 0)
  | succ k ih =>
      have hpoint : (fun y =>
          transfer (coefficient x V T) (fun s => v s y) (T 0) k.castSucc -
          transfer (coefficient x V T) (fun s => v s y) (T 0) k.succ) =
          (fun y => coefficient x V T k * (v k.succ y - v k.castSucc y)) := by
        funext y
        exact transfer_adjacent_delta _ _ _ k
      have hmean := congrArg (mean w) hpoint
      rw [mean_sub, mean_mul, mean_sub, hmarg, hmarg, ih,
        coefficient_transfer_delta hBIC k] at hmean
      linarith

/-- The finite transfer certificate used after monotone marginal lifting. -/
theorem modified_transfer_exists {n : ℕ} {Ω : Type*} [Fintype Ω]
    {x V T : Fin (n + 1) → ℝ} (hx : StrictMono x) (hBIC : ScalarIC x V T)
    (w : Ω → ℝ) (hw : ∑ y, w y = 1) (v : Fin (n + 1) → Ω → ℝ)
    (hv : ∀ y, Monotone (fun r => v r y))
    (hmarg : ∀ r, mean w (v r) = V r) :
    ∃ τ : Fin (n + 1) → Ω → ℝ,
      (∀ y, ScalarIC x (fun r => v r y) (fun r => τ r y)) ∧
      ∀ r, mean w (τ r) = T r := by
  refine ⟨fun r y => transfer (coefficient x V T) (fun s => v s y) (T 0) r, ?_, ?_⟩
  · intro y
    exact constructed_transfer_ic hx hBIC (hv y) (T 0)
  · intro r
    exact constructed_transfer_mean hBIC w hw v hmarg r

end Gershkov.Transfers
