module
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Tactic
public import Mathlib.Logic.Equiv.Prod
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Order.Fin.Basic

/-! Exact finite GGKMS Theorem 2 and supporting contracts. All model and support
definitions and named instances have genuine implementation bodies copied from
the library. Only the six named reference theorem proof bodies are intentional
placeholders. Complete proofs are exported by Solution under GGKMS and developed
under the distinct Gershkov namespace. Types are strictly ordered finite supports;
arbitrary independent positive support masses are permitted. Null-label deletion
preserves expectations and does not claim incentive compatibility at null reports. -/
@[expose] public section
open scoped BigOperators

namespace GGKMS
universe uP uK uI
variable {P : Type uP} {K : Type uK} {I : Type uI}
variable [Fintype P] [DecidableEq P] [Fintype K] [Fintype I]

noncomputable def value (a : I → K → ℝ) (q : P → K → ℝ) (i : I) (x : P) : ℝ :=
  ∑ k, a i k * q x k

def Feasible (q : P → K → ℝ) : Prop :=
  (∀ x k, 0 ≤ q x k) ∧ (∀ x, ∑ k, q x k = 1)

noncomputable def energy (μ : P → ℝ) (a : I → K → ℝ) (q : P → K → ℝ) : ℝ :=
  ∑ x, μ x * ∑ i, (value a q i x) ^ 2

end GGKMS

namespace GGKMS
universe uI uT uK
variable {I : Type uI} [Fintype I] [DecidableEq I]
variable {T : I → Type uT} [∀ i, Fintype (T i)] [∀ i, DecidableEq (T i)]
variable {K : Type uK} [Fintype K]

abbrev Profile (T : I → Type uT) := ∀ i, T i

abbrev Opponents (T : I → Type uT) (i : I) := ∀ j : {j : I // j ≠ i}, T j

def pack (i : I) (t : T i) (y : Opponents T i) : Profile T :=
  (Equiv.piSplitAt i T).symm (t, y)

noncomputable def joint (p : ∀ i, T i → ℝ) (x : Profile T) : ℝ := ∏ i, p i (x i)

noncomputable def opponentMass (p : ∀ i, T i → ℝ) (i : I) (y : Opponents T i) : ℝ :=
  ∏ j : {j : I // j ≠ i}, p j (y j)

def SupportPrior (p : ∀ i, T i → ℝ) : Prop :=
  (∀ i t, 0 < p i t) ∧ (∀ i, ∑ t, p i t = 1)

noncomputable def interim (p : ∀ i, T i → ℝ) (f : Profile T → ℝ) (i : I) (t : T i) : ℝ :=
  ∑ y, opponentMass p i y * f (pack i t y)

noncomputable def exAnte (p : ∀ i, T i → ℝ) (f : Profile T → ℝ) : ℝ := ∑ x, joint p x * f x

noncomputable def slope (p : ∀ i, T i → ℝ) (a : I → K → ℝ) (q : Profile T → K → ℝ)
    (i : I) (t : T i) : ℝ := interim p (value a q i) i t

def Matches (p : ∀ i, T i → ℝ) (a : I → K → ℝ) (q q₀ : Profile T → K → ℝ) : Prop :=
  Feasible q ∧ (∀ i t, slope p a q i t = slope p a q₀ i t) ∧
    (∀ k, exAnte p (fun x => q x k) = exAnte p (fun x => q₀ x k))

end GGKMS

namespace GGKMS
universe uI uK
variable {I : Type uI} [Fintype I] [DecidableEq I]
variable {K : Type uK} [Fintype K]
variable {n : I → ℕ}

abbrev Types (n : I → ℕ) (i : I) := Fin (n i + 1)

noncomputable def modified (c : I → K → ℝ) (q : Profile (Types n) → K → ℝ)
    (pay : I → Profile (Types n) → ℝ) (i : I) (x : Profile (Types n)) : ℝ :=
  pay i x + value c q i x

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

noncomputable def socialSurplus (p θ : ∀ i, Types n i → ℝ) (a c : I → K → ℝ)
    (q : Profile (Types n) → K → ℝ) : ℝ :=
  exAnte p (fun x => ∑ i, (θ i (x i) * value a q i x + value c q i x))

end GGKMS

namespace GGKMS.Transfers


def ScalarIC {n : ℕ} (x v t : Fin (n + 1) → ℝ) : Prop :=
  ∀ r s, x r * v s + t s ≤ x r * v r + t r

def AdjacentIC {n : ℕ} (x v t : Fin (n + 1) → ℝ) : Prop :=
  ∀ k : Fin n,
    x k.castSucc * (v k.succ - v k.castSucc) ≤ t k.castSucc - t k.succ ∧
    t k.castSucc - t k.succ ≤ x k.succ * (v k.succ - v k.castSucc)

end GGKMS.Transfers

namespace GGKMS
universe uA
variable {A : Type uA} [Fintype A] [DecidableEq A]

abbrev PositiveSupport (w : A → ℝ) := {a : A // 0 < w a}

noncomputable instance positiveSupportFintype (w : A → ℝ) : Fintype (PositiveSupport w) :=
  by classical exact Subtype.fintype _

instance positiveSupportDecidableEq (w : A → ℝ) : DecidableEq (PositiveSupport w) :=
  Subtype.instDecidableEq

end GGKMS

namespace GGKMS
universe uI uK
variable {I : Type uI} [Fintype I] [DecidableEq I]
variable {K : Type uK} [Fintype K]
variable {n : I → ℕ}

theorem finite_bayesian_dominant_equivalence (p θ : ∀ i, Types n i → ℝ)
    (hp : SupportPrior p) (hθ : ∀ i, StrictMono (θ i)) (a c : I → K → ℝ)
    (_ha : ∀ i k, 0 ≤ a i k) (q₀ : Profile (Types n) → K → ℝ)
    (pay₀ : I → Profile (Types n) → ℝ) (hfeasible : Feasible q₀)
    (hBIC : BIC p θ a c q₀ pay₀) :
    ∃ (q : Profile (Types n) → K → ℝ) (pay : I → Profile (Types n) → ℝ),
      Feasible q ∧ DIC θ a c q pay ∧
      (∀ i t, interimPayoff p θ a c q pay i t t = interimPayoff p θ a c q₀ pay₀ i t t) ∧
      socialSurplus p θ a c q = socialSurplus p θ a c q₀ ∧
      Matches p a q q₀ ∧
      (∀ i t, modifiedInterim p c q pay i t = modifiedInterim p c q₀ pay₀ i t) ∧
      (∀ q', Matches p a q' q₀ → energy (joint p) a q ≤ energy (joint p) a q') := by
  sorry

end GGKMS

namespace GGKMS
universe uI uT uK
variable {I : Type uI} [Fintype I] [DecidableEq I]
variable {T : I → Type uT} [∀ i, Fintype (T i)] [∀ i, DecidableEq (T i)]
variable {K : Type uK} [Fintype K]
variable [∀ i, Preorder (T i)]

theorem weighted_monotone_lifting (p : ∀ i, T i → ℝ) (hp : SupportPrior p)
    (a : I → K → ℝ) (q₀ : Profile T → K → ℝ) (hq₀ : Feasible q₀)
    (hmono : ∀ i, Monotone (slope p a q₀ i)) :
    ∃ q, Matches p a q q₀ ∧ (∀ i y, Monotone (fun t => value a q i (pack i t y))) ∧
      ∀ q', Matches p a q' q₀ → energy (joint p) a q ≤ energy (joint p) a q' := by
  sorry

end GGKMS

namespace GGKMS
universe uI uT uK
variable {I : Type uI} [Fintype I] [DecidableEq I]
variable {T : I → Type uT} [∀ i, Fintype (T i)] [∀ i, DecidableEq (T i)]
variable {K : Type uK} [Fintype K]
variable [∀ i, Preorder (T i)]

theorem minimizer_monotone (p : ∀ i, T i → ℝ) (hp : SupportPrior p)
    (a : I → K → ℝ) (q q₀ : Profile T → K → ℝ) (hq : Matches p a q q₀)
    (hmono : ∀ i, Monotone (slope p a q₀ i))
    (hmin : ∀ q', Matches p a q' q₀ → energy (joint p) a q ≤ energy (joint p) a q') :
    ∀ i y, Monotone (fun t => value a q i (pack i t y)) := by
  sorry

end GGKMS

namespace GGKMS.Transfers


theorem scalarIC_iff_monotone_adjacent {n : ℕ} {x v t : Fin (n + 1) → ℝ}
    (hx : StrictMono x) : ScalarIC x v t ↔ Monotone v ∧ AdjacentIC x v t := by
  sorry

end GGKMS.Transfers

namespace GGKMS
universe uA
variable {A : Type uA} [Fintype A] [DecidableEq A]

theorem expectation_on_support (w : A → ℝ) (hw : ∀ a, 0 ≤ w a) (f : A → ℝ) :
    (∑ a : PositiveSupport w, w a * f a) = ∑ a, w a * f a := by
  sorry

end GGKMS

namespace GGKMS
universe uI uT
variable {I : Type uI} [Fintype I] [DecidableEq I]
variable {T : I → Type uT} [∀ i, Fintype (T i)] [∀ i, DecidableEq (T i)]

theorem product_expectation_on_support (p : ∀ i, T i → ℝ)
    (hp : ∀ i t, 0 ≤ p i t) (f : Profile T → ℝ) :
    (∑ z : ∀ i, PositiveSupport (p i), (∏ i, p i (z i).val) * f (fun i => (z i).val)) =
      exAnte p f := by
  sorry

end GGKMS
