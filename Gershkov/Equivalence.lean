module
public import Gershkov.Mechanism
public import Gershkov.Lifting

@[expose] public section
open scoped BigOperators
namespace Gershkov
universe uI uK
variable {I : Type uI} [Fintype I] [DecidableEq I]
variable {K : Type uK} [Fintype K]
variable {n : I → ℕ}

/-- A monotone allocation with the correct weighted marginals admits the full finite transfer
construction. This lemma assumes a matching allocation; the final theorem constructs it. -/
theorem transfers_for_matching_allocation (p θ : ∀ i, Types n i → ℝ)
    (hp : SupportPrior p) (hθ : ∀ i, StrictMono (θ i)) (a c : I → K → ℝ)
    (q q₀ : Profile (Types n) → K → ℝ) (pay₀ : I → Profile (Types n) → ℝ)
    (hBIC : BIC p θ a c q₀ pay₀) (hq : Matches p a q q₀)
    (hmono : ∀ i y, Monotone (fun t => value a q i (pack i t y))) :
    ∃ pay : I → Profile (Types n) → ℝ,
      DIC θ a c q pay ∧
      (∀ i t, interimPayoff p θ a c q pay i t t = interimPayoff p θ a c q₀ pay₀ i t t) ∧
      (∀ i t, modifiedInterim p c q pay i t = modifiedInterim p c q₀ pay₀ i t) := by
  classical
  have hex (i : I) := Transfers.modified_transfer_exists (hθ i)
    (bic_scalar p θ a c q₀ pay₀ hBIC i) (opponentMass p i) (opponentMass_sum p hp i)
    (fun t y => value a q i (pack i t y)) (hmono i)
    (fun t => hq.2.1 i t)
  choose τ hic hmean using hex
  let pay : I → Profile (Types n) → ℝ :=
    fun i x => τ i (x i) (fun j => x j) - value c q i x
  have hmod (i : I) (t : Types n i) (y : Opponents (Types n) i) :
      modified c q pay i (pack i t y) = τ i t y := by
    have hctx : (fun j : {j : I // j ≠ i} => pack i t y j.val) = y := by
      funext j; exact pack_other i j j.property t y
    simp only [modified, pay, pack_self, hctx]
    ring
  have hm (i : I) (t : Types n i) :
      modifiedInterim p c q pay i t = modifiedInterim p c q₀ pay₀ i t := by
    unfold modifiedInterim interim
    simp only [hmod]
    exact hmean i t
  refine ⟨pay, ?_, ?_, hm⟩
  · intro i y t r
    simp only [payoff_modified, hmod]
    exact hic i y t r
  · intro i t
    rw [interimPayoff_modified, interimPayoff_modified, hq.2.1 i t, hm i t]

/-- Finite GGKMS (2013), Theorem 2: arbitrary independent finite scalar support distributions,
heterogeneous cardinalities, all social alternatives, exact interim utilities and ex ante surplus.
The weighted monotone lifting is constructed from a quadratic minimizer and proved perturbations.
The modified base transfer is constant, with the same expectation as source equation (5). -/
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
  have hmono (i : I) : Monotone (slope p a q₀ i) :=
    Transfers.monotone_of_ic (hθ i) (bic_scalar p θ a c q₀ pay₀ hBIC i)
  obtain ⟨q, hq, hqm, hmin⟩ := weighted_monotone_lifting p hp a q₀ hfeasible hmono
  obtain ⟨pay, hDIC, hutility, htransfer⟩ :=
    transfers_for_matching_allocation p θ hp hθ a c q q₀ pay₀ hBIC hq hqm
  exact ⟨q, pay, hq.1, hDIC, hutility, surplus_matches p θ a c q q₀ hq,
    hq, htransfer, hmin⟩

end Gershkov
