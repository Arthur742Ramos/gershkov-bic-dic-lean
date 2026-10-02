module
public import Gershkov.Model
public import Mathlib.Topology.Order.Compact
public import Mathlib.Tactic.FunProp

@[expose] public section
open scoped BigOperators
namespace Gershkov
universe uI uT uK
variable {I : Type uI} [Fintype I] [DecidableEq I]
variable {T : I → Type uT} [∀ i, Fintype (T i)] [∀ i, DecidableEq (T i)]
variable {K : Type uK} [Fintype K]

theorem feasible_entry_le_one (q : Profile T → K → ℝ) (hq : Feasible q)
    (x : Profile T) (k : K) : q x k ≤ 1 := by
  rw [← hq.2 x]
  exact Finset.single_le_sum (fun k _ => hq.1 x k) (Finset.mem_univ k)

theorem feasible_isClosed : IsClosed {q : Profile T → K → ℝ | Feasible q} := by
  simp only [Feasible, Set.setOf_and, Set.setOf_forall]
  apply IsClosed.inter
  · apply isClosed_iInter; intro x
    apply isClosed_iInter; intro k
    exact isClosed_le continuous_const (by fun_prop)
  · apply isClosed_iInter; intro x
    exact isClosed_eq (by fun_prop) continuous_const

theorem slope_continuous (p : ∀ i, T i → ℝ) (a : I → K → ℝ) (i : I) (t : T i) :
    Continuous (fun q : Profile T → K → ℝ => slope p a q i t) := by
  unfold slope interim value
  fun_prop

theorem alternative_continuous (p : ∀ i, T i → ℝ) (k : K) :
    Continuous (fun q : Profile T → K → ℝ => exAnte p (fun x => q x k)) := by
  unfold exAnte
  fun_prop

theorem matches_isClosed (p : ∀ i, T i → ℝ) (a : I → K → ℝ)
    (q₀ : Profile T → K → ℝ) : IsClosed {q | Matches p a q q₀} := by
  simp only [Matches, Set.setOf_and, Set.setOf_forall]
  apply feasible_isClosed.inter
  apply IsClosed.inter
  · apply isClosed_iInter; intro i
    apply isClosed_iInter; intro t
    exact isClosed_eq (slope_continuous p a i t) continuous_const
  · apply isClosed_iInter; intro k
    exact isClosed_eq (alternative_continuous p k) continuous_const

theorem matches_isCompact (p : ∀ i, T i → ℝ) (a : I → K → ℝ)
    (q₀ : Profile T → K → ℝ) : IsCompact {q | Matches p a q q₀} := by
  apply IsCompact.of_isClosed_subset (s := Set.Icc 0 1) isCompact_Icc (matches_isClosed p a q₀)
  intro q hq
  exact ⟨fun x k => hq.1.1 x k, fun x k => feasible_entry_le_one q hq.1 x k⟩

theorem energy_continuous (p : ∀ i, T i → ℝ) (a : I → K → ℝ) :
    Continuous (fun q : Profile T → K → ℝ => energy (joint p) a q) := by
  unfold energy value
  fun_prop

/-- The feasible weighted marginal polytope is nonempty and compact, so the actual quadratic
objective attains its minimum. Optimizer monotonicity is proved separately by perturbation. -/
theorem exists_minimizer (p : ∀ i, T i → ℝ) (a : I → K → ℝ)
    (q₀ : Profile T → K → ℝ) (hq₀ : Feasible q₀) :
    ∃ q, Matches p a q q₀ ∧
      ∀ q', Matches p a q' q₀ → energy (joint p) a q ≤ energy (joint p) a q' := by
  obtain ⟨q, hq, hm⟩ := (matches_isCompact p a q₀).exists_isMinOn
    ⟨q₀, hq₀, fun _ _ => rfl, fun _ => rfl⟩ (energy_continuous p a).continuousOn
  exact ⟨q, hq, hm⟩

end Gershkov
