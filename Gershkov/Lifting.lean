module
public import Gershkov.Compactness

@[expose] public section
open scoped BigOperators
namespace Gershkov
universe uI uT uK
variable {I : Type uI} [Fintype I] [DecidableEq I]
variable {T : I → Type uT} [∀ i, Fintype (T i)] [∀ i, DecidableEq (T i)]
variable {K : Type uK} [Fintype K]

theorem crossing_context (p : ∀ i, T i → ℝ) (hp : SupportPrior p) (a : I → K → ℝ)
    (q : Profile T → K → ℝ) (j : I) (u v : T j) (y : Opponents T j)
    (hm : slope p a q j u ≤ slope p a q j v)
    (hy : value a q j (pack j v y) < value a q j (pack j u y)) :
    ∃ z : Opponents T j, value a q j (pack j u z) < value a q j (pack j v z) := by
  by_contra hn
  push_neg at hn
  have hs : 0 < ∑ z, opponentMass p j z *
      (value a q j (pack j u z) - value a q j (pack j v z)) := by
    apply Finset.sum_pos'
    · intro z _; exact mul_nonneg (opponentMass_pos p hp j z).le (sub_nonneg.mpr (hn z))
    · exact ⟨y, Finset.mem_univ y, mul_pos (opponentMass_pos p hp j y) (sub_pos.mpr hy)⟩
  have he : (∑ z, opponentMass p j z *
      (value a q j (pack j u z) - value a q j (pack j v z))) =
      slope p a q j u - slope p a q j v := by
    simp [slope, interim, mul_sub, Finset.sum_sub_distrib]
  rw [he] at hs
  linarith

/-- Every violation of pointwise monotonicity has a genuine feasible improving perturbation,
preserving all weighted slope marginals and all weighted alternative probabilities. -/
theorem improving_perturbation (p : ∀ i, T i → ℝ) (hp : SupportPrior p)
    (a : I → K → ℝ) (q q₀ : Profile T → K → ℝ) (hq : Matches p a q q₀)
    (j : I) (u v : T j) (y : Opponents T j)
    (hm : slope p a q j u ≤ slope p a q j v)
    (hy : value a q j (pack j v y) < value a q j (pack j u y)) :
    ∃ q', Matches p a q' q₀ ∧ energy (joint p) a q' < energy (joint p) a q := by
  classical
  obtain ⟨z, hz⟩ := crossing_context p hp a q j u v y hm hy
  have huv : u ≠ v := by intro h; subst v; exact (lt_irrefl _ hy)
  have hyz : y ≠ z := by intro h; subst z; exact (not_lt_of_ge hy.le hz)
  let l := pack j u y
  let r := pack j v y
  let s := pack j u z
  let t := pack j v z
  have hlr : l ≠ r := by
    intro h
    have hh := congrArg (fun x : Profile T => x j) h
    exact huv (by simpa [l, r] using hh)
  have hst : s ≠ t := by
    intro h
    have hh := congrArg (fun x : Profile T => x j) h
    exact huv (by simpa [s, t] using hh)
  have hsl : s ≠ l := by
    intro h
    have hh := congrArg (Equiv.piSplitAt j T) h
    have hpair : (u, z) = (u, y) := by simpa only [s, l, pack, Equiv.apply_symm_apply] using hh
    exact hyz (congrArg Prod.snd hpair).symm
  have hsr : s ≠ r := by
    intro h
    have hh := congrArg (fun x : Profile T => x j) h
    exact huv (by simpa [s, r] using hh)
  have htl : t ≠ l := by
    intro h
    have hh := congrArg (fun x : Profile T => x j) h
    exact huv (by simpa [t, l] using hh.symm)
  have htr : t ≠ r := by
    intro h
    have hh := congrArg (Equiv.piSplitAt j T) h
    have hpair : (v, z) = (v, y) := by simpa only [t, r, pack, Equiv.apply_symm_apply] using hh
    exact hyz (congrArg Prod.snd hpair).symm
  let d := value a q j l - value a q j r
  let e := value a q j t - value a q j s
  have hd : 0 < d := sub_pos.mpr hy
  have he : 0 < e := sub_pos.mpr hz
  have hbound : 0 < min (min (joint p l * d) (joint p r * d))
      (min (joint p s * e) (joint p t * e)) :=
    lt_min (lt_min (mul_pos (joint_pos p hp l) hd) (mul_pos (joint_pos p hp r) hd))
      (lt_min (mul_pos (joint_pos p hp s) he) (mul_pos (joint_pos p hp t) he))
  obtain ⟨η, hη, hηb⟩ := exists_between hbound
  have hηl : η < joint p l * d := hηb.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hηr : η < joint p r * d := hηb.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hηs : η < joint p s * e := hηb.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hηt : η < joint p t * e := hηb.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  let δ := η / d
  let ε := η / e
  have hδ : 0 < δ := div_pos hη hd
  have hε : 0 < ε := div_pos hη he
  have hδl : δ < joint p l := (div_lt_iff₀ hd).mpr hηl
  have hδr : δ < joint p r := (div_lt_iff₀ hd).mpr hηr
  have hεs : ε < joint p s := (div_lt_iff₀ he).mpr hηs
  have hεt : ε < joint p t := (div_lt_iff₀ he).mpr hηt
  have hδd : δ * d = η := div_mul_cancel₀ η hd.ne'
  have hεe : ε * e = η := div_mul_cancel₀ η he.ne'
  let q' := doubleMix (joint p) q l r s t δ ε
  have hμ (x : Profile T) : joint p x ≠ 0 := (joint_pos p hp x).ne'
  have hmoment (C : Profile T → ℝ) (b : K → ℝ) :=
    doubleMix_moment (joint p) q l r s t hlr hst hsl hsr htl htr hμ δ ε C b
  refine ⟨q', ⟨?_, ?_, ?_⟩, ?_⟩
  · exact mixPair_feasible (joint p) (mixPair (joint p) q l r δ) s t ε
      (mixPair_feasible (joint p) q l r δ hq.1 (joint_pos p hp l) (joint_pos p hp r)
        hδ.le hδl.le hδr.le) (joint_pos p hp s) (joint_pos p hp t) hε.le hεs.le hεt.le
  · intro i w
    have hh := hmoment (fun x => if x i = w then 1 else 0) (a i)
    change (∑ x, joint p x * (if x i = w then 1 else 0) * value a q' i x) -
        (∑ x, joint p x * (if x i = w then 1 else 0) * value a q i x) = _ at hh
    rw [fiber_moment, fiber_moment] at hh
    have hzero : δ * ((if l i = w then 1 else 0) - (if r i = w then 1 else 0)) *
          (value a q i r - value a q i l) +
        ε * ((if s i = w then 1 else 0) - (if t i = w then 1 else 0)) *
          (value a q i t - value a q i s) = 0 := by
      by_cases hij : i = j
      · subst i
        have hl : l j = u := pack_self j u y
        have hr : r j = v := pack_self j v y
        have hs : s j = u := pack_self j u z
        have ht : t j = v := pack_self j v z
        rw [hl, hr, hs, ht]
        have hdiff : value a q j r - value a q j l = -d := by dsimp [d]; ring
        rw [hdiff]
        change δ * ((if u = w then 1 else 0) - (if v = w then 1 else 0)) * (-d) +
          ε * ((if u = w then 1 else 0) - (if v = w then 1 else 0)) * e = 0
        calc
          _ = (- (δ * d) + ε * e) * ((if u = w then 1 else 0) - (if v = w then 1 else 0)) := by ring
          _ = 0 := by rw [hδd, hεe]; ring
      · simp [l, r, s, t, pack_other j i hij]
    have hsame : slope p a q' i w = slope p a q i w := by
      change p i w * slope p a q' i w - p i w * slope p a q i w =
        δ * ((if l i = w then 1 else 0) - (if r i = w then 1 else 0)) *
          (value a q i r - value a q i l) +
        ε * ((if s i = w then 1 else 0) - (if t i = w then 1 else 0)) *
          (value a q i t - value a q i s) at hh
      rw [hzero] at hh
      exact (mul_left_cancel₀ (hp.1 i w).ne') (sub_eq_zero.mp hh)
    exact hsame.trans (hq.2.1 i w)
  · intro k
    have hh := hmoment (fun _ => 1) (fun h => if h = k then 1 else 0)
    simp [ite_mul, Finset.sum_ite_eq'] at hh
    have heq : exAnte p (fun x => q' x k) = exAnte p (fun x => q x k) := sub_eq_zero.mp hh
    exact heq.trans (hq.2.2 k)
  · exact doubleMix_energy_lt (joint p) a q l r s t hlr hst hsl hsr htl htr
      (joint_pos p hp) δ ε hδ hδl hδr hε hεs hεt j (ne_of_gt hy) (ne_of_lt hz)

variable [∀ i, Preorder (T i)]

/-- Weighted optimizer monotonicity is a conclusion, obtained from the explicit improvement. -/
theorem minimizer_monotone (p : ∀ i, T i → ℝ) (hp : SupportPrior p)
    (a : I → K → ℝ) (q q₀ : Profile T → K → ℝ) (hq : Matches p a q q₀)
    (hmono : ∀ i, Monotone (slope p a q₀ i))
    (hmin : ∀ q', Matches p a q' q₀ → energy (joint p) a q ≤ energy (joint p) a q') :
    ∀ i y, Monotone (fun t => value a q i (pack i t y)) := by
  intro i y u v huv
  by_contra hn
  have hy := lt_of_not_ge hn
  have hm : slope p a q i u ≤ slope p a q i v := by
    rw [hq.2.1 i u, hq.2.1 i v]
    exact hmono i huv
  obtain ⟨q', hq', hlt⟩ := improving_perturbation p hp a q q₀ hq i u v y hm hy
  exact not_lt_of_ge (hmin q' hq') hlt

theorem weighted_monotone_lifting (p : ∀ i, T i → ℝ) (hp : SupportPrior p)
    (a : I → K → ℝ) (q₀ : Profile T → K → ℝ) (hq₀ : Feasible q₀)
    (hmono : ∀ i, Monotone (slope p a q₀ i)) :
    ∃ q, Matches p a q q₀ ∧ (∀ i y, Monotone (fun t => value a q i (pack i t y))) ∧
      ∀ q', Matches p a q' q₀ → energy (joint p) a q ≤ energy (joint p) a q' := by
  obtain ⟨q, hq, hmin⟩ := exists_minimizer p a q₀ hq₀
  exact ⟨q, hq, minimizer_monotone p hp a q q₀ hq hmono hmin, hmin⟩

end Gershkov
