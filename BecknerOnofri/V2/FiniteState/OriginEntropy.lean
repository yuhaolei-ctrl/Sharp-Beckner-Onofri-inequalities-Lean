module

public import BecknerOnofri.V2.FiniteState.OriginRegression

@[expose] public section

/-!
# Origin vanishing order of `f(t) = F(p(t)) + 12 ψ(t)`: `f = O(t⁴)`

Appendix A.3, "Vanishing required at the origin": `H(p|b) = 6 t² + O(t⁴)` (normalisation cancels
the linear term, reflection kills the cubic term, `E_b ℓ² = 12`), `p^T W p = 12 t² + O(t⁴)`,
`12 ψ = O(t⁴)`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter Topology Asymptotics
open scoped BigOperators
namespace BecknerOnofri.V2.FiniteState
open BecknerOnofri.HighDim.Spin

/-- Scalar entropy remainder: `|(1+z) log(1+z) - (z + z²/2 - z³/6)| ≤ 4 |z|⁴` for `|z| ≤ 1/2`. -/
theorem abs_entropy_expansion_le {z : ℝ} (hz : |z| ≤ 1 / 2) :
    |(1 + z) * Real.log (1 + z) - (z + z ^ 2 / 2 - z ^ 3 / 6)| ≤ 4 * |z| ^ 4 := by
  have h1 : |(-z)| < 1 := by rw [abs_neg]; linarith
  have h := Real.abs_log_sub_add_sum_range_le h1 3
  simp only [abs_neg] at h
  have hsum : (∑ i ∈ Finset.range 3, (-z) ^ (i + 1) / ((i : ℝ) + 1)) =
      -z + z ^ 2 / 2 - z ^ 3 / 3 := by
    simp [Finset.sum_range_succ]; ring
  rw [hsum, show (1 : ℝ) - -z = 1 + z by ring] at h
  have hz0 : 0 ≤ |z| := abs_nonneg z
  have hden : 1 / 2 ≤ 1 - |z| := by linarith
  have h2 : |z| ^ 4 / (1 - |z|) ≤ 2 * |z| ^ 4 := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [pow_nonneg hz0 4]
  set E := Real.log (1 + z) - (z - z ^ 2 / 2 + z ^ 3 / 3) with hE
  have hE' : |E| ≤ 2 * |z| ^ 4 := by
    have : E = -z + z ^ 2 / 2 - z ^ 3 / 3 + Real.log (1 + z) := by rw [hE]; ring
    rw [this]
    exact h.trans h2
  have e : (1 + z) * Real.log (1 + z) - (z + z ^ 2 / 2 - z ^ 3 / 6) =
      z ^ 4 / 3 + (1 + z) * E := by
    rw [hE]; ring
  rw [e]
  have h3 : |z ^ 4 / 3| ≤ |z| ^ 4 / 3 := by
    rw [abs_div, abs_pow]; norm_num
  have h4 : |(1 + z) * E| ≤ (3 / 2) * (2 * |z| ^ 4) := by
    rw [abs_mul]
    have : |1 + z| ≤ 3 / 2 := by
      rw [abs_le]; constructor <;> linarith [abs_le.mp hz]
    exact mul_le_mul this hE' (abs_nonneg _) (by norm_num)
  calc |z ^ 4 / 3 + (1 + z) * E| ≤ |z ^ 4 / 3| + |(1 + z) * E| := abs_add_le _ _
    _ ≤ 4 * |z| ^ 4 := by nlinarith [pow_nonneg hz0 4]

/-- `z² = ℓ² t² + 2 ℓ d t³ + O(t⁴)` for a jet `z = ℓ t + d t² + O(t³)`. -/
theorem Jet2.sq_isBigO {z : ℝ → ℝ} {ℓ d : ℝ} (h : Jet2 z 0 ℓ d) :
    (fun t => z t ^ 2 - (ℓ ^ 2 * t ^ 2 + 2 * ℓ * d * t ^ 3)) =O[𝓝 0] fun t : ℝ => t ^ 4 := by
  have hR : (fun t : ℝ => z t - (0 + ℓ * t + d * t ^ 2)) =O[𝓝 0] fun t : ℝ => t ^ 3 := h
  have hzO : z =O[𝓝 0] fun t : ℝ => t := by
    have e : z = fun t => (z t - (0 + ℓ * t + d * t ^ 2)) + (ℓ * t + d * t ^ 2) := by
      funext t; ring
    rw [e]
    refine Asymptotics.IsBigO.add (hR.trans (isBigO_pow_id (by norm_num : 1 ≤ 3))) ?_
    exact ((Asymptotics.isBigO_refl _ _).const_mul_left ℓ).add
      ((isBigO_pow_id (by norm_num : 1 ≤ 2)).const_mul_left d)
  have hw : (fun t : ℝ => z t - ℓ * t) =O[𝓝 0] fun t : ℝ => t ^ 2 := by
    have e : (fun t : ℝ => z t - ℓ * t) =
        fun t => (z t - (0 + ℓ * t + d * t ^ 2)) + d * t ^ 2 := by
      funext t; ring
    rw [e]
    exact (hR.trans (isBigO_pow_pow (by norm_num : 2 ≤ 3))).add
      ((Asymptotics.isBigO_refl _ _).const_mul_left d)
  have hs : (fun t : ℝ => z t + ℓ * t) =O[𝓝 0] fun t : ℝ => t :=
    hzO.add ((Asymptotics.isBigO_refl _ _).const_mul_left ℓ)
  have a1 : (fun t : ℝ => d * t ^ 2 * (z t - ℓ * t)) =O[𝓝 0] fun t : ℝ => t ^ 4 := by
    have := ((Asymptotics.isBigO_refl (fun t : ℝ => t ^ 2) (𝓝 0)).const_mul_left d).mul hw
    exact this.congr (fun t => by ring) (fun t => by ring)
  have a2 : (fun t : ℝ => (z t - (0 + ℓ * t + d * t ^ 2)) * (z t + ℓ * t)) =O[𝓝 0]
      fun t : ℝ => t ^ 4 := by
    have := hR.mul hs
    exact this.congr (fun t => by ring) (fun t => by ring)
  refine (a1.add a2).congr_left (fun t => ?_)
  ring

/-- `z³ = ℓ³ t³ + O(t⁴)`. -/
theorem Jet2.cube_isBigO {z : ℝ → ℝ} {ℓ d : ℝ} (h : Jet2 z 0 ℓ d) :
    (fun t => z t ^ 3 - ℓ ^ 3 * t ^ 3) =O[𝓝 0] fun t : ℝ => t ^ 4 := by
  have hR : (fun t : ℝ => z t - (0 + ℓ * t + d * t ^ 2)) =O[𝓝 0] fun t : ℝ => t ^ 3 := h
  have hzO : z =O[𝓝 0] fun t : ℝ => t := by
    have e : z = fun t => (z t - (0 + ℓ * t + d * t ^ 2)) + (ℓ * t + d * t ^ 2) := by
      funext t; ring
    rw [e]
    refine Asymptotics.IsBigO.add (hR.trans (isBigO_pow_id (by norm_num : 1 ≤ 3))) ?_
    exact ((Asymptotics.isBigO_refl _ _).const_mul_left ℓ).add
      ((isBigO_pow_id (by norm_num : 1 ≤ 2)).const_mul_left d)
  have hw : (fun t : ℝ => z t - ℓ * t) =O[𝓝 0] fun t : ℝ => t ^ 2 := by
    have e : (fun t : ℝ => z t - ℓ * t) =
        fun t => (z t - (0 + ℓ * t + d * t ^ 2)) + d * t ^ 2 := by
      funext t; ring
    rw [e]
    exact (hR.trans (isBigO_pow_pow (by norm_num : 2 ≤ 3))).add
      ((Asymptotics.isBigO_refl _ _).const_mul_left d)
  have hq : (fun t : ℝ => z t ^ 2 + z t * (ℓ * t) + ℓ ^ 2 * t ^ 2) =O[𝓝 0] fun t : ℝ => t ^ 2 := by
    have h1 : (fun t : ℝ => z t ^ 2) =O[𝓝 0] fun t : ℝ => t ^ 2 := hzO.pow 2
    have h2 : (fun t : ℝ => z t * (ℓ * t)) =O[𝓝 0] fun t : ℝ => t ^ 2 := by
      have := hzO.mul ((Asymptotics.isBigO_refl (fun t : ℝ => t) (𝓝 0)).const_mul_left ℓ)
      exact this.congr (fun t => by ring) (fun t => by ring)
    have h3 : (fun t : ℝ => ℓ ^ 2 * t ^ 2) =O[𝓝 0] fun t : ℝ => t ^ 2 :=
      (Asymptotics.isBigO_refl _ _).const_mul_left _
    exact (h1.add h2).add h3
  have := hw.mul hq
  refine this.congr (fun t => ?_) (fun t => by ring)
  ring

/-- The ratio `p_j(t)/b_j`. -/
def famRatio (j : Count) (t : ℝ) : ℝ := famLaw t j / reference j

theorem famRatio_jet (j : Count) : Jet2 (famRatio j) 1 (famEll j) (famD2 j) := famLaw_ratio_jet j

theorem famRatio_sub_one_jet (j : Count) :
    Jet2 (fun t => famRatio j t - 1) 0 (famEll j) (famD2 j) :=
  ((famRatio_jet j).sub (Jet2.const 1)).coeff (by ring) (by ring) (by ring)

/-- Per-state remainder of the entropy density: `ρ log ρ = z + ½ℓ²t² + (ℓd - ℓ³/6)t³ + O(t⁴)`. -/
theorem famEntropyTerm_isBigO (j : Count) :
    (fun t => famRatio j t * Real.log (famRatio j t) -
      ((famRatio j t - 1) + (famEll j ^ 2 / 2) * t ^ 2 +
        (famEll j * famD2 j - famEll j ^ 3 / 6) * t ^ 3)) =O[𝓝 0] fun t : ℝ => t ^ 4 := by
  have hz := famRatio_sub_one_jet j
  have hR : (fun t : ℝ => (famRatio j t - 1) - (0 + famEll j * t + famD2 j * t ^ 2)) =O[𝓝 0]
      fun t : ℝ => t ^ 3 := hz
  have hzO : (fun t => famRatio j t - 1) =O[𝓝 0] fun t : ℝ => t := by
    have e : (fun t => famRatio j t - 1) = fun t =>
        ((famRatio j t - 1) - (0 + famEll j * t + famD2 j * t ^ 2)) +
          (famEll j * t + famD2 j * t ^ 2) := by
      funext t; ring
    rw [e]
    refine Asymptotics.IsBigO.add (hR.trans (isBigO_pow_id (by norm_num : 1 ≤ 3))) ?_
    exact ((Asymptotics.isBigO_refl _ _).const_mul_left _).add
      ((isBigO_pow_id (by norm_num : 1 ≤ 2)).const_mul_left _)
  have hzt : Tendsto (fun t => famRatio j t - 1) (𝓝 0) (𝓝 0) := by
    simpa using hz.tendsto
  have hsmall : ∀ᶠ t in 𝓝 (0 : ℝ), |famRatio j t - 1| ≤ 1 / 2 := by
    have := (hzt.abs).eventually (Iic_mem_nhds (by norm_num : |(0 : ℝ)| < 1 / 2))
    simpa using this
  have h4 : (fun t => famRatio j t * Real.log (famRatio j t) -
      ((famRatio j t - 1) + (famRatio j t - 1) ^ 2 / 2 - (famRatio j t - 1) ^ 3 / 6)) =O[𝓝 0]
      fun t : ℝ => t ^ 4 := by
    have hb : (fun t => famRatio j t * Real.log (famRatio j t) -
        ((famRatio j t - 1) + (famRatio j t - 1) ^ 2 / 2 - (famRatio j t - 1) ^ 3 / 6))
        =O[𝓝 0] fun t => (famRatio j t - 1) ^ 4 := by
      refine Asymptotics.IsBigO.of_bound 4 ?_
      filter_upwards [hsmall] with t ht
      have := abs_entropy_expansion_le ht
      have e : (1 : ℝ) + (famRatio j t - 1) = famRatio j t := by ring
      rw [e] at this
      simpa [abs_pow] using this
    exact hb.trans (hzO.pow 4)
  have hs := (Jet2.sq_isBigO hz).const_mul_left (1 / 2)
  have hc := (Jet2.cube_isBigO hz).const_mul_left (1 / 6)
  refine ((h4.add hs).sub hc).congr_left (fun t => ?_)
  ring

theorem famEntropy_eq (t : ℝ) : relativeEntropy (famLaw t) reference =
    ∑ j : Count, reference j * (famRatio j t * Real.log (famRatio j t)) := by
  unfold relativeEntropy famRatio
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have := (reference_pos j).ne'
  field_simp

/-- `E_b ℓ² = 144 E_b x² = 12`. -/
theorem sum_reference_ell_sq : ∑ j : Count, reference j * famEll j ^ 2 = 12 := by
  have e : ∀ j : Count, reference j * famEll j ^ 2 =
      ((Nat.choose 12 j.val : ℕ) : ℝ) / 4096 * (2 * (j.val : ℝ) - 12) ^ 2 := by
    intro j; rw [reference_eq]; unfold famEll; ring
  simp_rw [e]
  rw [Fin.sum_univ_eq_sum_range
    (fun j : ℕ => ((Nat.choose 12 j : ℕ) : ℝ) / 4096 * (2 * (j : ℝ) - 12) ^ 2) 13]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [Nat.choose]

/-- Reflection `j ↦ 12 - j` kills the cubic coefficient. -/
theorem sum_reference_cubic : ∑ j : Count,
    reference j * (famEll j * famD2 j - famEll j ^ 3 / 6) = 0 := by
  have e : ∀ j : Count, reference j * (famEll j * famD2 j - famEll j ^ 3 / 6) =
      ((Nat.choose 12 j.val : ℕ) : ℝ) / 4096 *
        ((2 * (j.val : ℝ) - 12) * ((32 / 31) * (2 * ((j.val : ℝ) - 6) ^ 2 - 6)) -
          (2 * (j.val : ℝ) - 12) ^ 3 / 6) := by
    intro j; rw [reference_eq]; unfold famEll famD2; ring
  simp_rw [e]
  rw [Fin.sum_univ_eq_sum_range
    (fun j : ℕ => ((Nat.choose 12 j : ℕ) : ℝ) / 4096 *
        ((2 * (j : ℝ) - 12) * ((32 / 31) * (2 * ((j : ℝ) - 6) ^ 2 - 6)) -
          (2 * (j : ℝ) - 12) ^ 3 / 6)) 13]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [Nat.choose]

theorem sum_reference_ratio_sub_one_eventually :
    ∀ᶠ t in 𝓝 (0 : ℝ), ∑ j : Count, reference j * (famRatio j t - 1) = 0 := by
  filter_upwards [famLaw_sum_eventually] with t hm
  have e : ∀ j : Count, reference j * (famRatio j t - 1) = famLaw t j - reference j := by
    intro j; unfold famRatio; have := (reference_pos j).ne'; field_simp
  simp_rw [e]
  rw [Finset.sum_sub_distrib, hm, reference_mass]; ring

/-- `H(p(t)|b) = 6 t² + O(t⁴)`. -/
theorem famEntropy_isBigO :
    (fun t => relativeEntropy (famLaw t) reference - 6 * t ^ 2) =O[𝓝 0] fun t : ℝ => t ^ 4 := by
  have hsum : (fun t => ∑ j : Count, reference j * (famRatio j t * Real.log (famRatio j t) -
      ((famRatio j t - 1) + (famEll j ^ 2 / 2) * t ^ 2 +
        (famEll j * famD2 j - famEll j ^ 3 / 6) * t ^ 3))) =O[𝓝 0] fun t : ℝ => t ^ 4 :=
    Asymptotics.IsBigO.fun_sum (fun j _ => (famEntropyTerm_isBigO j).const_mul_left _)
  refine hsum.congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [sum_reference_ratio_sub_one_eventually] with t h0
  rw [famEntropy_eq]
  simp only [mul_sub, Finset.sum_sub_distrib, mul_add, Finset.sum_add_distrib]
  have h2 : ∑ j : Count, reference j * (famEll j ^ 2 / 2 * t ^ 2) = 6 * t ^ 2 := by
    have : ∑ j : Count, reference j * (famEll j ^ 2 / 2 * t ^ 2) =
        (t ^ 2 / 2) * ∑ j : Count, reference j * famEll j ^ 2 := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun j _ => by ring)
    rw [this, sum_reference_ell_sq]; ring
  have h3 : ∑ j : Count, reference j * ((famEll j * famD2 j - famEll j ^ 3 / 6) * t ^ 3) = 0 := by
    have : ∑ j : Count, reference j * ((famEll j * famD2 j - famEll j ^ 3 / 6) * t ^ 3) =
        t ^ 3 * ∑ j : Count, reference j * (famEll j * famD2 j - famEll j ^ 3 / 6) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun j _ => by ring)
    rw [this, sum_reference_cubic]; ring
  simp only [mul_sub, Finset.sum_sub_distrib] at h0
  linarith

theorem famMoment_sq_isBigO (s : Order) :
    (fun t => famMoment s t ^ 2 - (if s.val = 0 then t ^ 2 else 0)) =O[𝓝 0] fun t : ℝ => t ^ 4 := by
  by_cases h0 : s.val = 0
  · have h1 : s.val ≠ 1 := by omega
    have hJ : Jet2 (famMoment s) 0 1 0 := by
      have := famMoment_jet s
      simpa [h0, h1] using this
    have hR : (fun t : ℝ => famMoment s t - t) =O[𝓝 0] fun t : ℝ => t ^ 3 := by
      have : (fun t : ℝ => famMoment s t - (0 + 1 * t + 0 * t ^ 2)) =O[𝓝 0] fun t : ℝ => t ^ 3 := hJ
      exact this.congr_left (fun t => by ring)
    have hM : (fun t => famMoment s t) =O[𝓝 0] fun t : ℝ => t := by
      have e : (fun t => famMoment s t) = fun t => (famMoment s t - t) + t := by funext t; ring
      rw [e]
      exact (hR.trans (isBigO_pow_id (by norm_num : 1 ≤ 3))).add (Asymptotics.isBigO_refl _ _)
    have hsum : (fun t => famMoment s t + t) =O[𝓝 0] fun t : ℝ => t :=
      hM.add (Asymptotics.isBigO_refl _ _)
    have := hR.mul hsum
    simp only [h0, ↓reduceIte]
    exact this.congr (fun t => by ring) (fun t => by ring)
  · have hM2 : (fun t => famMoment s t) =O[𝓝 0] fun t : ℝ => t ^ 2 := by
      by_cases h1 : s.val = 1
      · have hJ : Jet2 (famMoment s) 0 0 (32 / 31) := by
          have := famMoment_jet s
          simpa [h0, h1] using this
        have hR : (fun t : ℝ => famMoment s t - 32 / 31 * t ^ 2) =O[𝓝 0] fun t : ℝ => t ^ 3 := by
          have : (fun t : ℝ => famMoment s t - (0 + 0 * t + 32 / 31 * t ^ 2)) =O[𝓝 0]
              fun t : ℝ => t ^ 3 := hJ
          exact this.congr_left (fun t => by ring)
        have e : (fun t => famMoment s t) = fun t => (famMoment s t - 32 / 31 * t ^ 2) +
            32 / 31 * t ^ 2 := by funext t; ring
        rw [e]
        exact (hR.trans (isBigO_pow_pow (by norm_num : 2 ≤ 3))).add
          ((Asymptotics.isBigO_refl _ _).const_mul_left _)
      · have hJ : Jet2 (famMoment s) 0 0 0 := by
          have := famMoment_jet s
          simpa [h0, h1] using this
        have : (fun t : ℝ => famMoment s t - (0 + 0 * t + 0 * t ^ 2)) =O[𝓝 0]
            fun t : ℝ => t ^ 3 := hJ
        exact (this.congr_left (fun t => by ring)).trans (isBigO_pow_pow (by norm_num : 2 ≤ 3))
    have := hM2.pow 2
    simp only [h0, ↓reduceIte, sub_zero]
    exact this.congr_right (fun t => by ring)

/-- `p(t)^T W p(t) = 12 t² + O(t⁴)`. -/
theorem famQuadratic_isBigO :
    (fun t => quadratic (famLaw t) - 12 * t ^ 2) =O[𝓝 0] fun t : ℝ => t ^ 4 := by
  have hsum : (fun t => ∑ s : Order, weight s *
      (famMoment s t ^ 2 - (if s.val = 0 then t ^ 2 else 0))) =O[𝓝 0] fun t : ℝ => t ^ 4 :=
    Asymptotics.IsBigO.fun_sum (fun s _ => (famMoment_sq_isBigO s).const_mul_left _)
  refine hsum.congr_left (fun t => ?_)
  rw [quadratic_eq_sum]
  simp only [mul_sub, Finset.sum_sub_distrib]
  have h := sum_order_ite weight 0 (by norm_num) (t ^ 2)
  rw [weight_zero] at h
  have h' : ∑ s : Order, weight s * (if s.val = 0 then t ^ 2 else 0) = 12 * t ^ 2 := h
  rw [h']
  rfl

theorem psiV2_isBigO : psiV2 =O[𝓝 0] fun t : ℝ => t ^ 4 := by
  have hc : ContinuousAt (fun t : ℝ => (14 - 10 * t ^ 2)⁻¹) 0 := by
    apply ContinuousAt.inv₀
    · fun_prop
    · norm_num
  have hb : (fun t : ℝ => (14 - 10 * t ^ 2)⁻¹) =O[𝓝 0] fun _ : ℝ => (1 : ℝ) :=
    Filter.Tendsto.isBigO_one ℝ hc.tendsto
  have := (Asymptotics.isBigO_refl (fun t : ℝ => t ^ 4) (𝓝 0)).mul hb
  refine this.congr (fun t => ?_) (fun t => by ring)
  unfold psiV2; ring

/-- **Origin vanishing order** `f(t) = O(t⁴)`. -/
theorem famF_isBigO : famF =O[𝓝 0] fun t : ℝ => t ^ 4 := by
  have h := ((famEntropy_isBigO.const_mul_left 2).sub famQuadratic_isBigO).add
    (psiV2_isBigO.const_mul_left 12)
  refine h.congr_left (fun t => ?_)
  unfold famF functional
  ring

end BecknerOnofri.V2.FiniteState
