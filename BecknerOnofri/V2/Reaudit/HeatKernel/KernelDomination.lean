module

public import BecknerOnofri.V2.Reaudit.HeatKernel.HeatComparison

@[expose] public section

/-! # Pointwise kernel nonnegativity and domination (U05/S015, printed `eq:potential-kernel-domination`)

From the operator inequalities `0 ≤ e^{-tB_m} f ≤ e^{-ct} e^{-tP_D} f` (`HeatComparison`) and the
continuity of the eigenfunction-expansion kernel, test against indicators of boxes
`(a,b) × (c,d) ⊂ (0,π)²` to obtain, for `t > 0`, `x, y ∈ (0,π)`:

* `heatKernel_nonneg_V2`: `0 ≤ p_{B_m}(t;x,y)`,
* `heatKernel_le_decayed_V2`: `p_{B_m}(t;x,y) ≤ e^{-m(m-1)t} p_{P_D}(t;x,y)`,
* `heatKernel_le_dirichlet_V2` and `heatKernel_lt_dirichlet_V2` (`m ≥ 2`) as consequences.

The statements coincide with the legacy `heatKernel_nonnegative_all`, `heatKernel_le_dirichlet`,
`heatKernel_lt_dirichlet`; the proofs here do not use the legacy maximum principle.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology BigOperators ContDiff
namespace BecknerOnofri.V2.Reaudit.HeatKernel.Engine
open Legacy.BecknerOnofri Legacy.BecknerOnofri.JacobiEigenfunctions
  Legacy.BecknerOnofri.JacobiHeatBounds Legacy.BecknerOnofri.JacobiHeatPositivity
  Legacy.BecknerOnofri.PositiveOperatorNeumann Legacy.BecknerOnofri.BoundedL2Multiplier

/-! ### Continuity of box integrals -/

theorem continuous_box_inner {Q : ℝ → ℝ → ℝ} (hQ : Continuous (fun p : ℝ × ℝ => Q p.1 p.2))
    {c d : ℝ} (hcd : c ≤ d) : Continuous (fun x => ∫ y in Ioo c d, Q x y) := by
  have h := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (μ := volume)
    (f := Q) hQ c d
  convert h using 2 with x
  rw [intervalIntegral.integral_of_le hcd, integral_Ioc_eq_integral_Ioo]

theorem integrableOn_box_inner {Q : ℝ → ℝ → ℝ} (hQ : Continuous (fun p : ℝ × ℝ => Q p.1 p.2))
    {a b c d : ℝ} (hcd : c ≤ d) : IntegrableOn (fun x => ∫ y in Ioo c d, Q x y) (Ioo a b) := by
  exact ((continuous_box_inner hQ hcd).continuousOn.integrableOn_Icc (a := a) (b := b)).mono_set
    Ioo_subset_Icc_self

theorem integrableOn_slice {Q : ℝ → ℝ → ℝ} (hQ : Continuous (fun p : ℝ × ℝ => Q p.1 p.2))
    (x : ℝ) (c d : ℝ) : IntegrableOn (fun y => Q x y) (Ioo c d) := by
  have : Continuous (fun y => Q x y) := hQ.comp (continuous_const.prodMk continuous_id)
  exact (this.continuousOn.integrableOn_Icc (a := c) (b := d)).mono_set Ioo_subset_Icc_self

/-- A continuous kernel that is negative at a point of `(0,π)²` has a box in `(0,π)²` with
negative double integral. -/
theorem exists_box_neg {Q : ℝ → ℝ → ℝ} (hQ : Continuous (fun p : ℝ × ℝ => Q p.1 p.2)) {x0 y0 : ℝ}
    (hx : x0 ∈ Ioo 0 Real.pi) (hy : y0 ∈ Ioo 0 Real.pi) (hneg : Q x0 y0 < 0) :
    ∃ a b c d : ℝ, a < b ∧ c < d ∧ Ioo a b ⊆ Ioo 0 Real.pi ∧ Ioo c d ⊆ Ioo 0 Real.pi ∧
      ∫ x in Ioo a b, ∫ y in Ioo c d, Q x y < 0 := by
  set q := Q x0 y0 / 2 with hq
  have hqneg : q < 0 := by rw [hq]; linarith
  have hev : ∀ᶠ p in 𝓝 (x0, y0), Q p.1 p.2 < q := by
    have : Q x0 y0 < q := by rw [hq]; linarith
    exact hQ.continuousAt.eventually (Iio_mem_nhds this)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
  obtain ⟨δ, hδ⟩ : ∃ δ, δ = min (min (ε / 2) (min x0 (Real.pi - x0))) (min y0 (Real.pi - y0)) :=
    ⟨_, rfl⟩
  have hδpos : 0 < δ := by
    rw [hδ]
    refine lt_min (lt_min (by positivity) (lt_min hx.1 (by linarith [hx.2]))) (lt_min hy.1
      (by linarith [hy.2]))
  have hδ1 : δ ≤ ε / 2 := by rw [hδ]; exact (min_le_left _ _).trans (min_le_left _ _)
  have hδ2 : δ ≤ x0 := by
    rw [hδ]; exact (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδ3 : δ ≤ Real.pi - x0 := by
    rw [hδ]; exact (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hδ4 : δ ≤ y0 := by rw [hδ]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hδ5 : δ ≤ Real.pi - y0 := by rw [hδ]; exact (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨x0 - δ, x0 + δ, y0 - δ, y0 + δ, by linarith, by linarith, ?_, ?_, ?_⟩
  · intro z hz; exact ⟨by linarith [hz.1], by linarith [hz.2]⟩
  · intro z hz; exact ⟨by linarith [hz.1], by linarith [hz.2]⟩
  · have hinner : ∀ x ∈ Ioo (x0 - δ) (x0 + δ), ∫ y in Ioo (y0 - δ) (y0 + δ), Q x y ≤ q * (2 * δ) := by
      intro x hxI
      have h1 : ∫ y in Ioo (y0 - δ) (y0 + δ), Q x y ≤ ∫ y in Ioo (y0 - δ) (y0 + δ), q := by
        apply setIntegral_mono_on (integrableOn_slice hQ x _ _) (integrableOn_const (by simp))
          measurableSet_Ioo
        intro y hyJ
        refine le_of_lt (hball (y := (x, y)) ?_)
        rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, max_lt_iff]
        constructor
        · rw [abs_lt]; constructor <;> linarith [hxI.1, hxI.2]
        · rw [abs_lt]; constructor <;> linarith [hyJ.1, hyJ.2]
      have h2 : ∫ y in Ioo (y0 - δ) (y0 + δ), q = q * (2 * δ) := by
        rw [setIntegral_const, Measure.real, Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith)]
        simp only [smul_eq_mul]; ring
      linarith
    have houter : ∫ x in Ioo (x0 - δ) (x0 + δ), ∫ y in Ioo (y0 - δ) (y0 + δ), Q x y ≤
        ∫ x in Ioo (x0 - δ) (x0 + δ), q * (2 * δ) := by
      apply setIntegral_mono_on (integrableOn_box_inner hQ (by linarith))
        (integrableOn_const (by simp)) measurableSet_Ioo
      exact hinner
    have h3 : ∫ x in Ioo (x0 - δ) (x0 + δ), q * (2 * δ) = q * (2 * δ) * (2 * δ) := by
      rw [setIntegral_const, Measure.real, Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith)]
      simp only [smul_eq_mul]; ring
    have : q * (2 * δ) * (2 * δ) < 0 := by
      have h2δ : 0 < 2 * δ := by linarith
      exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hqneg h2δ) h2δ
    linarith

/-! ### Indicators of boxes -/

/-- The indicator of `(a,b)` in `L²(0,π)`. -/
def ind (a b : ℝ) : JacobiL2 :=
  indicatorConstLp 2 (measurableSet_Ioo (a := a) (b := b)) (measure_ne_top intervalMeasure _)
    (1 : ℝ)

theorem ind_ae (a b : ℝ) :
    (⇑(ind a b) : ℝ → ℝ) =ᵐ[intervalMeasure] (Ioo a b).indicator (fun _ => (1 : ℝ)) :=
  indicatorConstLp_coeFn

theorem ind_nonneg (a b : ℝ) : 0 ≤ ind a b := by
  apply (nonnegative_iff intervalMeasure _).mp
  filter_upwards [ind_ae a b] with x hx
  rw [hx]
  exact Set.indicator_nonneg (fun _ _ => zero_le_one) x

theorem inner_nonneg_L2 {g h : JacobiL2} (hg : 0 ≤ g) (hh : 0 ≤ h) : 0 ≤ inner ℝ g h := by
  have hg' := (nonnegative_iff intervalMeasure _).mpr hg
  have hh' := (nonnegative_iff intervalMeasure _).mpr hh
  rw [L2.inner_def]
  apply integral_nonneg_of_ae
  filter_upwards [hg', hh'] with x h1 h2
  simp only [RCLike.inner_apply, conj_trivial]
  exact mul_nonneg h2 h1

theorem kact_ind (m : ℕ) {t : ℝ} (ht : 0 < t) {c d : ℝ} (hcd : Ioo c d ⊆ Ioo 0 Real.pi) (x : ℝ) :
    kact m t (ind c d) x = ∫ y in Ioo c d, heatKernel m t x y := by
  unfold kact
  have h1 : ∫ y, heatKernel m t x y * (ind c d) y ∂intervalMeasure =
      ∫ y, (Ioo c d).indicator (fun y => heatKernel m t x y) y ∂intervalMeasure := by
    apply integral_congr_ae
    filter_upwards [ind_ae c d] with y hy
    rw [hy]
    by_cases hyI : y ∈ Ioo c d
    · simp [hyI]
    · simp [hyI]
  rw [h1, integral_indicator measurableSet_Ioo]
  unfold intervalMeasure
  rw [Measure.restrict_restrict measurableSet_Ioo, inter_eq_left.mpr hcd]

theorem inner_ind_heat {m : ℕ} (hm : 0 < m) {t : ℝ} (ht : 0 < t) {a b c d : ℝ}
    (hab : Ioo a b ⊆ Ioo 0 Real.pi) (hcd : Ioo c d ⊆ Ioo 0 Real.pi) :
    inner ℝ (ind a b) (heatOp hm t (ind c d)) =
      ∫ x in Ioo a b, ∫ y in Ioo c d, heatKernel m t x y := by
  rw [inner_heatOp_eq_tsum hm ht.le, ← integral_mul_kact m ht (ind c d) (ind a b)]
  have h1 : ∫ x, (ind a b) x * kact m t (ind c d) x ∂intervalMeasure =
      ∫ x, (Ioo a b).indicator (fun x => kact m t (ind c d) x) x ∂intervalMeasure := by
    apply integral_congr_ae
    filter_upwards [ind_ae a b] with x hx
    rw [hx]
    by_cases hxI : x ∈ Ioo a b
    · simp [hxI]
    · simp [hxI]
  rw [h1, integral_indicator measurableSet_Ioo]
  unfold intervalMeasure
  rw [Measure.restrict_restrict measurableSet_Ioo, inter_eq_left.mpr hab]
  apply integral_congr_ae
  filter_upwards [] with x
  exact kact_ind m ht hcd x

/-! ### The pointwise theorems -/

/-- Nonnegativity of the heat kernel of `B_m` (`m ≥ 1`). -/
theorem heatKernel_nonneg_V2 {m : ℕ} (hm : 0 < m) {t x y : ℝ} (ht : 0 < t)
    (hx : x ∈ Ioo 0 Real.pi) (hy : y ∈ Ioo 0 Real.pi) : 0 ≤ heatKernel m t x y := by
  by_contra hneg
  push_neg at hneg
  obtain ⟨a, b, c, d, hab, hcd, hI, hJ, hint⟩ := exists_box_neg
    (Q := fun x y => heatKernel m t x y) (heatKernel_continuous_joint m ht) hx hy hneg
  have h := inner_nonneg_L2 (ind_nonneg a b) (heatOp_nonneg hm ht (ind_nonneg c d))
  rw [inner_ind_heat hm ht hI hJ] at h
  linarith

theorem heatKernel_nonnegative_all_V2 (m : ℕ) {t x y : ℝ} (ht : 0 < t)
    (hx : x ∈ Ioo 0 Real.pi) (hy : y ∈ Ioo 0 Real.pi) : 0 ≤ heatKernel m t x y := by
  by_cases hm : m = 0
  · subst m
    exact (heatKernel_zero_pos ht x y).le
  · exact heatKernel_nonneg_V2 (Nat.pos_of_ne_zero hm) ht hx hy

/-- **Domination of the heat kernel of `B_m` by the decayed Dirichlet kernel.** -/
theorem heatKernel_le_decayed_V2 {m : ℕ} (hm : 0 < m) {t x y : ℝ} (ht : 0 < t)
    (hx : x ∈ Ioo 0 Real.pi) (hy : y ∈ Ioo 0 Real.pi) :
    heatKernel m t x y ≤ Real.exp (-(cc m) * t) * heatKernel 1 t x y := by
  by_contra hneg
  push_neg at hneg
  set A := Real.exp (-(cc m) * t) with hA
  have hQ : Continuous (fun p : ℝ × ℝ => A * heatKernel 1 t p.1 p.2 - heatKernel m t p.1 p.2) :=
    (continuous_const.mul (heatKernel_continuous_joint 1 ht)).sub (heatKernel_continuous_joint m ht)
  obtain ⟨a, b, c, d, hab, hcd, hI, hJ, hint⟩ := exists_box_neg
    (Q := fun x y => A * heatKernel 1 t x y - heatKernel m t x y) hQ hx hy (by linarith)
  have hK1 : Continuous (fun p : ℝ × ℝ => heatKernel 1 t p.1 p.2) := heatKernel_continuous_joint 1 ht
  have hKm : Continuous (fun p : ℝ × ℝ => heatKernel m t p.1 p.2) := heatKernel_continuous_joint m ht
  -- linearity of the box integral
  have hlin : ∫ x in Ioo a b, ∫ y in Ioo c d, (A * heatKernel 1 t x y - heatKernel m t x y) =
      A * (∫ x in Ioo a b, ∫ y in Ioo c d, heatKernel 1 t x y) -
        ∫ x in Ioo a b, ∫ y in Ioo c d, heatKernel m t x y := by
    have hin : ∀ x, ∫ y in Ioo c d, (A * heatKernel 1 t x y - heatKernel m t x y) =
        A * (∫ y in Ioo c d, heatKernel 1 t x y) - ∫ y in Ioo c d, heatKernel m t x y := by
      intro x
      rw [integral_sub ((integrableOn_slice hK1 x c d).const_mul A) (integrableOn_slice hKm x c d),
        integral_const_mul]
    simp_rw [hin]
    rw [integral_sub ((integrableOn_box_inner hK1 hcd.le).const_mul A)
      (integrableOn_box_inner hKm hcd.le), integral_const_mul]
  have hge : 0 ≤ A * inner ℝ (ind a b) (heatOp one_pos t (ind c d)) -
      inner ℝ (ind a b) (heatOp hm t (ind c d)) := by
    have h := inner_nonneg_L2 (ind_nonneg a b)
      (sub_nonneg.mpr (heatOp_le hm ht (ind_nonneg c d)))
    rw [inner_sub_right, inner_smul_right] at h
    exact h
  rw [inner_ind_heat one_pos ht hI hJ, inner_ind_heat hm ht hI hJ] at hge
  rw [hlin] at hint
  linarith

/-- Same statement as the legacy `heatKernel_le_dirichlet`. -/
theorem heatKernel_le_dirichlet_V2 {m : ℕ} (hm : 0 < m) {t x y : ℝ} (ht : 0 < t)
    (hx : x ∈ Ioo 0 Real.pi) (hy : y ∈ Ioo 0 Real.pi) :
    heatKernel m t x y ≤ heatKernel 1 t x y := by
  have hdec : Real.exp (-(cc m) * t) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (cc_nonneg hm)) ht.le
  exact (heatKernel_le_decayed_V2 hm ht hx hy).trans
    (mul_le_of_le_one_left (heatKernel_one_pos ht hx hy).le hdec)

/-- Same statement as the legacy `heatKernel_lt_dirichlet` (strict, `m ≥ 2`). -/
theorem heatKernel_lt_dirichlet_V2 {m : ℕ} (hm : 2 ≤ m) {t x y : ℝ} (ht : 0 < t)
    (hx : x ∈ Ioo 0 Real.pi) (hy : y ∈ Ioo 0 Real.pi) :
    heatKernel m t x y < heatKernel 1 t x y := by
  have hm0 : 0 < m := by omega
  have hc : 0 < cc m := by
    have h2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
    unfold cc
    nlinarith
  have hdec : Real.exp (-(cc m) * t) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  have hpos := heatKernel_one_pos ht hx hy
  calc heatKernel m t x y ≤ Real.exp (-(cc m) * t) * heatKernel 1 t x y :=
        heatKernel_le_decayed_V2 hm0 ht hx hy
    _ < 1 * heatKernel 1 t x y := mul_lt_mul_of_pos_right hdec hpos
    _ = _ := one_mul _

end BecknerOnofri.V2.Reaudit.HeatKernel.Engine
