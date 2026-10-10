module

public import BecknerOnofri.V2.Reaudit.Obstruction.ThetaGaussian
public import BecknerOnofri.V2.Reaudit.Obstruction.GreenAutocorrelation
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section

/-! # Row S006: a logarithmic lower bound for the Green energy of a localized density

Let `ψ` be a bounded, nonnegative, measurable function on the torus `𝕋^d` of integral `1`, vanishing
outside the set `{z : ‖z_j‖ ≤ c for all j}` (the circle norm `‖z_j‖` is the distance to `0` in
`ℝ/ℤ`), with `π d c² ≤ 1`.  Then the pairing of the Green function `G` of the torus with `ψ` satisfies

  `∫ G ψ ≥ log (1/c) - K`,    `K` depending only on `d`.

The printed argument (`lem:section2-universal-obstructions`, proof of (i)) obtains the asymptotics
`∬ γ(εx - εy) η(x) η(y) = log(1/ε) - ∬ log|x-y| η η + R + o(1)` from the Robin-constant expansion of
the Green function near the origin.  The Green function is available in this repository only as an
`L²` class (`GreenKernelReal.realGreen`), so a pointwise expansion is not used.  What the printed
argument uses of the expansion is the lower bound `log(1/ε) - O(1)` with the sharp coefficient `1`,
and this is obtained here from the Mellin representation (reused:
`GreenMellinPairing.realGreen_mellin_heat_pairing`)

  `2 ∫ G ψ = ∫_0^∞ u^{d/2-1} ∫ (θ_u - 1) ψ du`,

together with the Gaussian lower bound for the heat kernel (`torusTheta_re_ge_gaussian`):
for `u > 0`, `∫ θ_u ψ ≥ u^{-d/2} exp(-π d c²/u)`, hence `u^{d/2-1} ∫ (θ_u - 1) ψ ≥ 1/u - π d c²/u² -
u^{d/2-1}`, whose integral over `[π d c², 1]` is `log(1/(π d c²)) - O(1)`.  Outside that interval the
integrand is bounded below by `-u^{d/2-1}` for `u ≤ 1` (positivity of the heat kernel) and by
`-u^{d/2-1} T e^{-π u/2}` for `u > 1` (uniform exponential decay of `θ_u - 1`,
`TorusHeatBounds.torusTheta_sub_one_norm_le`), both integrable on the respective ranges. -/

noncomputable section
open MeasureTheory Set
open Legacy.TorusEndpoint Legacy.TorusEndpoint.TorusHeatPositivity
  Legacy.TorusEndpoint.TorusHeatBounds

namespace BecknerOnofri.V2.Reaudit.Obstruction

variable {d : ℕ}

/-- The Mellin integrand `u^{d/2-1} ∫ (θ_u - 1) ψ` of the heat representation of the Green pairing. -/
def heatPairing (d : ℕ) (ψ : Torus d → ℝ) (u : ℝ) : ℝ :=
  u ^ ((d : ℝ) / 2 - 1) * ∫ x, ((torusTheta u x).re - 1) * ψ x ∂torusMeasure d

/-- A majorant of the negative part of `heatPairing`: `u^{d/2-1}` for `u ≤ 1` and
`u^{d/2-1} T e^{-π u/2}` for `u > 1`, `T` the heat tail mass of `𝕋^d`. -/
def tailMajorant (d : ℕ) (u : ℝ) : ℝ :=
  u ^ ((d : ℝ) / 2 - 1) * (if u ≤ 1 then 1 else heatTailMass d * Real.exp (-Real.pi * u / 2))

lemma tailMajorant_integrableOn (hd : 0 < d) : IntegrableOn (tailMajorant d) (Ioi 0) := by
  have hs : (-1 : ℝ) < (d : ℝ) / 2 - 1 := by
    have : (0 : ℝ) < d := Nat.cast_pos.mpr hd
    linarith
  have hsplit : Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 := (Ioc_union_Ioi_eq_Ioi zero_le_one).symm
  rw [hsplit]
  refine IntegrableOn.union ?_ ?_
  · have h1 : IntegrableOn (fun u : ℝ => u ^ ((d : ℝ) / 2 - 1)) (Ioc 0 1) :=
      (intervalIntegral.intervalIntegrable_rpow' hs).1
    refine h1.congr_fun (fun u hu => ?_) measurableSet_Ioc
    simp [tailMajorant, hu.2]
  · have h1 := (integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := (d : ℝ) / 2 - 1)
      (b := Real.pi / 2) hs one_pos (by positivity)).mono_set (Ioi_subset_Ioi zero_le_one)
    have h2 : IntegrableOn (fun u : ℝ => heatTailMass d *
        (u ^ ((d : ℝ) / 2 - 1) * Real.exp (-(Real.pi / 2) * u ^ (1 : ℝ)))) (Ioi 1) :=
      h1.const_mul (heatTailMass d)
    refine IntegrableOn.congr_fun h2 (fun u hu => ?_) measurableSet_Ioi
    have hu1 : ¬ u ≤ 1 := not_le.mpr hu
    simp only [tailMajorant, hu1, ite_false, Real.rpow_one]
    have : -(Real.pi / 2) * u = -Real.pi * u / 2 := by ring
    rw [this]
    ring

section HeatPairing

variable {ψ : Torus d → ℝ}

lemma thetaRe_mul_integrable {u : ℝ} (hu : 0 < u) (hψi : Integrable ψ (torusMeasure d)) :
    Integrable (fun x => (torusTheta u x).re * ψ x) (torusMeasure d) := by
  refine hψi.bdd_mul (c := (torusTheta u (0 : Torus d)).re)
    (Complex.continuous_re.comp (torusTheta_continuous hu)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (torusTheta_re_pos hu x)]
  exact EndpointSharpnessHeat.heatDensity_le_peak d hu x

lemma integral_theta_sub_one {u : ℝ} (hu : 0 < u) (hψi : Integrable ψ (torusMeasure d))
    (hψ1 : ∫ x, ψ x ∂torusMeasure d = 1) :
    ∫ x, ((torusTheta u x).re - 1) * ψ x ∂torusMeasure d =
      (∫ x, (torusTheta u x).re * ψ x ∂torusMeasure d) - 1 := by
  simp_rw [sub_mul, one_mul]
  rw [integral_sub (thetaRe_mul_integrable hu hψi) hψi, hψ1]

/-- Gaussian lower bound for the heat pairing of a function localized in a sup-ball. -/
lemma gaussian_lower_integral {c : ℝ} (hψ0 : ∀ x, 0 ≤ ψ x) (hψi : Integrable ψ (torusMeasure d))
    (hψ1 : ∫ x, ψ x ∂torusMeasure d = 1) (hψs : ∀ z, ψ z ≠ 0 → ∀ j, ‖z j‖ ≤ c) {u : ℝ}
    (hu : 0 < u) :
    u ^ (-(d : ℝ) / 2) * Real.exp (-(Real.pi * d * c ^ 2) / u) ≤
      ∫ x, (torusTheta u x).re * ψ x ∂torusMeasure d := by
  have h1 : ∫ x, u ^ (-(d : ℝ) / 2) * Real.exp (-(Real.pi * d * c ^ 2) / u) * ψ x
      ∂torusMeasure d = u ^ (-(d : ℝ) / 2) * Real.exp (-(Real.pi * d * c ^ 2) / u) := by
    rw [integral_const_mul, hψ1, mul_one]
  rw [← h1]
  apply integral_mono (hψi.const_mul _) (thetaRe_mul_integrable hu hψi)
  intro x
  by_cases hx : ψ x = 0
  · simp [hx]
  · apply mul_le_mul_of_nonneg_right _ (hψ0 x)
    refine le_trans ?_ (torusTheta_re_ge_gaussian hu x)
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hu.le _)
    apply Real.exp_le_exp.mpr
    have hs : ∑ j, ‖x j‖ ^ 2 ≤ d * c ^ 2 := by
      calc ∑ j, ‖x j‖ ^ 2 ≤ ∑ _j : Fin d, c ^ 2 :=
            Finset.sum_le_sum fun j _ => pow_le_pow_left₀ (norm_nonneg _) (hψs x hx j) 2
        _ = d * c ^ 2 := by simp
    rw [div_le_div_iff_of_pos_right hu]
    nlinarith [Real.pi_pos]

/-- The lower bound on `[π d c², 1]`, valid for every `u > 0`. -/
lemma heatPairing_ge_main {c : ℝ} (hψ0 : ∀ x, 0 ≤ ψ x) (hψi : Integrable ψ (torusMeasure d))
    (hψ1 : ∫ x, ψ x ∂torusMeasure d = 1) (hψs : ∀ z, ψ z ≠ 0 → ∀ j, ‖z j‖ ≤ c) {u : ℝ}
    (hu : 0 < u) :
    u⁻¹ - (Real.pi * d * c ^ 2) * (u ^ 2)⁻¹ - u ^ ((d : ℝ) / 2 - 1) ≤ heatPairing d ψ u := by
  unfold heatPairing
  rw [integral_theta_sub_one hu hψi hψ1]
  have hI := gaussian_lower_integral hψ0 hψi hψ1 hψs hu
  have hexp : 1 - (Real.pi * d * c ^ 2) / u ≤ Real.exp (-(Real.pi * d * c ^ 2) / u) := by
    have := Real.add_one_le_exp (-(Real.pi * d * c ^ 2) / u)
    rw [neg_div] at this ⊢
    linarith
  have hprod : u ^ ((d : ℝ) / 2 - 1) * u ^ (-(d : ℝ) / 2) = u⁻¹ := by
    rw [← Real.rpow_add hu, show (d : ℝ) / 2 - 1 + -(d : ℝ) / 2 = -1 by ring, Real.rpow_neg_one]
  have hpos : 0 ≤ u ^ ((d : ℝ) / 2 - 1) := Real.rpow_nonneg hu.le _
  have h2 : u ^ (-(d : ℝ) / 2) * (1 - (Real.pi * d * c ^ 2) / u) ≤
      ∫ x, (torusTheta u x).re * ψ x ∂torusMeasure d :=
    le_trans (mul_le_mul_of_nonneg_left hexp (Real.rpow_nonneg hu.le _)) hI
  have h3 := mul_le_mul_of_nonneg_left (sub_le_sub_right h2 1) hpos
  refine le_trans (le_of_eq ?_) h3
  have e1 : u ^ ((d : ℝ) / 2 - 1) * (u ^ (-(d : ℝ) / 2) * (1 - (Real.pi * d * c ^ 2) / u) - 1) =
      (u ^ ((d : ℝ) / 2 - 1) * u ^ (-(d : ℝ) / 2)) * (1 - (Real.pi * d * c ^ 2) / u) -
        u ^ ((d : ℝ) / 2 - 1) := by ring
  rw [e1, hprod]
  have hu0 : u ≠ 0 := hu.ne'
  field_simp

lemma heatPairing_ge_neg (hψ0 : ∀ x, 0 ≤ ψ x) (hψi : Integrable ψ (torusMeasure d))
    (hψ1 : ∫ x, ψ x ∂torusMeasure d = 1) {u : ℝ} (hu : 0 < u) :
    -u ^ ((d : ℝ) / 2 - 1) ≤ heatPairing d ψ u := by
  unfold heatPairing
  rw [integral_theta_sub_one hu hψi hψ1]
  have h0 : 0 ≤ ∫ x, (torusTheta u x).re * ψ x ∂torusMeasure d :=
    integral_nonneg fun x => mul_nonneg (torusTheta_re_pos hu x).le (hψ0 x)
  have hpos : 0 ≤ u ^ ((d : ℝ) / 2 - 1) := Real.rpow_nonneg hu.le _
  nlinarith

lemma heatPairing_ge_tail (hψ0 : ∀ x, 0 ≤ ψ x) (hψi : Integrable ψ (torusMeasure d))
    (hψ1 : ∫ x, ψ x ∂torusMeasure d = 1) {u : ℝ} (hu : 1 < u) :
    -(u ^ ((d : ℝ) / 2 - 1) * (heatTailMass d * Real.exp (-Real.pi * u / 2))) ≤
      heatPairing d ψ u := by
  have hu0 : 0 < u := lt_trans zero_lt_one hu
  unfold heatPairing
  have hpos : 0 ≤ u ^ ((d : ℝ) / 2 - 1) := Real.rpow_nonneg hu0.le _
  have hb : -(heatTailMass d * Real.exp (-Real.pi * u / 2)) ≤
      ∫ x, ((torusTheta u x).re - 1) * ψ x ∂torusMeasure d := by
    have h1 : ∫ x, -(heatTailMass d * Real.exp (-Real.pi * u / 2)) * ψ x ∂torusMeasure d =
        -(heatTailMass d * Real.exp (-Real.pi * u / 2)) := by
      rw [integral_const_mul, hψ1, mul_one]
    rw [← h1]
    apply integral_mono (hψi.const_mul _)
    · simp_rw [sub_mul, one_mul]
      exact (thetaRe_mul_integrable hu0 hψi).sub hψi
    · intro x
      apply mul_le_mul_of_nonneg_right _ (hψ0 x)
      have h1 := torusTheta_sub_one_norm_le (d := d) hu.le x
      have h2 : |(torusTheta u x).re - 1| ≤ ‖torusTheta u x - 1‖ := by
        have := Complex.abs_re_le_norm (torusTheta u x - 1)
        simpa using this
      have := neg_abs_le ((torusTheta u x).re - 1)
      linarith
  nlinarith


/-- **Logarithmic lower bound for the Green pairing of a localized function.**  There is a constant
`K`, depending only on `d`, such that every bounded measurable `ψ ≥ 0` of integral `1` vanishing
outside `{z : ∀ j, ‖z j‖ ≤ c}`, with `π d c² ≤ 1`, satisfies `log (1/c) - K ≤ ∫ G ψ`. -/
theorem green_pairing_localized_lower (hd : 0 < d) :
    ∃ K : ℝ, ∀ (ψ : Torus d → ℝ) (c M : ℝ), 0 < c → Real.pi * d * c ^ 2 ≤ 1 →
      Measurable ψ → (∀ x, 0 ≤ ψ x) → (∀ x, ψ x ≤ M) → ∫ x, ψ x ∂torusMeasure d = 1 →
      (∀ z, ψ z ≠ 0 → ∀ j, ‖z j‖ ≤ c) →
      Real.log (1 / c) - K ≤ ∫ x, GreenKernelReal.realGreen d x * ψ x ∂torusMeasure d := by
  refine ⟨(1 / 2) * Real.log (Real.pi * d) + (1 / 2) * (1 + ∫ u in Ioi 0, tailMajorant d u), ?_⟩
  intro ψ c M hc hb hm hnn hM hmass hsupp
  have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  set T := ∫ u in Ioi 0, tailMajorant d u with hT
  set b := Real.pi * d * c ^ 2 with hbdef
  have hbpos : 0 < b := by positivity
  have hψi : Integrable ψ (torusMeasure d) :=
    (integrable_const M).mono' hm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hnn x)]; exact hM x)
  have hψ2 : MemLp ψ 2 (torusMeasure d) :=
    (MemLp.of_bound hm.aestronglyMeasurable M
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hnn x)]; exact hM x)).mono_exponent le_top
  have hgint : IntegrableOn (heatPairing d ψ) (Ioi 0) :=
    GreenMellinPairing.mellin_heat_pairing_integrable hd hψ2
  have hMellin : ∫ u in Ioi 0, heatPairing d ψ u =
      2 * ∫ x, GreenKernelReal.realGreen d x * ψ x ∂torusMeasure d :=
    GreenMellinPairing.realGreen_mellin_heat_pairing hd hψ2
  set F : ℝ → ℝ := fun u => u⁻¹ - b * (u ^ 2)⁻¹ with hFdef
  set L : ℝ → ℝ := fun u => (Icc b 1).indicator F u - tailMajorant d u with hLdef
  have hFint : IntegrableOn F (Icc b 1) := by
    have hcont : ContinuousOn F (Icc b 1) := by
      apply ContinuousOn.sub
      · exact continuousOn_inv₀.mono (fun u hu => (lt_of_lt_of_le hbpos hu.1).ne')
      · exact continuousOn_const.mul ((continuousOn_id.pow 2).inv₀
          (fun u hu => pow_ne_zero 2 (lt_of_lt_of_le hbpos hu.1).ne'))
    exact hcont.integrableOn_Icc
  have hIndInt : IntegrableOn ((Icc b 1).indicator F) (Ioi 0) :=
    (hFint.integrable_indicator measurableSet_Icc).integrableOn
  have hTint := tailMajorant_integrableOn hd
  have hLint : IntegrableOn L (Ioi 0) := hIndInt.sub hTint
  have hLle : ∀ u ∈ Ioi 0, L u ≤ heatPairing d ψ u := by
    intro u hu
    have hu0 : 0 < u := hu
    by_cases hI : u ∈ Icc b 1
    · have e : L u = u⁻¹ - b * (u ^ 2)⁻¹ - u ^ ((d : ℝ) / 2 - 1) := by
        simp only [hLdef, indicator_of_mem hI, hFdef, tailMajorant, if_pos hI.2, mul_one]
      rw [e]
      exact heatPairing_ge_main hnn hψi hmass hsupp hu0
    · by_cases hu1 : u ≤ 1
      · have e : L u = -u ^ ((d : ℝ) / 2 - 1) := by
          simp only [hLdef, indicator_of_notMem hI, tailMajorant, if_pos hu1, mul_one, zero_sub]
        rw [e]
        exact heatPairing_ge_neg hnn hψi hmass hu0
      · have e : L u = -(u ^ ((d : ℝ) / 2 - 1) *
            (heatTailMass d * Real.exp (-Real.pi * u / 2))) := by
          simp only [hLdef, indicator_of_notMem hI, tailMajorant, if_neg hu1, zero_sub]
        rw [e]
        exact heatPairing_ge_tail hnn hψi hmass (not_le.mp hu1)
  have hmono := setIntegral_mono_on hLint hgint measurableSet_Ioi hLle
  have hb1 : b ≤ 1 := hb
  have hLval : ∫ u in Ioi 0, L u = (∫ u in Icc b 1, F u) - T := by
    rw [hLdef]
    simp only
    have hinter : Ioi (0 : ℝ) ∩ Icc b 1 = Icc b 1 :=
      inter_eq_right.mpr (fun u (hu : u ∈ Icc b 1) => lt_of_lt_of_le hbpos hu.1)
    rw [integral_sub hIndInt hTint, setIntegral_indicator measurableSet_Icc, hinter]
  have hF : ∫ u in Icc b 1, F u = Real.log (1 / b) - (1 - b) := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hb1]
    have hne : ∀ u ∈ uIcc b 1, u ≠ 0 := fun u hu => by
      rw [uIcc_of_le hb1] at hu
      exact (lt_of_lt_of_le hbpos hu.1).ne'
    have i1 : IntervalIntegrable (fun u : ℝ => u⁻¹) volume b 1 :=
      (continuousOn_inv₀.mono (fun u hu => hne u hu)).intervalIntegrable
    have i2 : IntervalIntegrable (fun u : ℝ => b * (u ^ 2)⁻¹) volume b 1 :=
      (continuousOn_const.mul ((continuousOn_id.pow 2).inv₀
        (fun u hu => pow_ne_zero 2 (hne u hu)))).intervalIntegrable
    simp only [hFdef]
    rw [intervalIntegral.integral_sub i1 i2, intervalIntegral.integral_const_mul,
      integral_inv_of_pos hbpos one_pos]
    have hz : ∫ x in b..1, (x ^ 2)⁻¹ = b⁻¹ - 1 := by
      have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := fun x : ℝ => -x⁻¹) (f' := fun x : ℝ => (x ^ 2)⁻¹) (a := b) (b := 1)
        (fun x hx => by
          convert (hasDerivAt_inv (hne x hx)).neg using 1
          simp)
        (((continuousOn_id.pow 2).inv₀ (fun u hu => pow_ne_zero 2 (hne u hu))).intervalIntegrable)
      rw [h]
      ring
    rw [hz]
    field_simp
  have hlogb : Real.log (1 / b) = -(Real.log (Real.pi * d)) + 2 * Real.log (1 / c) := by
    have h1 : Real.log b = Real.log (Real.pi * d) + 2 * Real.log c := by
      rw [hbdef, Real.log_mul (by positivity) (by positivity), Real.log_pow]
      norm_num
    rw [one_div, Real.log_inv, h1, one_div, Real.log_inv]
    ring
  have hfinal : 2 * (Real.log (1 / c) - ((1 / 2) * Real.log (Real.pi * d) + (1 / 2) * (1 + T))) ≤
      2 * ∫ x, GreenKernelReal.realGreen d x * ψ x ∂torusMeasure d := by
    rw [← hMellin]
    refine le_trans ?_ hmono
    rw [hLval, hF, hlogb]
    nlinarith
  linarith

end HeatPairing

end BecknerOnofri.V2.Reaudit.Obstruction
