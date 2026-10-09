module

public import Mathlib.Tactic
public import BecknerOnofri.CircleBesselSeries
public import BecknerOnofri.CircleBesselSupersolution
public import BecknerOnofri.CircleGammaDefinitions

@[expose] public section

/-! # Existence of the inverse of `R = I_1(2.)/I_0(2.)` on `[0,1)` (Appendix A.2.1)

Manuscript route (RECON decision point 2): `R(0) = 0`, `R' > 0`, and `R(h) -> 1` by the
near-maximal-set estimate.  For `0 < delta <= 1` let `A = {cos >= 1 - delta/2}` (positive measure,
open set containing `0`).  Then `Z(h) = I_0(2h) >= |A| e^{2h(1-delta/2)}` and pointwise
`e^{2hcos}(cos - (1-delta)) >= -2 e^{2h(1-delta)}`, whence
`R(h) >= 1 - delta - (2/|A|) e^{-h delta}`, i.e. `liminf R >= 1`.

* `besselMoment_ge`: this inequality;
* `besselMoment_exceeds`: `t < 1 -> exists h >= 0, t < R(h)`;
* `parameter_mean_t`: `R(parameter t) = t` and `0 <= parameter t` for `0 <= t < 1`
  (the statement of the repository's `parameter_mean`, whose proof goes through the Riccati
  comparison `besselMoment_exceeds_mean` instead). -/
noncomputable section
open MeasureTheory Set Filter Topology
open BecknerOnofri.HighDim BecknerOnofri.HighDim.CircleScalar
namespace BecknerOnofri.V2.Circle

theorem circleCosine_continuous : Continuous circleCosine :=
  Complex.continuous_re.comp (fourier 1).continuous

theorem circleCosine_abs_le (x : UnitAddCircle) : |circleCosine x| ≤ 1 := by
  unfold circleCosine
  calc |(fourier 1 x).re| ≤ ‖fourier 1 x‖ := Complex.abs_re_le_norm _
    _ = 1 := circle_fourier_norm 1 x

theorem circleCosine_zero : circleCosine 0 = 1 := by
  have := circleCosine_coe 0
  simpa using this

/-- `R(h) = ∫ circleCosine · (tilted density)` (von Mises moment), with the tilted density
written out. -/
theorem besselMoment_one_eq (h : ℝ) :
    besselMoment 1 h = (∫ x : UnitAddCircle, Real.exp (2 * h * circleCosine x) * circleCosine x
      ∂AddCircle.haarAddCircle) / besselI0Two h := by
  have hc := GibbsTrialLower.circleTiltFourier_eq_ratio h (-(1:ℤ))
  simp only [circleTiltFourier, neg_neg, Int.natAbs_neg, Int.natAbs_one] at hc
  have hi : Integrable (fun x : UnitAddCircle => fourier (1:ℤ) x * (circleTiltDensity h x : ℂ))
      AddCircle.haarAddCircle := by
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    refine (fourier (1:ℤ)).continuous.mul (Complex.continuous_ofReal.comp ?_)
    unfold circleTiltDensity
    have := circleCosine_continuous
    fun_prop
  have hr := congrArg Complex.re hc
  have hre : (∫ x : UnitAddCircle, fourier (1:ℤ) x * (circleTiltDensity h x : ℂ)
      ∂AddCircle.haarAddCircle).re =
      ∫ x : UnitAddCircle, (fourier (1:ℤ) x * (circleTiltDensity h x : ℂ)).re
        ∂AddCircle.haarAddCircle := (integral_re hi).symm
  rw [hre] at hr
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] at hr
  rw [besselMoment_eq]
  simp only [mul_comm] at hr
  rw [← hr, ← integral_div]
  refine integral_congr_ae (Eventually.of_forall (fun x => ?_))
  simp only [circleTiltDensity, circleCosine]
  ring

/-- The near-maximal-set estimate. -/
theorem exists_set_measure (δ : ℝ) (hδ : 0 < δ) :
    ∃ m : ℝ, 0 < m ∧ ∀ h : ℝ, 0 ≤ h →
      m * Real.exp (2 * h * (1 - δ / 2)) ≤ besselI0Two h := by
  set μ : Measure UnitAddCircle := AddCircle.haarAddCircle with hμ
  let A : Set UnitAddCircle := {x | 1 - δ / 2 < circleCosine x}
  have hAo : IsOpen A := isOpen_lt continuous_const circleCosine_continuous
  have h0A : (0 : UnitAddCircle) ∈ A := by
    show 1 - δ / 2 < circleCosine 0
    rw [circleCosine_zero]; linarith
  have hmpos : 0 < μ.real A := by
    have := hAo.measure_pos μ ⟨0, h0A⟩
    exact ENNReal.toReal_pos this.ne' (measure_ne_top μ A)
  refine ⟨μ.real A, hmpos, fun h hh => ?_⟩
  rw [besselI0Two_eq_circle_integral]
  have hcont : Continuous fun x : UnitAddCircle => Real.exp (2 * h * circleCosine x) := by
    have := circleCosine_continuous; fun_prop
  have hint : Integrable (fun x : UnitAddCircle => Real.exp (2 * h * circleCosine x)) μ :=
    hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  calc μ.real A * Real.exp (2 * h * (1 - δ / 2))
      = ∫ _ in A, Real.exp (2 * h * (1 - δ / 2)) ∂μ := by
        rw [setIntegral_const]; simp [mul_comm]
    _ ≤ ∫ x in A, Real.exp (2 * h * circleCosine x) ∂μ := by
        apply setIntegral_mono_on (integrableOn_const (measure_ne_top μ A)) hint.integrableOn
          hAo.measurableSet
        intro x hx
        apply Real.exp_le_exp.mpr
        have : 1 - δ / 2 ≤ circleCosine x := le_of_lt hx
        nlinarith
    _ ≤ ∫ x, Real.exp (2 * h * circleCosine x) ∂μ :=
        setIntegral_le_integral hint (Eventually.of_forall (fun x => (Real.exp_pos _).le))

theorem besselMoment_ge {δ : ℝ} (hδ : 0 < δ) :
    ∃ m : ℝ, 0 < m ∧ ∀ h : ℝ, 0 ≤ h →
      1 - δ - 2 / m * Real.exp (-(h * δ)) ≤ besselMoment 1 h := by
  obtain ⟨m, hm, hZ⟩ := exists_set_measure δ hδ
  refine ⟨m, hm, fun h hh => ?_⟩
  set μ : Measure UnitAddCircle := AddCircle.haarAddCircle with hμ
  have hZpos := besselI0Two_pos h
  have hcont : Continuous fun x : UnitAddCircle => Real.exp (2 * h * circleCosine x) := by
    have := circleCosine_continuous; fun_prop
  have hint : Integrable (fun x : UnitAddCircle => Real.exp (2 * h * circleCosine x)) μ :=
    hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hint2 : Integrable (fun x : UnitAddCircle => Real.exp (2 * h * circleCosine x) *
      circleCosine x) μ :=
    (hcont.mul circleCosine_continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  set K1 := Real.exp (2 * h * (1 - δ)) with hK1
  have hpt : ∀ x : UnitAddCircle, (1 - δ) * Real.exp (2 * h * circleCosine x) - 2 * K1 ≤
      Real.exp (2 * h * circleCosine x) * circleCosine x := by
    intro x
    have hg := (Real.exp_pos (2 * h * circleCosine x))
    have hc1 := circleCosine_abs_le x
    have hcl := (abs_le.mp hc1).1
    rcases le_or_gt (1 - δ) (circleCosine x) with hge | hlt
    · nlinarith [Real.exp_pos (2 * h * (1 - δ))]
    · have hgle : Real.exp (2 * h * circleCosine x) ≤ K1 :=
        Real.exp_le_exp.mpr (by nlinarith)
      nlinarith [Real.exp_pos (2 * h * (1 - δ))]
  have hI : ∫ x, ((1 - δ) * Real.exp (2 * h * circleCosine x) - 2 * K1) ∂μ ≤
      ∫ x, Real.exp (2 * h * circleCosine x) * circleCosine x ∂μ :=
    integral_mono (hint.const_mul _ |>.sub (integrable_const _)) hint2 hpt
  rw [integral_sub (hint.const_mul _) (integrable_const _), integral_const_mul,
    ← besselI0Two_eq_circle_integral] at hI
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hI
  -- hI : (1-δ) Z - 2 K1 ≤ ∫ g c
  rw [besselMoment_one_eq, le_div_iff₀ hZpos]
  have hK1ne : K1 ≠ 0 := (Real.exp_pos _).ne'
  have hE := Real.exp_pos (h * δ)
  have hK2 : Real.exp (2 * h * (1 - δ / 2)) = K1 * Real.exp (h * δ) := by
    rw [hK1, ← Real.exp_add]; congr 1; ring
  have hneg : Real.exp (-(h * δ)) = (Real.exp (h * δ))⁻¹ := Real.exp_neg _
  have hZ' : m * (K1 * Real.exp (h * δ)) ≤ besselI0Two h := by
    have := hZ h hh; rwa [hK2] at this
  have h1 : K1 ≤ Real.exp (-(h * δ)) / m * besselI0Two h := by
    have e1 : Real.exp (-(h * δ)) / m * besselI0Two h = besselI0Two h / (m * Real.exp (h * δ)) := by
      rw [hneg]; field_simp
    rw [e1, le_div_iff₀ (by positivity)]
    nlinarith [hZ']
  have e2 : 2 / m * Real.exp (-(h * δ)) * besselI0Two h =
      2 * (Real.exp (-(h * δ)) / m * besselI0Two h) := by ring
  have e3 : (1 - δ - 2 / m * Real.exp (-(h * δ))) * besselI0Two h =
      (1 - δ) * besselI0Two h - 2 / m * Real.exp (-(h * δ)) * besselI0Two h := by ring
  linarith [hI, h1, e2, e3]

/-- `R(h) → 1`: for `t < 1` there is `h ≥ 0` with `t < R(h)`. -/
theorem besselMoment_exceeds {t : ℝ} (ht : t < 1) : ∃ h : ℝ, 0 ≤ h ∧ t < besselMoment 1 h := by
  set δ := min 1 ((1 - t) / 4) with hδ
  have hδ0 : 0 < δ := lt_min one_pos (by linarith)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδ2 : δ ≤ (1 - t) / 4 := min_le_right _ _
  obtain ⟨m, hm, hbd⟩ := besselMoment_ge hδ0
  -- choose `h` with `(2/m) e^{-hδ} ≤ δ`
  set h := 2 / (m * δ ^ 2) with hh
  have hh0 : 0 ≤ h := by positivity
  refine ⟨h, hh0, ?_⟩
  have hexp : h * δ ≤ Real.exp (h * δ) := by linarith [Real.add_one_le_exp (h * δ)]
  have hkey : 2 / m * Real.exp (-(h * δ)) ≤ δ := by
    rw [Real.exp_neg, ← div_eq_mul_inv, div_div, div_le_iff₀ (by positivity)]
    have : δ * (m * Real.exp (h * δ)) ≥ δ * (m * (h * δ)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp hm.le) hδ0.le
    have e : δ * (m * (h * δ)) = 2 := by rw [hh]; field_simp
    linarith
  have := hbd h hh0
  linarith

/-- The statement of the repository's `parameter_mean` (`R(h(t)) = t`, `h(t) ≥ 0`), proved from
`besselMoment_exceeds` (manuscript route: tilted-measure estimate) instead of the Riccati
comparison. -/
theorem parameter_mean_t {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) :
    besselMoment 1 (parameter t) = t ∧ 0 ≤ parameter t := by
  obtain ⟨h, hh, hR⟩ := besselMoment_exceeds ht1
  have hcont : Continuous (besselMoment 1) := continuous_iff_continuousAt.mpr
    (fun x => (besselMoment_first_derivative x).continuousAt)
  obtain ⟨x, hx, he⟩ := intermediate_value_Icc hh hcont.continuousOn
    (show t ∈ Icc (besselMoment 1 0) (besselMoment 1 h) from
      ⟨by simpa [besselMoment_one_zero] using ht, hR.le⟩)
  have hp : besselMoment 1 (parameter t) = t := Function.invFun_eq ⟨x, he⟩
  have heq : parameter t = x := besselMoment_first_strictMono.injective (hp.trans he.symm)
  exact ⟨hp, by simpa [heq] using hx.1⟩

end BecknerOnofri.V2.Circle
