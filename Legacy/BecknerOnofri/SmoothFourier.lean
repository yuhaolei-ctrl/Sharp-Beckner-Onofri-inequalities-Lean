module

public import Legacy.BecknerOnofri.SubcriticalWiener
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

@[expose] public section

/-! Rapid absolutely summable Fourier moments give a genuinely smooth
periodic lift on real coordinate space. -/

open MeasureTheory
open scoped BigOperators ContDiff

namespace Legacy.BecknerOnofri.SmoothFourier

open Legacy.TorusEndpoint TorusSobolev WienerFourier RadialWiener

set_option maxHeartbeats 800000

abbrev Space (d : ℕ) := Fin d → ℝ

def quotient {d : ℕ} (x : Space d) : Torus d := fun i => (x i : UnitAddCircle)

theorem quotient_add_int {d : ℕ} (x : Space d) (j : Frequency d) :
    quotient (x + fun i => (j i : ℝ)) = quotient x := by
  funext i
  change ((x i + (j i : ℝ) : ℝ) : UnitAddCircle) = (x i : UnitAddCircle)
  rw [AddCircle.coe_add]
  have hj : ((j i : ℝ) : UnitAddCircle) = 0 := by
    calc
      _ = ((j i • (1 : ℝ) : ℝ) : UnitAddCircle) := by simp
      _ = j i • ((1 : ℝ) : UnitAddCircle) := AddCircle.coe_zsmul (1 : ℝ)
      _ = 0 := by rw [AddCircle.coe_period]; simp
  rw [hj, add_zero]

noncomputable def dotLinear {d : ℕ} (k : Frequency d) : Space d →L[ℝ] ℝ :=
  ∑ i, (k i : ℝ) • ContinuousLinearMap.proj i

theorem dotLinear_apply {d : ℕ} (k : Frequency d) (x : Space d) :
    dotLinear k x = ∑ i, (k i : ℝ) * x i := by
  simp [dotLinear]

theorem norm_dotLinear_le {d : ℕ} (k : Frequency d) :
    ‖dotLinear k‖ ≤ (d : ℝ) * frequencyRadius k := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (by positivity) (frequencyRadius_nonneg k))
  intro x
  rw [dotLinear_apply]
  calc
    _ ≤ ∑ i, ‖(k i : ℝ) * x i‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin d, frequencyRadius k * ‖x‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul, Real.norm_eq_abs]
      exact mul_le_mul (coordinate_abs_le_radius k i) (norm_le_pi_norm x i)
        (norm_nonneg _) (frequencyRadius_nonneg k)
    _ = _ := by simp; ring

noncomputable def phase {d : ℕ} (k : Frequency d) : Space d →L[ℝ] ℂ :=
  ((2 * Real.pi : ℝ) : ℂ) • (Complex.I • (Complex.ofRealCLM.comp (dotLinear k)))

theorem phase_apply {d : ℕ} (k : Frequency d) (x : Space d) :
    phase k x = ((2 * Real.pi : ℝ) : ℂ) * Complex.I * (dotLinear k x : ℂ) := by
  simp [phase, mul_assoc]

theorem phase_re {d : ℕ} (k : Frequency d) (x : Space d) : (phase k x).re = 0 := by
  simp [phase_apply, Complex.mul_re, Complex.mul_im]

theorem norm_phase_le {d : ℕ} (k : Frequency d) :
    ‖phase k‖ ≤ (2 * Real.pi * d) * frequencyRadius k := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (by positivity) (frequencyRadius_nonneg k))
  intro x
  rw [phase_apply, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
    Complex.norm_I, mul_one, Real.norm_of_nonneg (by positivity : 0 ≤ 2 * Real.pi)]
  calc
    _ ≤ (2*Real.pi) * (‖dotLinear k‖ * ‖x‖) :=
      mul_le_mul_of_nonneg_left ((dotLinear k).le_opNorm x) (by positivity)
    _ ≤ (2*Real.pi) * (((d:ℝ)*frequencyRadius k) * ‖x‖) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (norm_dotLinear_le k) (norm_nonneg _)) (by positivity)
    _ = _ := by ring

theorem mFourier_quotient {d : ℕ} (k : Frequency d) (x : Space d) :
    UnitAddTorus.mFourier k (quotient x) = Complex.exp (phase k x) := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, quotient, fourier_coe_apply,
    Complex.ofReal_one, div_one]
  rw [← Complex.exp_sum]
  congr 1
  rw [phase_apply, dotLinear_apply, Complex.ofReal_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  push_cast
  ring

theorem norm_iteratedFDeriv_exp (m : ℕ) (z : ℂ) :
    ‖iteratedFDeriv ℝ m Complex.exp z‖ = ‖Complex.exp z‖ := by
  have h : ContDiffAt ℂ (m : ℕ∞ω) Complex.exp z := Complex.contDiff_exp.contDiffAt
  rw [← h.restrictScalars_iteratedFDeriv (𝕜 := ℝ)]
  simp only [Function.comp_apply, ContinuousMultilinearMap.norm_restrictScalars,
    norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate, Complex.iter_deriv_exp]

theorem character_contDiff {d : ℕ} (k : Frequency d) :
    ContDiff ℝ ∞ (fun x : Space d => Complex.exp (phase k x)) :=
  (phase k).contDiff.cexp

theorem character_derivative_bound {d : ℕ} (k : Frequency d) (m : ℕ) (x : Space d) :
    ‖iteratedFDeriv ℝ m (fun y => Complex.exp (phase k y)) x‖ ≤
      (2 * Real.pi * d)^m * radialWeight m k := by
  have he : ‖Complex.exp (phase k x)‖ = 1 := by
    rw [Complex.norm_exp, phase_re, Real.exp_zero]
  change ‖iteratedFDeriv ℝ m (Complex.exp ∘ phase k) x‖ ≤ _
  rw [(phase k).iteratedFDeriv_comp_right (Complex.contDiff_exp (n := (m : ℕ∞ω))) x le_rfl]
  calc
    _ ≤ ‖iteratedFDeriv ℝ m Complex.exp (phase k x)‖ *
        ∏ _ : Fin m, ‖phase k‖ := ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ = ‖phase k‖^m := by rw [norm_iteratedFDeriv_exp, he]; simp
    _ ≤ ((2*Real.pi*d)*frequencyRadius k)^m :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_phase_le k) m
    _ ≤ (2*Real.pi*d)^m * radialWeight m k := by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (frequencyRadius_nonneg k) (by linarith) m) (by positivity)

theorem term_derivative_bound {d : ℕ} (a : Frequency d → ℂ) (k : Frequency d)
    (m : ℕ) (x : Space d) :
    ‖iteratedFDeriv ℝ m (fun y => a k * Complex.exp (phase k y)) x‖ ≤
      (2 * Real.pi * d)^m * (radialWeight m k * ‖a k‖) := by
  have hc : ContDiffAt ℝ (m : ℕ∞ω) (fun y : Space d => Complex.exp (phase k y)) x :=
    ((phase k).contDiff.cexp).contDiffAt
  have hh := iteratedFDeriv_const_smul_apply' (a := a k) hc
  simp only [smul_eq_mul] at hh
  rw [hh, norm_smul]
  calc
    _ ≤ ‖a k‖ * ((2*Real.pi*d)^m*radialWeight m k) :=
      mul_le_mul_of_nonneg_left (character_derivative_bound k m x) (norm_nonneg _)
    _ = _ := by ring

theorem series_contDiff {d : ℕ} (a : Frequency d → ℂ)
    (ha : ∀ m : ℕ, RadialSummable a m) :
    ContDiff ℝ ∞ (fun x : Space d => absoluteFourierSeries a (quotient x)) := by
  have he : (fun x : Space d => absoluteFourierSeries a (quotient x)) =
      fun x => ∑' k, a k * Complex.exp (phase k x) := by
    funext x
    unfold absoluteFourierSeries
    simp only [mFourier_quotient]
  rw [he]
  apply contDiff_tsum (v := fun m k => (2*Real.pi*d)^m*(radialWeight m k*‖a k‖))
  · intro k
    exact contDiff_const.mul (character_contDiff k)
  · intro m _
    exact (ha m).mul_left _
  · intro m k x _
    exact term_derivative_bound a k m x

theorem lift_periodic {d : ℕ} (f : Torus d → ℂ) (x : Space d) (j : Frequency d) :
    f (quotient (x + fun i => (j i : ℝ))) = f (quotient x) := by rw [quotient_add_int]

open SubcriticalAttainment SubcriticalEuler

theorem maximizer_contDiff_lift {d : ℕ} (hd : 0 < d) {b Ab A : ℝ}
    (hR : RoughExponentialBound d b Ab) (hA : 0 < A) {u : TorusL2 d} (hu : Admissible u)
    (hmax : ∀ v : TorusL2 d, Admissible v → functional A v ≤ functional A u) :
    ContDiff ℝ ∞ (fun x : Space d => representative u (quotient x)) :=
  series_contDiff _ (maximizer_radialSummable hd hR hA hu hmax)

theorem maximizer_real_contDiff_lift {d : ℕ} (hd : 0 < d) {b Ab A : ℝ}
    (hR : RoughExponentialBound d b Ab) (hA : 0 < A) {u : TorusL2 d} (hu : Admissible u)
    (hmax : ∀ v : TorusL2 d, Admissible v → functional A v ≤ functional A u) :
    ContDiff ℝ ∞ (fun x : Space d => (representative u (quotient x)).re) :=
  Complex.reCLM.contDiff.comp (maximizer_contDiff_lift hd hR hA hu hmax)

noncomputable def smoothGibbsValue {d : ℕ} (u : TorusL2 d) (x : Torus d) : ℝ :=
  Real.exp (representative u x).re / partition u

theorem smoothGibbsValue_ae_eq {d : ℕ} (u : TorusL2 d)
    (hu : Summable (fun k => ‖fourierIsometry d u k‖)) :
    smoothGibbsValue u =ᵐ[torusMeasure d] gibbsValue u := by
  filter_upwards [representative_ae_eq u hu] with x hx
  simp only [smoothGibbsValue, gibbsValue, hx]

theorem smoothGibbsValue_continuous {d : ℕ} (u : TorusL2 d)
    (hu : Summable (fun k => ‖fourierIsometry d u k‖)) :
    Continuous (smoothGibbsValue u) :=
  ((Complex.continuous_re.comp (representative_continuous u hu)).rexp).div_const _

theorem smoothGibbsValue_pos {d : ℕ} {b Ab : ℝ} (hR : RoughExponentialBound d b Ab)
    {u : TorusL2 d} (hu : Admissible u) (x : Torus d) : 0 < smoothGibbsValue u x :=
  div_pos (Real.exp_pos _) (partition_pos hR hu)

theorem maximizer_gibbs_contDiff_lift {d : ℕ} (hd : 0 < d) {b Ab A : ℝ}
    (hR : RoughExponentialBound d b Ab) (hA : 0 < A) {u : TorusL2 d} (hu : Admissible u)
    (hmax : ∀ v : TorusL2 d, Admissible v → functional A v ≤ functional A u) :
    ContDiff ℝ ∞ (fun x : Space d => smoothGibbsValue u (quotient x)) :=
  ((maximizer_real_contDiff_lift hd hR hA hu hmax).exp).div_const _

noncomputable def smoothGibbsDensity {d : ℕ} {b Ab : ℝ} (hR : RoughExponentialBound d b Ab)
    {u : TorusL2 d} (hu : Admissible u) (hs : Summable (fun k => ‖fourierIsometry d u k‖)) :
    ProbabilityDensity d where
  value := smoothGibbsValue u
  nonneg := Filter.Eventually.of_forall (fun x => (smoothGibbsValue_pos hR hu x).le)
  integrable := (gibbsValue_integrable hR hu).congr (smoothGibbsValue_ae_eq u hs).symm
  mass := (integral_congr_ae (smoothGibbsValue_ae_eq u hs)).trans (gibbsValue_mass hR hu)

theorem smoothGibbsDensity_memLp {d : ℕ} {b Ab : ℝ} (hR : RoughExponentialBound d b Ab)
    {u : TorusL2 d} (hu : Admissible u) (hs : Summable (fun k => ‖fourierIsometry d u k‖)) :
    MemLp (smoothGibbsDensity hR hu hs).value 2 (torusMeasure d) :=
  (memLp_congr_ae (smoothGibbsValue_ae_eq u hs)).mpr (gibbsValue_memLp_two hR hu)

theorem smoothGibbsDensity_fourier {d : ℕ} {b Ab : ℝ} (hR : RoughExponentialBound d b Ab)
    {u : TorusL2 d} (hu : Admissible u) (hs : Summable (fun k => ‖fourierIsometry d u k‖))
    (k : Frequency d) :
    densityFourier (smoothGibbsDensity hR hu hs).value k = densityFourier (gibbsValue u) k := by
  apply integral_congr_ae
  filter_upwards [smoothGibbsValue_ae_eq u hs] with x hx
  change UnitAddTorus.mFourier (-k) x * (smoothGibbsValue u x : ℂ) = _
  rw [hx]

theorem smoothGibbsDensity_entropy {d : ℕ} {b Ab : ℝ} (hR : RoughExponentialBound d b Ab)
    {u : TorusL2 d} (hu : Admissible u) (hs : Summable (fun k => ‖fourierIsometry d u k‖)) :
    densityEntropy (smoothGibbsDensity hR hu hs).value = densityEntropy (gibbsValue u) := by
  apply integral_congr_ae
  filter_upwards [smoothGibbsValue_ae_eq u hs] with x hx
  change smoothGibbsValue u x * Real.log (smoothGibbsValue u x) = _
  rw [hx]

theorem smoothGibbsDensity_finiteEntropy {d : ℕ} {b Ab : ℝ} (hR : RoughExponentialBound d b Ab)
    {u : TorusL2 d} (hu : Admissible u) (hs : Summable (fun k => ‖fourierIsometry d u k‖)) :
    (smoothGibbsDensity hR hu hs).FiniteEntropy := by
  apply (gibbsDensity_finiteEntropy hR hu).congr
  filter_upwards [smoothGibbsValue_ae_eq u hs] with x hx
  change gibbsValue u x * Real.log (gibbsValue u x) =
    smoothGibbsValue u x * Real.log (smoothGibbsValue u x)
  rw [hx]

#print axioms mFourier_quotient
#print axioms term_derivative_bound
#print axioms series_contDiff
#print axioms maximizer_contDiff_lift
#print axioms maximizer_gibbs_contDiff_lift
#print axioms smoothGibbsDensity_fourier
#print axioms smoothGibbsDensity_entropy
#print axioms smoothGibbsDensity_finiteEntropy

end Legacy.BecknerOnofri.SmoothFourier
