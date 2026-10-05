import Legacy.TorusEndpoint.GreenHeatLowerBound
import Legacy.TorusEndpoint.GreenMellinPairing
import Legacy.TorusEndpoint.PhysicalGreenL2

/-!
# Actual heat densities for endpoint sharpness

This module constructs genuine positive, continuous, finite-entropy torus
probability densities, and identifies their physical Green energy. It does
not assume the endpoint inequality or a concentration asymptotic. A theorem
about these test densities is not by itself an endpoint inequality.
-/

open MeasureTheory Filter Set
open scoped BigOperators Topology

namespace Legacy.TorusEndpoint.EndpointSharpnessHeat

open TorusHeatPositivity TorusHeatBounds GreenHeatLowerBound GreenHeatRegularization
  GreenMultiplierSummability GreenMellinSeries GreenMellinPairing PhysicalGreenL2

noncomputable def heatDensity (d : ℕ) {t : ℝ} (ht : 0 < t) : ProbabilityDensity d where
  value x := (torusTheta t x).re
  nonneg := Eventually.of_forall (fun x => (torusTheta_re_pos ht x).le)
  integrable := (Complex.continuous_re.comp (torusTheta_continuous ht)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  mass := torusTheta_re_integral ht

theorem heatDensity_continuous (d : ℕ) {t : ℝ} (ht : 0 < t) :
    Continuous (heatDensity d ht).value :=
  Complex.continuous_re.comp (torusTheta_continuous ht)

theorem heatDensity_pos (d : ℕ) {t : ℝ} (ht : 0 < t) (x : Torus d) :
    0 < (heatDensity d ht).value x := torusTheta_re_pos ht x

theorem heatDensity_memLp (d : ℕ) {t : ℝ} (ht : 0 < t) :
    MemLp (heatDensity d ht).value 2 (torusMeasure d) :=
  (heatDensity_continuous d ht).memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem heatDensity_finiteEntropy (d : ℕ) {t : ℝ} (ht : 0 < t) :
    (heatDensity d ht).FiniteEntropy :=
  finiteEntropy_of_memLp _ (heatDensity_memLp d ht)

theorem heatDensity_fourierCoeff (d : ℕ) {t : ℝ} (ht : 0 < t) (k : Frequency d) :
    densityFourier (heatDensity d ht).value k = (heatWeight t k : ℂ) := by
  have hc : (fun x => ((torusTheta (d := d) t x).re : ℂ)) = torusTheta t := by
    funext x
    apply Complex.ext
    · rfl
    · simp [torusTheta_im_zero ht]
  change UnitAddTorus.mFourierCoeff (fun x => ((torusTheta t x).re : ℂ)) k = _
  rw [hc]
  exact torusTheta_actual_fourierCoefficient ht k

theorem heatWeight_add {d : ℕ} (s t : ℝ) (k : Frequency d) :
    heatWeight (s + t) k = heatWeight s k * heatWeight t k := by
  unfold heatWeight
  rw [← Real.exp_add]
  congr 1
  ring

theorem heatWeight_two_mul {d : ℕ} (t : ℝ) (k : Frequency d) :
    heatWeight (2 * t) k = heatWeight t k ^ 2 := by
  rw [two_mul, heatWeight_add, pow_two]

theorem torusTheta_zero_eq_tsum {d : ℕ} {t : ℝ} (ht : 0 < t) :
    (torusTheta t (0 : Torus d)).re = ∑' k : Frequency d, heatWeight t k := by
  have hs := Complex.hasSum_re (torusTheta_summable ht (0 : Torus d)).hasSum
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, Pi.zero_apply,
    fourier_eval_zero, Finset.prod_const_one, mul_one, Complex.ofReal_re] at hs
  simpa only [torusTheta, heatWeight, radiusSq, UnitAddTorus.mFourier,
    ContinuousMap.coe_mk, Pi.zero_apply, fourier_eval_zero, Finset.prod_const_one,
    mul_one] using hs.tsum_eq.symm

theorem heatDensity_le_peak (d : ℕ) {t : ℝ} (ht : 0 < t) (x : Torus d) :
    (heatDensity d ht).value x ≤ (torusTheta t (0 : Torus d)).re := by
  rw [torusTheta_zero_eq_tsum ht]
  change (torusTheta t x).re ≤ _
  apply (Complex.re_le_norm _).trans
  change ‖∑' k : Frequency d, (heatWeight t k : ℂ) * UnitAddTorus.mFourier k x‖ ≤ _
  apply tsum_of_norm_bounded (heatWeight_summable ht).hasSum
  intro k
  simp only [norm_mul, mFourier_norm_apply, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (heatWeight_pos t k), le_refl]

/-- A quantitative entropy upper bound for an actual, finite-entropy density. -/
theorem heatDensity_entropy_le_log_peak (d : ℕ) {t : ℝ} (ht : 0 < t) :
    densityEntropy (heatDensity d ht).value ≤ Real.log (torusTheta t (0 : Torus d)).re := by
  calc
    _ ≤ ∫ x, (heatDensity d ht).value x * Real.log (torusTheta t (0 : Torus d)).re
        ∂torusMeasure d := by
      apply integral_mono_ae (heatDensity_finiteEntropy d ht)
        ((heatDensity d ht).integrable.mul_const _)
      apply Eventually.of_forall
      intro x
      exact mul_le_mul_of_nonneg_left
        (Real.log_le_log (heatDensity_pos d ht x) (heatDensity_le_peak d ht x))
        (heatDensity_pos d ht x).le
    _ = _ := by rw [integral_mul_const, (heatDensity d ht).mass, one_mul]

/-- The energy is the actual double integral of the singular Green representative. -/
theorem heatDensity_energy_eq_diagonal (d : ℕ) {t : ℝ} (ht : 0 < t) :
    physicalGreenEnergy (heatDensity d ht) = (heatGreenKernel d (2 * t) 0).re := by
  have hs := hasSum_physicalGreenEnergy _ (heatDensity_memLp d ht)
  have hg := hasSum_heatGreenKernel_re (show 0 < 2 * t by positivity) (0 : Torus d)
  have he (k : Frequency d) : greenMultiplier d k *
      ‖densityFourier (heatDensity d ht).value k‖ ^ 2 =
      heatGreenWeight d (2 * t) k * (UnitAddTorus.mFourier k 0).re := by
    rw [heatDensity_fourierCoeff, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (heatWeight_pos t k), heatGreenWeight, heatWeight_two_mul]
    simp [UnitAddTorus.mFourier]
  exact (hs.congr_fun (fun k => (he k).symm)).unique hg

theorem heatDensity_spectral_finite_and_physical {d : ℕ} (hd : 0 < d)
    {t : ℝ} (ht : 0 < t) :
    Summable (densitySpectralTerm (heatDensity d ht)) ∧
    physicalGreenEnergy (heatDensity d ht) = densitySpectralEnergy (heatDensity d ht) :=
  physicalGreenEnergy_eq_spectral hd _ (heatDensity_memLp d ht)

theorem theta_zero_re_eq_tsum {t : ℝ} (ht : 0 < t) :
    (theta t 0).re = ∑' n : ℤ, Real.exp (-Real.pi * t * (n : ℝ)^2) := by
  have hs := Complex.hasSum_re (theta_summable ht 0).hasSum
  simpa only [theta, fourier_eval_zero, mul_one, Complex.ofReal_re] using hs.tsum_eq.symm

theorem theta_zero_re_mono {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) :
    (theta t 0).re ≤ (theta s 0).re := by
  rw [theta_zero_re_eq_tsum (hs.trans_le hst), theta_zero_re_eq_tsum hs]
  apply (theta_weights_summable (hs.trans_le hst)).tsum_le_tsum _ (theta_weights_summable hs)
  intro n
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_right hst (sq_nonneg (n : ℝ))
  have h' := mul_le_mul_of_nonneg_left h Real.pi_pos.le
  nlinarith

/-- Exact scalar reciprocal-time formula at the heat peak. -/
theorem theta_zero_re_reciprocal {t : ℝ} (ht : 0 < t) :
    (theta t 0).re = (t ^ (1 / 2 : ℝ))⁻¹ * (theta (1 / t) 0).re := by
  have hp := congrArg Complex.re (theta_coe_eq_shifted_gaussian ht 0)
  simp only [AddCircle.coe_zero, sub_zero, Complex.ofReal_re, one_div] at hp
  rw [hp, theta_zero_re_eq_tsum (one_div_pos.mpr ht)]
  simp only [div_eq_mul_inv, one_mul]

/-- A proved small-time upper bound. The constant is an actual convergent theta value. -/
theorem heat_peak_le {d : ℕ} {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    (torusTheta t (0 : Torus d)).re ≤
      ((t ^ (1 / 2 : ℝ))⁻¹ * (theta 1 0).re) ^ d := by
  rw [torusTheta_eq_ofReal_product ht, Complex.ofReal_re]
  simp only [Pi.zero_apply, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  apply pow_le_pow_left₀ (theta_re_pos ht 0).le
  rw [theta_zero_re_reciprocal ht]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Real.rpow_nonneg ht.le _))
  apply theta_zero_re_mono (by norm_num : (0 : ℝ) < 1)
  exact (le_div_iff₀ ht).mpr (by simpa using ht1)

/-- This establishes the correct d/2 logarithmic entropy growth, with a finite constant. -/
theorem heatDensity_entropy_log_bound {d : ℕ} {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    densityEntropy (heatDensity d ht).value ≤
      -(d : ℝ) / 2 * Real.log t + (d : ℝ) * Real.log (theta 1 0).re := by
  apply (heatDensity_entropy_le_log_peak d ht).trans
  have hp := Real.log_le_log (torusTheta_re_pos ht (0 : Torus d)) (heat_peak_le ht ht1)
  rw [Real.log_pow, Real.log_mul
    (inv_ne_zero (Real.rpow_pos_of_pos ht _).ne') (theta_re_pos (by norm_num : (0 : ℝ) < 1) 0).ne',
    Real.log_inv, Real.log_rpow ht] at hp
  exact hp.trans_eq (by ring)

theorem nonzeroHeatWeight_mul {d : ℕ} (s t : ℝ) (k : Frequency d) :
    nonzeroHeatWeight s k * heatWeight t k = nonzeroHeatWeight (s + t) k := by
  by_cases hk : k = 0
  · simp [nonzeroHeatWeight, hk]
  · simp only [nonzeroHeatWeight, if_neg hk, heatWeight_add]

theorem nonzeroHeatWeight_tsum {d : ℕ} {t : ℝ} (ht : 0 < t) :
    (∑' k : Frequency d, nonzeroHeatWeight t k) = (torusTheta t (0 : Torus d)).re - 1 := by
  have h := (heatWeight_summable (d := d) ht).tsum_eq_add_tsum_ite (0 : Frequency d)
  rw [heatWeight_zero, ← torusTheta_zero_eq_tsum ht] at h
  change _ = 1 + ∑' k : Frequency d, nonzeroHeatWeight t k at h
  linarith

theorem heatDensity_heat_pairing {d : ℕ} {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    (∫ x, ((torusTheta s x).re - 1) * (heatDensity d ht).value x ∂torusMeasure d) =
      (torusTheta (s + t) (0 : Torus d)).re - 1 := by
  rw [← (TorusHeatPairing.hasSum_real_heat_pairing hs (heatDensity_memLp d ht)).tsum_eq]
  simp only [heatDensity_fourierCoeff, Complex.ofReal_re, nonzeroHeatWeight_mul]
  exact nonzeroHeatWeight_tsum (add_pos hs ht)

theorem realGreen_heatDensity_pairing {d : ℕ} {t : ℝ} (ht : 0 < t) :
    (∫ x, GreenKernelReal.realGreen d x * (heatDensity d ht).value x ∂torusMeasure d) =
      (heatGreenKernel d t 0).re := by
  have hs := GreenPairing.hasSum_realGreen_pairing (heatDensity_memLp d ht)
  have hg := hasSum_heatGreenKernel_re ht (0 : Torus d)
  apply (hs.congr_fun (fun k => ?_)).unique hg
  rw [heatDensity_fourierCoeff, Complex.ofReal_re]
  simp [heatGreenWeight, UnitAddTorus.mFourier]

noncomputable def heatEnergyIntegrand (d : ℕ) (t u : ℝ) : ℝ :=
  u ^ ((d : ℝ) / 2 - 1) * ((torusTheta (u + 2 * t) (0 : Torus d)).re - 1)

theorem heatEnergyIntegrand_integrable {d : ℕ} (hd : 0 < d) {t : ℝ} (ht : 0 < t) :
    IntegrableOn (heatEnergyIntegrand d t) (Ioi 0) := by
  have hi := mellin_heat_pairing_integrable hd
    (heatDensity_memLp d (show 0 < 2 * t by positivity))
  apply hi.congr
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
  rw [heatDensity_heat_pairing hu]
  rfl

/-- Exact Mellin identity for the actual physical energy of the actual heat density.
Both the time integral and the physical double integral have proved integrability. -/
theorem heatDensity_energy_mellin {d : ℕ} (hd : 0 < d) {t : ℝ} (ht : 0 < t) :
    (∫ u in Ioi 0, heatEnergyIntegrand d t u) = 2 * physicalGreenEnergy (heatDensity d ht) := by
  have h := realGreen_mellin_heat_pairing hd
    (heatDensity_memLp d (show 0 < 2 * t by positivity))
  rw [realGreen_heatDensity_pairing, ← heatDensity_energy_eq_diagonal d ht] at h
  rw [← h]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u hu
  dsimp only
  rw [heatDensity_heat_pairing hu]
  rfl

theorem theta_zero_one_le {t : ℝ} (ht : 0 < t) : 1 ≤ (theta t 0).re := by
  rw [theta_zero_re_eq_tsum ht]
  simpa using (theta_weights_summable ht).le_tsum 0 (fun n _ => (Real.exp_pos _).le)

theorem heat_peak_one_le {d : ℕ} {t : ℝ} (ht : 0 < t) :
    1 ≤ (torusTheta t (0 : Torus d)).re := by
  rw [torusTheta_eq_ofReal_product ht, Complex.ofReal_re]
  simp only [Pi.zero_apply, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact one_le_pow₀ (theta_zero_one_le ht)

/-- Retaining the zero image in the proved Poisson representation gives the
Euclidean heat lower bound, with the exact normalization. -/
theorem heat_peak_rpow_lower {d : ℕ} {t : ℝ} (ht : 0 < t) :
    t ^ (-(d : ℝ) / 2) ≤ (torusTheta t (0 : Torus d)).re := by
  rw [torusTheta_eq_ofReal_product ht, Complex.ofReal_re]
  simp only [Pi.zero_apply, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have h1 : (t ^ (1 / 2 : ℝ))⁻¹ ≤ (theta t 0).re := by
    rw [theta_zero_re_reciprocal ht]
    exact le_mul_of_one_le_right (by positivity) (theta_zero_one_le (one_div_pos.mpr ht))
  have hp := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (t ^ (1 / 2 : ℝ))⁻¹) h1 d
  calc
    _ = ((t ^ (1 / 2 : ℝ))⁻¹) ^ d := by
      rw [← Real.rpow_neg ht.le, ← Real.rpow_mul_natCast ht.le]
      congr 1
      ring
    _ ≤ _ := hp

theorem heatEnergyIntegrand_nonneg {d : ℕ} {t u : ℝ} (ht : 0 < t) (hu : 0 < u) :
    0 ≤ heatEnergyIntegrand d t u := by
  exact mul_nonneg (Real.rpow_nonneg hu.le _) (sub_nonneg.mpr (heat_peak_one_le (by positivity)))

/-- The elementary tangent inequality is proved from exp and log bounds, not assumed. -/
theorem rpow_one_add_neg_lower {a x : ℝ} (ha : 0 ≤ a) (hx : 0 ≤ x) :
    1 - a * x ≤ (1 + x) ^ (-a) := by
  have hpos : 0 < 1 + x := by linarith
  have hl : Real.log (1 + x) ≤ x := by
    simpa using Real.log_le_sub_one_of_pos hpos
  have he := Real.add_one_le_exp (-a * Real.log (1 + x))
  have hm := mul_le_mul_of_nonneg_left hl ha
  rw [Real.rpow_def_of_pos hpos]
  rw [mul_comm (Real.log (1 + x)) (-a)]
  linarith

theorem rpow_heat_comparison {a t u : ℝ} (ha : 0 ≤ a) (ht : 0 < t) (hu : 0 < u) :
    u⁻¹ - (2 * a * t) * (u ^ 2)⁻¹ ≤
      u ^ (a - 1) * (u + 2 * t) ^ (-a) := by
  have hx : 0 ≤ 2 * t / u := by positivity
  have h := mul_le_mul_of_nonneg_left (rpow_one_add_neg_lower ha hx) (inv_nonneg.mpr hu.le)
  have he : u + 2 * t = u * (1 + 2 * t / u) := by field_simp
  have hpow : u ^ (a - 1) * (u + 2 * t) ^ (-a) =
      u⁻¹ * (1 + 2 * t / u) ^ (-a) := by
    rw [he, Real.mul_rpow hu.le (by positivity), ← mul_assoc, ← Real.rpow_add hu]
    rw [show a - 1 + -a = (-1 : ℝ) by ring, Real.rpow_neg_one]
  rw [hpow]
  calc
    _ = u⁻¹ * (1 - a * (2 * t / u)) := by field_simp
    _ ≤ _ := h

theorem heatEnergyIntegrand_lower {d : ℕ} {t u : ℝ} (ht : 0 < t) (hu : 0 < u) :
    u⁻¹ - ((d : ℝ) * t) * (u ^ 2)⁻¹ - u ^ ((d : ℝ) / 2 - 1) ≤
      heatEnergyIntegrand d t u := by
  have hp := mul_le_mul_of_nonneg_left
    (heat_peak_rpow_lower (d := d) (show 0 < u + 2 * t by positivity))
    (Real.rpow_nonneg hu.le ((d : ℝ) / 2 - 1))
  have hc := rpow_heat_comparison (show (0 : ℝ) ≤ (d : ℝ) / 2 by positivity) ht hu
  have he : (-(d : ℝ) / 2) = -((d : ℝ) / 2) := by ring
  rw [he] at hp
  have he2 : 2 * ((d : ℝ) / 2) * t = (d : ℝ) * t := by ring
  rw [he2] at hc
  unfold heatEnergyIntegrand
  nlinarith

end Legacy.TorusEndpoint.EndpointSharpnessHeat
