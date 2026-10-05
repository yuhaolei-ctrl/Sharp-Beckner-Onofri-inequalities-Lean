module

public import BecknerOnofri.PressureDuality

@[expose] public section

/-! Full raw Sobolev equality classification from density endpoint rigidity. -/
noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators
namespace BecknerOnofri.HighDim

theorem fourierCoeff_congr_ae {d : ℕ} {u v : Torus d → ℝ}
    (huv : u =ᵐ[torusMeasure d] v) (k : Frequency d) : fourierCoeff u k = fourierCoeff v k := by
  apply integral_congr_ae
  filter_upwards [huv] with x hx
  rw [hx]

theorem constant_potentialTerm {d : ℕ} (c : ℝ) (k : NonzeroFrequency d) :
    potentialTerm (fun _ : Torus d => c) k = 0 := by
  have hf : fourierCoeff (fun _ : Torus d => c) k.val =
      fourierCoeff (fun _ : Torus d => 1) k.val * (c : ℂ) := by
    simp only [fourierCoeff, Complex.ofReal_one, mul_one]
    exact integral_mul_const _ _
  simp [potentialTerm, hf, fourierCoeff_one_nonzero k.val k.property]

theorem constant_potential_equality {d : ℕ} (u : Torus d → ℝ) {c : ℝ}
    (hu : u =ᵐ[torusMeasure d] (fun _ => c)) :
    logPartition u = ((spectralCoefficient d * potentialEnergy u : ℝ) : EReal) := by
  have hm : (∫ x, u x ∂torusMeasure d) = c := by
    rw [integral_congr_ae hu]
    simp
  have hc : centered u =ᵐ[torusMeasure d] (fun _ => 0) := by
    filter_upwards [hu] with x hx
    simp [centered, hx, hm]
  have hZ : logPartition u = 0 := by
    unfold logPartition
    have he : (fun x => ENNReal.ofReal (Real.exp (centered u x))) =ᵐ[torusMeasure d]
        (fun _ => (1 : ℝ≥0∞)) := by
      filter_upwards [hc] with x hx
      simp [hx]
    rw [lintegral_congr_ae he]
    simp
  have hE : potentialEnergy u = 0 := by
    calc
      _ = ∑' k : NonzeroFrequency d, (0 : ℝ) := by
        apply tsum_congr
        intro k
        have he : potentialTerm u k = potentialTerm (fun _ : Torus d => c) k := by
          simp only [potentialTerm, fourierCoeff_congr_ae hu]
        exact he.trans (constant_potentialTerm c k)
      _ = 0 := tsum_zero
  rw [hZ, hE]
  simp

theorem potential_rigidity_of_density {d : ℕ} (hd : 0 < d)
    (hE : ∀ ρ : ProbabilityDensity d, ρ.FiniteEntropy →
      spectralEnergy ρ ≤ ENNReal.ofReal (2 * entropy ρ))
    (hRigid : ∀ ρ : ProbabilityDensity d, ρ.FiniteEntropy →
      spectralEnergy ρ = ENNReal.ofReal (2 * entropy ρ) →
        ρ.value =ᵐ[torusMeasure d] (fun _ => 1))
    (u : Torus d → ℝ) (hu : InCriticalSobolev u) :
    logPartition u = ((spectralCoefficient d * potentialEnergy u : ℝ) : EReal) ↔
      ∃ c : ℝ, u =ᵐ[torusMeasure d] (fun _ => c) := by
  constructor
  · intro heq
    have hC : 0 < Legacy.BecknerOnofri.endpointConstant d :=
      div_pos (Nat.cast_pos.mpr hd) (Legacy.TorusEndpoint.endpointSigma_pos hd)
    have hR := GenericAttainment.rough_bound hd
      (by positivity : 0 < Legacy.BecknerOnofri.endpointConstant d / 2)
      (by linarith : Legacy.BecknerOnofri.endpointConstant d / 2 <
        Legacy.BecknerOnofri.endpointConstant d)
    let v := Legacy.BecknerOnofri.SobolevCentering.center (Bridge.potentialLp u hu.1)
    have hv := Legacy.BecknerOnofri.SobolevCentering.center_admissible hd
      (Bridge.potentialLp_real u hu.1) (Bridge.potentialLp_summable hd u hu)
    let r := Legacy.BecknerOnofri.SubcriticalEuler.gibbsDensity hR hv
    have hr : (Bridge.rawDensity r).FiniteEntropy :=
      Legacy.BecknerOnofri.SubcriticalEuler.gibbsDensity_finiteEntropy hR hv
    have hAn : spectralCoefficient d * (2 * Real.pi) ^ d = (1 / 2 : ℝ) := by
      unfold spectralCoefficient
      field_simp
    have heq' := RawAttainment.rawFunctional_eq_legacy hd (spectralCoefficient d) u hu
    unfold RawAttainment.rawFunctional at heq'
    rw [heq, ← EReal.coe_sub, sub_self, EReal.coe_zero, hAn] at heq'
    have hzero : Legacy.BecknerOnofri.SubcriticalAttainment.functional (1 / 2) v = 0 := by
      exact_mod_cast heq'.symm
    have hD := Legacy.BecknerOnofri.SubcriticalPrimalDual.dual_le_gibbs hd hR
      (by norm_num : (0 : ℝ) < 1 / 2) hv
    rw [hzero] at hD
    change 0 ≤ Legacy.BecknerOnofri.SubcriticalPrimalDual.densityFunctional (1 / 2) r at hD
    unfold Legacy.BecknerOnofri.SubcriticalPrimalDual.densityFunctional at hD
    norm_num at hD
    have hs : Summable (Legacy.TorusEndpoint.densitySpectralTerm r) := by
      exact (Legacy.TorusEndpoint.PhysicalGreenL2.physicalGreenEnergy_eq_spectral hd r
        (Legacy.BecknerOnofri.SubcriticalEuler.gibbsValue_memLp_two hR hv)).1
    have hb := hE (Bridge.rawDensity r) hr
    rw [Bridge.rawDensity_spectralEnergy r hs] at hb
    have hb' := (ENNReal.ofReal_le_ofReal_iff
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (entropy_nonneg _ hr))).mp hb
    have he : spectralEnergy (Bridge.rawDensity r) = ENNReal.ofReal (2 * entropy (Bridge.rawDensity r)) := by
      rw [Bridge.rawDensity_spectralEnergy r hs]
      congr 1
      change Legacy.BecknerOnofri.fourierEnergy r ≤
        2 * Legacy.TorusEndpoint.densityEntropy r.value at hb'
      change Legacy.BecknerOnofri.fourierEnergy r =
        2 * Legacy.TorusEndpoint.densityEntropy r.value
      linarith
    have hg := hRigid (Bridge.rawDensity r) hr he
    refine ⟨Real.log (Legacy.BecknerOnofri.SubcriticalAttainment.partition v) +
      ∫ y, u y ∂torusMeasure d, ?_⟩
    filter_upwards [hg, Bridge.centeredLp_ae u hu.1] with x hx hc
    have hl := Legacy.BecknerOnofri.SubcriticalEuler.log_gibbsValue hR hv x
    change Legacy.BecknerOnofri.SubcriticalEuler.gibbsValue v x = 1 at hx
    change (v x).re = centered u x at hc
    rw [hx, Real.log_one] at hl
    unfold centered at hc
    linarith
  · rintro ⟨c, hc⟩
    exact constant_potential_equality u hc

#print axioms potential_rigidity_of_density
end BecknerOnofri.HighDim
