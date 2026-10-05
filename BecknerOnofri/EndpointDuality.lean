import BecknerOnofri.PartitionRegularity
import BecknerOnofri.Entropy
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
The genuine density-to-potential implication, with full function domains and
the physical (2π)^d normalization. The density endpoint is an explicit premise
of this intermediate implication; this file does not claim to prove it.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators

namespace BecknerOnofri.HighDim

namespace Bridge

def rawDensity {d : ℕ} (ρ : Legacy.TorusEndpoint.ProbabilityDensity d) : ProbabilityDensity d where
  value := ρ.value
  nonneg := ρ.nonneg
  integrable := ρ.integrable
  mass := ρ.mass

theorem rawDensity_spectralEnergy {d : ℕ} (ρ : Legacy.TorusEndpoint.ProbabilityDensity d)
    (hs : Summable (Legacy.TorusEndpoint.densitySpectralTerm ρ)) :
    spectralEnergy (rawDensity ρ) = ENNReal.ofReal (Legacy.BecknerOnofri.fourierEnergy ρ) := by
  have he : spectralTerm (rawDensity ρ) = Legacy.TorusEndpoint.densitySpectralTerm ρ := by
    funext k
    exact (densitySpectralTerm_eq (rawDensity ρ) k).symm
  have hn (k : NonzeroFrequency d) : 0 ≤ Legacy.TorusEndpoint.densitySpectralTerm ρ k := by
    unfold Legacy.TorusEndpoint.densitySpectralTerm
    exact div_nonneg (sq_nonneg _) (pow_nonneg (Real.sqrt_nonneg _) _)
  unfold spectralEnergy Legacy.BecknerOnofri.fourierEnergy
  rw [he, ENNReal.ofReal_tsum_of_nonneg hn hs]

end Bridge

/-- Full critical Sobolev primal endpoint follows from the exact density
endpoint; exponential integrability remains a conclusion. -/
theorem potential_endpoint_of_density {d : ℕ} (hd : 0 < d)
    (hE : ∀ ρ : ProbabilityDensity d, ρ.FiniteEntropy →
      spectralEnergy ρ ≤ ENNReal.ofReal (2 * entropy ρ))
    (u : Torus d → ℝ) (hu : InCriticalSobolev u) :
    Integrable (fun x => Real.exp (centered u x)) (torusMeasure d) ∧
      logPartition u ≤ ((spectralCoefficient d * potentialEnergy u : ℝ) : EReal) := by
  have hD : ∀ ρ : Legacy.TorusEndpoint.ProbabilityDensity d,
      MemLp ρ.value 2 (Legacy.TorusEndpoint.torusMeasure d) →
      (1 / 2 : ℝ) * Legacy.BecknerOnofri.fourierEnergy ρ ≤
        Legacy.TorusEndpoint.densityEntropy ρ.value + Real.log 1 := by
    intro ρ hρ
    have hs := (Legacy.TorusEndpoint.PhysicalGreenL2.physicalGreenEnergy_eq_spectral hd ρ hρ).1
    have hEnt : (Bridge.rawDensity ρ).FiniteEntropy :=
      Legacy.TorusEndpoint.PhysicalGreenL2.finiteEntropy_of_memLp ρ hρ
    have h := hE (Bridge.rawDensity ρ) hEnt
    rw [Bridge.rawDensity_spectralEnergy ρ hs] at h
    have hn : 0 ≤ 2 * entropy (Bridge.rawDensity ρ) :=
      mul_nonneg (by norm_num) (entropy_nonneg _ hEnt)
    have hreal := (ENNReal.ofReal_le_ofReal_iff hn).mp h
    change Legacy.BecknerOnofri.fourierEnergy ρ ≤
      2 * Legacy.TorusEndpoint.densityEntropy ρ.value at hreal
    rw [Real.log_one]
    linarith
  have hR := Legacy.BecknerOnofri.SubcriticalAttainment.roughExponentialBound_of_density_bound
    hd (by norm_num : (0 : ℝ) < 1 / 2) hD
  have hadm := Legacy.BecknerOnofri.SobolevCentering.center_admissible hd
    (Bridge.potentialLp_real u hu.1) (Bridge.potentialLp_summable hd u hu)
  have h := (hR _ hadm 1 zero_lt_one).2
  have hZ :
      (∫ x, Real.exp ((Legacy.BecknerOnofri.SobolevCentering.center
        (Bridge.potentialLp u hu.1) x).re) ∂Legacy.TorusEndpoint.torusMeasure d) =
      ∫ x, Real.exp (centered u x) ∂torusMeasure d := by
    apply integral_congr_ae
    filter_upwards [Bridge.centeredLp_ae u hu.1] with x hx
    rw [hx]
  simp only [one_mul, one_pow, Real.log_one, add_zero] at h
  rw [hZ, Legacy.BecknerOnofri.SobolevCentering.center_energy hd] at h
  have hc : spectralCoefficient d * potentialEnergy u =
      Legacy.BecknerOnofri.TorusSobolev.criticalEnergy (Bridge.potentialLp u hu.1) / 2 := by
    rw [Bridge.potentialLp_energy hd u hu]
    unfold spectralCoefficient
    field_simp
  refine ⟨exp_centered_integrable hd u hu, ?_⟩
  rw [logPartition_eq_log_integral hd u hu, hc]
  norm_num at h
  exact_mod_cast h

#print axioms potential_endpoint_of_density

end BecknerOnofri.HighDim
