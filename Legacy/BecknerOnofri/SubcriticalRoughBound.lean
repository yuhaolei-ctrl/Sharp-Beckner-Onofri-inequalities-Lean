module

public import Legacy.BecknerOnofri.TruncatedGibbs
public import Legacy.BecknerOnofri.SobolevDensityPairing
public import Legacy.BecknerOnofri.GreenExponentialIntegrability
public import Legacy.BecknerOnofri.SubcriticalAttainment

@[expose] public section

/-! The full-function rough exponential inequality is obtained from actual
truncated Gibbs densities and proved Fourier pairing. The final theorems
use the actual Green exponential estimate and have no rough-bound hypothesis. -/
noncomputable section
open Set Filter MeasureTheory Legacy.TorusEndpoint
open scoped BigOperators Topology ENNReal
namespace Legacy.BecknerOnofri.SubcriticalAttainment
open TorusSobolev

theorem roughExponentialBound_of_density_bound {d : ℕ} (hd : 0 < d) {b Ab : ℝ}
    (hb : 0 < b)
    (hD : ∀ r : ProbabilityDensity d, MemLp r.value 2 (torusMeasure d) →
      b * fourierEnergy r ≤ densityEntropy r.value + Real.log Ab) :
    RoughExponentialBound d b Ab := by
  intro u hu p hp
  have hf : MemLp (fun x => p*(u x).re) 2 (torusMeasure d) := by
    simpa only [Function.comp_def, Complex.reCLM_apply] using (Complex.reCLM.comp_memLp u).const_mul p
  apply TruncatedGibbs.integrable_exp_of_truncated_log_bound hf
  intro N
  let r := TruncatedGibbs.density hf N
  have hr : MemLp r.value 2 (torusMeasure d) := TruncatedGibbs.density_memLp hf N
  have hZ := TruncatedGibbs.log_partition_le_pairing_sub_entropy hf N
  have hpair := SobolevDensityPairing.pairing_quadratic_bound hd u hu.2 r hr b hb p hp.le
  have hrough := hD r hr
  have he : (∫ x, r.value x * (p*(u x).re) ∂torusMeasure d) =
      p * (∫ x, r.value x * (u x).re ∂torusMeasure d) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all _ (fun x => by ring)
  change Real.log (TruncatedGibbs.partition (fun x => p*(u x).re) N) ≤
    (∫ x, r.value x * (p*(u x).re) ∂torusMeasure d) - densityEntropy r.value at hZ
  rw [he] at hZ
  linarith

/-- The actual Green kernel supplies the estimate for every real critical Sobolev potential. -/
theorem roughExponentialBound {d : ℕ} (hd : 0 < d) {b : ℝ}
    (hb : 0 < b) (hbd : b < endpointConstant d) :
    RoughExponentialBound d b (GreenRoughEnergy.partition d b) :=
  roughExponentialBound_of_density_bound hd hb
    (fun r hr => GreenExponentialIntegrability.rough_energy hd r hr hb.le hbd)

/-- Genuine subcritical attainment, with the rough inequality fully discharged. -/
theorem exists_global_maximizer_of_b {d : ℕ} (hd : 0 < d) {b A : ℝ}
    (hb : 0 < b) (hbd : b < endpointConstant d) (hA : 1/(4*b) < A) :
    ∃ u : TorusL2 d, Admissible u ∧ 0 ≤ functional A u ∧
      ∀ v : TorusL2 d, Admissible v → functional A v ≤ functional A u := by
  obtain ⟨u, hu, _, hzero, hmax⟩ := exists_global_maximizer hd hb hA (roughExponentialBound hd hb hbd)
  exact ⟨u, hu, hzero, hmax⟩

/-- Every coefficient strictly above the concentration threshold attains its
supremum on the actual real mean-zero critical Sobolev class, in every positive dimension. -/
theorem exists_subcritical_maximizer {d : ℕ} (hd : 0 < d) {A : ℝ}
    (hA : 1/(4*endpointConstant d) < A) :
    ∃ u : TorusL2 d, Admissible u ∧ 0 ≤ functional A u ∧
      ∀ v : TorusL2 d, Admissible v → functional A v ≤ functional A u := by
  have hC : 0 < endpointConstant d :=
    div_pos (by exact_mod_cast hd) (endpointSigma_pos hd)
  have hA0 : 0 < A := (by positivity : 0 < 1/(4*endpointConstant d)).trans hA
  have hbC : 1/(4*A) < endpointConstant d := by
    have hh := (div_lt_iff₀ (by positivity : 0 < 4*endpointConstant d)).mp hA
    apply (div_lt_iff₀ (by positivity : 0 < 4*A)).mpr
    nlinarith
  obtain ⟨b, hb, hbd⟩ := exists_between hbC
  have hb0 : 0 < b := (by positivity : 0 < 1/(4*A)).trans hb
  have hAb : 1/(4*b) < A := by
    have hh := (div_lt_iff₀ (by positivity : 0 < 4*A)).mp hb
    apply (div_lt_iff₀ (by positivity : 0 < 4*b)).mpr
    nlinarith
  exact exists_global_maximizer_of_b hd hb0 hbd hAb

#print axioms roughExponentialBound_of_density_bound
#print axioms roughExponentialBound
#print axioms exists_global_maximizer_of_b
#print axioms exists_subcritical_maximizer
end Legacy.BecknerOnofri.SubcriticalAttainment
