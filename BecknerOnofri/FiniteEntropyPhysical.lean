import BecknerOnofri.FiniteEntropyEnergy
import BecknerOnofri.HeatEnergyLimit
import Legacy.BecknerOnofri.FiniteEnergyGreenIdentification

/-! The finite-entropy Green assertions in Section 2 for every positive
dimension, including the literal singular-kernel integral and heat limit. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped Topology
namespace BecknerOnofri.HighDim.FiniteEntropyPhysical
open Legacy.TorusEndpoint Legacy.BecknerOnofri
open GreenKernelReal PhysicalGreenL2 PhysicalGreenFiniteEnergy

local instance : (AddCircle.haarAddCircle (T := 1)).IsNegInvariant := by
  have he : AddCircle.haarAddCircle (T := 1) = (volume : Measure UnitAddCircle) := by
    simpa using (AddCircle.volume_eq_smul_haarAddCircle (T := 1)).symm
  rw [he]
  infer_instance

lemma summable_energy {d : ℕ} (hd : 0 < d) (ρ : Legacy.TorusEndpoint.ProbabilityDensity d)
    (hρ : ρ.FiniteEntropy) : Summable (densitySpectralTerm ρ) := by
  have hC : 0 < endpointConstant d := div_pos (Nat.cast_pos.mpr hd) (endpointSigma_pos hd)
  exact (legacy_rough_finite_entropy hd ρ hρ
    (by positivity : 0 < endpointConstant d/2) (by linarith)).1

theorem physical_eq_spectral {d : ℕ} (hd : 0 < d) (ρ : Legacy.TorusEndpoint.ProbabilityDensity d)
    (hρ : ρ.FiniteEntropy) : physicalGreenEnergy ρ = densitySpectralEnergy ρ :=
  FiniteEnergyGreenIdentification.physicalGreen_eq_spectral hd ρ (summable_energy hd ρ hρ)

theorem interaction_integrable {d : ℕ} (hd : 0 < d) (ρ : Legacy.TorusEndpoint.ProbabilityDensity d)
    (hρ : ρ.FiniteEntropy) : Integrable (fun z : Legacy.TorusEndpoint.Torus d × Legacy.TorusEndpoint.Torus d =>
      realGreen d (z.1-z.2)*ρ.value z.1*ρ.value z.2)
      ((Legacy.TorusEndpoint.torusMeasure d).prod (Legacy.TorusEndpoint.torusMeasure d)) :=
  (physicalGreen_integrable_and_le_spectral hd ρ (summable_energy hd ρ hρ)).1

lemma partition_double {d : ℕ} (hd : 0 < d) (a : ℝ) :
    GreenRoughEnergy.partition d (a/endpointSigma d) =
      ∫ x, ∫ y, Real.exp (a*realGreen d (x-y)) ∂Legacy.TorusEndpoint.torusMeasure d
        ∂Legacy.TorusEndpoint.torusMeasure d := by
  have hσ := (endpointSigma_pos hd).ne'
  haveI : (Legacy.TorusEndpoint.torusMeasure d).IsAddLeftInvariant := by
    rw [torusMeasure_explicit]; infer_instance
  haveI : (Legacy.TorusEndpoint.torusMeasure d).IsNegInvariant := by
    rw [torusMeasure_explicit]; infer_instance
  have he (x : Legacy.TorusEndpoint.Torus d) :
      (∫ y, Real.exp (a*realGreen d (x-y)) ∂Legacy.TorusEndpoint.torusMeasure d) =
        ∫ y, Real.exp (a*realGreen d y) ∂Legacy.TorusEndpoint.torusMeasure d :=
    integral_sub_left_eq_self (fun y => Real.exp (a*realGreen d y)) _ x
  simp only [he, integral_const, measureReal_univ_eq_one, one_smul]
  unfold GreenRoughEnergy.partition GreenRoughEnergy.kernel
  congr 1
  funext x
  congr 1
  field_simp

theorem interaction_bound {d : ℕ} (hd : 0 < d) (ρ : Legacy.TorusEndpoint.ProbabilityDensity d)
    (hρ : ρ.FiniteEntropy) (a : ℝ) (ha : 0 < a) (had : a < (d:ℝ)) :
    0 ≤ physicalGreenEnergy ρ ∧
    physicalGreenEnergy ρ ≤ 2/a*densityEntropy ρ.value + 1/a*Real.log
      (∫ x, ∫ y, Real.exp (a*realGreen d (x-y)) ∂Legacy.TorusEndpoint.torusMeasure d
        ∂Legacy.TorusEndpoint.torusMeasure d) := by
  have hσ := endpointSigma_pos hd
  have hb : a/endpointSigma d < endpointConstant d :=
    (div_lt_div_iff_of_pos_right hσ).mpr had
  have hh := (legacy_rough_finite_entropy hd ρ hρ (div_pos ha hσ) hb).2
  rw [partition_double hd a] at hh
  rw [physical_eq_spectral hd ρ hρ, normalized_energy]
  have he : 0 ≤ densityEntropy ρ.value := by
    exact densityEntropy_nonneg_of_finite ρ hρ
  have hQ : 0 ≤ fourierEnergy ρ := tsum_nonneg (fun k => by
    unfold densitySpectralTerm
    exact div_nonneg (sq_nonneg _) (pow_nonneg (Real.sqrt_nonneg _) _))
  refine ⟨div_nonneg hQ hσ.le, ?_⟩
  apply (mul_le_mul_iff_left₀ ha).mp
  have halg : (2/a*densityEntropy ρ.value + 1/a*Real.log
      (∫ x, ∫ y, Real.exp (a*realGreen d (x-y)) ∂Legacy.TorusEndpoint.torusMeasure d
        ∂Legacy.TorusEndpoint.torusMeasure d))*a =
      2*densityEntropy ρ.value + Real.log
      (∫ x, ∫ y, Real.exp (a*realGreen d (x-y)) ∂Legacy.TorusEndpoint.torusMeasure d
        ∂Legacy.TorusEndpoint.torusMeasure d) := by field_simp
  rw [halg]
  have heq : fourierEnergy ρ / endpointSigma d * a = a / endpointSigma d * fourierEnergy ρ := by ring
  rw [heq]
  linarith

theorem heat_interaction_tendsto {d : ℕ} (hd : 0 < d)
    (ρ : Legacy.TorusEndpoint.ProbabilityDensity d) (hρ : ρ.FiniteEntropy)
    (t : ℕ → ℝ) (ht : ∀ n, 0 < t n) (ht0 : Tendsto t atTop (𝓝 0)) :
    Tendsto (fun n => physicalGreenEnergy (HeatDensityApproximation.heatDensity ρ (ht n)))
      atTop (𝓝 (physicalGreenEnergy ρ)) := by
  have he (n : ℕ) := physical_eq_spectral hd (HeatDensityApproximation.heatDensity ρ (ht n))
    (HeatDensityApproximation.heatDensity_finiteEntropy ρ (ht n))
  simp only [he,physical_eq_spectral hd ρ hρ,normalized_energy]
  exact (heat_fourierEnergy_tendsto hd ρ hρ t ht ht0).div_const _

#print axioms interaction_bound
#print axioms interaction_integrable
#print axioms heat_interaction_tendsto
end BecknerOnofri.HighDim.FiniteEntropyPhysical
