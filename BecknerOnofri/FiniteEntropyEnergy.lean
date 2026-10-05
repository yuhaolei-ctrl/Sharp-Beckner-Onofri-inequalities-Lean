module

public import BecknerOnofri.EndpointDuality
public import Legacy.BecknerOnofri.HeatDensityApproximation
public import Legacy.BecknerOnofri.EndpointClosure

@[expose] public section

/-! The actual energy of every finite-entropy density is finite. Heat
regularization and finite-frequency limits extend the proved rough bound. -/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology ENNReal

namespace BecknerOnofri.HighDim

theorem legacy_rough_finite_entropy {d : ℕ} (hd : 0 < d)
    (ρ : Legacy.TorusEndpoint.ProbabilityDensity d) (hρ : ρ.FiniteEntropy)
    {b : ℝ} (hb : 0 < b) (hbd : b < Legacy.BecknerOnofri.endpointConstant d) :
    Summable (Legacy.TorusEndpoint.densitySpectralTerm ρ) ∧
      b * Legacy.BecknerOnofri.fourierEnergy ρ ≤
        Legacy.TorusEndpoint.densityEntropy ρ.value +
          Real.log (Legacy.BecknerOnofri.GreenRoughEnergy.partition d b) := by
  let t : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have ht (n : ℕ) : 0 < t n := by dsimp [t]; positivity
  let r := fun n => Legacy.BecknerOnofri.HeatDensityApproximation.heatDensity ρ (ht n)
  have hr (n : ℕ) : MemLp (r n).value 2 (Legacy.TorusEndpoint.torusMeasure d) :=
    (Legacy.BecknerOnofri.HeatDensityApproximation.heatValue_continuous ρ (ht n)).memLp_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hs (n : ℕ) :=
    (Legacy.TorusEndpoint.PhysicalGreenL2.physicalGreenEnergy_eq_spectral hd (r n) (hr n)).1
  have hbnd (n : ℕ) : b * Legacy.BecknerOnofri.fourierEnergy (r n) ≤
      Legacy.TorusEndpoint.densityEntropy ρ.value +
        Real.log (Legacy.BecknerOnofri.GreenRoughEnergy.partition d b) := by
    have h := Legacy.BecknerOnofri.GreenExponentialIntegrability.rough_energy
      hd (r n) (hr n) hb.le hbd
    have hEnt := Legacy.BecknerOnofri.HeatDensityApproximation.heatDensity_entropy_le ρ hρ (ht n)
    linarith
  have hF := Legacy.BecknerOnofri.HeatDensityApproximation.heatDensity_fourier_tendsto
    ρ t ht tendsto_one_div_add_atTop_nhds_zero_nat
  have hn (η : Legacy.TorusEndpoint.ProbabilityDensity d)
      (k : Legacy.TorusEndpoint.NonzeroFrequency d) :
      0 ≤ Legacy.TorusEndpoint.densitySpectralTerm η k :=
    div_nonneg (sq_nonneg _) (pow_nonneg (Real.sqrt_nonneg _) _)
  let M := (Legacy.TorusEndpoint.densityEntropy ρ.value +
    Real.log (Legacy.BecknerOnofri.GreenRoughEnergy.partition d b)) / b
  have hsum (s : Finset (Legacy.TorusEndpoint.NonzeroFrequency d)) :
      ∑ k ∈ s, Legacy.TorusEndpoint.densitySpectralTerm ρ k ≤ M := by
    apply (le_div_iff₀ hb).mpr
    have hlim : Tendsto
        (fun n => b * ∑ k ∈ s, Legacy.TorusEndpoint.densitySpectralTerm (r n) k)
        atTop (𝓝 (b * ∑ k ∈ s, Legacy.TorusEndpoint.densitySpectralTerm ρ k)) := by
      apply Tendsto.const_mul
      apply tendsto_finsetSum
      intro k _
      exact ((hF k.val).norm.pow 2).div_const _
    have h := le_of_tendsto hlim (Eventually.of_forall (fun n =>
      (mul_le_mul_of_nonneg_left ((hs n).sum_le_tsum s (fun k _ => hn (r n) k)) hb.le).trans
        (hbnd n)))
    simpa [mul_comm] using h
  refine ⟨summable_of_sum_le (hn ρ) hsum, ?_⟩
  have h := Real.tsum_le_of_sum_le (hn ρ) hsum
  have he : b * M = Legacy.TorusEndpoint.densityEntropy ρ.value +
      Real.log (Legacy.BecknerOnofri.GreenRoughEnergy.partition d b) := by
    dsimp [M]
    field_simp
  exact (mul_le_mul_of_nonneg_left h hb.le).trans_eq he

theorem finiteEntropy_spectralTerm_summable {d : ℕ} (hd : 0 < d)
    (ρ : ProbabilityDensity d) (hρ : ρ.FiniteEntropy) : Summable (spectralTerm ρ) := by
  have hC : 0 < Legacy.BecknerOnofri.endpointConstant d :=
    div_pos (Nat.cast_pos.mpr hd) (Legacy.TorusEndpoint.endpointSigma_pos hd)
  have hs := (legacy_rough_finite_entropy hd (Bridge.density ρ) hρ
    (by positivity : 0 < Legacy.BecknerOnofri.endpointConstant d / 2)
    (by linarith : Legacy.BecknerOnofri.endpointConstant d / 2 <
      Legacy.BecknerOnofri.endpointConstant d)).1
  exact hs.congr (Bridge.densitySpectralTerm_eq ρ)

theorem finiteEntropy_spectralEnergy_ne_top {d : ℕ} (hd : 0 < d)
    (ρ : ProbabilityDensity d) (hρ : ρ.FiniteEntropy) : spectralEnergy ρ ≠ ⊤ := by
  have hs := finiteEntropy_spectralTerm_summable hd ρ hρ
  have hn (k : NonzeroFrequency d) : 0 ≤ spectralTerm ρ k := by
    unfold spectralTerm frequencyLength
    positivity
  unfold spectralEnergy
  rw [← ENNReal.ofReal_tsum_of_nonneg hn hs]
  exact ENNReal.ofReal_ne_top

#print axioms finiteEntropy_spectralEnergy_ne_top

theorem spectralEnergy_coe_eq_tsum {d : ℕ} (hd : 0 < d)
    (ρ : ProbabilityDensity d) (hρ : ρ.FiniteEntropy) :
    (spectralEnergy ρ).toEReal = ((∑' k, spectralTerm ρ k : ℝ) : EReal) := by
  have hs := finiteEntropy_spectralTerm_summable hd ρ hρ
  have hn (k : NonzeroFrequency d) : 0 ≤ spectralTerm ρ k := by
    unfold spectralTerm frequencyLength
    positivity
  unfold spectralEnergy
  rw [← ENNReal.ofReal_tsum_of_nonneg hn hs]
  change ((ENNReal.ofReal (∑' k, spectralTerm ρ k) : ℝ≥0∞) : EReal) = _
  rw [EReal.coe_ennreal_ofReal, max_eq_left]
  exact_mod_cast tsum_nonneg hn

end BecknerOnofri.HighDim
