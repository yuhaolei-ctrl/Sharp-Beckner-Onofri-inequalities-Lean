module

public import Legacy.BecknerOnofri.Endpoint

@[expose] public section

/-! Passage to limits of actual probability densities. The full spectral
bound follows from finite frequency sets, so no energy convergence is assumed. -/

noncomputable section
open MeasureTheory Legacy.TorusEndpoint Filter
open scoped Topology BigOperators

namespace Legacy.BecknerOnofri.EndpointClosure

theorem densityFourier_sub_bound {d : ℕ} (rho eta : ProbabilityDensity d)
    (k : Frequency d) :
    ‖densityFourier rho.value k - densityFourier eta.value k‖ ≤
      ∫ x, ‖rho.value x - eta.value x‖ ∂torusMeasure d := by
  rw [densityFourier, densityFourier,
    ← integral_sub (densityFourier_integrable rho k) (densityFourier_integrable eta k)]
  calc
    _ ≤ ∫ x, ‖UnitAddTorus.mFourier (-k) x * (rho.value x : ℂ) -
      UnitAddTorus.mFourier (-k) x * (eta.value x : ℂ)‖ ∂torusMeasure d :=
      norm_integral_le_integral_norm _
    _ ≤ _ := by
      apply integral_mono
        ((densityFourier_integrable rho k).sub (densityFourier_integrable eta k)).norm
        (rho.integrable.sub eta.integrable).norm
      intro x
      dsimp only [Pi.sub_apply]
      rw [← mul_sub, ← Complex.ofReal_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_of_le_one_left (abs_nonneg _) (fourier_character_norm_le_one _ _)

theorem fourier_tendsto_of_L1 {d : ℕ} (rho : ℕ → ProbabilityDensity d)
    (eta : ProbabilityDensity d)
    (hL1 : Tendsto (fun n => ∫ x, ‖(rho n).value x - eta.value x‖ ∂torusMeasure d)
      atTop (𝓝 0)) (k : Frequency d) :
    Tendsto (fun n => densityFourier (rho n).value k) atTop (𝓝 (densityFourier eta.value k)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  exact squeeze_zero (fun _ => norm_nonneg _)
    (fun n => densityFourier_sub_bound (rho n) eta k) hL1

theorem spectral_bound_of_limits {d : ℕ} (C : ℝ) (hC : 0 < C)
    (rho : ℕ → ProbabilityDensity d) (eta : ProbabilityDensity d)
    (hvalid : ∀ n, Summable (densitySpectralTerm (rho n)) ∧
      C * fourierEnergy (rho n) ≤ densityEntropy (rho n).value)
    (hFourier : ∀ k, Tendsto (fun n => densityFourier (rho n).value k)
      atTop (𝓝 (densityFourier eta.value k)))
    (hEntropy : Tendsto (fun n => densityEntropy (rho n).value)
      atTop (𝓝 (densityEntropy eta.value))) :
    Summable (densitySpectralTerm eta) ∧ C * fourierEnergy eta ≤ densityEntropy eta.value := by
  have hn (r : ProbabilityDensity d) (k : NonzeroFrequency d) :
      0 ≤ densitySpectralTerm r k := by
    exact div_nonneg (sq_nonneg _) (pow_nonneg (Real.sqrt_nonneg _) _)
  have hfinite (s : Finset (NonzeroFrequency d)) :
      C * ∑ k ∈ s, densitySpectralTerm eta k ≤ densityEntropy eta.value := by
    have ht : Tendsto (fun n => C * ∑ k ∈ s, densitySpectralTerm (rho n) k)
        atTop (𝓝 (C * ∑ k ∈ s, densitySpectralTerm eta k)) := by
      apply Tendsto.const_mul
      apply tendsto_finsetSum
      intro k hk
      exact ((hFourier k.val).norm.pow 2).div_const _
    apply le_of_tendsto_of_tendsto' ht hEntropy
    intro n
    exact (mul_le_mul_of_nonneg_left
      ((hvalid n).1.sum_le_tsum s (fun k _ => hn (rho n) k)) hC.le).trans (hvalid n).2
  have hsum (s : Finset (NonzeroFrequency d)) :
      ∑ k ∈ s, densitySpectralTerm eta k ≤ densityEntropy eta.value / C := by
    exact (le_div_iff₀ hC).mpr (by simpa [mul_comm] using hfinite s)
  refine ⟨summable_of_sum_le (hn eta) hsum, ?_⟩
  have h := Real.tsum_le_of_sum_le (hn eta) hsum
  exact (mul_le_mul_of_nonneg_left h hC.le).trans_eq (by field_simp)

theorem endpoint_of_L1_entropy_limit {d : ℕ} (hd : 0 < d)
    (rho : ℕ → ProbabilityDensity d) (eta : ProbabilityDensity d)
    (hvalid : ∀ n, Summable (densitySpectralTerm (rho n)) ∧
      endpointConstant d * fourierEnergy (rho n) ≤ densityEntropy (rho n).value)
    (hL1 : Tendsto (fun n => ∫ x, ‖(rho n).value x - eta.value x‖ ∂torusMeasure d)
      atTop (𝓝 0))
    (hEntropy : Tendsto (fun n => densityEntropy (rho n).value)
      atTop (𝓝 (densityEntropy eta.value))) :
    Summable (densitySpectralTerm eta) ∧
      endpointConstant d * fourierEnergy eta ≤ densityEntropy eta.value :=
  spectral_bound_of_limits _ (div_pos (Nat.cast_pos.mpr hd) (endpointSigma_pos hd))
    rho eta hvalid (fourier_tendsto_of_L1 rho eta hL1) hEntropy

/-- An entropy upper bound suffices for regularizations: no convergence of
the entropy or the full spectral energy needs to be assumed. -/
theorem spectral_bound_of_fourier_limits_entropy_le {d : ℕ} (C : ℝ) (hC : 0 < C)
    (rho : ℕ → ProbabilityDensity d) (eta : ProbabilityDensity d)
    (hvalid : ∀ n, Summable (densitySpectralTerm (rho n)) ∧
      C * fourierEnergy (rho n) ≤ densityEntropy (rho n).value)
    (hFourier : ∀ k, Tendsto (fun n => densityFourier (rho n).value k)
      atTop (𝓝 (densityFourier eta.value k)))
    (hEntropy_le : ∀ n, densityEntropy (rho n).value ≤ densityEntropy eta.value) :
    Summable (densitySpectralTerm eta) ∧ C * fourierEnergy eta ≤ densityEntropy eta.value := by
  have hn (r : ProbabilityDensity d) (k : NonzeroFrequency d) :
      0 ≤ densitySpectralTerm r k :=
    div_nonneg (sq_nonneg _) (pow_nonneg (Real.sqrt_nonneg _) _)
  have hsum (s : Finset (NonzeroFrequency d)) :
      ∑ k ∈ s, densitySpectralTerm eta k ≤ densityEntropy eta.value / C := by
    apply (le_div_iff₀ hC).mpr
    have ht : Tendsto (fun n => C * ∑ k ∈ s, densitySpectralTerm (rho n) k)
        atTop (𝓝 (C * ∑ k ∈ s, densitySpectralTerm eta k)) :=
      (tendsto_finsetSum _ (fun k _ => ((hFourier k.val).norm.pow 2).div_const _)).const_mul C
    have h := le_of_tendsto ht (Eventually.of_forall (fun n =>
      (mul_le_mul_of_nonneg_left
        ((hvalid n).1.sum_le_tsum s (fun k _ => hn (rho n) k)) hC.le).trans
          ((hvalid n).2.trans (hEntropy_le n))))
    simpa [mul_comm] using h
  refine ⟨summable_of_sum_le (hn eta) hsum, ?_⟩
  have h := Real.tsum_le_of_sum_le (hn eta) hsum
  exact (mul_le_mul_of_nonneg_left h hC.le).trans_eq (by field_simp)

end Legacy.BecknerOnofri.EndpointClosure
