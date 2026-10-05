import Legacy.BecknerOnofri.StrictFiniteMixture

/-! The finite scalar margin survives the actual normalized finite approximations.
The countable theorem assumes the same summable uniform majorant as its constructive approximation. -/
noncomputable section
open Finset MeasureTheory Legacy.TorusEndpoint Filter
open scoped BigOperators Topology
namespace Legacy.BecknerOnofri.StrictMixture
open CosineMixtureApproximation

/-- Finite-frequency lower semicontinuity retains a convergent quantitative margin. -/
theorem spectral_gap_of_limits {d : ℕ} {C G : ℝ} (hC : 0 < C)
    (r : ℕ → ProbabilityDensity d) (eta : ProbabilityDensity d) (g : ℕ → ℝ)
    (hvalid : ∀ᶠ n in atTop, Summable (densitySpectralTerm (r n)) ∧
      C * fourierEnergy (r n) + g n ≤ densityEntropy (r n).value)
    (hFourier : ∀ k, Tendsto (fun n => densityFourier (r n).value k)
      atTop (𝓝 (densityFourier eta.value k)))
    (hEntropy : Tendsto (fun n => densityEntropy (r n).value)
      atTop (𝓝 (densityEntropy eta.value)))
    (hg : Tendsto g atTop (𝓝 G)) :
    Summable (densitySpectralTerm eta) ∧ C * fourierEnergy eta + G ≤ densityEntropy eta.value := by
  have hn (rho : ProbabilityDensity d) (k : NonzeroFrequency d) :
      0 ≤ densitySpectralTerm rho k :=
    div_nonneg (sq_nonneg _) (pow_nonneg (Real.sqrt_nonneg _) _)
  have hsum (s : Finset (NonzeroFrequency d)) :
      ∑ k ∈ s, densitySpectralTerm eta k ≤ (densityEntropy eta.value - G) / C := by
    apply (le_div_iff₀ hC).mpr
    have ht : Tendsto (fun n => C * ∑ k ∈ s, densitySpectralTerm (r n) k)
        atTop (𝓝 (C * ∑ k ∈ s, densitySpectralTerm eta k)) :=
      (tendsto_finsetSum _ (fun k _ => ((hFourier k.val).norm.pow 2).div_const _)).const_mul C
    have hle : ∀ᶠ n in atTop, C * (∑ k ∈ s, densitySpectralTerm (r n) k) ≤
        densityEntropy (r n).value - g n := by
      filter_upwards [hvalid] with n hv
      have hp := mul_le_mul_of_nonneg_left
        (hv.1.sum_le_tsum s (fun k _ => hn (r n) k)) hC.le
      change C * (∑ k ∈ s, densitySpectralTerm (r n) k) ≤ C * fourierEnergy (r n) at hp
      linarith [hv.2]
    have h := le_of_tendsto_of_tendsto ht (hEntropy.sub hg) hle
    simpa [mul_comm] using h
  refine ⟨summable_of_sum_le (hn eta) hsum, ?_⟩
  have h := mul_le_mul_of_nonneg_left (Real.tsum_le_of_sum_le (hn eta) hsum) hC.le
  have hc : C * ((densityEntropy eta.value - G) / C) = densityEntropy eta.value - G := by
    field_simp
  rw [hc] at h
  change C * fourierEnergy eta ≤ densityEntropy eta.value - G at h
  linarith

theorem countable_mixture_gap {d : ℕ} (hd2 : 2 ≤ d) (hd10 : d ≤ 10)
    (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ) (hw : ∀ n, 0 ≤ w n) (hm : HasSum w 1)
    (hSup : Summable (fun n => w n * CosineMixture.tensor (N n) 0))
    (a : ℕ) (hN : N a ≠ 0) :
    endpointConstant d * fourierEnergy (probabilityDensity w N hw hm hSup) +
      w a * w a * Legacy.D10.latentWeight (N a) (N a) (N a) * gap d / 2 ≤
        densityEntropy (probabilityDensity w N hw hm hSup).value := by
  let g : ℕ → ℝ := fun m => ((1 - epsilon m) * w a) * ((1 - epsilon m) * w a) *
    Legacy.D10.latentWeight (N a) (N a) (N a) * gap d / 2
  have hvalid : ∀ᶠ m in atTop,
      Summable (densitySpectralTerm (approximatingDensity w N hw hm m)) ∧
      endpointConstant d * fourierEnergy (approximatingDensity w N hw hm m) + g m ≤
        densityEntropy (approximatingDensity w N hw hm m).value := by
    filter_upwards [eventually_gt_atTop a] with m ham
    refine ⟨CosineMixtureEnergy.spectral_summable _ _ _ _ _, ?_⟩
    have h := finite_mixture_gap hd2 hd10 (range (m + 1)) (finiteWeight w m) (finiteIndex N m)
      (fun n _ => finiteWeight_nonneg w hw hm m n) (finiteWeight_mass w m)
      (approximatingDensity_pos w N hw hm m) a (by simp; omega)
      (by simpa [finiteIndex, ham] using hN)
    simpa only [finiteWeight, finiteIndex, if_pos ham, approximatingDensity, g] using h
  have hg : Tendsto g atTop (𝓝 (w a * w a * Legacy.D10.latentWeight (N a) (N a) (N a) * gap d / 2)) := by
    have h : Tendsto (fun m => (1 - epsilon m) * w a) atTop (𝓝 (w a)) := by
      simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub epsilon_tendsto).mul_const (w a)
    exact (((h.mul h).mul_const _).mul_const _).div_const _
  exact (spectral_gap_of_limits
    (div_pos (Nat.cast_pos.mpr (by omega : 0 < d)) (endpointSigma_pos (by omega)))
    (approximatingDensity w N hw hm) (probabilityDensity w N hw hm hSup) g hvalid
    (EndpointClosure.fourier_tendsto_of_L1 _ _ (density_L1_tendsto w N hw hm hSup))
    (density_entropy_tendsto w N hw hm hSup) hg).2

theorem countable_mixture_strict_of_component {d : ℕ} (hd2 : 2 ≤ d) (hd10 : d ≤ 10)
    (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ) (hw : ∀ n, 0 ≤ w n) (hm : HasSum w 1)
    (hSup : Summable (fun n => w n * CosineMixture.tensor (N n) 0))
    (a : ℕ) (ha : 0 < w a) (hN : N a ≠ 0) :
    endpointConstant d * fourierEnergy (probabilityDensity w N hw hm hSup) <
      densityEntropy (probabilityDensity w N hw hm hSup).value := by
  have hgap := countable_mixture_gap hd2 hd10 w N hw hm hSup a hN
  have hpositive : 0 < w a * w a * Legacy.D10.latentWeight (N a) (N a) (N a) * gap d / 2 :=
    div_pos (mul_pos (mul_pos (mul_pos ha ha) (latentWeight_self_pos (N a)))
      (gap_pos (by omega))) (by norm_num)
  linarith

theorem countable_uniform_of_no_component {d : ℕ}
    (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ) (hw : ∀ n, 0 ≤ w n) (hm : HasSum w 1)
    (hn : ∀ n, 0 < w n → N n = 0) (x : Torus d) : rho w N x = 1 := by
  unfold rho
  have heq : (fun n => w n * CosineMixture.tensor (N n) x) = w := by
    funext n
    by_cases h : w n = 0
    · simp [h]
    · rw [hn n (lt_of_le_of_ne (hw n) (Ne.symm h))]
      simp only [Pi.zero_def, tensor_zero_index, mul_one]
  rw [heq, hm.tsum_eq]

theorem countable_mixture_uniform_of_equality {d : ℕ} (hd2 : 2 ≤ d) (hd10 : d ≤ 10)
    (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ) (hw : ∀ n, 0 ≤ w n) (hm : HasSum w 1)
    (hSup : Summable (fun n => w n * CosineMixture.tensor (N n) 0))
    (heq : endpointConstant d * fourierEnergy (probabilityDensity w N hw hm hSup) =
      densityEntropy (probabilityDensity w N hw hm hSup).value) : ∀ x, rho w N x = 1 := by
  apply countable_uniform_of_no_component w N hw hm
  intro n hn
  by_contra hN
  exact (ne_of_lt (countable_mixture_strict_of_component hd2 hd10 w N hw hm hSup n hn hN)) heq

#print axioms spectral_gap_of_limits
#print axioms countable_mixture_gap
#print axioms countable_mixture_uniform_of_equality
end Legacy.BecknerOnofri.StrictMixture
