import BecknerOnofri.OnsetWienerBounds
import BecknerOnofri.RawAttainment

/-! Convergence of actual global maximizers in every fixed Sobolev space.
Uniform polynomial Wiener bounds, combined with L² convergence, control the
full Fourier series in the physical (2π)-normalized Sobolev norm. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology ENNReal
namespace BecknerOnofri.OnsetSobolev
open Legacy.TorusEndpoint Legacy.BecknerOnofri
open TorusSobolev SubcriticalAttainment SubcriticalEuler RadialWiener OnsetWienerBounds
open HighDim.RawAttainment

theorem physical_weight_le_radial {d : ℕ} {s : ℝ} {m : ℕ} (hs : s ≤ (m:ℝ))
    (k : Frequency d) :
    (1 + (2 * Real.pi * HighDim.frequencyLength k)^2)^s ≤
      (1 + 2*Real.pi)^(2*m) * radialWeight (2*m) k := by
  rw [HighDim.Bridge.frequencyLength_eq]
  have hr : 0 ≤ frequencyRadius k := frequencyRadius_nonneg k
  have hc : 0 ≤ 2*Real.pi := by positivity
  have h1 : 1 + (2*Real.pi*frequencyRadius k)^2 ≤ (1+2*Real.pi*frequencyRadius k)^2 := by
    nlinarith [mul_nonneg hc hr]
  have h2 : 1+2*Real.pi*frequencyRadius k ≤ (1+2*Real.pi)*(1+frequencyRadius k) := by
    nlinarith
  calc
    _ ≤ (1 + (2*Real.pi*frequencyRadius k)^2)^(m:ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg (2*Real.pi*frequencyRadius k)]) hs
    _ = (1 + (2*Real.pi*frequencyRadius k)^2)^m := Real.rpow_natCast _ _
    _ ≤ ((1+2*Real.pi*frequencyRadius k)^2)^m :=
      pow_le_pow_left₀ (by positivity) h1 m
    _ ≤ (((1+2*Real.pi)*(1+frequencyRadius k))^2)^m := by
      gcongr
    _ = _ := by simp only [radialWeight, ← pow_mul, mul_pow]

theorem realValue_fourier {d : ℕ} (u : TorusL2 d) (hu : RealPotential u) (k : Frequency d) :
    HighDim.fourierCoeff (realValue u) k = fourierIsometry d u k := by
  rw [← HighDim.Bridge.potentialLp_fourier (realValue u) (realValue_memLp u),
    potentialLp_realValue u hu]

theorem coefficient_norm_le {d : ℕ} (u : TorusL2 d) (k : Frequency d) :
    ‖fourierIsometry d u k‖ ≤ ‖u‖ := by
  simpa only [(fourierIsometry d).norm_map] using
    lp.norm_apply_le_norm (by norm_num : (2:ℝ≥0∞) ≠ 0) (fourierIsometry d u) k

theorem physical_term_le_radial {d : ℕ} (u : TorusL2 d) (hu : RealPotential u)
    {s : ℝ} {m : ℕ} (hs : s ≤ (m:ℝ)) (k : Frequency d) :
    HighDim.sobolevTerm s (realValue u) k ≤
      ((1+2*Real.pi)^(2*m) * ‖u‖) * (radialWeight (2*m) k * ‖fourierIsometry d u k‖) := by
  unfold HighDim.sobolevTerm
  rw [realValue_fourier u hu]
  have hcoef := coefficient_norm_le u k
  calc
    _ ≤ ((1+2*Real.pi)^(2*m) * radialWeight (2*m) k) * ‖fourierIsometry d u k‖^2 :=
      mul_le_mul_of_nonneg_right (physical_weight_le_radial hs k) (sq_nonneg _)
    _ ≤ ((1+2*Real.pi)^(2*m) * radialWeight (2*m) k) * (‖u‖*‖fourierIsometry d u k‖) := by
      apply mul_le_mul_of_nonneg_left _ (by
        exact mul_nonneg (by positivity) ((radialWeight_isWeight (2*m)).nonneg k))
      nlinarith [norm_nonneg (fourierIsometry d u k)]
    _ = _ := by ring

theorem realValue_mem_sobolev {d : ℕ} (u : TorusL2 d) (hu : RealPotential u)
    {s : ℝ} {m : ℕ} (hs : s ≤ (m:ℝ))
    (hRad : RadialSummable (fourierIsometry d u) (2*m)) : HighDim.InSobolev s (realValue u) := by
  refine ⟨realValue_memLp u, ?_⟩
  apply (hRad.mul_left ((1+2*Real.pi)^(2*m)*‖u‖)).of_nonneg_of_le
  · intro k
    unfold HighDim.sobolevTerm
    positivity
  · exact physical_term_le_radial u hu hs

theorem sobolev_sum_le_radial {d : ℕ} (u : TorusL2 d) (hu : RealPotential u)
    {s : ℝ} {m : ℕ} (hs : s ≤ (m:ℝ))
    (hRad : RadialSummable (fourierIsometry d u) (2*m)) :
    (∑' k, HighDim.sobolevTerm s (realValue u) k) ≤
      ((1+2*Real.pi)^(2*m)*‖u‖) * radialSize (2*m) (fourierIsometry d u) := by
  rw [radialSize, ← tsum_mul_left]
  exact Summable.tsum_le_tsum (physical_term_le_radial u hu hs)
    (realValue_mem_sobolev u hu hs hRad).2 (hRad.mul_left _)

/-- Every fixed physical Sobolev norm of the actual real potential tends to
zero. Sobolev membership is established eventually, rather than assuming that
the totalized norm already represents a convergent Fourier series. -/
theorem maximizers_sobolev_tendsto_zero {d : ℕ} (hd : 12 ≤ d)
    (hEndpoint : EndpointRigidity.CoefficientEndpoint d (1/2))
    (hRigidity : OnsetCompactness.DensityRigidity d)
    {A : ℕ → ℝ} (hA : Tendsto A atTop (𝓝 (1/2)))
    (u : ℕ → TorusL2 d) (hu : ∀ n, Admissible (u n))
    (hmax : ∀ n (v : TorusL2 d), Admissible v → functional (A n) v ≤ functional (A n) (u n))
    (s : ℝ) :
    (∀ᶠ n in atTop, HighDim.InSobolev s (realValue (u n))) ∧
      Tendsto (fun n => HighDim.sobolevNorm s (realValue (u n))) atTop (𝓝 0) := by
  have hd0 : 0 < d := by omega
  obtain ⟨b, Ab, hb, hR, hgap⟩ := OnsetCompactness.exists_rough_gap hd
  obtain ⟨B, hB, hbound⟩ := OnsetCompactness.eventual_energy_bound hR hgap hA u hu hmax
  obtain ⟨m, hm⟩ := exists_nat_ge s
  obtain ⟨M, hM, hUniform⟩ := exists_uniform_radialSize_bound hd0 hb hR hB (2*m)
  have hAevent : ∀ᶠ n in atTop, (1/4:ℝ) ≤ A n :=
    (hA.eventually (lt_mem_nhds (by norm_num : (1/4:ℝ)<1/2))).mono (fun _ hn => hn.le)
  have hRad : ∀ᶠ n in atTop, RadialSummable (fourierIsometry d (u n)) (2*m) := by
    filter_upwards [hAevent] with n hn
    exact maximizer_radialSummable hd0 hR (by linarith : 0 < A n) (hu n) (hmax n) (2*m)
  refine ⟨hRad.mono (fun n hn => realValue_mem_sobolev (u n) (hu n).1 hm hn), ?_⟩
  have hnorm : Tendsto (fun n => ‖u n‖) atTop (𝓝 0) := by
    simpa using (OnsetCompactness.maximizers_tendsto_zero hd hEndpoint hRigidity hA u hu hmax).norm
  have hsum : Tendsto (fun n => ∑' k, HighDim.sobolevTerm s (realValue (u n)) k)
      atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun n => tsum_nonneg (fun k => by
      unfold HighDim.sobolevTerm
      positivity)))
      (g := fun n => ((1+2*Real.pi)^(2*m)*‖u n‖)*M)
    · filter_upwards [hRad, hAevent, hbound] with n hn hAn hbn
      exact (sobolev_sum_le_radial (u n) (hu n).1 hm hn).trans
        (mul_le_mul_of_nonneg_left (hUniform (A n) (u n) hAn hbn (hmax n)) (by positivity))
    · simpa using (hnorm.const_mul ((1+2*Real.pi)^(2*m))).mul_const M
  simpa only [HighDim.sobolevNorm, Real.sqrt_zero] using hsum.sqrt

#print axioms maximizers_sobolev_tendsto_zero
end BecknerOnofri.OnsetSobolev
