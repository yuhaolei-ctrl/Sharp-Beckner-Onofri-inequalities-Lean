module

public import BecknerOnofri.OnsetSobolev

@[expose] public section

/-! Actual optimizer convergence in the unweighted Wiener norm, retaining
the exact endpoint and rigidity premises. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology
namespace BecknerOnofri.OnsetWienerBounds
open Legacy.TorusEndpoint Legacy.BecknerOnofri
open TorusSobolev SubcriticalAttainment SubcriticalEuler RadialWiener GreenMultiplierSummability

theorem coefficient_green_majorant {d : ℕ} (hd : 0 < d) {a : Frequency d → ℂ}
    (ha0 : a 0 = 0) (ha : RadialSummable a (2*d)) {M : ℝ}
    (hM : radialSize (2*d) a ≤ M) (k : Frequency d) :
    ‖a k‖ ≤ (M*(endpointSigma d)^2)*greenMultiplier d k^2 := by
  by_cases hk : k = 0
  · simp [hk,ha0,greenMultiplier]
  · have hr := frequencyRadius_pos hk
    have hσ := endpointSigma_pos hd
    have hs : radialWeight (2*d) k*‖a k‖ ≤ M :=
      (ha.le_tsum k (fun j _ => mul_nonneg ((radialWeight_isWeight _).nonneg j) (norm_nonneg _))).trans hM
    have hp : frequencyRadius k^(2*d)*‖a k‖ ≤ M := by
      apply le_trans _ hs
      unfold radialWeight
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ hr.le (by linarith) (2*d)) (norm_nonneg _)
    have he : (M*(endpointSigma d)^2)*greenMultiplier d k^2 = M/frequencyRadius k^(2*d) := by
      rw [greenMultiplier_of_ne_zero hk]
      rw [show 2*d=d*2 by omega, pow_mul]
      field_simp
    rw [he]
    exact (le_div_iff₀ (pow_pos hr _)).mpr (by simpa only [mul_comm] using hp)

theorem maximizers_wiener_tendsto_zero {d : ℕ} (hd : 12 ≤ d)
    (hEndpoint : EndpointRigidity.CoefficientEndpoint d (1/2))
    (hRigidity : OnsetCompactness.DensityRigidity d)
    {A : ℕ → ℝ} (hA : Tendsto A atTop (𝓝 (1/2)))
    (u : ℕ → TorusL2 d) (hu : ∀ n, Admissible (u n))
    (hmax : ∀ n (v : TorusL2 d), Admissible v → functional (A n) v ≤ functional (A n) (u n)) :
    Tendsto (fun n => radialSize 0 (fourierIsometry d (u n))) atTop (𝓝 0) := by
  have hd0 : 0 < d := by omega
  obtain ⟨b,Ab,hb,hR,hgap⟩ := OnsetCompactness.exists_rough_gap hd
  obtain ⟨B,hB,hbound⟩ := OnsetCompactness.eventual_energy_bound hR hgap hA u hu hmax
  obtain ⟨M,hM,hUniform⟩ := exists_uniform_radialSize_bound hd0 hb hR hB (2*d)
  have hAevent : ∀ᶠ n in atTop, (1/4:ℝ) ≤ A n :=
    (hA.eventually (lt_mem_nhds (by norm_num : (1/4:ℝ)<1/2))).mono (fun _ hn => hn.le)
  have hnorm : Tendsto (fun n => ‖u n‖) atTop (𝓝 0) := by
    simpa using (OnsetCompactness.maximizers_tendsto_zero hd hEndpoint hRigidity hA u hu hmax).norm
  have hpt (k : Frequency d) : Tendsto (fun n => ‖fourierIsometry d (u n) k‖) atTop (𝓝 0) :=
    squeeze_zero (fun _ => norm_nonneg _) (fun n => OnsetSobolev.coefficient_norm_le (u n) k) hnorm
  have hdom : ∀ᶠ n in atTop, ∀ k : Frequency d,
      ‖‖fourierIsometry d (u n) k‖‖ ≤ (M*(endpointSigma d)^2)*greenMultiplier d k^2 := by
    filter_upwards [hAevent,hbound] with n hn hbn
    intro k
    rw [norm_norm]
    exact coefficient_green_majorant hd0 (hu n).2.1
      (maximizer_radialSummable hd0 hR (by linarith : 0 < A n) (hu n) (hmax n) (2*d))
      (hUniform (A n) (u n) hn hbn (hmax n)) k
  have hs := tendsto_tsum_of_dominated_convergence
    ((summable_greenMultiplier_sq d).mul_left (M*(endpointSigma d)^2)) hpt hdom
  simpa only [radialSize,radialWeight,pow_zero,one_mul,tsum_zero] using hs

#print axioms maximizers_wiener_tendsto_zero
end BecknerOnofri.OnsetWienerBounds
