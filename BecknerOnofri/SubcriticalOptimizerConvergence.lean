module

public import BecknerOnofri.OnsetWienerConvergence
public import BecknerOnofri.ContinuousOptimizers

@[expose] public section

/-! For genuine optimizers in a common critical-energy ball, L2 convergence
to zero upgrades to the Wiener norm and hence to uniform convergence. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped BigOperators Topology
namespace BecknerOnofri.SubcriticalOptimizerConvergence
open Legacy.TorusEndpoint Legacy.BecknerOnofri
open TorusSobolev SubcriticalAttainment SubcriticalEuler RadialWiener GreenMultiplierSummability
open OnsetWienerBounds

lemma wiener_tendsto_zero {d : ℕ} (hd : 0 < d) {b Ab B : ℝ}
    (hb : 0 < b) (hR : RoughExponentialBound d b Ab) (hB : 0 ≤ B)
    (A : ℕ → ℝ) (u : ℕ → TorusL2 d)
    (hu : ∀ n, Admissible (u n))
    (hmax : ∀ n (v : TorusL2 d), Admissible v → functional (A n) v ≤ functional (A n) (u n))
    (hA : ∀ᶠ n in atTop, (1/4:ℝ) ≤ A n)
    (hbound : ∀ᶠ n in atTop, u n ∈ realSobolevBall d B)
    (hlim : Tendsto u atTop (𝓝 0)) :
    Tendsto (fun n => radialSize 0 (fourierIsometry d (u n))) atTop (𝓝 0) := by
  obtain ⟨M,hM,hUniform⟩ := exists_uniform_radialSize_bound hd hb hR hB (2*d)
  have hnorm : Tendsto (fun n => ‖u n‖) atTop (𝓝 0) := by simpa using hlim.norm
  have hpt (k : Frequency d) : Tendsto (fun n => ‖fourierIsometry d (u n) k‖) atTop (𝓝 0) :=
    squeeze_zero (fun _ => norm_nonneg _) (fun n => OnsetSobolev.coefficient_norm_le (u n) k) hnorm
  have hdom : ∀ᶠ n in atTop, ∀ k : Frequency d,
      ‖‖fourierIsometry d (u n) k‖‖ ≤ (M*(endpointSigma d)^2)*greenMultiplier d k^2 := by
    filter_upwards [hA,hbound] with n hn hbn
    intro k
    rw [norm_norm]
    exact coefficient_green_majorant hd (hu n).2.1
      (maximizer_radialSummable hd hR (by linarith : 0 < A n) (hu n) (hmax n) (2*d))
      (hUniform (A n) (u n) hn hbn (hmax n)) k
  have hs := tendsto_tsum_of_dominated_convergence
    ((summable_greenMultiplier_sq d).mul_left (M*(endpointSigma d)^2)) hpt hdom
  simpa only [radialSize,radialWeight,pow_zero,one_mul,tsum_zero] using hs

lemma continuous_tendsto_zero {d : ℕ} (hd : 0 < d) {b Ab B : ℝ}
    (hb : 0 < b) (hR : RoughExponentialBound d b Ab) (hB : 0 ≤ B)
    (A : ℕ → ℝ) (u : ℕ → HighDim.ContinuousGibbs.Space d)
    (hu : ∀ n, Admissible (HighDim.ContinuousFirstShell.toL2 d (u n)))
    (hmax : ∀ n (v : TorusL2 d), Admissible v → functional (A n) v ≤
      functional (A n) (HighDim.ContinuousFirstShell.toL2 d (u n)))
    (hA : ∀ᶠ n in atTop, (1/4:ℝ) ≤ A n)
    (hbound : ∀ᶠ n in atTop, HighDim.ContinuousFirstShell.toL2 d (u n) ∈ realSobolevBall d B)
    (hlim : Tendsto (fun n => HighDim.ContinuousFirstShell.toL2 d (u n)) atTop (𝓝 0)) :
    Tendsto u atTop (𝓝 0) := by
  have hw := wiener_tendsto_zero hd hb hR hB A _ hu hmax hA hbound hlim
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun n => norm_nonneg (u n))) _ hw
  filter_upwards [hA] with n hn
  apply HighDim.OnsetContinuous.norm_le_wiener
  exact maximizer_fourier_summable hd hR (by linarith : 0 < A n) (hu n) (hmax n)

#print axioms continuous_tendsto_zero
end BecknerOnofri.SubcriticalOptimizerConvergence
