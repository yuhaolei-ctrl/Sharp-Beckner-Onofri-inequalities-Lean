import BecknerOnofri.SubcriticalOptimizerConvergence

/-! The same compact sequence of actual optimizers converges to zero in
every fixed physical Sobolev norm whenever its L2 limit is zero. This
includes the H11 convergence used in the dimension-eleven contradiction. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped Topology
namespace BecknerOnofri.SubcriticalOptimizerConvergence
open Legacy.TorusEndpoint Legacy.BecknerOnofri
open TorusSobolev SubcriticalAttainment SubcriticalEuler RadialWiener
open OnsetWienerBounds OnsetSobolev HighDim.RawAttainment

lemma sobolev_tendsto_zero {d : ℕ} (hd : 0 < d) {b Ab B : ℝ}
    (hb : 0 < b) (hR : RoughExponentialBound d b Ab) (hB : 0 ≤ B)
    (A : ℕ → ℝ) (u : ℕ → TorusL2 d)
    (hu : ∀ n, Admissible (u n))
    (hmax : ∀ n (v : TorusL2 d), Admissible v → functional (A n) v ≤ functional (A n) (u n))
    (hA : ∀ᶠ n in atTop, (1/4:ℝ) ≤ A n)
    (hbound : ∀ᶠ n in atTop, u n ∈ realSobolevBall d B)
    (hlim : Tendsto u atTop (𝓝 0)) (s : ℝ) :
    (∀ᶠ n in atTop, HighDim.InSobolev s (realValue (u n))) ∧
      Tendsto (fun n => HighDim.sobolevNorm s (realValue (u n))) atTop (𝓝 0) := by
  obtain ⟨m, hm⟩ := exists_nat_ge s
  obtain ⟨M, hM, hUniform⟩ := exists_uniform_radialSize_bound hd hb hR hB (2*m)
  have hRad : ∀ᶠ n in atTop, RadialSummable (fourierIsometry d (u n)) (2*m) := by
    filter_upwards [hA] with n hn
    exact maximizer_radialSummable hd hR (by linarith : 0 < A n) (hu n) (hmax n) (2*m)
  refine ⟨hRad.mono (fun n hn => realValue_mem_sobolev (u n) (hu n).1 hm hn), ?_⟩
  have hnorm : Tendsto (fun n => ‖u n‖) atTop (𝓝 0) := by simpa using hlim.norm
  have hsum : Tendsto (fun n => ∑' k, HighDim.sobolevTerm s (realValue (u n)) k)
      atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun n => tsum_nonneg (fun k => by
      unfold HighDim.sobolevTerm
      positivity)))
      (g := fun n => ((1+2*Real.pi)^(2*m)*‖u n‖)*M)
    · filter_upwards [hRad, hA, hbound] with n hn hAn hbn
      exact (sobolev_sum_le_radial (u n) (hu n).1 hm hn).trans
        (mul_le_mul_of_nonneg_left (hUniform (A n) (u n) hAn hbn (hmax n)) (by positivity))
    · simpa using (hnorm.const_mul ((1+2*Real.pi)^(2*m))).mul_const M
  simpa only [HighDim.sobolevNorm, Real.sqrt_zero] using hsum.sqrt

#print axioms sobolev_tendsto_zero
end BecknerOnofri.SubcriticalOptimizerConvergence
