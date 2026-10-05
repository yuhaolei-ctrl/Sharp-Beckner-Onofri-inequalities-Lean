import BecknerOnofri.LocalElevenCore.ReducedEnergyJointExpansion

/-! The joint remainder in the manuscript's exact variables:
δ=1−1/μ and S=Σ|zᵢ|². -/
noncomputable section
open Filter Asymptotics
open scoped Topology BigOperators
namespace BecknerOnofri.HighDim.LocalEleven.UniformComplementBounds
open ContinuousFirstShell ReducedEnergyGradient ReducedQuarticExpansion

def squaredAmplitude {d : ℕ} (z : Coordinates d) : ℝ := ∑ i,‖z i‖^2

theorem squaredAmplitude_nonneg {d : ℕ} (z : Coordinates d) : 0 ≤ squaredAmplitude z :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem norm_sq_le_squaredAmplitude {d : ℕ} (z : Coordinates d) :
    ‖z‖^2 ≤ squaredAmplitude z := by
  have hs := squaredAmplitude_nonneg z
  have hn : ‖z‖ ≤ Real.sqrt (squaredAmplitude z) := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
    intro i
    exact Real.le_sqrt_of_sq_le
      (Finset.single_le_sum (fun j _ => sq_nonneg ‖z j‖) (Finset.mem_univ i))
  nlinarith [Real.sq_sqrt hs,Real.sqrt_nonneg (squaredAmplitude z),norm_nonneg z]

theorem parameter_delta_bound :
    ∀ᶠ μ : ℝ in 𝓝 1, |μ-1| ≤ 2*|1-1/μ| := by
  filter_upwards [Icc_mem_nhds (by norm_num : (1/2:ℝ)<1)
    (by norm_num : (1:ℝ)<2)] with μ hμ
  have hp : 0 < μ := by linarith [hμ.1]
  have he : μ-1 = μ*(1-1/μ) := by field_simp [hp.ne']
  rw [he,abs_mul,abs_of_pos hp]
  exact mul_le_mul_of_nonneg_right hμ.2 (abs_nonneg _)

theorem joint_remainder_paper_bound (d : ℕ) :
    (fun x : ℝ × Coordinates d => ‖x.2‖^6+|x.1-1| *‖x.2‖^4)
      =O[𝓝 (1,0)] (fun x => (squaredAmplitude x.2)^3+
        |1-1/x.1| *(squaredAmplitude x.2)^2) := by
  apply IsBigO.of_bound 2
  have ht : Tendsto (Prod.fst : ℝ × Coordinates d → ℝ) (𝓝 (1,0)) (𝓝 1) :=
    continuous_fst.continuousAt
  filter_upwards [ht.eventually parameter_delta_bound] with x hx
  have hS := squaredAmplitude_nonneg x.2
  have hnorm := norm_sq_le_squaredAmplitude x.2
  have h4 : ‖x.2‖^4 ≤ (squaredAmplitude x.2)^2 := by
    simpa only [← pow_mul] using pow_le_pow_left₀ (sq_nonneg ‖x.2‖) hnorm 2
  have h6 : ‖x.2‖^6 ≤ (squaredAmplitude x.2)^3 := by
    simpa only [← pow_mul] using pow_le_pow_left₀ (sq_nonneg ‖x.2‖) hnorm 3
  rw [Real.norm_of_nonneg (by positivity),Real.norm_of_nonneg (by positivity)]
  have hm := mul_le_mul hx h4 (by positivity) (by positivity : 0 ≤ 2*|1-1/x.1|)
  nlinarith [pow_nonneg hS 3]

/-- The exact two-parameter remainder from the September 21 manuscript,
now including d=11, for the actual physical dual energy on the solved graph. -/
theorem physicalReducedEnergy_quartic_paper {d : ℕ} (hd : 11 ≤ d) :
    (fun x : ℝ × Coordinates d => physicalReducedEnergy hd x -
      (1-1/x.1)*squaredAmplitude x.2 - quarticValue x.2)
      =O[𝓝 (1,0)] (fun x => (squaredAmplitude x.2)^3+
        |1-1/x.1| *(squaredAmplitude x.2)^2) :=
  (physicalReducedEnergy_joint_quartic hd).trans (joint_remainder_paper_bound d)

#print axioms physicalReducedEnergy_quartic_paper
end BecknerOnofri.HighDim.LocalEleven.UniformComplementBounds
