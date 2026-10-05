import BecknerOnofri.LocalElevenCore.SobolevDensitySlaving

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter Asymptotics
open scoped Topology
namespace BecknerOnofri.HighDim.LocalEleven.QuadraticSlaving
open ContinuousGibbs ContinuousFirstShell

lemma quadraticCorrection_smul {d : ℕ} (hd : 11≤d) (t : ℝ) (z : Coordinates d) :
    quadraticCorrection hd (t • z)=t^2 • quadraticCorrection hd z := by
  have hs : (assembly d (t • z))^2=t^2 • (assembly d z)^2 := by
    ext x
    simp only [map_smul,ContinuousMap.pow_apply,ContinuousMap.smul_apply,smul_eq_mul,mul_pow]
  unfold quadraticCorrection
  rw [quadraticTerm_of_mean_zero (mean_assembly (t • z)),
    quadraticTerm_of_mean_zero (mean_assembly z),hs]
  simp only [map_smul]
  rw [smul_comm (1/2:ℝ) (t^2)]

private lemma norm_smul_cubic {d : ℕ} (z : Coordinates d) :
    (fun t : ℝ => ‖t • z‖^3) =O[𝓝 (0:ℝ)] (fun t => ‖t‖^3) := by
  apply IsBigO.of_bound (‖z‖^3)
  exact Eventually.of_forall (fun t => by
    simp only [norm_mul,norm_pow,norm_norm,norm_smul,mul_pow]
    exact le_of_eq (mul_comm _ _))

/-- The literal fixed-direction Taylor expansion from the manuscript. -/
theorem correction_directional_sobolev {d : ℕ} (hd : 11≤d) (s : ℝ) (z : Coordinates d) :
    (fun t : ℝ => sobolevNorm s
      ((sliceCorrection hd (t • z)-t^2 • quadraticCorrection hd z).val : Space d))
      =O[𝓝 (0:ℝ)] (fun t => ‖t‖^3) := by
  have ht : Tendsto (fun t : ℝ => t • z) (𝓝 0) (𝓝 (0 : Coordinates d)) := by
    simpa only [zero_smul] using (show Continuous (fun t : ℝ => t • z) from continuous_id.smul continuous_const).tendsto (0:ℝ)
  simpa only [Function.comp_def,quadraticCorrection_smul] using
    ((correction_quadratic_expansion_all_sobolev hd s).comp_tendsto ht).trans (norm_smul_cubic z)

#print axioms quadraticCorrection_smul
#print axioms correction_directional_sobolev
end BecknerOnofri.HighDim.LocalEleven.QuadraticSlaving
