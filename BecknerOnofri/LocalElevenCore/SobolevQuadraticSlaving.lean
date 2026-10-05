import BecknerOnofri.LocalElevenCore.ComplementResolventSobolev

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter Asymptotics
open scoped Topology
namespace BecknerOnofri.HighDim.LocalEleven.QuadraticSlaving
open ContinuousGibbs ContinuousFirstShell ContinuousComplement QuadraticModes GraphSobolevBounds

theorem inverseGreen_sobolev_bound {d : ℕ} (hd : 11≤d) {s : ℝ} (hs : s≤d)
    (f : Space d) : sobolevNorm s (inverseGreen hd f).val≤
      (2*Real.sqrt (ellipticWeightConstant d)*‖complementMap d‖)*‖f‖ := by
  rw [inverseGreen_factor]
  have h := resolvent_sobolevNorm_bound hd hs (complementMap d f)
  have hh : ‖(complementMap d f).val‖≤‖complementMap d‖*‖f‖ :=
    (complementMap d).le_opNorm f
  calc
    _ ≤ (2*Real.sqrt (ellipticWeightConstant d))*‖(complementMap d f).val‖ := h
    _ ≤ (2*Real.sqrt (ellipticWeightConstant d))*(‖complementMap d‖*‖f‖) :=
      mul_le_mul_of_nonneg_left hh (by positivity)
    _ = _ := by ring

/-- The manuscript's quadratic slaving has an actual H^s cubic remainder
through one full elliptic order. Higher s and H^s-valued analyticity are separate. -/
theorem correction_quadratic_expansion_sobolev {d : ℕ} (hd : 11≤d) {s : ℝ} (hs : s≤d) :
    (fun z => sobolevNorm s ((sliceCorrection hd z-quadraticCorrection hd z).val : Space d))
      =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖^3) := by
  have hb : (fun z => sobolevNorm s ((sliceCorrection hd z-quadraticCorrection hd z).val : Space d))
      =O[𝓝 (0 : Coordinates d)]
        (fun z => nonlinearRemainder (slicePotential hd z)-quadraticTerm (assembly d z)) := by
    apply IsBigO.of_bound (2*Real.sqrt (ellipticWeightConstant d)*‖complementMap d‖)
    filter_upwards [sliceCorrection_inverse hd] with z hz
    rw [Real.norm_of_nonneg (show 0≤sobolevNorm s ((sliceCorrection hd z-quadraticCorrection hd z).val : Space d) from Real.sqrt_nonneg _)]
    have he : sliceCorrection hd z-quadraticCorrection hd z =
        inverseGreen hd (nonlinearRemainder (slicePotential hd z)-quadraticTerm (assembly d z)) := by
      rw [map_sub,hz,quadraticCorrection]
    rw [he]
    exact inverseGreen_sobolev_bound hd hs _
  exact hb.trans (nonlinear_error_cubic hd)

#print axioms correction_quadratic_expansion_sobolev
end BecknerOnofri.HighDim.LocalEleven.QuadraticSlaving
