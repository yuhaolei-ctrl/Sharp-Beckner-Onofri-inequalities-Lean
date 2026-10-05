import BecknerOnofri.LocalElevenCore.WeightedGibbsCubicRemainder
import BecknerOnofri.LocalElevenCore.WeightedQuadraticDifference
import BecknerOnofri.LocalElevenCore.InverseGreenWiener
import BecknerOnofri.LocalElevenCore.GraphAllSobolevBounds

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter Asymptotics
open scoped Topology
namespace BecknerOnofri.HighDim.LocalEleven.QuadraticSlaving
open ContinuousGibbs ContinuousFirstShell ContinuousComplement GreenLocalBranch ReducedEquation
open GraphRegularity GraphWienerBounds WienerAlgebraBounds
open BecknerOnofri.OnsetWienerBounds

private lemma slice_tendsto' (d : ℕ) :
    Tendsto (fun z : Coordinates d => ((1:ℝ),z)) (𝓝 0) (𝓝 (1,0)) :=
  (continuous_const.prodMk continuous_id).continuousAt

lemma slice_radial {d : ℕ} (hd : 11≤d) (m : ℕ) :
    ∀ᶠ z in 𝓝 (0 : Coordinates d),
      Radial m (slicePotential hd z) ∧ Radial m (sliceCorrection hd z : Space d) := by
  filter_upwards [(slice_tendsto' d).eventually (correction_solves hd)] with z hz
  exact ⟨reconstruction_radial (by omega) 1 z (correction hd (1,z)) hz m,
    correction_radial (by omega) 1 z (correction hd (1,z)) hz m⟩

lemma slice_potential_wiener_linear {d : ℕ} (hd : 11≤d) (m : ℕ) :
    (fun z => wienerSize m (slicePotential hd z)) =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖) :=
  (potential_wiener_linear hd m).comp_tendsto (slice_tendsto' d)

lemma slice_correction_wiener_quadratic {d : ℕ} (hd : 11≤d) (m : ℕ) :
    (fun z => wienerSize m (sliceCorrection hd z : Space d))
      =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖^2) :=
  (correction_wiener_quadratic hd m).comp_tendsto (slice_tendsto' d)

lemma gibbs_remainder_wiener_cubic {d : ℕ} (hd : 11≤d) (m : ℕ) :
    (fun z => wienerSize m (nonlinearRemainder (slicePotential hd z)-quadraticTerm (slicePotential hd z)))
      =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖^3) := by
  have hu := slice_potential_wiener_linear hd m
  have ht : Tendsto (fun z : Coordinates d => ‖z‖) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_id.continuousAt (x := (0 : Coordinates d))).norm.tendsto
  have hsmall := (hu.trans_tendsto ht).eventually_le_const (by norm_num : (0:ℝ)<1)
  have hb : (fun z => wienerSize m (nonlinearRemainder (slicePotential hd z)-quadraticTerm (slicePotential hd z)))
      =O[𝓝 (0 : Coordinates d)] (fun z => (wienerSize m (slicePotential hd z))^3) := by
    apply IsBigO.of_bound 4
    filter_upwards [slice_radial hd m,hsmall] with z hz hs
    rw [Real.norm_of_nonneg (radialSize_nonneg _ _), Real.norm_of_nonneg (pow_nonneg (radialSize_nonneg _ _) _)]
    exact WeightedGibbsCubicRemainder.cubic_bound m _ hz.1 (mean_slicePotential hd z) hs
  exact hb.trans (hu.pow 3)

lemma quadratic_difference_wiener_cubic {d : ℕ} (hd : 11≤d) (m : ℕ) :
    (fun z => wienerSize m (quadraticTerm (slicePotential hd z)-quadraticTerm (assembly d z)))
      =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖^3) := by
  have hv : (fun z => wienerSize m (assembly d z)) =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖) := by
    apply IsBigO.of_bound (2^(m+1)*d)
    exact Eventually.of_forall (fun z => by
      simpa only [Real.norm_of_nonneg (radialSize_nonneg _ _),norm_norm] using wienerSize_assembly_le m z)
  have hw := slice_correction_wiener_quadratic hd m
  have hw1 := hw.trans pow_down
  have hp : (fun z => wienerSize m (assembly d z)*wienerSize m (sliceCorrection hd z : Space d))
      =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖^3) := by
    simpa only [← pow_succ'] using hv.mul hw
  have hq : (fun z => (wienerSize m (sliceCorrection hd z : Space d))^2)
      =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖^3) := by
    convert! hw.mul hw1 using 1 <;> (ext z; simp [pow_succ])
  have hb : (fun z => wienerSize m (quadraticTerm (slicePotential hd z)-quadraticTerm (assembly d z)))
      =O[𝓝 (0 : Coordinates d)] (fun z =>
        2*(wienerSize m (assembly d z)*wienerSize m (sliceCorrection hd z : Space d))+
        (wienerSize m (sliceCorrection hd z : Space d))^2) := by
    apply IsBigO.of_bound 1
    filter_upwards [slice_radial hd m] with z hz
    have hv0 : 0≤wienerSize m (assembly d z) := radialSize_nonneg _ _
    have hw0 : 0≤wienerSize m (sliceCorrection hd z : Space d) := radialSize_nonneg _ _
    rw [Real.norm_of_nonneg (radialSize_nonneg _ _),Real.norm_of_nonneg
      (by positivity : 0≤2*(wienerSize m (assembly d z)*wienerSize m (sliceCorrection hd z : Space d))+
        (wienerSize m (sliceCorrection hd z : Space d))^2),one_mul]
    simpa only [mul_assoc,slicePotential,ReducedEquation.potential,reconstruction_apply,
      sliceCorrection,wienerSize] using WeightedQuadraticDifference.difference_bound m
      (assembly d z) (sliceCorrection hd z : Space d) (radial_assembly m z) hz.2
      (mean_assembly z) ((mem_complement_iff _).mp (sliceCorrection hd z).property).1
  exact hb.trans ((hp.const_mul_left 2).add hq)

lemma nonlinear_error_radial {d : ℕ} (hd : 11≤d) (m : ℕ) :
    ∀ᶠ z in 𝓝 (0 : Coordinates d),
      Radial m (nonlinearRemainder (slicePotential hd z)-quadraticTerm (assembly d z)) := by
  filter_upwards [slice_radial hd m] with z hz
  exact radial_sub m _ _ (WeightedExponentialRemainder.nonlinear_radial m _ hz.1)
    (WeightedGibbsCubicRemainder.radial_quadratic m _ (radial_assembly m z) (mean_assembly z))

lemma nonlinear_error_wiener_cubic {d : ℕ} (hd : 11≤d) (m : ℕ) :
    (fun z => wienerSize m (nonlinearRemainder (slicePotential hd z)-quadraticTerm (assembly d z)))
      =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖^3) := by
  have hb : (fun z => wienerSize m (nonlinearRemainder (slicePotential hd z)-quadraticTerm (assembly d z)))
      =O[𝓝 (0 : Coordinates d)] (fun z =>
        wienerSize m (nonlinearRemainder (slicePotential hd z)-quadraticTerm (slicePotential hd z))+
        wienerSize m (quadraticTerm (slicePotential hd z)-quadraticTerm (assembly d z))) := by
    apply IsBigO.of_bound 1
    filter_upwards [slice_radial hd m] with z hz
    rw [Real.norm_of_nonneg (radialSize_nonneg _ _),Real.norm_of_nonneg
      (add_nonneg (radialSize_nonneg _ _) (radialSize_nonneg _ _)),one_mul]
    have hQ := WeightedGibbsCubicRemainder.radial_quadratic m _ hz.1 (mean_slicePotential hd z)
    have hv := WeightedGibbsCubicRemainder.radial_quadratic m _ (radial_assembly m z) (mean_assembly z)
    simpa only [sub_add_sub_cancel] using wienerSize_add_le m
      (nonlinearRemainder (slicePotential hd z)-quadraticTerm (slicePotential hd z))
      (quadraticTerm (slicePotential hd z)-quadraticTerm (assembly d z))
      (radial_sub m _ _ (WeightedExponentialRemainder.nonlinear_radial m _ hz.1) hQ)
      (radial_sub m _ _ hQ hv)
  exact hb.trans ((gibbs_remainder_wiener_cubic hd m).add (quadratic_difference_wiener_cubic hd m))

lemma slaving_error_identity {d : ℕ} (hd : 11≤d) :
    ∀ᶠ z in 𝓝 (0 : Coordinates d), sliceCorrection hd z-quadraticCorrection hd z =
      inverseGreen hd (nonlinearRemainder (slicePotential hd z)-quadraticTerm (assembly d z)) := by
  filter_upwards [sliceCorrection_inverse hd] with z hz
  rw [map_sub,hz,quadraticCorrection]

/-- The manuscript's quadratic complementary term has a cubic remainder in
 every fixed physical Sobolev norm, without a regularity assumption on the graph. -/
theorem correction_quadratic_expansion_all_sobolev {d : ℕ} (hd : 11≤d) (s : ℝ) :
    (fun z => sobolevNorm s ((sliceCorrection hd z-quadraticCorrection hd z).val : Space d))
      =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖^3) := by
  obtain ⟨m, hm⟩ := exists_nat_ge s
  have hb : (fun z => sobolevNorm s ((sliceCorrection hd z-quadraticCorrection hd z).val : Space d))
      =O[𝓝 (0 : Coordinates d)] (fun z =>
        wienerSize m (nonlinearRemainder (slicePotential hd z)-quadraticTerm (assembly d z))) := by
    apply IsBigO.of_bound ((1+2*Real.pi)^m)
    filter_upwards [slaving_error_identity hd, nonlinear_error_radial hd m] with z hz hr
    rw [Real.norm_of_nonneg (show 0≤sobolevNorm s ((sliceCorrection hd z-quadraticCorrection hd z).val : Space d) from Real.sqrt_nonneg _),
      Real.norm_of_nonneg (radialSize_nonneg _ _),hz]
    exact (GraphAllSobolevBounds.sobolevNorm_le_wiener hm _ (inverseGreen_radial hd m _ hr)).trans
      (mul_le_mul_of_nonneg_left (inverseGreen_wienerSize_le hd m _ hr) (by positivity))
  exact hb.trans (nonlinear_error_wiener_cubic hd m)

#print axioms correction_quadratic_expansion_all_sobolev
end BecknerOnofri.HighDim.LocalEleven.QuadraticSlaving
