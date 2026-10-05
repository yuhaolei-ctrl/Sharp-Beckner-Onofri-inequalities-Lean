import BecknerOnofri.LocalElevenCore.WienerAlgebraBounds

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace BecknerOnofri.HighDim.LocalEleven.WeightedQuadraticDifference
open ContinuousGibbs ContinuousFirstShell GraphRegularity GraphWienerBounds WienerAlgebraBounds
open BecknerOnofri.OnsetWienerBounds

lemma quadratic_difference {d : ℕ} (v w : Space d) (hv : mean d v=0) (hw : mean d w=0) :
    quadraticTerm (v+w)-quadraticTerm v=
      (1/2:ℝ) • center d ((2:ℝ) • (v*w)+w^2) := by
  have hm : mean d (v+w)=0 := by rw [map_add,hv,hw,add_zero]
  rw [quadraticTerm_of_mean_zero hm,quadraticTerm_of_mean_zero hv,← smul_sub,← map_sub]
  congr 2
  ext x
  simp only [ContinuousMap.add_apply,ContinuousMap.sub_apply,ContinuousMap.pow_apply,
    ContinuousMap.smul_apply,ContinuousMap.mul_apply,smul_eq_mul]
  ring

lemma difference_radial {d : ℕ} (m : ℕ) (v w : Space d)
    (hv : Radial m v) (hw : Radial m w) (hmv : mean d v=0) (hmw : mean d w=0) :
    Radial m (quadraticTerm (v+w)-quadraticTerm v) := by
  rw [quadratic_difference v w hmv hmw]
  apply radial_smul
  apply radial_center
  exact radial_add m _ _ (radial_smul m 2 _ (radial_mul m v w hv hw))
    (by simpa only [pow_two] using radial_mul m w w hw hw)

lemma difference_bound {d : ℕ} (m : ℕ) (v w : Space d)
    (hv : Radial m v) (hw : Radial m w) (hmv : mean d v=0) (hmw : mean d w=0) :
    wienerSize m (quadraticTerm (v+w)-quadraticTerm v)≤
      2*wienerSize m v*wienerSize m w+(wienerSize m w)^2 := by
  have hp := wienerSize_mul_le m v w hv hw
  have hw2 : Radial m (w^2) := by simpa only [pow_two] using radial_mul m w w hw hw
  have hp2 : wienerSize m (w^2)≤(wienerSize m w)^2 := by
    simpa only [pow_two] using wienerSize_mul_le m w w hw hw
  have hsum := wienerSize_add_le m ((2:ℝ) • (v*w)) (w^2)
    (radial_smul m 2 _ (radial_mul m v w hv hw)) hw2
  have hcenter := wienerSize_center_le m ((2:ℝ) • (v*w)+w^2)
    (radial_add m _ _ (radial_smul m 2 _ (radial_mul m v w hv hw)) hw2)
  rw [quadratic_difference v w hmv hmw,wienerSize_smul]
  rw [wienerSize_smul] at hsum
  rw [show ‖(2:ℝ)‖=2 by norm_num] at hsum
  rw [show ‖(1/2:ℝ)‖=(1/2:ℝ) by norm_num]
  nlinarith

#print axioms difference_bound
end BecknerOnofri.HighDim.LocalEleven.WeightedQuadraticDifference
