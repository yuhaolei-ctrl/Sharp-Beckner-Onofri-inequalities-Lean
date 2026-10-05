module

public import BecknerOnofri.UniformComplementBounds

@[expose] public section

/-! Uniform complementary Gibbs pairings along the actual two-parameter graph. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Filter Asymptotics
open scoped Topology
namespace BecknerOnofri.HighDim.UniformComplementBounds
open ContinuousGibbs ContinuousFirstShell ContinuousComplement GreenLocalBranch ReducedEquation SlavedMoments

/-- Orthogonality removes the constant and first-shell terms of the Gibbs density exactly. -/
theorem complement_normalized_pairing {d : ℕ} (hd : 12 ≤ d) (x : ℝ × Coordinates d) :
    mean d ((correction hd x : Space d) * normalized (potential hd x)) =
      mean d ((correction hd x : Space d)^2) +
      mean d ((correction hd x : Space d) * nonlinearRemainder (potential hd x)) := by
  have hm : mean d (potential hd x) = 0 := mean_reconstruction _
  have hc : center d (potential hd x) = potential hd x := by
    ext y
    simp only [center_apply, hm, sub_zero]
  have hN : normalized (potential hd x) = 1 + potential hd x + nonlinearRemainder (potential hd x) := by
    unfold nonlinearRemainder
    rw [hc]
    abel
  rw [hN, mul_add, mul_add, map_add, map_add, mul_one]
  have hw : mean d (correction hd x : Space d) = 0 := (correction hd x).property.1
  rw [hw, zero_add]
  congr 1
  change mean d ((correction hd x : Space d) *
    (assembly d x.2 + (correction hd x : Space d))) = _
  rw [mul_add, map_add, mean_mul_assembly, zero_add, pow_two]

/-- This is a joint bound in μ and z, with no pure-parameter error. -/
theorem complement_normalized_pairing_quartic {d : ℕ} (hd : 12 ≤ d) :
    (fun x => mean d ((correction hd x : Space d) * normalized (potential hd x)))
      =O[𝓝 (1,(0 : Coordinates d))] (fun x => ‖x.2‖^4) := by
  have hw := correction_coe_uniform_quadratic hd
  have hww := hw.pow 2
  simp only [← pow_mul, show 2*2=4 from rfl] at hww
  have hN := ((nonlinearRemainder_quadratic d).comp_tendsto (potential_tendsto hd)).trans
    ((potential_uniform_linear hd).norm_left.pow 2)
  have hWN : (fun x => (correction hd x : Space d) * nonlinearRemainder (potential hd x))
      =O[𝓝 (1,(0 : Coordinates d))] (fun x => ‖x.2‖^4) := by
    convert! hw.mul hN using 1 <;> (ext x; ring)
  apply ((((mean d).isBigO_comp _ _).trans hww).add
    (((mean d).isBigO_comp _ _).trans hWN)).congr_left
  intro x
  exact (complement_normalized_pairing hd x).symm

#print axioms complement_normalized_pairing_quartic
end BecknerOnofri.HighDim.UniformComplementBounds
