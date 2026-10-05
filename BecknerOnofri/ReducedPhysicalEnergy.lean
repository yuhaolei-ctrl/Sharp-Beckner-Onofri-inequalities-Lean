module

public import BecknerOnofri.GraphEnergy
public import BecknerOnofri.ReducedQuarticExpansion

@[expose] public section

/-! The quartic expansion is an expansion of the actual trusted physical
dual functional on the solved complementary graph. -/
noncomputable section
open Filter Asymptotics
open scoped Topology BigOperators
namespace BecknerOnofri.HighDim.ReducedPhysicalEnergy
open ContinuousGibbs ContinuousFirstShell ContinuousComplement GreenLocalBranch ReducedEquation
open QuadraticSlaving SlavedMoments ReducedQuarticExpansion GraphEnergy

/-- The actual trusted dual energy, restricted to the genuine implicit graph
at the critical physical parameter. -/
def criticalReducedEnergy {d : ℕ} (hd : 12 ≤ d) (z : Coordinates d) : ℝ :=
  (dualFunctional (spectralThreshold d) (U hd z)).toReal

theorem dualFunctional_graphExpression {d : ℕ} (hd : 12 ≤ d) :
    ∀ᶠ z in 𝓝 (0 : Coordinates d),
      dualFunctional (spectralThreshold d) (U hd z) = (graphExpression hd z : EReal) := by
  have ht : Tendsto (fun z : Coordinates d => ((1:ℝ),z)) (𝓝 0) (𝓝 (1,0)) :=
    (continuous_const.prodMk continuous_id).continuousAt
  filter_upwards [ht.eventually (correction_solves hd)] with z hz
  have hh := graph_dualFunctional (by omega : 0 < d) (by norm_num : (0:ℝ)<1)
    z (sliceCorrection hd z) hz
  change dualFunctional (1 * spectralThreshold d) (U hd z) = _ at hh
  rw [one_mul, div_one] at hh
  rw [hh]
  congr 1
  unfold graphExpression
  rw [centeredLogPartition_eq, mean_slicePotential, sub_zero, assembly_square_mean]
  change logPartitionReal (U hd z) - (∑ i, ‖z i‖^2) -
    (1/2:ℝ)*mean d (W hd z * normalized (U hd z)) =
      logPartitionReal (U hd z) - (2 * ∑ i, ‖z i‖^2)/2 -
        mean d (W hd z * normalized (U hd z))/2
  ring

theorem criticalReducedEnergy_eq {d : ℕ} (hd : 12 ≤ d) :
    criticalReducedEnergy hd =ᶠ[𝓝 (0 : Coordinates d)] graphExpression hd := by
  filter_upwards [dualFunctional_graphExpression hd] with z hz
  simp only [criticalReducedEnergy, hz, EReal.toReal_coe]

/-- Exact manuscript quartic coefficients and fifth-order norm remainder for
the physical dual functional, not an auxiliary formal polynomial. -/
theorem criticalReducedEnergy_quartic {d : ℕ} (hd : 12 ≤ d) :
    (fun z => criticalReducedEnergy hd z - quarticValue z)
      =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖^5) := by
  exact (graphExpression_quartic hd).congr'
    ((criticalReducedEnergy_eq hd).sub (Filter.EventuallyEq.rfl)).symm Filter.EventuallyEq.rfl

#print axioms dualFunctional_graphExpression
#print axioms criticalReducedEnergy_quartic
end BecknerOnofri.HighDim.ReducedPhysicalEnergy
