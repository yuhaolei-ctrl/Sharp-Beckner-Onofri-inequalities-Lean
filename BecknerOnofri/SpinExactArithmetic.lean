import BecknerOnofri.SpinDefinitions
import Mathlib.Tactic

/-! Kernel-checked rational calculations for the new thirteen-state argument.
No external numerical program or saved numerical report is a premise. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
open scoped BigOperators
namespace BecknerOnofri.HighDim.Spin

theorem vertex_energy_bound :
    ∀ i j k : Count, 1 ≤ i.val → i < j → j < k →
      vertexEnergyQ i j k ≤ 3187261891510618067287/3722907769367296702500 := by
  decide +kernel

theorem vertex_energy_attained :
    vertexEnergyQ 1 9 12 = 3187261891510618067287/3722907769367296702500 := by
  decide +kernel

theorem vertex_energy_lt_seven_eighths :
    (3187261891510618067287:ℚ)/3722907769367296702500 < 7/8 := by norm_num

theorem correcting_vectors_bounds :
    quadraticQ correctionVQ < 4 ∧ quadraticQ correctionZQ < 16 := by
  decide +kernel

theorem correcting_vectors_constraints :
    (∑ j : Count,correctionVQ j)=0 ∧
    (∑ j : Count,meanCoordinateQ j*correctionVQ j)=0 ∧
    (∑ j : Count,correctionZQ j)=0 ∧
    (∑ j : Count,meanCoordinateQ j*correctionZQ j)=1 := by
  decide +kernel

theorem curvature_constants :
    (7/8:ℚ)+(35/11)^2/4096=434889/495616 ∧
    (434889/495616:ℚ)<9/10 ∧
    ((19/20:ℚ)*(56/11)^2)/(19/20-434889/495616)=61014016/179731 ∧
    (61014016/179731:ℚ)<350 := by
  norm_num

#print axioms vertex_energy_bound
#print axioms correcting_vectors_bounds
end BecknerOnofri.HighDim.Spin
