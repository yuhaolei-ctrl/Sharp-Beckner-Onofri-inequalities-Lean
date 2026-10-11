module

public import BecknerOnofri.LocalElevenContinuousInverse
public import BecknerOnofri.ContinuousComplement

@[expose] public section

/-! The three elementary lemmas about the Green operator on the first shell
(`green_assembly`, `green_first_complement_zero`, `linearPart_eq`) used by the complement
equation.  They are moved here verbatim from `LocalElevenCore/GreenLocalBranch.lean`
(which imports this module) so that the Sobolev construction of the complement graph, which
only needs these lemmas, can lie below `GreenLocalBranch.correction`. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Topology
namespace BecknerOnofri.HighDim.LocalEleven.GreenLocalBranch

open ContinuousGibbs ContinuousFirstShell ContinuousComplement

theorem green_assembly {d : ℕ} (hd : 0 < d) (z : Coordinates d) :
    greenContinuous d (assembly d z) = assembly d z := by
  apply coefficient_ext
  intro k
  rw [coefficient_green hd]
  by_cases hk : InFirstShell k
  · have hs : latticeSquare k = 1 := (latticeSquare_eq_one_iff k).mpr hk
    have h0 : k ≠ 0 := by
      intro he
      have hz := (latticeSquare_eq_zero_iff k).mpr he
      omega
    simp [h0, frequencyLength_pow_eq, hs]
  · have hc : coefficient k (assembly d z) = 0 := by
      rw [← projection_assembly z]
      exact coefficient_projection_off_shell _ k hk
    simp [hc]

theorem green_first_complement_zero {d : ℕ} (hd : 0 < d) (z : Coordinates d) :
    complementMap d (greenContinuous d (assembly d z)) = 0 := by
  rw [green_assembly hd]
  apply Subtype.ext
  change complementProjection d (assembly d z) = 0
  rw [complementProjection_apply, meanProjection_apply, mean_assembly, projection_assembly]
  simp

theorem linearPart_eq {d : ℕ} (hd : 0 < d) :
    linearPart (greenContinuous d) = continuousComplementGreen hd := by
  apply ContinuousLinearMap.ext
  intro w
  apply Subtype.ext
  exact complementProjection_eq_self (greenContinuous_mem_complement hd w)

end BecknerOnofri.HighDim.LocalEleven.GreenLocalBranch
