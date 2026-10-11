module

public import BecknerOnofri.V2.Reaudit.HeatKernel.KernelDomination

@[expose] public section

/-! # Drop-in replacements for the two legacy parabolic-maximum-principle theorems (U05/S015)

The legacy development proves the two one-dimensional heat-kernel facts that the whole tensor /
Mellin / Euler-operator chain consumes by a maximum principle on finite spectral truncations:

* `JacobiHeatPositivity.heatKernel_nonnegative_interior` (`0 ≤ K_m`),
* `JacobiHeatPositivity.heatKernel_le_decayed_dirichlet` (`K_m ≤ e^{-m(m-1)t} K_1`).

This file proves the same two statements (verbatim, up to the definitional unfolding
`potentialBottom m = m(m-1)`) from `KernelDomination` (positive Neumann series of the truncated
potentials, strong resolvent limit on the explicit eigenbasis, exponential formula, box tests),
extended from `x ∈ (0,π)` to `x ∈ [0,π]` by the Dirichlet vanishing of the eigenfunctions.
It imports neither the maximum principle nor any legacy heat-kernel comparison module, so a legacy
module can import it and re-prove the two statements without an import cycle.
-/

noncomputable section
open Set
namespace BecknerOnofri.V2.Reaudit.HeatKernel.Engine
open Legacy.BecknerOnofri Legacy.BecknerOnofri.JacobiHeatBounds

theorem heatKernel_left_zero {m : ℕ} (hm : 0 < m) (t y : ℝ) : heatKernel m t 0 y = 0 := by
  simp [heatKernel, JacobiEigenfunctions.normalizedFunction_zero hm]

theorem heatKernel_left_pi {m : ℕ} (hm : 0 < m) (t y : ℝ) : heatKernel m t Real.pi y = 0 := by
  simp [heatKernel, JacobiEigenfunctions.normalizedFunction_pi hm]

/-- Same statement as `JacobiHeatPositivity.heatKernel_nonnegative_interior`. -/
theorem heatKernel_nonnegative_interior_V2 {m : ℕ} (hm : 0 < m) {t x y : ℝ}
    (ht : 0 < t) (hx : x ∈ Icc 0 Real.pi) (hy : y ∈ Ioo 0 Real.pi) :
    0 ≤ heatKernel m t x y := by
  by_cases hx0 : x = 0
  · subst hx0; rw [heatKernel_left_zero hm]
  by_cases hxp : x = Real.pi
  · subst hxp; rw [heatKernel_left_pi hm]
  exact heatKernel_nonneg_V2 hm ht
    ⟨lt_of_le_of_ne hx.1 (Ne.symm hx0), lt_of_le_of_ne hx.2 hxp⟩ hy

/-- Same statement as `JacobiHeatPositivity.heatKernel_le_decayed_dirichlet`
(`potentialBottom m = m(m-1) = cc m` by definition). -/
theorem heatKernel_le_decayed_dirichlet_V2 {m : ℕ} (hm : 0 < m) {t x y : ℝ}
    (ht : 0 < t) (hx : x ∈ Icc 0 Real.pi) (hy : y ∈ Ioo 0 Real.pi) :
    heatKernel m t x y ≤ Real.exp (-((m : ℝ) * ((m : ℝ) - 1)) * t) * heatKernel 1 t x y := by
  by_cases hx0 : x = 0
  · subst hx0
    rw [heatKernel_left_zero hm, heatKernel_left_zero one_pos]; simp
  by_cases hxp : x = Real.pi
  · subst hxp
    rw [heatKernel_left_pi hm, heatKernel_left_pi one_pos]; simp
  exact heatKernel_le_decayed_V2 hm ht
    ⟨lt_of_le_of_ne hx.1 (Ne.symm hx0), lt_of_le_of_ne hx.2 hxp⟩ hy

#print axioms heatKernel_nonnegative_interior_V2
#print axioms heatKernel_le_decayed_dirichlet_V2

end BecknerOnofri.V2.Reaudit.HeatKernel.Engine
