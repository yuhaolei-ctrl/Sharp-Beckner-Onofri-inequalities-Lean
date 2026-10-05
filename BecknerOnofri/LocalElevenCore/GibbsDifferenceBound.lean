import BecknerOnofri.LocalElevenContinuousInverse
import BecknerOnofri.QuarticSignsEleven
import BecknerOnofri.GibbsDifferenceBound
import BecknerOnofri.LocalElevenCore.UniformComplementBounds

/-! A uniform quadratic Lipschitz estimate for the actual normalized Gibbs remainder. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Asymptotics
open scoped Topology
namespace BecknerOnofri.HighDim.LocalEleven.UniformComplementBounds

open BecknerOnofri.HighDim.UniformComplementBounds hiding correction_coe_uniform_quadratic correction_controlled_by_nonlinear correction_inverse_parameter correction_potential_quadratic correction_tendsto correction_uniform_quadratic nonlinearGreen nonlinearRemainder_difference parameter_interval potential_tendsto potential_uniform_linear uniformInverseBound uniformInverseBound_pos

open ContinuousGibbs

theorem nonlinearRemainder_difference (d : ℕ) :
    (fun y : Space d × Space d => nonlinearRemainder y.1 - nonlinearRemainder y.2)
      =O[𝓝 (0,0)] (fun y => max ‖y.1‖ ‖y.2‖ * ‖y.1-y.2‖) := by
  obtain ⟨p,hp⟩ := nonlinearRemainder_analytic (0 : Space d)
  have h1 : continuousMultilinearCurryFin1 ℝ (Space d) (Space d) (p 1) = 0 :=
    hp.hasFDerivAt.unique (hasFDerivAt_remainder_zero d)
  have h1' (v : Space d) : p 1 (fun _ => v) = 0 :=
    congrArg (fun g : Space d →L[ℝ] Space d => g v) h1
  simpa [h1', Prod.norm_def] using hp.isBigO_image_sub_norm_mul_norm_sub

#print axioms nonlinearRemainder_difference
end BecknerOnofri.HighDim.LocalEleven.UniformComplementBounds
