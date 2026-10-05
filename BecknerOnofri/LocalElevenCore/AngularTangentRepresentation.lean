import BecknerOnofri.LocalElevenContinuousInverse
import BecknerOnofri.QuarticSignsEleven
import BecknerOnofri.AngularTangentRepresentation
import BecknerOnofri.LocalElevenCore.AngularReducedKernel
import BecknerOnofri.LocalElevenCore.GraphHessian

/-! The imaginary graph tangent space is exactly the actual spatial
translation tangent space, with the manuscript's directional derivatives. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false

open Filter
open scoped Topology BigOperators
namespace BecknerOnofri.HighDim.LocalEleven.AngularTangentRepresentation

open BecknerOnofri.HighDim.AngularTangentRepresentation hiding imaginary_tangent_representation of_re_zero real_part_angle_sum_zero tangentMap_angles
open BecknerOnofri.HighDim.GraphHessian hiding differentiated_projected_equation hasFDerivAt_graphResidual hessianPairing hessianPairing_continuous hessianPairing_linearized_complement hessianPairing_self hessianPairing_tangentMap_complement linearized_energy_term linearized_fourier_euler linearized_inCriticalSobolev linearized_normalizedEnergy linearized_pairing_complement normalizedEnergyPairing normalizedEnergyPairing_self physical_factor secondVariation_graph secondVariation_linearized secondVariation_tangentMap shell_residual_pairing tangentMap tangentMap_apply tangentMap_eq tangentMap_equation weighted_norm_pairing
open BecknerOnofri.HighDim.ReducedEquation hiding complementMap_assembly complementMap_reconstruction coordinates_complement coordinates_green coordinates_one coordinates_reconstruction full full_complement full_coordinates full_mean full_zero_iff graph_full_iff_reduced local_full_iff_reduced meanZero_zero_iff mean_green potential potential_analytic reduced reduced_analytic
open ContinuousGibbs ContinuousFirstShell ReducedEquation GraphHessian
open BecknerOnofri.HighDim.AngularReducedKernel hiding angular_kernel imaginaryCoordinates imaginary_as_angles imaginary_kernel
open BecknerOnofri.HighDim.GraphTranslationTangents hiding angularDirection axisTranslation coordinates_tangent hasDerivAt_phase_axisTranslation phase_axisTranslation phase_axisTranslation_zero tangent tangentIndependent tangent_eq_coordinateDerivative
open BecknerOnofri.HighDim.ReducedCubicExpansion hiding U_cube_difference U_square_difference coordinates_U coordinates_center coordinates_const coordinates_quadraticTerm_difference coordinates_shellSquare cubicModel cubicModel_analytic cubicModel_apply cubicModel_diagonal cubicModel_neg cubicTerm_assembly_analytic cubicTerm_difference nonlinear_graph_derivative_axis potential_axis quadraticCorrection_analytic quadraticCorrection_product_error realDiagonal realDiagonal_apply reduced_cubic_expansion reduced_cubic_expansion_fifth reduced_derivative_axis reduced_diagonal_cubic_expansion reduced_diagonal_cubic_expansion_fifth reduced_diagonal_derivative_axis reduced_eq_linear_remainder
open GraphTranslationTangents AngularReducedKernel ReducedCubicExpansion

theorem tangentMap_angles {d : ℕ} (hd : 11 ≤ d) :
    ∀ᶠ x in 𝓝 (1,(0:Coordinates d)), ∀ a : Fin d → ℝ,
      (tangentMap hd x (∑ j : Fin d, a j • angularDirection x.2 j) : Torus d → ℝ) =
        tangentCombination (potential hd x) a := by
  filter_upwards [tangent_eq_coordinateDerivative hd] with x hx a
  funext y
  simp only [map_sum,map_smul,ContinuousMap.sum_apply,ContinuousMap.smul_apply,smul_eq_mul,
    tangentMap_apply,tangentCombination]
  exact Finset.sum_congr rfl (fun j _ => by rw [← hx j y]; rfl)

theorem of_re_zero {d : ℕ} (z : Coordinates d) (hz : ∀ i, (z i).re=0) :
    z=imaginaryCoordinates d (fun i => (z i).im) := by
  funext i
  apply Complex.ext <;> simp [imaginaryCoordinates,Complex.mul_re,Complex.mul_im,hz i]

/-- Every purely angular graph direction is literally a translation tangent. -/
theorem imaginary_tangent_representation {d : ℕ} (hd : 11 ≤ d) :
    ∀ᶠ x in 𝓝 (1,(0:Coordinates d)), ∀ t : ℝ, t≠0 → x.2=realDiagonal d t →
      ∀ z : Coordinates d, (∀ i, (z i).re=0) →
        ∃ a : Fin d → ℝ, (tangentMap hd x z : Torus d → ℝ)=tangentCombination (potential hd x) a := by
  filter_upwards [tangentMap_angles hd] with x hx t ht he z hz
  let a : Fin d → ℝ := fun j => (z j).im/(2*Real.pi*t)
  refine ⟨a,?_⟩
  rw [of_re_zero z hz,imaginary_as_angles ht]
  rw [← he]
  exact hx a

/-- The Fourier first-shell vector of a translation tangent has zero real part
at the real diagonal branch. -/
theorem real_part_angle_sum_zero {d : ℕ} (t : ℝ) (a : Fin d → ℝ) :
    ∀ i, ((∑ j : Fin d, a j • angularDirection (realDiagonal d t) j) i).re=0 := by
  classical
  intro i
  simp only [Finset.sum_apply,Pi.smul_apply,Complex.re_sum,Complex.smul_re]
  apply Finset.sum_eq_zero
  intro j _
  by_cases hi : i=j
  · subst i
    simp [angularDirection,realDiagonal,Complex.mul_re]
  · simp [angularDirection,Pi.single_eq_of_ne hi]

#print axioms imaginary_tangent_representation
#print axioms real_part_angle_sum_zero
end BecknerOnofri.HighDim.LocalEleven.AngularTangentRepresentation
