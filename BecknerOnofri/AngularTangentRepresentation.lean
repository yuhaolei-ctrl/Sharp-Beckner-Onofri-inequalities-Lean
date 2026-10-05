import BecknerOnofri.AngularReducedKernel
import BecknerOnofri.GraphHessian

/-! The imaginary graph tangent space is exactly the actual spatial
translation tangent space, with the manuscript's directional derivatives. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter
open scoped Topology BigOperators
namespace BecknerOnofri.HighDim.AngularTangentRepresentation
open ContinuousGibbs ContinuousFirstShell ReducedEquation GraphHessian
open GraphTranslationTangents AngularReducedKernel ReducedCubicExpansion

theorem tangentMap_angles {d : ℕ} (hd : 12 ≤ d) :
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
theorem imaginary_tangent_representation {d : ℕ} (hd : 12 ≤ d) :
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
end BecknerOnofri.HighDim.AngularTangentRepresentation
