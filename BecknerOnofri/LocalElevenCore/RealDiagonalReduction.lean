module

public import BecknerOnofri.LocalElevenContinuousInverse
public import BecknerOnofri.QuarticSignsEleven
public import BecknerOnofri.RealDiagonalReduction
public import BecknerOnofri.LocalElevenCore.ReflectionSymmetry
public import BecknerOnofri.LocalElevenCore.ReducedAxisDerivative

@[expose] public section

/-! The full complex first-shell equation really restricts to one real
equation on the symmetric diagonal, by actual torus symmetries. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false

open Filter
open scoped Topology ComplexConjugate
namespace BecknerOnofri.HighDim.LocalEleven.RealDiagonalReduction

open BecknerOnofri.HighDim.RealDiagonalReduction hiding conjugate_realDiagonal diagonalEmbedding diagonalEmbedding_apply diagonalEmbedding_tendsto diagonalResidual diagonalResidual_analytic diagonalResidual_axis diagonalResidual_cubic diagonalResidual_derivative_axis diagonalResidual_odd firstIndex permutation_realDiagonal reduced_realDiagonal reduced_realDiagonal_zero_iff
open BecknerOnofri.HighDim.ContinuousSymmetry hiding allHalfTranslation axis_phase_eq_one_iff center_permutation coefficient_permutation coefficient_reflection complementMap_permutation complementMap_reflection complementPermutation complementPermutation_coe complementProjection_permutation complementProjection_reflection complementReflection complementReflection_coe conjugateCoordinates conjugateCoordinates_apply conjugateCoordinates_norm coordinatePermutation coordinatePermutation_apply coordinates_permutation coordinates_reflection correction_permutation correction_reflection correction_translation exists_phase_nonnegative exponential_permutation exponential_reflection firstShell_permutation_iff fourier_one_half frequencyLength_permutation frequencyPermutation frequencyPermutation_axis frequencyPermutation_eq_zero_iff frequencyPermutation_neg full_translation green_permutation green_reflection green_translation halfTranslation halfTranslation_fixes_of_zero integral_pointPermutation latticeSquare_permutation meanProjection_permutation meanProjection_reflection mean_permutation mean_reflection nonlinearRemainder_permutation normalized_permutation normalized_reflection partition_permutation partition_reflection permutation permutation_apply permutation_assembly permutation_const permutation_mem_complement_iff permutation_one permuteCoordinates permuteCoordinates_norm phaseNormalizer phaseNormalizer_spec phaseNormalizer_toCircle phase_allHalfTranslation phase_coordinate_norm phase_halfTranslation phase_orbit_iff phase_stabilizer_iff phase_stabilizer_trivial_of_full_support pointPermutation pointPermutation_apply pointPermutation_continuous pointPermutation_isometry pointPermutation_measurePreserving potential_neg potential_permutation potential_reflection potential_translation projectedEquation_permutation projectedEquation_reflection projection_permutation projection_reflection reconstructed_correction_translation reconstruction_permutation reconstruction_reflection reduced_neg reduced_nonnegative_zero_iff reduced_permutation reduced_reflection reduced_translation reduced_zero_on_inactive reduced_zero_permutation_iff reduced_zero_translation_iff reflection reflection_apply reflection_assembly reflection_const reflection_involutive reflection_mem_complement_iff reflection_one reflection_synthesis zero_coordinate_of_stabilizer
open BecknerOnofri.HighDim.GreenLocalBranch hiding correction correction_analytic correction_axis correction_base correction_derivative_zero correction_quadratic correction_solves correction_unique exists_analytic_complement green_assembly green_first_complement_zero linearPart_eq zero_axis_of_unique
open BecknerOnofri.HighDim.ReducedEquation hiding complementMap_assembly complementMap_reconstruction coordinates_complement coordinates_green coordinates_one coordinates_reconstruction full full_complement full_coordinates full_mean full_zero_iff graph_full_iff_reduced local_full_iff_reduced meanZero_zero_iff mean_green potential potential_analytic reduced reduced_analytic
open ContinuousGibbs ContinuousFirstShell ContinuousSymmetry GreenLocalBranch ReducedEquation
open BecknerOnofri.HighDim.ReducedCubicExpansion hiding U_cube_difference U_square_difference coordinates_U coordinates_center coordinates_const coordinates_quadraticTerm_difference coordinates_shellSquare cubicModel cubicModel_analytic cubicModel_apply cubicModel_diagonal cubicModel_neg cubicTerm_assembly_analytic cubicTerm_difference nonlinear_graph_derivative_axis potential_axis quadraticCorrection_analytic quadraticCorrection_product_error realDiagonal realDiagonal_apply reduced_cubic_expansion reduced_cubic_expansion_fifth reduced_derivative_axis reduced_diagonal_cubic_expansion reduced_diagonal_cubic_expansion_fifth reduced_diagonal_derivative_axis reduced_eq_linear_remainder
open ReducedCubicExpansion

def firstIndex {d : ℕ} (hd : 11 ≤ d) : Fin d := ⟨0,by omega⟩

def diagonalEmbedding (d : ℕ) : ℝ × ℝ →L[ℝ] ℝ × Coordinates d :=
  (ContinuousLinearMap.id ℝ ℝ).prodMap (realDiagonal d)

@[simp] theorem diagonalEmbedding_apply (d : ℕ) (x : ℝ × ℝ) :
    diagonalEmbedding d x = (x.1,realDiagonal d x.2) := rfl

theorem diagonalEmbedding_tendsto (d : ℕ) :
    Tendsto (diagonalEmbedding d) (𝓝 (1,0)) (𝓝 (1,(0 : Coordinates d))) := by
  simpa only [diagonalEmbedding_apply, map_zero] using
    (diagonalEmbedding d).continuous.continuousAt.tendsto (x := ((1,0) : ℝ × ℝ))

@[simp] theorem permutation_realDiagonal {d : ℕ} (σ : Equiv.Perm (Fin d)) (t : ℝ) :
    permuteCoordinates σ (realDiagonal d t) = realDiagonal d t := rfl

@[simp] theorem conjugate_realDiagonal (d : ℕ) (t : ℝ) :
    conjugateCoordinates (realDiagonal d t) = realDiagonal d t := by
  ext i
  simp only [conjugateCoordinates_apply, realDiagonal_apply, Complex.conj_ofReal]

/-- The actual real scalar equation, taken from the full actual reduced map. -/
def diagonalResidual {d : ℕ} (hd : 11 ≤ d) (x : ℝ × ℝ) : ℝ :=
  (reduced hd (x.1,realDiagonal d x.2) (firstIndex hd)).re

theorem diagonalResidual_analytic {d : ℕ} (hd : 11 ≤ d) :
    AnalyticAt ℝ (diagonalResidual hd) (1,0) := by
  have he := (diagonalEmbedding d).analyticAt ((1,0) : ℝ × ℝ)
  have ho : AnalyticAt ℝ (reduced hd) (diagonalEmbedding d (1,0)) := by
    simpa only [diagonalEmbedding_apply, map_zero] using reduced_analytic hd
  have hr := ho.comp he
  let ev : Coordinates d →L[ℝ] ℝ := Complex.reCLM.comp (ContinuousLinearMap.proj (firstIndex hd))
  have hh := (ev.analyticAt (reduced hd (diagonalEmbedding d (1,0)))).comp
    (f := fun x : ℝ × ℝ => reduced hd (diagonalEmbedding d x))
    (x := ((1,0) : ℝ × ℝ)) (by convert! hr using 1)
  convert! hh using 1

/-- All entries on the real symmetric diagonal are the same real number.
The reality follows from spatial inversion, not a restriction on solutions. -/
theorem reduced_realDiagonal {d : ℕ} (hd : 11 ≤ d) :
    ∀ᶠ x : ℝ × ℝ in 𝓝 (1,0),
      reduced hd (x.1,realDiagonal d x.2) = realDiagonal d (diagonalResidual hd x) := by
  filter_upwards [(diagonalEmbedding_tendsto d).eventually (reduced_permutation hd),
    (diagonalEmbedding_tendsto d).eventually (reduced_reflection hd)] with x hp hr
  simp only [diagonalEmbedding_apply, conjugate_realDiagonal] at hr
  ext i
  have hc : reduced hd (x.1,realDiagonal d x.2) i =
      reduced hd (x.1,realDiagonal d x.2) (firstIndex hd) := by
    have hh := hp (Equiv.swap i (firstIndex hd))
    simp only [diagonalEmbedding_apply, permutation_realDiagonal] at hh
    simpa only [permuteCoordinates, Equiv.swap_apply_left] using congrFun hh i
  have him : (reduced hd (x.1,realDiagonal d x.2) i).im = 0 := by
    have hh := congrArg Complex.im (congrFun hr i)
    simp only [conjugateCoordinates_apply, Complex.conj_im] at hh
    linarith
  apply Complex.ext
  · change (reduced hd (x.1,realDiagonal d x.2) i).re =
      (reduced hd (x.1,realDiagonal d x.2) (firstIndex hd)).re
    exact congrArg Complex.re hc
  · simpa only [realDiagonal_apply, Complex.ofReal_im] using him

theorem reduced_realDiagonal_zero_iff {d : ℕ} (hd : 11 ≤ d) :
    ∀ᶠ x : ℝ × ℝ in 𝓝 (1,0),
      reduced hd (x.1,realDiagonal d x.2) = 0 ↔ diagonalResidual hd x = 0 := by
  filter_upwards [reduced_realDiagonal hd] with x hx
  rw [hx]
  constructor
  · intro hh
    have hi := congrFun hh (firstIndex hd)
    simpa only [realDiagonal_apply, Pi.zero_apply, Complex.ofReal_eq_zero] using hi
  · intro hh
    rw [hh, map_zero]

theorem diagonalResidual_axis {d : ℕ} (hd : 11 ≤ d) :
    ∀ᶠ μ in 𝓝 (1:ℝ), diagonalResidual hd (μ,0) = 0 := by
  filter_upwards [potential_axis hd] with μ hμ
  simp only [diagonalResidual, map_zero, reduced, hμ, normalized_zero,
    coordinates_one, smul_zero, sub_zero, Pi.zero_apply, Complex.zero_re]

theorem diagonalResidual_derivative_axis {d : ℕ} (hd : 11 ≤ d) :
    ∀ᶠ μ in 𝓝 (1:ℝ), HasDerivAt (fun t => diagonalResidual hd (μ,t)) (1-μ) 0 :=
  reduced_diagonal_derivative_axis hd (firstIndex hd)

theorem diagonalResidual_odd {d : ℕ} (hd : 11 ≤ d) :
    ∀ᶠ x : ℝ × ℝ in 𝓝 (1,0), diagonalResidual hd (x.1,-x.2) = -diagonalResidual hd x := by
  filter_upwards [(diagonalEmbedding_tendsto d).eventually (reduced_neg hd)] with x hx
  have hh := congrArg (fun z : Coordinates d => (z (firstIndex hd)).re) hx
  simpa only [diagonalEmbedding_apply, diagonalResidual, map_neg, Pi.neg_apply,
    Complex.neg_re] using hh

theorem diagonalResidual_cubic {d : ℕ} (hd : 11 ≤ d) :
    (fun t : ℝ => diagonalResidual hd (1,t) - kappa d*t^3)
      =O[𝓝 0] (fun t : ℝ => ‖t‖^5) :=
  reduced_diagonal_cubic_expansion_fifth hd (firstIndex hd)

#print axioms diagonalResidual_analytic
#print axioms reduced_realDiagonal
#print axioms reduced_realDiagonal_zero_iff
end BecknerOnofri.HighDim.LocalEleven.RealDiagonalReduction
