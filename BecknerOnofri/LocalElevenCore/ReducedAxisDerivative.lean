module

public import BecknerOnofri.LocalElevenContinuousInverse
public import BecknerOnofri.ReducedAxisDerivative
public import BecknerOnofri.LocalElevenCore.ReducedCubicParity

@[expose] public section

/-! Exact linearization of the genuine reduced equation along the uniform parameter axis. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter
open scoped Topology
namespace BecknerOnofri.HighDim.LocalEleven.ReducedCubicExpansion

open BecknerOnofri.HighDim.ReducedCubicExpansion hiding U_cube_difference U_square_difference coordinates_U coordinates_center coordinates_const coordinates_quadraticTerm_difference coordinates_shellSquare cubicModel cubicModel_analytic cubicModel_apply cubicModel_diagonal cubicModel_neg cubicTerm_assembly_analytic cubicTerm_difference nonlinear_graph_derivative_axis potential_axis quadraticCorrection_analytic quadraticCorrection_product_error realDiagonal realDiagonal_apply reduced_cubic_expansion reduced_cubic_expansion_fifth reduced_derivative_axis reduced_diagonal_cubic_expansion reduced_diagonal_cubic_expansion_fifth reduced_diagonal_derivative_axis reduced_eq_linear_remainder
open BecknerOnofri.HighDim.GreenLocalBranch hiding correction correction_analytic correction_axis correction_base correction_derivative_zero correction_quadratic correction_solves correction_unique exists_analytic_complement green_assembly green_first_complement_zero linearPart_eq zero_axis_of_unique
open BecknerOnofri.HighDim.ReducedEquation hiding complementMap_assembly complementMap_reconstruction coordinates_complement coordinates_green coordinates_one coordinates_reconstruction full full_complement full_coordinates full_mean full_zero_iff graph_full_iff_reduced local_full_iff_reduced meanZero_zero_iff mean_green potential potential_analytic reduced reduced_analytic
open ContinuousGibbs ContinuousFirstShell ContinuousComplement GreenLocalBranch ReducedEquation

/-- Exact separation of the spectral linear term and the actual nonlinear Gibbs remainder. -/
theorem reduced_eq_linear_remainder {d : ℕ} (hd : 11 ≤ d) (x : ℝ × Coordinates d) :
    reduced hd x = (1-x.1) • x.2 - x.1 • coordinates d (nonlinearRemainder (potential hd x)) := by
  have hc : coordinates d (potential hd x) = x.2 := coordinates_reconstruction _
  unfold reduced nonlinearRemainder
  rw [map_sub, map_sub, coordinates_one, coordinates_center, hc, sub_zero]
  module

theorem potential_axis {d : ℕ} (hd : 11 ≤ d) :
    ∀ᶠ μ in 𝓝 (1:ℝ), potential hd (μ,0) = 0 := by
  filter_upwards [correction_axis hd] with μ hμ
  simp [potential, reconstruction_apply, hμ]

theorem nonlinear_graph_derivative_axis {d : ℕ} (hd : 11 ≤ d) :
    ∀ᶠ μ in 𝓝 (1:ℝ), HasFDerivAt (𝕜 := ℝ)
      (fun x : ℝ × Coordinates d => coordinates d (nonlinearRemainder (potential hd x))) 0 (μ,0) := by
  have ht : Tendsto (fun μ : ℝ => (μ,(0 : Coordinates d))) (𝓝 1) (𝓝 (1,0)) :=
    (continuous_id.prodMk continuous_const).continuousAt
  filter_upwards [potential_axis hd, ht.eventually (potential_analytic hd).eventually_analyticAt]
    with μ hzero hana
  have hN : HasFDerivAt (𝕜 := ℝ) nonlinearRemainder 0 (potential hd (μ,0)) := by
    rw [hzero]
    exact hasFDerivAt_remainder_zero d
  have h := hN.comp (μ,0) hana.differentiableAt.hasFDerivAt
  have h' := (coordinates d).hasFDerivAt.comp (μ,0) h
  convert! h' using 1 <;> simp

/-- For every nearby parameter, the complete real derivative is exactly (1−μ) times first-shell projection. -/
theorem reduced_derivative_axis {d : ℕ} (hd : 11 ≤ d) :
    ∀ᶠ μ in 𝓝 (1:ℝ), HasFDerivAt (𝕜 := ℝ) (reduced hd)
      ((1-μ) • ContinuousLinearMap.snd ℝ ℝ (Coordinates d)) (μ,0) := by
  filter_upwards [potential_axis hd, nonlinear_graph_derivative_axis hd] with μ hzero hN
  have hNv : coordinates d (nonlinearRemainder (potential hd (μ,0))) = 0 := by
    rw [hzero, nonlinearRemainder_zero, map_zero]
  have hf := (ContinuousLinearMap.fst ℝ ℝ (Coordinates d)).hasFDerivAt (x := (μ,(0 : Coordinates d)))
  have hs := (ContinuousLinearMap.snd ℝ ℝ (Coordinates d)).hasFDerivAt (x := (μ,(0 : Coordinates d)))
  have h1 := ((hasFDerivAt_const (1:ℝ) (μ,(0 : Coordinates d))).sub hf).smul hs
  have h2 := hf.smul hN
  have h := h1.sub h2
  convert! h using 1
  · funext x
    exact reduced_eq_linear_remainder hd x
  · simp [hNv]

/-- The exact scalar derivative needed by analytic division by the diagonal amplitude. -/
theorem reduced_diagonal_derivative_axis {d : ℕ} (hd : 11 ≤ d) (i : Fin d) :
    ∀ᶠ μ in 𝓝 (1:ℝ), HasDerivAt
      (fun t : ℝ => (reduced hd (μ,realDiagonal d t) i).re) (1-μ) 0 := by
  filter_upwards [reduced_derivative_axis hd] with μ hμ
  have hi : HasFDerivAt (𝕜 := ℝ) (fun t : ℝ => (μ,realDiagonal d t))
      ((0 : ℝ →L[ℝ] ℝ).prod (realDiagonal d)) 0 :=
    (hasFDerivAt_const μ (0:ℝ)).prodMk (realDiagonal d).hasFDerivAt
  have he : HasFDerivAt (𝕜 := ℝ) (fun z : Coordinates d => (z i).re)
      (Complex.reCLM.comp (ContinuousLinearMap.proj i)) (reduced hd (μ,0)) :=
    by
      let ev : Coordinates d →L[ℝ] ℝ := Complex.reCLM.comp (ContinuousLinearMap.proj i)
      convert! ev.hasFDerivAt (x := reduced hd (μ,0)) using 1
  have hh := he.comp (0:ℝ) (hμ.comp (0:ℝ) (by simpa only [map_zero] using hi))
  convert! hh.hasDerivAt using 1
  simp [ContinuousLinearMap.comp_apply, realDiagonal_apply]

#print axioms reduced_derivative_axis
#print axioms reduced_diagonal_derivative_axis
end BecknerOnofri.HighDim.LocalEleven.ReducedCubicExpansion
