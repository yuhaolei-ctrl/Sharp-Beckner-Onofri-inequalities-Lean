import BecknerOnofri.ReducedCubicParity

/-! Exact linearization of the genuine reduced equation along the uniform parameter axis. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Filter
open scoped Topology
namespace BecknerOnofri.HighDim.ReducedCubicExpansion
open ContinuousGibbs ContinuousFirstShell ContinuousComplement GreenLocalBranch ReducedEquation

/-- Exact separation of the spectral linear term and the actual nonlinear Gibbs remainder. -/
theorem reduced_eq_linear_remainder {d : ℕ} (hd : 12 ≤ d) (x : ℝ × Coordinates d) :
    reduced hd x = (1-x.1) • x.2 - x.1 • coordinates d (nonlinearRemainder (potential hd x)) := by
  have hc : coordinates d (potential hd x) = x.2 := coordinates_reconstruction _
  unfold reduced nonlinearRemainder
  rw [map_sub, map_sub, coordinates_one, coordinates_center, hc, sub_zero]
  module

theorem potential_axis {d : ℕ} (hd : 12 ≤ d) :
    ∀ᶠ μ in 𝓝 (1:ℝ), potential hd (μ,0) = 0 := by
  filter_upwards [correction_axis hd] with μ hμ
  simp [potential, reconstruction_apply, hμ]

theorem nonlinear_graph_derivative_axis {d : ℕ} (hd : 12 ≤ d) :
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
theorem reduced_derivative_axis {d : ℕ} (hd : 12 ≤ d) :
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
theorem reduced_diagonal_derivative_axis {d : ℕ} (hd : 12 ≤ d) (i : Fin d) :
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
end BecknerOnofri.HighDim.ReducedCubicExpansion
