module

public import BecknerOnofri.ComplementParameterBound

@[expose] public section

/-! The exact cubic reduced equation with a quantitative joint parameter remainder. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Filter Asymptotics
open scoped Topology
namespace BecknerOnofri.HighDim.UniformComplementBounds
open ContinuousGibbs ContinuousFirstShell ContinuousComplement GreenLocalBranch ReducedEquation
open ReducedCubicExpansion QuadraticSlaving

theorem nonlinear_parameter_bound {d : ℕ} (hd : 12 ≤ d) :
    (fun x => nonlinearRemainder (potential hd x) - nonlinearRemainder (potential hd (sliceMap d x)))
      =O[𝓝 (1,(0 : Coordinates d))] (fun x => |x.1-1| * ‖x.2‖^3) := by
  have hUpair : Tendsto (fun x => (potential hd x,potential hd (sliceMap d x)))
      (𝓝 (1,(0 : Coordinates d))) (𝓝 (0,0)) :=
    (potential_tendsto hd).prodMk_nhds ((potential_tendsto hd).comp (sliceMap_tendsto d))
  have hdiff := (nonlinearRemainder_difference d).comp_tendsto hUpair
  have hmax0 : (fun x => max ‖potential hd x‖ ‖potential hd (sliceMap d x)‖)
      =O[𝓝 (1,(0 : Coordinates d))]
        (fun x => ‖potential hd x‖ + ‖potential hd (sliceMap d x)‖) := by
    apply IsBigO.of_norm_le
    intro x
    rw [Real.norm_of_nonneg (le_trans (norm_nonneg _) (le_max_left _ _))]
    exact max_le (le_add_of_nonneg_right (norm_nonneg _)) (le_add_of_nonneg_left (norm_nonneg _))
  have hmax := hmax0.trans ((potential_uniform_linear hd).norm_left.add
    (((potential_uniform_linear hd).comp_tendsto (sliceMap_tendsto d)).norm_left))
  have hwdiff : (fun x => ‖potential hd x - potential hd (sliceMap d x)‖)
      =O[𝓝 (1,(0 : Coordinates d))] (fun x => |x.1-1| * ‖x.2‖^2) := by
    simpa only [potential_difference, Submodule.norm_coe] using (correction_parameter_bound hd).norm_left
  have hh := hdiff.trans (hmax.mul hwdiff)
  convert! hh using 1 <;> (ext x; ring)

theorem reduced_parameter_difference {d : ℕ} (hd : 12 ≤ d) :
    (fun x => reduced hd x - (1-x.1) • x.2 - reduced hd (sliceMap d x))
      =O[𝓝 (1,(0 : Coordinates d))] (fun x => |x.1-1| * ‖x.2‖^3) := by
  have hδ : (fun x : ℝ × Coordinates d => x.1-1)
      =O[𝓝 (1,0)] (fun x => |x.1-1|) := (isBigO_refl _ _).norm_right
  have hN0 := (nonlinear_coordinates_uniform_cubic hd).comp_tendsto (sliceMap_tendsto d)
  have ha := hδ.smul hN0
  have hμ : (Prod.fst : ℝ × Coordinates d → ℝ) =O[𝓝 (1,0)] (fun _ => (1:ℝ)) :=
    continuous_fst.continuousAt.isBigO
  have hb := hμ.smul (((coordinates d).isBigO_comp _ _).trans (nonlinear_parameter_bound hd))
  simp only [smul_eq_mul, one_mul] at ha hb
  apply (ha.neg_left.sub hb).congr_left
  intro x
  dsimp only [Function.comp_apply]
  rw [map_sub, reduced_eq_linear_remainder, reduced_eq_linear_remainder]
  simp only [sliceMap, sub_self, zero_smul, one_smul, zero_sub]
  module

/-- Actual full first-shell equation, uniformly in parameter and amplitude near onset. -/
theorem reduced_parameter_cubic_expansion {d : ℕ} (hd : 12 ≤ d) :
    (fun x => reduced hd x - (1-x.1) • x.2 - cubicModel hd x.2)
      =O[𝓝 (1,(0 : Coordinates d))] (fun x => ‖x.2‖^5 + |x.1-1| * ‖x.2‖^3) := by
  have ht : Tendsto (Prod.snd : ℝ × Coordinates d → Coordinates d) (𝓝 (1,0)) (𝓝 0) :=
    continuous_snd.continuousAt
  have hslice := (reduced_cubic_expansion_fifth hd).comp_tendsto ht
  have hh := hslice.add_add (reduced_parameter_difference hd)
  dsimp only [Function.comp_apply] at hh
  simp only [norm_pow, norm_norm, norm_mul, Real.norm_eq_abs, abs_abs, abs_norm] at hh
  apply hh.congr_left
  intro x
  dsimp only [Function.comp_apply, sliceMap]
  abel

theorem realDiagonal_norm {d : ℕ} (hd : 0 < d) (t : ℝ) : ‖realDiagonal d t‖ = ‖t‖ := by
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  change ‖fun _ : Fin d => (t:ℂ)‖ = ‖t‖
  rw [pi_norm_const, Complex.norm_real]

/-- The scalar diagonal equation is (1−μ)t+κt³+O(t⁵+|μ−1|t³), for the actual Gibbs reduction. -/
theorem reduced_diagonal_parameter_expansion {d : ℕ} (hd : 12 ≤ d) (i : Fin d) :
    (fun x : ℝ × ℝ => (reduced hd (x.1,realDiagonal d x.2) i).re -
      (1-x.1)*x.2 - kappa d*x.2^3)
      =O[𝓝 (1,0)] (fun x : ℝ × ℝ => ‖x.2‖^5 + |x.1-1| * ‖x.2‖^3) := by
  have ht : Tendsto (fun x : ℝ × ℝ => (x.1, realDiagonal d x.2))
      (𝓝 (1,0)) (𝓝 (1,0)) := by
    convert! (continuous_fst.prodMk ((realDiagonal d).continuous.comp continuous_snd)).continuousAt.tendsto
      (x := ((1,0) : ℝ × ℝ)) using 1 <;> simp only [Function.comp_apply, map_zero]
  have hh := (reduced_parameter_cubic_expansion hd).comp_tendsto ht
  simp only [Function.comp_def, realDiagonal_norm (by omega : 0<d)] at hh
  let ev : Coordinates d →L[ℝ] ℝ := Complex.reCLM.comp (ContinuousLinearMap.proj i)
  apply ((ev.isBigO_comp _ _).trans hh).congr_left
  intro x
  change (reduced hd (x.1,realDiagonal d x.2) i - (1-x.1) • realDiagonal d x.2 i -
    cubicModel hd (realDiagonal d x.2) i).re = _
  rw [cubicModel_diagonal]
  simp only [Complex.sub_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, realDiagonal_apply, mul_zero, sub_zero]

#print axioms reduced_parameter_cubic_expansion
#print axioms reduced_diagonal_parameter_expansion
end BecknerOnofri.HighDim.UniformComplementBounds
