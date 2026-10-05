import BecknerOnofri.UniformComplementBounds

/-! Uniform cubic size of the nonlinear part of the actual reduced equation. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Filter Asymptotics
open scoped Topology
namespace BecknerOnofri.HighDim.UniformComplementBounds
open ContinuousGibbs ContinuousFirstShell ContinuousComplement GreenLocalBranch ReducedEquation
open ReducedCubicExpansion QuadraticSlaving

theorem potential_square_coordinates {d : ℕ} (hd : 12 ≤ d) (x : ℝ × Coordinates d) :
    coordinates d (potential hd x ^ 2) =
      (2:ℝ) • coordinates d (assembly d x.2 * (correction hd x : Space d)) +
      coordinates d ((correction hd x : Space d)^2) := by
  have he : potential hd x ^ 2 = (assembly d x.2)^2 +
      (2:ℝ) • (assembly d x.2 * (correction hd x : Space d)) +
      (correction hd x : Space d)^2 := by
    change (assembly d x.2 + (correction hd x : Space d))^2 = _
    ext t
    simp only [ContinuousMap.add_apply, ContinuousMap.pow_apply, ContinuousMap.smul_apply,
      ContinuousMap.mul_apply, smul_eq_mul]
    ring
  rw [he, map_add, map_add, map_smul, coordinates_shellSquare, zero_add]

theorem potential_square_coordinates_cubic {d : ℕ} (hd : 12 ≤ d) :
    (fun x => coordinates d (potential hd x^2))
      =O[𝓝 (1,(0 : Coordinates d))] (fun x => ‖x.2‖^3) := by
  have hV : (fun x : ℝ × Coordinates d => assembly d x.2)
      =O[𝓝 (1,0)] (fun x => ‖x.2‖) := ((assembly d).isBigO_comp _ _).norm_right
  have hVW : (fun x => assembly d x.2 * (correction hd x : Space d))
      =O[𝓝 (1,(0 : Coordinates d))] (fun x => ‖x.2‖^3) := by
    convert! hV.mul (correction_coe_uniform_quadratic hd) using 1 <;> (ext x; ring)
  have hW1 := (correction_coe_uniform_quadratic hd).trans
    (pow_down.comp_tendsto (continuous_snd.continuousAt :
      Tendsto (Prod.snd : ℝ × Coordinates d → Coordinates d) (𝓝 (1,0)) (𝓝 0)))
  have hWW : (fun x => (correction hd x : Space d)^2)
      =O[𝓝 (1,(0 : Coordinates d))] (fun x => ‖x.2‖^3) := by
    convert! (correction_coe_uniform_quadratic hd).mul hW1 using 1 <;> (ext x; ring)
  exact ((((coordinates d).isBigO_comp _ _).trans hVW).const_smul_left (2:ℝ)).add
    (((coordinates d).isBigO_comp _ _).trans hWW) |>.congr_left
      (fun x => (potential_square_coordinates hd x).symm)

theorem nonlinear_coordinates_uniform_cubic {d : ℕ} (hd : 12 ≤ d) :
    (fun x => coordinates d (nonlinearRemainder (potential hd x)))
      =O[𝓝 (1,(0 : Coordinates d))] (fun x => ‖x.2‖^3) := by
  have hN := ((normalized_quadratic_remainder d).comp_tendsto (potential_tendsto hd)).trans
    ((potential_uniform_linear hd).norm_left.pow 3)
  have hQ := (potential_square_coordinates_cubic hd).const_smul_left (1/2:ℝ)
  apply ((((coordinates d).isBigO_comp _ _).trans hN).add hQ).congr_left
  intro x
  dsimp only [Pi.smul_apply]
  have hm : mean d (potential hd x) = 0 := mean_reconstruction _
  rw [← coordinates_center (potential hd x^2), ← map_smul,
    ← quadraticTerm_of_mean_zero hm, ← map_add]
  congr 1
  dsimp only [Function.comp_apply]
  unfold quadraticPolynomial nonlinearRemainder
  abel

/-- The parameter-axis linearization is removed exactly, leaving a uniform cubic bound. -/
theorem reduced_uniform_cubic {d : ℕ} (hd : 12 ≤ d) :
    (fun x => reduced hd x - (1-x.1) • x.2)
      =O[𝓝 (1,(0 : Coordinates d))] (fun x => ‖x.2‖^3) := by
  have hμ : (Prod.fst : ℝ × Coordinates d → ℝ) =O[𝓝 (1,0)] (fun _ => (1:ℝ)) :=
    continuous_fst.continuousAt.isBigO
  have hh := hμ.smul (nonlinear_coordinates_uniform_cubic hd)
  simp only [smul_eq_mul, one_mul] at hh
  apply hh.neg_left.congr_left
  intro x
  rw [reduced_eq_linear_remainder]
  abel

#print axioms nonlinear_coordinates_uniform_cubic
#print axioms reduced_uniform_cubic
end BecknerOnofri.HighDim.UniformComplementBounds
