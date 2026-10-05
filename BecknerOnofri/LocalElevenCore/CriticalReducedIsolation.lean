module

public import BecknerOnofri.QuarticCoercivityEleven
public import BecknerOnofri.LocalElevenContinuousInverse
public import BecknerOnofri.QuarticSignsEleven
public import BecknerOnofri.CriticalReducedIsolation
public import BecknerOnofri.LocalElevenCore.CriticalGraphCoercivity
public import BecknerOnofri.LocalElevenCore.ReducedCubicParity

@[expose] public section

/-! The true reduced equation has an isolated zero at critical coupling. -/
noncomputable section

open Filter Asymptotics
open scoped Topology BigOperators
namespace BecknerOnofri.HighDim.LocalEleven.ReducedCubicExpansion

open BecknerOnofri.HighDim.ReducedCubicExpansion hiding U_cube_difference U_square_difference coordinates_U coordinates_center coordinates_const coordinates_quadraticTerm_difference coordinates_shellSquare cubicModel cubicModel_analytic cubicModel_apply cubicModel_diagonal cubicModel_neg cubicModel_norm_lower cubicTerm_assembly_analytic cubicTerm_difference quadraticCorrection_analytic quadraticCorrection_product_error realDiagonal realDiagonal_apply reduced_critical_norm_lower reduced_critical_zero_iff reduced_cubic_expansion reduced_cubic_expansion_fifth reduced_diagonal_cubic_expansion reduced_diagonal_cubic_expansion_fifth
open BecknerOnofri.HighDim.ReducedEquation hiding complementMap_assembly complementMap_reconstruction coordinates_complement coordinates_green coordinates_one coordinates_reconstruction full full_complement full_coordinates full_mean full_zero_iff graph_full_iff_reduced local_full_iff_reduced meanZero_zero_iff mean_green potential potential_analytic reduced reduced_analytic
open ContinuousFirstShell ReducedEquation

theorem cubicModel_norm_lower {d : ℕ} (hd : 11 ≤ d) (z : Coordinates d) :
    kappa d * ‖z‖^3 ≤ ‖cubicModel hd z‖ := by
  classical
  haveI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp (by omega : 0 < d)
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ (fun i : Fin d => ‖z i‖)
    Finset.univ_nonempty
  have hnorm : ‖z‖ = ‖z i‖ := le_antisymm
    ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr (fun j => hi j (Finset.mem_univ j)))
    (norm_le_pi_norm z i)
  have hs : (∑ j, ‖z j‖^2) ≤ (d:ℝ)*‖z i‖^2 := by
    have h := Finset.sum_le_sum (s := Finset.univ) (fun j hj =>
      pow_le_pow_left₀ (norm_nonneg (z j)) (hi j hj) 2)
    simpa using h
  let c : ℝ := -(2*quarticA d*‖z i‖^2 + quarticB d*((∑ j, ‖z j‖^2)-‖z i‖^2))
  have hc : kappa d*‖z i‖^2 ≤ c := by
    have hb := BecknerOnofri.HighDim.LocalQuartic.quarticB_positive hd
    have hk : 2*quarticA d + ((d:ℝ)-1)*quarticB d = -kappa d := by
      unfold kappa
      ring
    dsimp [c]
    nlinarith [mul_le_mul_of_nonneg_left hs hb.le,
      congrArg (fun x : ℝ => x*‖z i‖^2) hk]
  have hc0 : 0 ≤ c := (mul_nonneg (BecknerOnofri.HighDim.LocalQuartic.kappa_positive hd).le (sq_nonneg _)).trans hc
  have he : cubicModel hd z i = (c:ℂ)*z i := by
    rw [cubicModel_apply]
    dsimp [c]
    push_cast
    ring
  calc
    kappa d*‖z‖^3 = (kappa d*‖z i‖^2)*‖z i‖ := by rw [hnorm]; ring
    _ ≤ c*‖z i‖ := mul_le_mul_of_nonneg_right hc (norm_nonneg _)
    _ = ‖cubicModel hd z i‖ := by rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc0]
    _ ≤ ‖cubicModel hd z‖ := norm_le_pi_norm _ i

theorem reduced_critical_norm_lower {d : ℕ} (hd : 11 ≤ d) :
    ∀ᶠ z in 𝓝 (0 : Coordinates d), kappa d/2 * ‖z‖^3 ≤ ‖reduced hd (1,z)‖ := by
  have ho : (fun z => reduced hd (1,z) - cubicModel hd z)
      =o[𝓝 (0 : Coordinates d)] (fun z => ‖z‖^3) :=
    (reduced_cubic_expansion_fifth hd).trans_isLittleO
      (isLittleO_norm_pow_norm_pow (by decide : 3 < 5))
  filter_upwards [ho.bound (show 0 < kappa d/2 by have := BecknerOnofri.HighDim.LocalQuartic.kappa_positive hd; positivity)] with z hz
  simp only [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg z) 3)] at hz
  have ht : ‖cubicModel hd z‖ ≤ ‖reduced hd (1,z)‖ + ‖reduced hd (1,z) - cubicModel hd z‖ := by
    have h := norm_sub_le (reduced hd (1,z)) (reduced hd (1,z) - cubicModel hd z)
    simpa only [sub_sub_cancel] using h
  have hc := cubicModel_norm_lower hd z
  linarith

/-- No nonzero small first-shell vector solves the genuine critical reduced equation. -/
theorem reduced_critical_zero_iff {d : ℕ} (hd : 11 ≤ d) :
    ∀ᶠ z in 𝓝 (0 : Coordinates d), reduced hd (1,z) = 0 ↔ z = 0 := by
  filter_upwards [reduced_critical_norm_lower hd] with z hz
  constructor
  · intro he
    rw [he, norm_zero] at hz
    by_contra hn
    have hp : 0 < kappa d/2*‖z‖^3 :=
      mul_pos (by have := BecknerOnofri.HighDim.LocalQuartic.kappa_positive hd; positivity) (pow_pos (norm_pos_iff.mpr hn) 3)
    linarith
  · rintro rfl
    simp [reduced, potential, GreenLocalBranch.correction_base, ContinuousComplement.reconstruction,
      ContinuousGibbs.normalized_zero, coordinates_one]

#print axioms reduced_critical_norm_lower
#print axioms reduced_critical_zero_iff
end BecknerOnofri.HighDim.LocalEleven.ReducedCubicExpansion
