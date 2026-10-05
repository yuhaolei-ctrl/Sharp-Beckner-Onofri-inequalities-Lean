module

public import BecknerOnofri.CriticalGraphCoercivity
public import BecknerOnofri.ReducedCubicParity

@[expose] public section

/-! The true reduced equation has an isolated zero at critical coupling. -/
noncomputable section
open Filter Asymptotics
open scoped Topology BigOperators
namespace BecknerOnofri.HighDim.ReducedCubicExpansion
open ContinuousFirstShell ReducedEquation

theorem cubicModel_norm_lower {d : ℕ} (hd : 12 ≤ d) (z : Coordinates d) :
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
    have hb := quarticB_pos hd
    have hk : 2*quarticA d + ((d:ℝ)-1)*quarticB d = -kappa d := by
      unfold kappa
      ring
    dsimp [c]
    nlinarith [mul_le_mul_of_nonneg_left hs hb.le,
      congrArg (fun x : ℝ => x*‖z i‖^2) hk]
  have hc0 : 0 ≤ c := (mul_nonneg (kappa_pos d hd).le (sq_nonneg _)).trans hc
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

theorem reduced_critical_norm_lower {d : ℕ} (hd : 12 ≤ d) :
    ∀ᶠ z in 𝓝 (0 : Coordinates d), kappa d/2 * ‖z‖^3 ≤ ‖reduced hd (1,z)‖ := by
  have ho : (fun z => reduced hd (1,z) - cubicModel hd z)
      =o[𝓝 (0 : Coordinates d)] (fun z => ‖z‖^3) :=
    (reduced_cubic_expansion_fifth hd).trans_isLittleO
      (isLittleO_norm_pow_norm_pow (by decide : 3 < 5))
  filter_upwards [ho.bound (show 0 < kappa d/2 by have := kappa_pos d hd; positivity)] with z hz
  simp only [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg z) 3)] at hz
  have ht : ‖cubicModel hd z‖ ≤ ‖reduced hd (1,z)‖ + ‖reduced hd (1,z) - cubicModel hd z‖ := by
    have h := norm_sub_le (reduced hd (1,z)) (reduced hd (1,z) - cubicModel hd z)
    simpa only [sub_sub_cancel] using h
  have hc := cubicModel_norm_lower hd z
  linarith

/-- No nonzero small first-shell vector solves the genuine critical reduced equation. -/
theorem reduced_critical_zero_iff {d : ℕ} (hd : 12 ≤ d) :
    ∀ᶠ z in 𝓝 (0 : Coordinates d), reduced hd (1,z) = 0 ↔ z = 0 := by
  filter_upwards [reduced_critical_norm_lower hd] with z hz
  constructor
  · intro he
    rw [he, norm_zero] at hz
    by_contra hn
    have hp : 0 < kappa d/2*‖z‖^3 :=
      mul_pos (by have := kappa_pos d hd; positivity) (pow_pos (norm_pos_iff.mpr hn) 3)
    linarith
  · rintro rfl
    simp [reduced, potential, GreenLocalBranch.correction_base, ContinuousComplement.reconstruction,
      ContinuousGibbs.normalized_zero, coordinates_one]

#print axioms reduced_critical_norm_lower
#print axioms reduced_critical_zero_iff
end BecknerOnofri.HighDim.ReducedCubicExpansion
