import BecknerOnofri.ReducedQuarticParity
import BecknerOnofri.QuarticBranches

/-! Strict local negativity of the actual physical critical reduced energy,
with a uniform quartic norm bound. -/
noncomputable section
open Filter Asymptotics
open scoped Topology BigOperators
namespace BecknerOnofri.HighDim.ReducedPhysicalEnergy
open ContinuousFirstShell ReducedQuarticExpansion QuadraticModes

theorem quarticValue_eq_reducedQuartic {d : ℕ} (z : Coordinates d) :
    quarticValue z = reducedQuartic d 0 (fun i => ‖z i‖^2) := by
  have h := amplitude_sum_square z
  unfold quarticValue reducedQuartic
  simp only [zero_mul, zero_add, ← pow_mul, show 2*2=4 from rfl]
  rw [h]
  ring

theorem norm_fourth_le_sum {d : ℕ} (hd : 0 < d) (z : Coordinates d) :
    ‖z‖^4 ≤ ∑ i, ‖z i‖^4 := by
  classical
  haveI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ (fun i : Fin d => ‖z i‖)
    Finset.univ_nonempty
  have hnorm : ‖z‖ ≤ ‖z i‖ :=
    (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr (fun j => hi j (Finset.mem_univ j))
  exact (pow_le_pow_left₀ (norm_nonneg z) hnorm 4).trans
    (Finset.single_le_sum (fun j _ => pow_nonneg (norm_nonneg (z j)) 4) (Finset.mem_univ i))

theorem quarticValue_coercive {d : ℕ} (hd : 12 ≤ d) (z : Coordinates d) :
    quarticValue z ≤ -(kappa d / 2) * ‖z‖^4 := by
  have h := reducedQuartic_coercive hd 0 (fun i => ‖z i‖^2)
  rw [← quarticValue_eq_reducedQuartic] at h
  simp only [zero_pow (by decide : 2 ≠ 0), mul_zero, zero_div, sub_zero,
    zero_sub, ← pow_mul, show 2*2=4 from rfl] at h
  have hs := norm_fourth_le_sum (by omega : 0 < d) z
  have hk := kappa_pos d hd
  nlinarith

/-- At critical coupling the exact reduced energy is bounded above by a
strict negative quartic, throughout one neighborhood of zero. -/
theorem criticalReducedEnergy_coercive {d : ℕ} (hd : 12 ≤ d) :
    ∀ᶠ z in 𝓝 (0 : Coordinates d),
      criticalReducedEnergy hd z ≤ -(kappa d / 4) * ‖z‖^4 := by
  have ho : (fun z => criticalReducedEnergy hd z - quarticValue z)
      =o[𝓝 (0 : Coordinates d)] (fun z => ‖z‖^4) :=
    (criticalReducedEnergy_quartic_sixth hd).trans_isLittleO
      (isLittleO_norm_pow_norm_pow (by decide : 4 < 6))
  have hk := kappa_pos d hd
  filter_upwards [ho.bound (show 0 < kappa d / 4 by positivity)] with z hz
  have hab : criticalReducedEnergy hd z - quarticValue z ≤ kappa d / 4 * ‖z‖^4 := by
    have hh : |criticalReducedEnergy hd z - quarticValue z| ≤ kappa d / 4 * ‖z‖^4 := by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg z) 4)] using hz
    exact (le_abs_self _).trans hh
  have hq := quarticValue_coercive hd z
  linarith

theorem criticalReducedEnergy_strictly_negative {d : ℕ} (hd : 12 ≤ d) :
    ∀ᶠ z in 𝓝 (0 : Coordinates d), z ≠ 0 → criticalReducedEnergy hd z < 0 := by
  filter_upwards [criticalReducedEnergy_coercive hd] with z hz
  intro hne
  exact hz.trans_lt (mul_neg_of_neg_of_pos (by have := kappa_pos d hd; linarith)
    (pow_pos (norm_pos_iff.mpr hne) 4))

#print axioms criticalReducedEnergy_coercive
#print axioms criticalReducedEnergy_strictly_negative
end BecknerOnofri.HighDim.ReducedPhysicalEnergy
