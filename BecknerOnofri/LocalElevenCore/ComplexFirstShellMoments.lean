import BecknerOnofri.LocalElevenContinuousInverse
import BecknerOnofri.ComplexFirstShellMoments
import BecknerOnofri.LocalElevenCore.QuadraticSlavingBridge

/-! Exact second, third and fourth moments of the full complex-coordinate first shell. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators ComplexConjugate

open Classical
namespace BecknerOnofri.HighDim.LocalEleven.QuadraticModes

open BecknerOnofri.HighDim.QuadraticModes hiding actual_quartic_coefficients amplitude_sum_square assembly_fourth_moment assembly_quartic_cumulant assembly_second_moment assembly_third_moment complementGreen_synthesis complementMap_center complementMap_const complementMap_synthesis complementMap_synthesis_zero complementSynthesis green_complementMap green_synthesis inverseGreen_factor mixedAmplitudeSum off_diagonal_sum quadraticCorrection_eq_resolvent quadraticSource_expansion quadraticSource_value quadratic_schur_identity quartic_slaving_contribution resolvent resolventPair resolventPair_apply resolventPair_synthesis resolvent_synthesis schur_diagonal schur_double_sum schur_off_diagonal shellSquare_first_coefficient shellSquare_mean shellSquare_projection sourcePair sourcePair_diagonal sourcePair_off_diagonal source_norm_moment source_norm_sq synthesis_mem_complement

open ContinuousGibbs ContinuousFirstShell

theorem shellSquare_first_coefficient {d : ℕ} (z : Coordinates d) (i : Fin d) :
    coefficient (axisFrequency i) (shellSquare z) = 0 := by
  apply shellSquare_support
  rintro ⟨j,k,h|h|h⟩ <;>
    have hh := congrArg (fun a : Frequency d => ∑ l, a l) h <;>
    simp [Finset.sum_add_distrib, Finset.sum_sub_distrib] at hh

theorem shellSquare_projection {d : ℕ} (z : Coordinates d) : projection d (shellSquare z) = 0 :=
  (projection_zero_iff _).mpr (shellSquare_first_coefficient z)

theorem shellSquare_mean {d : ℕ} (z : Coordinates d) :
    mean d (shellSquare z) = 2 * ∑ i : Fin d, ‖z i‖^2 := by
  apply Complex.ofReal_injective
  rw [← coefficient_zero, shellSquare_coefficient]
  have hn (i j : Fin d) : (0 : Frequency d) ≠ -(axisFrequency i+axisFrequency j) := by
    intro h
    apply sum_ne_zero i j
    simpa only [neg_zero, neg_neg] using congrArg Neg.neg h.symm
  simp only [if_neg (Ne.symm (sum_ne_zero _ _)), if_neg (hn _ _), zero_add,
    neg_sub, zero_eq_diff_iff, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  simp
  have hr (i : Fin d) : z i * conj (z i) + conj (z i) * z i =
      ((2 * ‖z i‖^2 : ℝ):ℂ) := by
    rw [mul_comm (z i), ← Complex.normSq_eq_conj_mul_self]
    simp only [Complex.normSq_eq_norm_sq]
    push_cast
    ring
  rw [← Finset.sum_add_distrib]
  simp only [hr, ← Complex.ofReal_sum, ← Finset.mul_sum]
  push_cast
  rfl

theorem assembly_second_moment {d : ℕ} (z : Coordinates d) :
    mean d ((assembly d z)^2) = 2 * ∑ i : Fin d, ‖z i‖^2 := shellSquare_mean z

theorem assembly_third_moment {d : ℕ} (z : Coordinates d) : mean d ((assembly d z)^3) = 0 := by
  have h : (assembly d z)^3 = shellSquare z * assembly d z := by
    unfold shellSquare
    ring
  rw [h, ← pairing_apply, assembly_apply, map_sum]
  apply Finset.sum_eq_zero
  intro i _
  rw [pairing_synthesis, shellSquare_first_coefficient]
  simp

theorem quadraticSource_value {d : ℕ} (z : Coordinates d) :
    (quadraticSource z).val = shellSquare z - ContinuousMap.const (Torus d) (mean d (shellSquare z)) := by
  change complementProjection d (shellSquare z) = _
  rw [complementProjection_apply, meanProjection_apply, shellSquare_projection, sub_zero]

def sourcePair {d : ℕ} (z : Coordinates d) : complement d →L[ℝ] ℝ :=
  (pairing (quadraticSource z).val).comp (complement d).subtypeL

theorem sourcePair_diagonal {d : ℕ} (z : Coordinates d) (i : Fin d) :
    sourcePair z
      (complementMap d (synthesis (axisFrequency i+axisFrequency i) (z i*z i)) +
       complementMap d (synthesis (axisFrequency i-axisFrequency i) (z i*conj (z i)))) = 2*‖z i‖^4 := by
  rw [sub_self, complementMap_synthesis_zero, add_zero, complementMap_synthesis (complement_double i)]
  change pairing (quadraticSource z).val (synthesis _ (z i*z i)) = _
  rw [← pow_two, pairing_double]

theorem sourcePair_off_diagonal {d : ℕ} (z : Coordinates d) {i j : Fin d} (hij : i ≠ j) :
    sourcePair z
      (complementMap d (synthesis (axisFrequency i+axisFrequency j) (z i*z j)) +
       complementMap d (synthesis (axisFrequency i-axisFrequency j) (z i*conj (z j)))) =
      8*‖z i‖^2*‖z j‖^2 := by
  rw [map_add, complementMap_synthesis (complement_sum hij), complementMap_synthesis (complement_diff hij)]
  change pairing (quadraticSource z).val (synthesis _ (z i*z j)) +
    pairing (quadraticSource z).val (synthesis _ (z i*conj (z j))) = _
  rw [pairing_sum z hij, pairing_diff z hij]
  ring

theorem source_norm_sq {d : ℕ} (z : Coordinates d) :
    pairing (quadraticSource z).val (quadraticSource z).val =
      2*(∑ i : Fin d, ‖z i‖^4) + 16*mixedAmplitudeSum z := by
  change sourcePair z (quadraticSource z) = _
  rw [quadraticSource_expansion, map_sum]
  have hp (i j : Fin d) : sourcePair z
      (complementMap d (synthesis (axisFrequency i+axisFrequency j) (z i*z j)) +
       complementMap d (synthesis (axisFrequency i-axisFrequency j) (z i*conj (z j)))) =
      (if i=j then 2*‖z i‖^4 else 0) + 8*(if i=j then 0 else ‖z i‖^2*‖z j‖^2) := by
    by_cases h : i=j
    · subst j
      rw [if_pos rfl, if_pos rfl, mul_zero, add_zero, sourcePair_diagonal]
    · rw [if_neg h, if_neg h, zero_add, sourcePair_off_diagonal z h]
      ring
  simp_rw [map_sum]
  simp only [hp, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [off_diagonal_sum]
  simp
  simp only [← Finset.mul_sum]
  ring

theorem amplitude_sum_square {d : ℕ} (z : Coordinates d) :
    (∑ i : Fin d, ‖z i‖^2)^2 = (∑ i : Fin d, ‖z i‖^4) + 2*mixedAmplitudeSum z := by
  have hp (i j : Fin d) : ‖z i‖^2*‖z j‖^2 =
      (if i=j then ‖z i‖^4 else 0) + (if i=j then 0 else ‖z i‖^2*‖z j‖^2) := by
    by_cases h : i=j <;> simp [h] <;> ring
  rw [pow_two, Finset.sum_mul]
  simp only [Finset.mul_sum]
  calc
    _ = ∑ i : Fin d, ∑ j : Fin d,
        ((if i=j then ‖z i‖^4 else 0) + (if i=j then 0 else ‖z i‖^2*‖z j‖^2)) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact hp i j
    _ = _ := by
      simp only [Finset.sum_add_distrib]
      rw [off_diagonal_sum]
      simp

theorem source_norm_moment {d : ℕ} (z : Coordinates d) :
    pairing (quadraticSource z).val (quadraticSource z).val =
      mean d ((assembly d z)^4) - (mean d (shellSquare z))^2 := by
  have h : (quadraticSource z).val * (quadraticSource z).val =
      (assembly d z)^4 - (2*mean d (shellSquare z)) • shellSquare z +
        ContinuousMap.const (Torus d) ((mean d (shellSquare z))^2) := by
    rw [quadraticSource_value]
    ext x
    simp only [ContinuousMap.mul_apply, ContinuousMap.sub_apply, ContinuousMap.pow_apply,
      ContinuousMap.add_apply, ContinuousMap.const_apply, ContinuousMap.smul_apply,
      smul_eq_mul, shellSquare]
    ring
  rw [pairing_apply, h, map_add, map_sub, map_smul, mean_const]
  change mean d ((assembly d z)^4) - (2*mean d (shellSquare z))*mean d (shellSquare z) +
    mean d (shellSquare z)^2 = _
  ring

/-- Exact fourth moment for every complex first-shell parameter vector. -/
theorem assembly_fourth_moment {d : ℕ} (z : Coordinates d) :
    mean d ((assembly d z)^4) = 12*(∑ i : Fin d, ‖z i‖^2)^2 - 6*(∑ i : Fin d, ‖z i‖^4) := by
  have h := source_norm_moment z
  rw [source_norm_sq, shellSquare_mean] at h
  have hs := amplitude_sum_square z
  nlinarith

/-- The actual first-shell fourth cumulant is strictly diagonal. -/
theorem assembly_quartic_cumulant {d : ℕ} (z : Coordinates d) :
    mean d ((assembly d z)^4)/24 - (mean d ((assembly d z)^2))^2/8 =
      -(1/4:ℝ)*(∑ i : Fin d, ‖z i‖^4) := by
  rw [assembly_fourth_moment, assembly_second_moment]
  ring

/-- Actual cumulant plus exact Schur term gives the two coefficients in the source. -/
theorem actual_quartic_coefficients {d : ℕ} (hd : 11 ≤ d) (z : Coordinates d) :
    mean d ((assembly d z)^4)/24 - (mean d ((assembly d z)^2))^2/8 +
      (1/8:ℝ)*pairing (quadraticSource z).val (resolvent hd (quadraticSource z)).val =
      quarticA d * (∑ i : Fin d, ‖z i‖^4) + quarticB d * mixedAmplitudeSum z := by
  rw [assembly_quartic_cumulant, quartic_slaving_contribution]
  unfold quarticA quarticB
  ring

#print axioms assembly_second_moment
#print axioms assembly_third_moment
#print axioms source_norm_sq
#print axioms assembly_fourth_moment
#print axioms actual_quartic_coefficients
end BecknerOnofri.HighDim.LocalEleven.QuadraticModes
