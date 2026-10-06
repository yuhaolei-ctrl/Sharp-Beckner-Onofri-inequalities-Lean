module

public import BecknerOnofri.LocalElevenContinuousInverse
public import BecknerOnofri.QuadraticSchur
public import BecknerOnofri.LocalElevenCore.QuadraticResolvent

@[expose] public section

/-! Exact quartic Schur contribution of the genuine quadratic slaved mode. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators ComplexConjugate

open Classical
namespace BecknerOnofri.HighDim.LocalEleven.QuadraticModes

open BecknerOnofri.HighDim.QuadraticModes hiding complementGreen_synthesis complementMap_synthesis complementMap_synthesis_zero complementSynthesis green_synthesis mixedAmplitudeSum off_diagonal_sum quadraticSource_expansion quadratic_schur_identity resolvent resolventPair resolventPair_apply resolventPair_synthesis resolvent_synthesis schur_diagonal schur_double_sum schur_off_diagonal synthesis_mem_complement

open ContinuousGibbs ContinuousFirstShell

def resolventPair {d : ℕ} (hd : 11 ≤ d) (f : complement d) : complement d →L[ℝ] ℝ :=
  (pairing f.val).comp ((complement d).subtypeL.comp (resolvent hd))

@[simp] theorem resolventPair_apply {d : ℕ} (hd : 11 ≤ d) (f g : complement d) :
    resolventPair hd f g = pairing f.val (resolvent hd g).val := rfl

theorem resolventPair_synthesis {d : ℕ} (hd : 11 ≤ d) (f : complement d)
    {k : Frequency d} (hk : ComplementFrequency k) (z : ℂ) :
    resolventPair hd f (complementMap d (synthesis k z)) =
      (1/(frequencyLength k^d-1))*pairing f.val (synthesis k z) := by
  rw [complementMap_synthesis hk, resolventPair_apply, resolvent_synthesis]
  change pairing f.val ((1/(frequencyLength k^d-1)) • synthesis k z) = _
  rw [map_smul, smul_eq_mul]

theorem schur_diagonal {d : ℕ} (hd : 11 ≤ d) (z : Coordinates d) (i : Fin d) :
    resolventPair hd (quadraticSource z)
      (complementMap d (synthesis (axisFrequency i+axisFrequency i) (z i*z i)) +
       complementMap d (synthesis (axisFrequency i-axisFrequency i) (z i*conj (z i)))) =
      (2/((2:ℝ)^d-1))*‖z i‖^4 := by
  rw [sub_self, complementMap_synthesis_zero, add_zero]
  rw [resolventPair_synthesis hd _ (complement_double i), eigenvalue_double, ← pow_two, pairing_double]
  ring

theorem schur_off_diagonal {d : ℕ} (hd : 11 ≤ d) (z : Coordinates d)
    {i j : Fin d} (hij : i ≠ j) :
    resolventPair hd (quadraticSource z)
      (complementMap d (synthesis (axisFrequency i+axisFrequency j) (z i*z j)) +
       complementMap d (synthesis (axisFrequency i-axisFrequency j) (z i*conj (z j)))) =
      (8/((2:ℝ)^((d:ℝ)/2)-1))*‖z i‖^2*‖z j‖^2 := by
  rw [map_add, resolventPair_synthesis hd _ (complement_sum hij),
    resolventPair_synthesis hd _ (complement_diff hij), eigenvalue_sum hij,
    eigenvalue_diff hij, pairing_sum z hij, pairing_diff z hij]
  ring

theorem schur_double_sum {d : ℕ} (hd : 11 ≤ d) (z : Coordinates d) :
    resolventPair hd (quadraticSource z) (quadraticSource z) =
      ∑ i : Fin d, ∑ j : Fin d, if i=j then (2/((2:ℝ)^d-1))*‖z i‖^4
        else (8/((2:ℝ)^((d:ℝ)/2)-1))*‖z i‖^2*‖z j‖^2 := by
  conv_lhs => arg 2; rw [quadraticSource_expansion]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i=j
  · subst j
    rw [if_pos rfl]
    exact schur_diagonal hd z i
  · rw [if_neg hij]
    exact schur_off_diagonal hd z hij

/-- The source's unordered mixed-amplitude sum. -/
def mixedAmplitudeSum {d : ℕ} (z : Coordinates d) : ℝ :=
  ∑ i : Fin d, ∑ j ∈ Finset.univ.filter (fun j : Fin d => i < j), ‖z i‖^2*‖z j‖^2

theorem off_diagonal_sum {d : ℕ} (z : Coordinates d) :
    (∑ i : Fin d, ∑ j : Fin d, if i=j then 0 else ‖z i‖^2*‖z j‖^2) =
      2*mixedAmplitudeSum z := by
  have hp (i j : Fin d) : (if i=j then 0 else ‖z i‖^2*‖z j‖^2) =
      (if i < j then ‖z i‖^2*‖z j‖^2 else 0) +
      (if j < i then ‖z i‖^2*‖z j‖^2 else 0) := by
    rcases lt_trichotomy i j with h|h|h
    · simp [h, ne_of_lt h, not_lt_of_ge h.le]
    · subst j
      simp
    · simp [h, ne_of_gt h, not_lt_of_ge h.le]
  simp only [hp, Finset.sum_add_distrib]
  have hs : (∑ i : Fin d, ∑ j : Fin d, if j < i then ‖z i‖^2*‖z j‖^2 else 0) =
      ∑ i : Fin d, ∑ j : Fin d, if i < j then ‖z i‖^2*‖z j‖^2 else 0 := by
    rw [Finset.sum_comm]
    simp only [mul_comm]
  rw [hs]
  unfold mixedAmplitudeSum
  simp only [Finset.sum_filter]
  ring

/-- Exact source formula, in the actual continuous Haar pairing and actual inverse (D−I)⁻¹. -/
theorem quadratic_schur_identity {d : ℕ} (hd : 11 ≤ d) (z : Coordinates d) :
    pairing (quadraticSource z).val (resolvent hd (quadraticSource z)).val =
      (2/((2:ℝ)^d-1)) * (∑ i : Fin d, ‖z i‖^4) +
      (16/((2:ℝ)^((d:ℝ)/2)-1)) * mixedAmplitudeSum z := by
  change resolventPair hd (quadraticSource z) (quadraticSource z) = _
  rw [schur_double_sum]
  have hp (i j : Fin d) :
      (if i=j then (2/((2:ℝ)^d-1))*‖z i‖^4 else
        (8/((2:ℝ)^((d:ℝ)/2)-1))*‖z i‖^2*‖z j‖^2) =
      (if i=j then (2/((2:ℝ)^d-1))*‖z i‖^4 else 0) +
      (8/((2:ℝ)^((d:ℝ)/2)-1))*(if i=j then 0 else ‖z i‖^2*‖z j‖^2) := by
    by_cases h : i=j <;> simp [h] <;> ring
  simp only [hp, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    ← Finset.mul_sum, ← mul_assoc]
  rw [off_diagonal_sum]
  simp
  simp only [← Finset.mul_sum, ← Finset.sum_mul]
  ring

#print axioms quadratic_schur_identity
end BecknerOnofri.HighDim.LocalEleven.QuadraticModes
