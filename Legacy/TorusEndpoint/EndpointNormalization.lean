import Legacy.TorusEndpoint.TorusFourier
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# The exact normalization of the proposed endpoint

The radius is the Euclidean lattice radius, explicitly the square root of
the sum of coordinate squares (not the sup norm on a function space).
These definitions do not assert an endpoint inequality or identify a
singular Green kernel with its Fourier series.
-/

open scoped BigOperators

namespace Legacy.TorusEndpoint

noncomputable def frequencyRadius {d : ℕ} (k : Frequency d) : ℝ :=
  Real.sqrt (∑ j : Fin d, (k j : ℝ) ^ 2)

noncomputable def endpointSigma (d : ℕ) : ℝ :=
  2 * Real.pi ^ ((d : ℝ) / 2) / Real.Gamma ((d : ℝ) / 2)

noncomputable def endpointCoupling (d : ℕ) : ℝ :=
  2 * (d : ℝ) / endpointSigma d

/-- The positive-cone atom weight λ_d / |k|^d. -/
noncomputable def endpointAtomWeight (d : ℕ) (k : Frequency d) : ℝ :=
  endpointCoupling d / frequencyRadius k ^ d

/-- The reciprocal atom weight used on the right of the exponential inequality. -/
noncomputable def endpointDualWeight (d : ℕ) (k : Frequency d) : ℝ :=
  frequencyRadius k ^ d / endpointCoupling d

theorem frequencyRadius_nonneg {d : ℕ} (k : Frequency d) :
    0 ≤ frequencyRadius k := Real.sqrt_nonneg _

theorem frequencyRadius_pos {d : ℕ} {k : Frequency d} (hk : k ≠ 0) :
    0 < frequencyRadius k := by
  classical
  have hn : ∃ j : Fin d, k j ≠ 0 := by
    by_contra h
    push Not at h
    exact hk (funext h)
  obtain ⟨j, hj⟩ := hn
  apply Real.sqrt_pos.mpr
  apply Finset.sum_pos'
  · intro i _
    exact sq_nonneg _
  · exact ⟨j, Finset.mem_univ j, sq_pos_of_ne_zero (by exact_mod_cast hj)⟩

@[simp] theorem frequencyRadius_neg {d : ℕ} (k : Frequency d) :
    frequencyRadius (-k) = frequencyRadius k := by
  simp [frequencyRadius]

@[simp] theorem frequencyRadius_zero (d : ℕ) :
    frequencyRadius (0 : Frequency d) = 0 := by
  simp [frequencyRadius]

theorem endpointSigma_pos {d : ℕ} (hd : 0 < d) : 0 < endpointSigma d := by
  have hdr : 0 < (d : ℝ) := Nat.cast_pos.mpr hd
  exact div_pos (mul_pos (by norm_num) (Real.rpow_pos_of_pos Real.pi_pos _))
    (Real.Gamma_pos_of_pos (div_pos hdr (by norm_num)))

theorem endpointCoupling_pos {d : ℕ} (hd : 0 < d) :
    0 < endpointCoupling d := by
  exact div_pos (mul_pos (by norm_num) (Nat.cast_pos.mpr hd)) (endpointSigma_pos hd)

theorem endpointCoupling_half (d : ℕ) :
    endpointCoupling d / 2 = (d : ℝ) / endpointSigma d := by
  unfold endpointCoupling
  ring

theorem endpointAtomWeight_pos {d : ℕ} (hd : 0 < d)
    {k : Frequency d} (hk : k ≠ 0) : 0 < endpointAtomWeight d k :=
  div_pos (endpointCoupling_pos hd) (pow_pos (frequencyRadius_pos hk) _)

theorem endpointDualWeight_pos {d : ℕ} (hd : 0 < d)
    {k : Frequency d} (hk : k ≠ 0) : 0 < endpointDualWeight d k :=
  div_pos (pow_pos (frequencyRadius_pos hk) _) (endpointCoupling_pos hd)

@[simp] theorem endpointAtomWeight_neg (d : ℕ) (k : Frequency d) :
    endpointAtomWeight d (-k) = endpointAtomWeight d k := by
  simp [endpointAtomWeight]

@[simp] theorem endpointDualWeight_neg (d : ℕ) (k : Frequency d) :
    endpointDualWeight d (-k) = endpointDualWeight d k := by
  simp [endpointDualWeight]

theorem endpointDualWeight_eq_inv (d : ℕ) (k : Frequency d) :
    endpointDualWeight d k = (endpointAtomWeight d k)⁻¹ := by
  simp [endpointDualWeight, endpointAtomWeight]

end Legacy.TorusEndpoint
