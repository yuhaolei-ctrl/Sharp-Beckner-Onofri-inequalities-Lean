module

public import BecknerOnofri.ContinuousComplementInverse

@[expose] public section

/-! Actual finite Fourier expansion of the square of the full first shell. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators ComplexConjugate
open Classical
namespace BecknerOnofri.HighDim.QuadraticModes
open ContinuousGibbs ContinuousFirstShell

theorem synthesis_mul {d : ℕ} (k l : Frequency d) (z w : ℂ) :
    synthesis k z * synthesis l w =
      synthesis (k+l) (z*w) + synthesis (k-l) (z*conj w) := by
  ext x
  simp only [ContinuousMap.mul_apply, ContinuousMap.add_apply, synthesis_apply,
    sub_eq_add_neg, UnitAddTorus.mFourier_add, UnitAddTorus.mFourier_neg]
  simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

/-- The actual square of the full 2d-dimensional real first shell. -/
def shellSquare {d : ℕ} (z : Coordinates d) : Space d := (assembly d z)^2

theorem shellSquare_expansion {d : ℕ} (z : Coordinates d) :
    shellSquare z = ∑ i : Fin d, ∑ j : Fin d,
      (synthesis (axisFrequency i + axisFrequency j) (z i*z j) +
       synthesis (axisFrequency i - axisFrequency j) (z i*conj (z j))) := by
  simp only [shellSquare, pow_two, assembly_apply, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_comm]
  exact synthesis_mul _ _ _ _

/-- Exact coefficients, with no finite-support or spectral hypothesis on the input parameters. -/
theorem shellSquare_coefficient {d : ℕ} (z : Coordinates d) (k : Frequency d) :
    coefficient k (shellSquare z) = ∑ i : Fin d, ∑ j : Fin d,
      ((if k = axisFrequency i + axisFrequency j then z i*z j else 0) +
       (if k = -(axisFrequency i + axisFrequency j) then conj (z i*z j) else 0) +
       ((if k = axisFrequency i - axisFrequency j then z i*conj (z j) else 0) +
        (if k = -(axisFrequency i - axisFrequency j) then conj (z i*conj (z j)) else 0))) := by
  rw [shellSquare_expansion]
  simp only [map_sum, map_add, coefficient_synthesis]

/-- All possible frequencies in an actual squared first-shell function. -/
def QuadraticFrequency {d : ℕ} (k : Frequency d) : Prop :=
  ∃ i j : Fin d, k = axisFrequency i + axisFrequency j ∨
    k = -(axisFrequency i + axisFrequency j) ∨ k = axisFrequency i - axisFrequency j

theorem shellSquare_support {d : ℕ} (z : Coordinates d) (k : Frequency d)
    (hk : ¬ QuadraticFrequency k) : coefficient k (shellSquare z) = 0 := by
  classical
  rw [shellSquare_coefficient]
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  have h₁ : k ≠ axisFrequency i + axisFrequency j := fun h => hk ⟨i,j,Or.inl h⟩
  have h₂ : k ≠ -(axisFrequency i + axisFrequency j) := fun h => hk ⟨i,j,Or.inr (Or.inl h)⟩
  have h₃ : k ≠ axisFrequency i - axisFrequency j := fun h => hk ⟨i,j,Or.inr (Or.inr h)⟩
  have h₄ : k ≠ -(axisFrequency i - axisFrequency j) := by
    intro h
    apply hk
    exact ⟨j,i, Or.inr (Or.inr (by simpa only [neg_sub] using h))⟩
  simp only [if_neg h₁, if_neg h₂, if_neg h₃, if_neg h₄, add_zero]

theorem complementMap_coefficient {d : ℕ} (f : Space d) (k : Frequency d) :
    coefficient k (complementMap d f).val =
      if ComplementFrequency k then coefficient k f else 0 := by
  classical
  by_cases hk : ComplementFrequency k
  · rw [if_pos hk, complementMap_coe, complementProjection_apply, map_sub, map_sub,
      meanProjection_apply, coefficient_const, if_neg hk.1,
      coefficient_projection_off_shell f k hk.2, sub_zero, sub_zero]
  · rw [if_neg hk]
    exact (mem_complement_fourier_iff (complementMap d f).val).mp
      (complementMap d f).property k hk

/-- Actual quadratic source for the complement equation. -/
def quadraticSource {d : ℕ} (z : Coordinates d) : complement d := complementMap d (shellSquare z)

@[simp] theorem quadraticSource_coefficient {d : ℕ} (z : Coordinates d) (k : Frequency d) :
    coefficient k (quadraticSource z).val =
      if ComplementFrequency k then coefficient k (shellSquare z) else 0 :=
  complementMap_coefficient _ _

#print axioms shellSquare_coefficient
#print axioms shellSquare_support
end BecknerOnofri.HighDim.QuadraticModes
