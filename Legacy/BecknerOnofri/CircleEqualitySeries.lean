module

public import Legacy.BecknerOnofri.WienerFourier
public import Legacy.BecknerOnofri.CosineMixtureAxis
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

@[expose] public section

/-! Actual two-sided Fourier series on the one-dimensional torus. -/
noncomputable section
open MeasureTheory Legacy.TorusEndpoint
open scoped BigOperators ComplexConjugate
namespace Legacy.BecknerOnofri.CircleEquality
set_option maxHeartbeats 800000

def frequency (j : ℤ) : Frequency 1 := fun _ => j

def integerCoefficient (a : ℕ → ℂ) : ℤ → ℂ
  | .ofNat n => a n
  | .negSucc n => conj (a (n + 1))

def coefficient (a : ℕ → ℂ) (k : Frequency 1) : ℂ := integerCoefficient a (k 0)

def series (a : ℕ → ℂ) : Torus 1 → ℂ := absoluteFourierSeries (coefficient a)

def character (x : Torus 1) : ℂ := UnitAddTorus.mFourier (frequency 1) x

@[simp] theorem frequency_zero : frequency 0 = 0 := rfl
@[simp] theorem frequency_neg (j : ℤ) : frequency (-j) = -frequency j := rfl
@[simp] theorem frequency_add (i j : ℤ) : frequency (i+j) = frequency i + frequency j := rfl
@[simp] theorem frequency_apply (j : ℤ) (i : Fin 1) : frequency j i = j := rfl

theorem frequency_eq (k : Frequency 1) : frequency (k 0) = k := by
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  simp [hi]

@[simp] theorem character_norm (x : Torus 1) : ‖character x‖ = 1 := mFourier_norm_apply _ _

theorem character_pow (n : ℕ) (x : Torus 1) :
    character x ^ n = UnitAddTorus.mFourier (frequency (n : ℤ)) x := by
  induction n with
  | zero => simp [UnitAddTorus.mFourier_zero]
  | succ n ih =>
    rw [pow_succ, ih]
    simp only [Nat.cast_add, Nat.cast_one, frequency_add, UnitAddTorus.mFourier_add]
    rfl

theorem character_pow_succ (n : ℕ) (x : Torus 1) :
    character x ^ (n + 1) = UnitAddTorus.mFourier (frequency ((n : ℤ) + 1)) x := by
  simpa using character_pow (n + 1) x

@[simp] theorem integerCoefficient_nat (a : ℕ → ℂ) (n : ℕ) :
    integerCoefficient a (n : ℤ) = a n := rfl

@[simp] theorem integerCoefficient_neg_succ (a : ℕ → ℂ) (n : ℕ) :
    integerCoefficient a (-(n+1 : ℤ)) = conj (a (n+1)) := rfl

theorem coefficient_summable (a : ℕ → ℂ) (ha : Summable (fun n => ‖a n‖)) :
    Summable (fun k => ‖coefficient a k‖) := by
  have hi : Summable (fun j : ℤ => ‖integerCoefficient a j‖) := by
    apply Summable.of_nat_of_neg_add_one
    · simpa only [integerCoefficient_nat] using ha
    · simpa only [integerCoefficient_neg_succ,
        Complex.norm_conj] using (summable_nat_add_iff 1).mpr ha
  exact CosineMixtureAxis.frequencyOneEquivInt.summable_iff.mpr hi

theorem series_continuous (a : ℕ → ℂ) (ha : Summable (fun n => ‖a n‖)) :
    Continuous (series a) := absoluteFourierSeries_continuous _ (coefficient_summable a ha)

theorem series_fourier (a : ℕ → ℂ) (ha : Summable (fun n => ‖a n‖)) (k : Frequency 1) :
    UnitAddTorus.mFourierCoeff (series a) k = coefficient a k :=
  absoluteFourierSeries_coefficient _ (coefficient_summable a ha) k

theorem series_integral (a : ℕ → ℂ) (ha : Summable (fun n => ‖a n‖)) :
    (∫ x, series a x ∂torusMeasure 1) = a 0 :=
  absoluteFourierSeries_integral _ (coefficient_summable a ha)

theorem series_eq (a : ℕ → ℂ) (ha : Summable (fun n => ‖a n‖)) (x : Torus 1) :
    series a x = (∑' n : ℕ, a n * character x ^ n) +
      conj (∑' n : ℕ, a n * character x ^ n) - conj (a 0) := by
  have hn : Summable (fun n : ℕ => a n * character x ^ n) := by
    apply ha.of_norm_bounded
    intro n
    simp only [norm_mul, norm_pow, character_norm, one_pow, mul_one, le_refl]
  have hs : Summable (fun n => conj (a n * character x ^ n)) :=
    hn.map (starRingEnd ℂ).toAddMonoidHom continuous_star
  have hi1 : Summable (fun n : ℕ =>
      integerCoefficient a (n : ℤ) * UnitAddTorus.mFourier (frequency (n : ℤ)) x) := by
    simpa only [integerCoefficient_nat, ← character_pow] using hn
  have hi2 : Summable (fun n : ℕ =>
      integerCoefficient a (-(n+1 : ℤ)) *
        UnitAddTorus.mFourier (frequency (-(n+1 : ℤ))) x) := by
    simpa only [integerCoefficient_neg_succ, frequency_neg, UnitAddTorus.mFourier_neg,
      ← character_pow_succ, ← map_mul] using (summable_nat_add_iff 1).mpr hs
  have hfull : series a x = ∑' j : ℤ, integerCoefficient a j *
      UnitAddTorus.mFourier (frequency j) x := by
    unfold series absoluteFourierSeries coefficient
    exact (CosineMixtureAxis.frequencyOneEquivInt.symm.tsum_eq _).symm
  rw [hfull, tsum_of_nat_of_neg_add_one
    (f := fun j : ℤ => integerCoefficient a j * UnitAddTorus.mFourier (frequency j) x) hi1 hi2]
  simp only [integerCoefficient_nat, ← character_pow]
  have hneg : (∑' n : ℕ, integerCoefficient a (-(n+1 : ℤ)) *
      UnitAddTorus.mFourier (frequency (-(n+1 : ℤ))) x) =
      conj (∑' n : ℕ, a n * character x ^ n) - conj (a 0) := by
    have ht := hs.tsum_eq_zero_add
    simp only [pow_zero, mul_one] at ht
    rw [← Complex.conj_tsum] at ht
    rw [eq_sub_iff_add_eq]
    rw [add_comm]
    convert! ht.symm using 1
    apply congrArg (fun z => conj (a 0) + z)
    apply tsum_congr
    intro n
    simp only [integerCoefficient_neg_succ, frequency_neg, UnitAddTorus.mFourier_neg,
      ← character_pow_succ, map_mul]
  rw [hneg]
  ring

#print axioms series_eq
#print axioms series_fourier
end Legacy.BecknerOnofri.CircleEquality
