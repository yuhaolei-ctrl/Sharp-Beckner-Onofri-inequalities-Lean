import BecknerOnofri.LocalElevenContinuousInverse
import BecknerOnofri.GreenCritical
import BecknerOnofri.LocalElevenContinuousInverse
import BecknerOnofri.LocalElevenCore.ReducedEquation

/-! Critical Sobolev regularity of actual continuous Green potentials. -/
noncomputable section

open MeasureTheory
open scoped BigOperators
namespace BecknerOnofri.HighDim.LocalEleven.GreenCritical

open BecknerOnofri.HighDim.GreenCritical hiding coefficient_square_summable green_inCriticalSobolev nonzero_eigenvalue_ge_one potentialTerm_green

open ContinuousGibbs ContinuousFirstShell

/-- Parseval summability of the actual continuous Fourier coefficients. -/
theorem coefficient_square_summable {d : ℕ} (f : Space d) :
    Summable (fun k : Frequency d => ‖coefficient k f‖^2) := by
  have h := lp.summable_mul (by simpa using Real.HolderConjugate.two_two)
    (continuousFourier d f) (continuousFourier d f)
  simpa only [continuousFourier_apply, pow_two] using h

theorem nonzero_eigenvalue_ge_one {d : ℕ} (k : NonzeroFrequency d) :
    1 ≤ frequencyLength k.val^d := by
  rw [frequencyLength_pow_eq]
  have hn : 1 ≤ latticeSquare k.val := by
    have h := (latticeSquare_eq_zero_iff k.val).not.mpr k.property
    omega
  exact Real.one_le_rpow (by exact_mod_cast hn) (by positivity)

theorem potentialTerm_green {d : ℕ} (hd : 0 < d) (f : Space d) (k : NonzeroFrequency d) :
    potentialTerm (greenContinuous d f) k =
      (2*Real.pi)^d * (frequencyLength k.val^d)⁻¹ * ‖coefficient k.val f‖^2 := by
  have hp : 0 < frequencyLength k.val^d := lt_of_lt_of_le zero_lt_one (nonzero_eigenvalue_ge_one k)
  simp only [potentialTerm, ← coefficient_eq_fourierCoeff, coefficient_green hd,
    if_neg k.property, norm_mul, Complex.norm_real, Real.norm_of_nonneg (one_div_nonneg.mpr hp.le),
    mul_pow]
  field_simp
  <;> ring

theorem green_inCriticalSobolev {d : ℕ} (hd : 0 < d) (f : Space d) :
    InCriticalSobolev (greenContinuous d f) := by
  refine ⟨(greenContinuous d f).continuous.memLp_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _), ?_⟩
  have hs := ((coefficient_square_summable f).subtype {k : Frequency d | k ≠ 0}).mul_left ((2*Real.pi)^d)
  apply hs.of_nonneg_of_le
  · intro k
    unfold potentialTerm frequencyLength
    positivity
  · intro k
    rw [potentialTerm_green hd]
    have hi : (frequencyLength k.val^d)⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ (nonzero_eigenvalue_ge_one k)
    calc
      _ ≤ (2*Real.pi)^d * 1 * ‖coefficient k.val f‖^2 := by gcongr
      _ = _ := by simp

#print axioms green_inCriticalSobolev
end BecknerOnofri.HighDim.LocalEleven.GreenCritical
