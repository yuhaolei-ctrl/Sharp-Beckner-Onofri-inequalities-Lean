module

public import BecknerOnofri.CountableMixtureTransfer
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni

@[expose] public section

/-! The actual harmonic/binomial tail budget R_n from §5.2.2 of the
2026-09-21 manuscript, including its all-large-index logarithmic lower bound. -/
noncomputable section
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
open scoped BigOperators
namespace BecknerOnofri.HighDim.EntropyTail
open Legacy.D10

def tailBudget (n : ℕ) : ℝ :=
  12*((21/500)*binomialCoeffReal n 2+
    (67/100)*((harmonic n:ℝ)-2*binomialCoeffReal n 1-binomialCoeffReal n 2))

theorem first_coefficient (n : ℕ) : binomialCoeffReal n 1=(n:ℝ)/(n+1) := by
  have h := binomialCoeff_step n 0 (Nat.zero_le n)
  norm_num only [Nat.cast_zero,add_zero,zero_add,sub_zero,binomialCoeff_zero,mul_one] at h
  have h' : ((n:ℝ)+1)*binomialCoeffReal n 1=n := by
    unfold binomialCoeffReal
    exact_mod_cast h
  apply (eq_div_iff (by positivity : (n:ℝ)+1≠0)).mpr
  linarith

theorem second_coefficient (n : ℕ) :
    binomialCoeffReal n 2=(n:ℝ)*(n-1)/((n+1)*(n+2)) := by
  by_cases hn : n=0
  · subst n
    norm_num [binomialCoeffReal,binomialCoeff]
  have h := binomialCoeff_step n 1 (by omega)
  have h' : ((n:ℝ)+2)*binomialCoeffReal n 2=((n:ℝ)-1)*binomialCoeffReal n 1 := by
    have hh := congrArg (fun z : ℚ => (z:ℝ)) h
    norm_num only [Rat.cast_mul,Rat.cast_add,Rat.cast_sub,Rat.cast_natCast,
      Rat.cast_one,show (1+1:ℕ)=2 from rfl] at hh
    change ((n:ℝ)+2)*(binomialCoeff n 2:ℝ)=((n:ℝ)-1)*(binomialCoeff n 1:ℝ)
    convert hh using 1 <;> congr 1 <;> ring
  rw [first_coefficient] at h'
  apply (eq_div_iff (by positivity : ((n:ℝ)+1)*(n+2)≠0)).mpr
  field_simp at h'
  nlinarith

/-- The lower bound `R_n ≥ 12 c H_n - 12 (3c - ε)` used for large indices
in Lemma 5.13, with `c = 67/100` and `ε = 21/500`. -/
theorem tailBudget_harmonic_lower (n : ℕ) :
    (201/25:ℝ)*(harmonic n:ℝ)-2952/125≤tailBudget n := by
  have h1 := CosineMixtureTransfer.coeff_le_one n 1
  have h2 := CosineMixtureTransfer.coeff_le_one n 2
  have h2p := binomialCoeff_nonneg n 2
  have h2r : 0≤binomialCoeffReal n 2 := by
    unfold binomialCoeffReal
    exact_mod_cast h2p
  unfold tailBudget
  nlinarith

#print axioms tailBudget_harmonic_lower
end BecknerOnofri.HighDim.EntropyTail
