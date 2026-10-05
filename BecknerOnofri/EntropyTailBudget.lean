import BecknerOnofri.CountableMixtureTransfer
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

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
    (27/40)*((harmonic n:ℝ)-2*binomialCoeffReal n 1-binomialCoeffReal n 2))

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

theorem tailBudget_harmonic_lower (n : ℕ) :
    (81/10:ℝ)*((harmonic n:ℝ)-3)≤tailBudget n := by
  have h1 := CosineMixtureTransfer.coeff_le_one n 1
  have h2 := CosineMixtureTransfer.coeff_le_one n 2
  have h2p := binomialCoeff_nonneg n 2
  have h2r : 0≤binomialCoeffReal n 2 := by
    unfold binomialCoeffReal
    exact_mod_cast h2p
  unfold tailBudget
  nlinarith

theorem harmonic_hundred_lower : (5187/1000:ℝ)<(harmonic 100:ℝ) := by
  have h : (5187/1000:ℚ)<harmonic 100 := by decide +kernel
  have hh := Rat.cast_lt (K:=ℝ).mpr h
  norm_num only [Rat.cast_div,Rat.cast_ofNat] at hh
  exact hh

theorem log_hundred_one_upper : Real.log 101<(4617/1000:ℝ) := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  apply lt_of_lt_of_le _ (Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ)≤4617/1000) 24)
  norm_num [Finset.sum_range_succ,Nat.factorial_succ]

theorem harmonic_log_gap {n : ℕ} (hn : 100≤n) :
    Real.log ((n:ℝ)+1)+(57/100:ℝ)<(harmonic n:ℝ) := by
  have h := Real.strictMono_eulerMascheroniSeq.monotone hn
  simp only [Real.eulerMascheroniSeq,Nat.cast_ofNat] at h
  have h100 := harmonic_hundred_lower
  have hlog := log_hundred_one_upper
  norm_num at h
  linarith

/-- Covers every n≥100, not merely the last finite row. -/
theorem tailBudget_log_lower {n : ℕ} (hn : 100≤n) :
    (81/10:ℝ)*Real.log ((n:ℝ)+1/2)-19683/1000<tailBudget n := by
  have hg := harmonic_log_gap hn
  have hm : Real.log ((n:ℝ)+1/2)≤Real.log ((n:ℝ)+1) :=
    Real.log_le_log (by positivity) (by linarith)
  have hb := tailBudget_harmonic_lower n
  nlinarith

#print axioms tailBudget_log_lower
end BecknerOnofri.HighDim.EntropyTail
