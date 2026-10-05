module

public import BecknerOnofri.EntropyLogCertificate
public import BecknerOnofri.EntropyExpCertificate

@[expose] public section

/-! Directed, fixed-precision Horner evaluation for logarithm enclosures.
All rounding is rational. The error bound comes from the analytic atanh
remainder, with a uniform tail on the reduced interval 1 ≤ x ≤ 2. -/
set_option backward.isDefEq.respectTransparency false
namespace BecknerOnofri.HighDim.EntropyLogCertificate
open EntropyTail.ExpCertificate

def hornerExact (z : ℚ) (n : ℕ) : ℕ → ℚ
  | 0 => 0
  | r+1 => 1/(2*n+1 : ℚ)+z^2*hornerExact z (n+1) r

def hornerBounds (P : ℕ) (z : ℚ) (n : ℕ) : ℕ → ℚ × ℚ
  | 0 => (0,0)
  | r+1 =>
    let c := hornerBounds P z (n+1) r
    (roundDown P (1/(2*n+1 : ℚ)+z^2*c.1),
      roundUp P (1/(2*n+1 : ℚ)+z^2*c.2))

theorem hornerBounds_sound (P : ℕ) (hP : 0<P) (z : ℚ) (n r : ℕ) :
    (hornerBounds P z n r).1≤hornerExact z n r ∧
      hornerExact z n r≤(hornerBounds P z n r).2 := by
  induction r generalizing n with
  | zero => exact ⟨le_rfl,le_rfl⟩
  | succ r ih =>
    have h := ih (n+1)
    simp only [hornerBounds, hornerExact]
    constructor
    · exact (roundDown_le P hP _).trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left h.1 (sq_nonneg z)))
    · exact (add_le_add le_rfl (mul_le_mul_of_nonneg_left h.2 (sq_nonneg z))).trans (le_roundUp P hP _)

theorem hornerExact_eq (z : ℚ) (n r : ℕ) :
    hornerExact z n r=∑ i ∈ Finset.range r,z^(2*i)/(2*(n+i)+1 : ℚ) := by
  induction r generalizing n with
  | zero => simp [hornerExact]
  | succ r ih =>
    rw [hornerExact, ih, Finset.sum_range_succ']
    simp only [Nat.cast_add, Nat.cast_one, pow_zero, one_div, Nat.add_zero]
    rw [Finset.mul_sum]
    have he (i : ℕ) : z^2*(z^(2*i)/(2*((n : ℚ)+1+i)+1))=
        z^(2*(i+1))/(2*((n : ℚ)+(i+1))+1) := by
      rw [← mul_div_assoc, ← pow_add]
      congr 1 <;> ring
    simp_rw [he]
    ring

theorem atanhPartial_eq_horner (z : ℚ) (r : ℕ) : atanhPartial z r=z*hornerExact z 0 r := by
  rw [hornerExact_eq, Finset.mul_sum]
  unfold atanhPartial
  apply Finset.sum_congr rfl
  intro i _
  simp only [Nat.cast_zero, zero_add, mul_div_assoc]
  rw [← mul_div_assoc, ← pow_succ']

def reducedLower (P : ℕ) (x : ℚ) (r : ℕ) : ℚ :=
  2*((x-1)/(x+1))*(hornerBounds P ((x-1)/(x+1)) 0 r).1

def reducedUpper (P : ℕ) (x : ℚ) (r : ℕ) : ℚ :=
  2*((x-1)/(x+1))*(hornerBounds P ((x-1)/(x+1)) 0 r).2+
    (9/4 : ℚ)*(1/3 : ℚ)^(2*r+1)

theorem reduced_bounds (P : ℕ) (hP : 0<P) (x : ℚ) (r : ℕ)
    (hx : 1≤x) (hx2 : x≤2) :
    (reducedLower P x r : ℝ)≤Real.log (x : ℝ) ∧
      Real.log (x : ℝ)≤(reducedUpper P x r : ℝ) := by
  let z : ℚ := (x-1)/(x+1)
  have hz0 : 0≤z := div_nonneg (by linarith) (by linarith)
  have hz : z≤1/3 := (div_le_iff₀ (by linarith : 0<x+1)).mpr (by linarith)
  have hb := hornerBounds_sound P hP z 0 r
  have hlow : reducedLower P x r≤lower x r := by
    unfold reducedLower lower
    rw [atanhPartial_eq_horner]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hb.1
      (show (0 : ℚ)≤2*z from mul_nonneg (by norm_num : (0 : ℚ)≤2) hz0)
  have htail : 2*z^(2*r+1)/(1-z^2)≤(9/4 : ℚ)*(1/3 : ℚ)^(2*r+1) := by
    have hzsq := pow_le_pow_left₀ hz0 hz 2
    have hd : (8/9 : ℚ)≤1-z^2 := by norm_num at hzsq; linarith
    calc
      _ ≤ 2*(1/3 : ℚ)^(2*r+1)/(8/9) := by gcongr
      _ = _ := by ring
  have hupp : upper x r≤reducedUpper P x r := by
    unfold upper lower reducedUpper
    rw [atanhPartial_eq_horner]
    have h := mul_le_mul_of_nonneg_left hb.2 (mul_nonneg (by norm_num : (0 : ℚ)≤2) hz0)
    change 2*(z*hornerExact z 0 r)+2*z^(2*r+1)/(1-z^2)≤_
    linarith
  have hlog := unit_bounds x r hx
  exact ⟨((Rat.cast_le (K := ℝ)).mpr hlow).trans hlog.1,
    hlog.2.trans ((Rat.cast_le (K := ℝ)).mpr hupp)⟩

#print axioms reduced_bounds
end BecknerOnofri.HighDim.EntropyLogCertificate
