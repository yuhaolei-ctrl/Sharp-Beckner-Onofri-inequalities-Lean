import BecknerOnofri.EntropyLogInteger

namespace BecknerOnofri.HighDim.EntropyLogCertificate
open EntropyTail.ExpCertificate

def integerReduced (P : ℕ) (a b : ℤ) (r : ℕ) : ℚ × ℚ :=
  let q := a-b
  let D := a+b
  let c := integerHorner P q D 0 r
  (2*(q : ℚ)*c.1/((D : ℚ)*P),
   2*(q : ℚ)*c.2/((D : ℚ)*P)+(9/4 : ℚ)*(1/3 : ℚ)^(2*r+1))

theorem integerReduced_eq (P : ℕ) (hP : 0<P) (a b : ℤ) (hb : 0<b) (hab : b≤a) (r : ℕ) :
    integerReduced P a b r=(reducedLower P ((a : ℚ)/b) r,reducedUpper P ((a : ℚ)/b) r) := by
  have hd : 0<a+b := by omega
  have hbq : (b : ℚ)≠0 := by exact_mod_cast hb.ne'
  have hz : (((a : ℚ)/b)-1)/(((a : ℚ)/b)+1)=((a-b : ℤ) : ℚ)/(a+b : ℤ) := by
    push_cast
    field_simp
  have hc := integerHorner_eq P hP (a-b) (a+b) hd 0 r
  unfold integerReduced reducedLower reducedUpper
  rw [hz, ← hc]
  simp only [ratPair]
  apply Prod.ext <;> dsimp only <;> ring

theorem integerReduced_sound (P : ℕ) (hP : 0<P) (a b : ℤ) (hb : 0<b)
    (hab : b≤a) (ha2b : a≤2*b) (r : ℕ) :
    ((integerReduced P a b r).1 : ℝ)≤Real.log ((a : ℝ)/b) ∧
      Real.log ((a : ℝ)/b)≤((integerReduced P a b r).2 : ℝ) := by
  have hbq : (0 : ℚ)<b := by exact_mod_cast hb
  have hx : (1 : ℚ)≤(a : ℚ)/b := (le_div_iff₀ hbq).mpr (by simpa only [one_mul] using (show (b : ℚ)≤a from by exact_mod_cast hab))
  have hx2 : (a : ℚ)/b≤2 := (div_le_iff₀ hbq).mpr (by exact_mod_cast ha2b)
  rw [integerReduced_eq P hP a b hb hab r]
  simpa only [Rat.cast_div, Rat.cast_intCast] using reduced_bounds P hP ((a : ℚ)/b) r hx hx2

def integerScaled (P : ℕ) (a b k : ℤ) (r : ℕ) : ℚ × ℚ :=
  let c := integerReduced P a b r
  let d := integerReduced P 2 1 r
  (c.1+min ((k : ℚ)*d.1) ((k : ℚ)*d.2),
   c.2+max ((k : ℚ)*d.1) ((k : ℚ)*d.2))

theorem integerScaled_sound (P : ℕ) (hP : 0<P) (a b k : ℤ) (hb : 0<b)
    (hab : b≤a) (ha2b : a≤2*b) (r : ℕ) :
    ((integerScaled P a b k r).1 : ℝ)≤Real.log (((a : ℝ)/b)*2^k) ∧
      Real.log (((a : ℝ)/b)*2^k)≤((integerScaled P a b k r).2 : ℝ) := by
  have h := integerReduced_sound P hP a b hb hab ha2b r
  have h2 := integerReduced_sound P hP 2 1 (by norm_num) (by norm_num) (by norm_num) r
  norm_num only [Int.cast_ofNat, Int.cast_one, div_one] at h2
  have hx : (0 : ℝ)<(a : ℝ)/b := div_pos (by exact_mod_cast (lt_of_lt_of_le hb hab)) (by exact_mod_cast hb)
  rw [Real.log_mul hx.ne' (zpow_ne_zero _ (by norm_num)),Real.log_zpow]
  simp only [integerScaled, Rat.cast_add, Rat.cast_min, Rat.cast_max, Rat.cast_mul, Rat.cast_intCast]
  by_cases hk : 0≤(k : ℝ)
  · constructor
    · exact add_le_add h.1 ((min_le_left _ _).trans (mul_le_mul_of_nonneg_left h2.1 hk))
    · exact add_le_add h.2 ((mul_le_mul_of_nonneg_left h2.2 hk).trans (le_max_right _ _))
  · constructor
    · exact add_le_add h.1 ((min_le_right _ _).trans (mul_le_mul_of_nonpos_left h2.2 (le_of_not_ge hk)))
    · exact add_le_add h.2 ((mul_le_mul_of_nonpos_left h2.1 (le_of_not_ge hk)).trans (le_max_left _ _))

#print axioms integerScaled_sound
end BecknerOnofri.HighDim.EntropyLogCertificate
