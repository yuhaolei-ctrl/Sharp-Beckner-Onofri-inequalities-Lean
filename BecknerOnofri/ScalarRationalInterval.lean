import Mathlib.Tactic

/-! Small signed rational interval algebra for the scalar gamma certificate.
Every arithmetic operation carries a theorem about actual real values. -/
namespace BecknerOnofri.HighDim.ScalarCertificate

structure RationalInterval where
  lower : ℚ
  upper : ℚ

def RationalInterval.Contains (a : RationalInterval) (x : ℝ) : Prop :=
  (a.lower : ℝ)≤x ∧ x≤(a.upper : ℝ)

def RationalInterval.add (a b : RationalInterval) : RationalInterval :=
  ⟨a.lower+b.lower,a.upper+b.upper⟩
def RationalInterval.neg (a : RationalInterval) : RationalInterval := ⟨-a.upper,-a.lower⟩
def RationalInterval.mul (a b : RationalInterval) : RationalInterval :=
  ⟨min (min (a.lower*b.lower) (a.lower*b.upper)) (min (a.upper*b.lower) (a.upper*b.upper)),
   max (max (a.lower*b.lower) (a.lower*b.upper)) (max (a.upper*b.lower) (a.upper*b.upper))⟩
def RationalInterval.hull (a b : RationalInterval) : RationalInterval :=
  ⟨min a.lower b.lower,max a.upper b.upper⟩

theorem RationalInterval.contains_add {a b : RationalInterval} {x y : ℝ}
    (hx : a.Contains x) (hy : b.Contains y) : (a.add b).Contains (x+y) := by
  simp only [Contains,add,Rat.cast_add]
  exact ⟨add_le_add hx.1 hy.1,add_le_add hx.2 hy.2⟩

theorem RationalInterval.contains_neg {a : RationalInterval} {x : ℝ}
    (hx : a.Contains x) : a.neg.Contains (-x) := by
  simp only [Contains,neg,Rat.cast_neg]
  exact ⟨neg_le_neg hx.2,neg_le_neg hx.1⟩

private theorem mul_endpoints {a b x : ℝ} (hx : a≤x ∧ x≤b) (y : ℝ) :
    min (a*y) (b*y)≤x*y ∧ x*y≤max (a*y) (b*y) := by
  by_cases hy : 0≤y
  · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_right hx.1 hy),
      (mul_le_mul_of_nonneg_right hx.2 hy).trans (le_max_right _ _)⟩
  · have hy' : y≤0 := le_of_not_ge hy
    exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_right hx.2 hy'),
      (mul_le_mul_of_nonpos_right hx.1 hy').trans (le_max_left _ _)⟩

theorem RationalInterval.contains_mul {a b : RationalInterval} {x y : ℝ}
    (hx : a.Contains x) (hy : b.Contains y) : (a.mul b).Contains (x*y) := by
  have h := mul_endpoints hx y
  have hl := mul_endpoints hy (a.lower : ℝ)
  have hu := mul_endpoints hy (a.upper : ℝ)
  simp only [mul_comm y, mul_comm (b.lower : ℝ),mul_comm (b.upper : ℝ)] at hl hu
  simp only [Contains,mul,Rat.cast_min,Rat.cast_max,Rat.cast_mul]
  exact ⟨(min_le_min hl.1 hu.1).trans h.1,h.2.trans (max_le_max hl.2 hu.2)⟩

theorem RationalInterval.contains_hull_left {a b : RationalInterval} {x : ℝ}
    (hx : a.Contains x) : (a.hull b).Contains x := by
  simp only [Contains,hull,Rat.cast_min,Rat.cast_max]
  exact ⟨(min_le_left _ _).trans hx.1,hx.2.trans (le_max_left _ _)⟩

theorem RationalInterval.contains_hull_right {a b : RationalInterval} {x : ℝ}
    (hx : b.Contains x) : (a.hull b).Contains x := by
  simp only [Contains,hull,Rat.cast_min,Rat.cast_max]
  exact ⟨(min_le_right _ _).trans hx.1,hx.2.trans (le_max_right _ _)⟩

#print axioms RationalInterval.contains_mul
end BecknerOnofri.HighDim.ScalarCertificate
