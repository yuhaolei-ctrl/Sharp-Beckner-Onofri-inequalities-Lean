import BecknerOnofri.CircleVonMisesComparison
import Mathlib.Analysis.Convex.Deriv

/-! The three convex polynomial tests and their exact cosine identities. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
namespace BecknerOnofri.HighDim.CircleScalar

def secondPolynomial (x : ℝ) : ℝ := 2*x^2-1
def thirdPolynomial (x : ℝ) : ℝ := 4*x^3-3*x

theorem moment_polynomial_convex (a b : ℝ) (hab : 6*|b|≤a) :
    ConvexOn ℝ (Icc (-1:ℝ) 1) (fun x => a*secondPolynomial x+b*thirdPolynomial x) := by
  let f' : ℝ → ℝ := fun x => 4*a*x+b*(12*x^2-3)
  let f'' : ℝ → ℝ := fun x => 4*a+24*b*x
  have hd (x : ℝ) : HasDerivAt (fun y => a*secondPolynomial y+b*thirdPolynomial y) (f' x) x := by
    have he := ((((hasDerivAt_id x).pow 2).const_mul 2).sub_const 1).const_mul a |>.add
      (((((hasDerivAt_id x).pow 3).const_mul 4).sub ((hasDerivAt_id x).const_mul 3)).const_mul b)
    convert he using 1 <;> try rfl
    dsimp only [f']
    simp only [id_eq]
    ring
  have hdd (x : ℝ) : HasDerivAt f' (f'' x) x := by
    have he := ((hasDerivAt_id x).const_mul (4*a)).add
      (((((hasDerivAt_id x).pow 2).const_mul 12).sub_const 3).const_mul b)
    convert he using 1 <;> try rfl
    dsimp only [f'']
    simp only [id_eq]
    ring
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc _ _)
    (by unfold secondPolynomial thirdPolynomial; fun_prop)
    (fun x _ => (hd x).hasDerivWithinAt) (fun x _ => (hdd x).hasDerivWithinAt)
  intro x hx
  have hx' : x ∈ Icc (-1:ℝ) 1 := interior_subset hx
  have hbx : |b*x|≤|b| := by
    rw [abs_mul]
    simpa using mul_le_mul_of_nonneg_left (abs_le.mpr hx') (abs_nonneg b)
  have hlo := (abs_le.mp hbx).1
  dsimp only [f'']
  nlinarith

theorem second_polynomial_cosine (x : UnitAddCircle) :
    secondPolynomial ((fourier 1 x).re)=(fourier 2 x).re := by
  induction x using Quotient.inductionOn with
  | h x =>
    simp only [fourier_coe_apply]
    norm_num [secondPolynomial,Complex.exp_re]
    convert (Real.cos_two_mul (2*Real.pi*x)).symm using 1 <;> congr 1 <;> ring

theorem third_polynomial_cosine (x : UnitAddCircle) :
    thirdPolynomial ((fourier 1 x).re)=(fourier 3 x).re := by
  induction x using Quotient.inductionOn with
  | h x =>
    simp only [fourier_coe_apply]
    norm_num [thirdPolynomial,Complex.exp_re]
    convert (Real.cos_three_mul (2*Real.pi*x)).symm using 1 <;> congr 1 <;> ring

#print axioms moment_polynomial_convex
#print axioms second_polynomial_cosine
#print axioms third_polynomial_cosine
end BecknerOnofri.HighDim.CircleScalar
