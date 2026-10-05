module

public import BecknerOnofri.SpinCurvature
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Analysis.Convex.Deriv

@[expose] public section

/-! Actual derivatives of the thirteen-state functional along affine segments.
The entropy continuity statement includes zero coordinates. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
namespace BecknerOnofri.HighDim.Spin

def bilinear (p q : Count → ℝ) : ℝ :=
  ∑ i : Count, ∑ j : Count,p i*interaction i j*q j

theorem bilinear_symm (p q : Count → ℝ) : bilinear p q=bilinear q p := by
  unfold bilinear
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  rw [interaction_symmetric i j]
  ring

theorem quadratic_affine (p v : Count → ℝ) (t : ℝ) :
    quadratic (p+t•v)=quadratic p+2*t*bilinear p v+t^2*quadratic v := by
  have he : quadratic (p+t•v)=quadratic p+t*bilinear p v+t*bilinear v p+t^2*quadratic v := by
    simp only [quadratic,bilinear,Pi.add_apply,Pi.smul_apply,smul_eq_mul,
      Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he,bilinear_symm v p]
  ring

theorem entropy_coordinate_identity (x : ℝ) (j : Count) :
    x*Real.log (x/reference j)=x*Real.log x-x*Real.log (reference j) := by
  by_cases hx : x=0
  · simp [hx]
  rw [Real.log_div hx (reference_pos j).ne']
  ring

theorem relativeEntropy_reference_continuous :
    Continuous (fun p : Count → ℝ => relativeEntropy p reference) := by
  simp only [relativeEntropy,entropy_coordinate_identity]
  apply continuous_finset_sum
  intro j _
  exact ((Real.continuous_mul_log.comp (continuous_apply j)).sub
    ((continuous_apply j).mul continuous_const))

def entropySlope (p v : Count → ℝ) (t : ℝ) : ℝ :=
  ∑ j : Count,(Real.log (p j+t*v j)-Real.log (reference j)+1)*v j

def entropyHessian (p v : Count → ℝ) (t : ℝ) : ℝ :=
  ∑ j : Count,v j^2/(p j+t*v j)

theorem entropy_segment_derivative (p v : Count → ℝ) (t : ℝ)
    (hpos : ∀ j,0<p j+t*v j) :
    HasDerivAt (fun a => relativeEntropy (p+a•v) reference) (entropySlope p v t) t := by
  have hd (j : Count) : HasDerivAt (fun a : ℝ => p j+a*v j) (v j) t := by
    simpa using ((hasDerivAt_id t).mul_const (v j)).const_add (p j)
  have h (j : Count) := ((Real.hasDerivAt_mul_log (hpos j).ne').comp t (hd j)).sub
    ((hd j).mul_const (Real.log (reference j)))
  have hh := HasDerivAt.sum (u:=Finset.univ) (fun j _ => h j)
  convert hh using 1 <;> try rfl
  · ext a
    simp [relativeEntropy,entropy_coordinate_identity]
  · simp only [entropySlope]
    apply Finset.sum_congr rfl
    intro j _
    ring

theorem entropy_segment_second_derivative (p v : Count → ℝ) (t : ℝ)
    (hpos : ∀ j,0<p j+t*v j) :
    HasDerivAt (entropySlope p v) (entropyHessian p v t) t := by
  have hd (j : Count) : HasDerivAt (fun a : ℝ => p j+a*v j) (v j) t := by
    simpa using ((hasDerivAt_id t).mul_const (v j)).const_add (p j)
  have h (j : Count) := ((((Real.hasDerivAt_log (hpos j).ne').comp t (hd j)).sub_const
    (Real.log (reference j))).add_const 1).mul_const (v j)
  have hh := HasDerivAt.sum (u:=Finset.univ) (fun j _ => h j)
  convert hh using 1 <;> try rfl
  simp only [entropyHessian]
  apply Finset.sum_congr rfl
  intro j _
  field_simp

def functionalSlope (p v : Count → ℝ) (t : ℝ) : ℝ :=
  2*entropySlope p v t-2*bilinear p v-2*t*quadratic v

def functionalHessian (p v : Count → ℝ) (t : ℝ) : ℝ :=
  2*entropyHessian p v t-2*quadratic v

theorem functional_segment_continuous (p v : Count → ℝ) :
    Continuous (fun t : ℝ => functional (p+t•v)) := by
  unfold functional
  apply Continuous.sub
  · exact continuous_const.mul (relativeEntropy_reference_continuous.comp (by fun_prop))
  · exact quadratic_continuous.comp (by fun_prop)

theorem functional_segment_derivative (p v : Count → ℝ) (t : ℝ)
    (hpos : ∀ j,0<p j+t*v j) :
    HasDerivAt (fun a => functional (p+a•v)) (functionalSlope p v t) t := by
  have h := (((entropy_segment_derivative p v t hpos).const_mul 2).sub_const (quadratic p)).sub
    (((hasDerivAt_id t).const_mul 2).mul_const (bilinear p v))
  have hh := h.sub (((hasDerivAt_id t).pow 2).mul_const (quadratic v))
  convert hh using 1 <;> try rfl
  · ext a
    simp [functional,quadratic_affine]
    ring
  · simp [functionalSlope]

theorem functional_segment_second_derivative (p v : Count → ℝ) (t : ℝ)
    (hpos : ∀ j,0<p j+t*v j) :
    HasDerivAt (functionalSlope p v) (functionalHessian p v t) t := by
  have h := ((entropy_segment_second_derivative p v t hpos).const_mul 2).sub_const
    (2*bilinear p v)
  have hh := h.sub (((hasDerivAt_id t).const_mul 2).mul_const (quadratic v))
  convert hh using 1 <;> first | rfl | simp [functionalSlope,functionalHessian]

#print axioms functional_segment_second_derivative
end BecknerOnofri.HighDim.Spin
