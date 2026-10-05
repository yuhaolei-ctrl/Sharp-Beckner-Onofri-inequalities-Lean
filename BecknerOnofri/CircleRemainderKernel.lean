import BecknerOnofri.CirclePoissonWeight

noncomputable section
open MeasureTheory Set
namespace BecknerOnofri.HighDim.CirclePoisson

def remainderKernel (n : ℕ) (t s : ℝ) : ℝ :=
  2*Real.exp (-2*(n+1:ℝ)*s)/(1-t^2*Real.exp (-2*s))

theorem remainder_denominator (t s : ℝ) (ht : t^2<1) (hs : 0≤s) :
    0<1-t^2 ∧ 1-t^2≤1-t^2*Real.exp (-2*s) := by
  have he : Real.exp (-2*s)≤1 := Real.exp_le_one_iff.mpr (by linarith)
  constructor
  · linarith
  · nlinarith [mul_le_mul_of_nonneg_left he (sq_nonneg t)]

theorem remainder_kernel_nonneg (n : ℕ) (t s : ℝ) (ht : t^2<1) (hs : 0≤s) :
    0≤remainderKernel n t s := by
  unfold remainderKernel
  exact div_nonneg (by positivity) ((remainder_denominator t s ht hs).1.trans_le
    (remainder_denominator t s ht hs).2).le

theorem remainder_kernel_integrable (n : ℕ) (t : ℝ) (ht : t^2<1) :
    IntegrableOn (remainderKernel n t) (Ioi (0:ℝ)) := by
  have hn : -2*(n+1:ℝ)<0 := by nlinarith [Nat.cast_nonneg (α:=ℝ) n]
  have hmajor := (integrableOn_exp_mul_Ioi hn 0).const_mul (2/(1-t^2))
  apply hmajor.mono'
  · have hm : Measurable (remainderKernel n t) := by unfold remainderKernel; fun_prop
    exact hm.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    rw [Real.norm_eq_abs,abs_of_nonneg (remainder_kernel_nonneg n t s ht hs.le)]
    obtain ⟨hd,hde⟩ := remainder_denominator t s ht hs.le
    calc
      remainderKernel n t s≤(2*Real.exp (-2*(n+1:ℝ)*s))/(1-t^2) :=
        div_le_div_of_nonneg_left (by positivity) hd hde
      _ = (2/(1-t^2))*Real.exp (-2*(n+1:ℝ)*s) := by ring

theorem remainder_kernel_integral (n : ℕ) (t : ℝ) (ht : 0≤t) (ht1 : t<1) :
    (∫ s in Ioi (0:ℝ),remainderKernel n t s)=CircleScalar.weight n t :=
  (CircleScalar.poisson_weight_integral n t ht ht1).symm

theorem weight_abs (n : ℕ) (t : ℝ) : CircleScalar.weight n |t|=CircleScalar.weight n t := by
  unfold CircleScalar.weight
  simp_rw [pow_mul,sq_abs]

theorem remainder_kernel_integral_of_sq_lt (n : ℕ) (t : ℝ) (ht : t^2<1) :
    (∫ s in Ioi (0:ℝ),remainderKernel n t s)=CircleScalar.weight n t := by
  have ht1 : |t|<1 := by nlinarith [sq_abs t,abs_nonneg t]
  have h := remainder_kernel_integral n |t| (abs_nonneg t) ht1
  simpa only [remainderKernel,sq_abs,weight_abs] using h

#print axioms remainder_kernel_integral_of_sq_lt
#print axioms remainder_kernel_integrable
end BecknerOnofri.HighDim.CirclePoisson
