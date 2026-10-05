module

public import BecknerOnofri.CircleDeficitDefinitions
public import BecknerOnofri.CircleDensityParseval
public import BecknerOnofri.CircleRemainderKernel

@[expose] public section

noncomputable section
open MeasureTheory
namespace BecknerOnofri.HighDim.CirclePoisson

theorem adjacent_square_summable (r : ℕ → ℝ)
    (hr : Summable (fun n : ℕ => (r (n+1))^2)) :
    Summable (fun n : ℕ => (r (n+2)-r 1*r (n+1))^2) := by
  have hshift : Summable (fun n : ℕ => (r (n+2))^2) := by
    simpa only [Nat.add_assoc] using (summable_nat_add_iff 1).mpr hr
  apply Summable.of_nonneg_of_le (fun n => sq_nonneg _)
    (fun n => ?_) ((hshift.mul_left 2).add (hr.mul_left (2*(r 1)^2)))
  nlinarith [sq_nonneg (r (n+2)+r 1*r (n+1))]

theorem remainder_kernel_scaled (r : ℕ → ℝ) (n : ℕ) (s : ℝ) :
    remainderKernel (n+1) (r 1) s*(r (n+2)-r 1*r (n+1))^2=
      2/(1-(Real.exp (-s)*r 1)^2)*
      (Real.exp (-(n+2:ℝ)*s)*r (n+2)-Real.exp (-s)*r 1*(Real.exp (-(n+1:ℝ)*s)*r (n+1)))^2 := by
  have hA : Real.exp (-s)*Real.exp (-(n+1:ℝ)*s)=Real.exp (-(n+2:ℝ)*s) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hB : (Real.exp (-(n+2:ℝ)*s))^2=Real.exp (-2*(n+2:ℝ)*s) := by
    rw [pow_two,← Real.exp_add]
    congr 1
    ring
  have hC : (Real.exp (-s))^2=Real.exp (-2*s) := by
    rw [pow_two,← Real.exp_add]
    congr 1
    ring
  have hdiff : Real.exp (-(n+2:ℝ)*s)*r (n+2)-Real.exp (-s)*r 1*(Real.exp (-(n+1:ℝ)*s)*r (n+1))=
      Real.exp (-(n+2:ℝ)*s)*(r (n+2)-r 1*r (n+1)) := by
    rw [← hA]
    ring
  rw [hdiff]
  simp only [mul_pow,hB,hC]
  unfold remainderKernel
  simp only [Nat.cast_add,Nat.cast_one]
  have hn : ((n:ℝ)+1+1)=(n:ℝ)+2 := by ring
  rw [hn]
  ring

#print axioms adjacent_square_summable
#print axioms remainder_kernel_scaled
end BecknerOnofri.HighDim.CirclePoisson
