module

public import BecknerOnofri.CircleHardyDefinitions
public import Mathlib.Tactic

@[expose] public section

/-! Actual sequence shifts, their adjoint identity, and the consecutive-moment
Cauchy--Schwarz estimate in the circle entropy remainder proof. -/
noncomputable section
namespace BecknerOnofri.HighDim.CircleHardy

theorem summable_sq (f : Space) : Summable (fun m => (f m)^2) := by
  simpa using lp.summable_inner (𝕜:=ℝ) f f

/-- `B^n` on the actual square-summable Taylor coefficients. -/
def backward (n : ℕ) (f : Space) : Space :=
  ⟨fun m => f (m+n), by
    apply memℓp_gen
    simpa using ((summable_nat_add_iff n).mpr (summable_sq f))⟩

/-- The forward shift `B*`, multiplication by the disk coordinate. -/
def forward (f : Space) : Space :=
  ⟨fun m => match m with | 0 => 0 | k+1 => f k, by
    apply memℓp_gen
    apply (summable_nat_add_iff 1).mp
    simpa using summable_sq f⟩

@[simp] theorem backward_apply (n : ℕ) (f : Space) (m : ℕ) :
    backward n f m=f (m+n) := rfl
@[simp] theorem forward_zero (f : Space) : forward f 0=0 := rfl
@[simp] theorem forward_succ (f : Space) (m : ℕ) : forward f (m+1)=f m := rfl

theorem inner_backward (f g : Space) (n : ℕ) :
    inner ℝ (backward n f) g=∑' m,f (m+n)*g m := by
  rw [lp.inner_eq_tsum]
  simp [mul_comm]

theorem moment_eq_inner (f : Space) (n : ℕ) :
    moment f n=inner ℝ (backward n f) f := (inner_backward f f n).symm

theorem forward_adjoint (f g : Space) :
    inner ℝ f (forward g)=inner ℝ (backward 1 f) g := by
  rw [lp.inner_eq_tsum, (lp.summable_inner (𝕜:=ℝ) f (forward g)).tsum_eq_zero_add]
  simp only [forward_zero, inner_zero_right, zero_add, forward_succ]
  exact (lp.inner_eq_tsum (backward 1 f) g).symm

theorem forward_norm_sq (f : Space) : ‖forward f‖^2=‖f‖^2 := by
  rw [← real_inner_self_eq_norm_sq, forward_adjoint]
  have h : backward 1 (forward f)=f := by ext m; rfl
  rw [h,real_inner_self_eq_norm_sq]

theorem backward_add (n k : ℕ) (f : Space) :
    backward n (backward k f)=backward (n+k) f := by
  ext m
  simp [Nat.add_assoc]

theorem moment_zero (f : Space) : moment f 0=‖f‖^2 := by
  rw [moment_eq_inner]
  have h : backward 0 f=f := by ext m; simp
  rw [h,real_inner_self_eq_norm_sq]

theorem forward_residual_norm (f : Space) (hf : ‖f‖=1) :
    ‖forward f-moment f 1 • f‖^2=1-(moment f 1)^2 := by
  have h1 : inner ℝ f (forward f)=moment f 1 := by
    rw [forward_adjoint,← moment_eq_inner]
  have h2 : inner ℝ (forward f) f=moment f 1 := by
    rw [real_inner_comm, h1]
  rw [← real_inner_self_eq_norm_sq]
  simp only [inner_sub_left,inner_sub_right,real_inner_smul_left,real_inner_smul_right,
    h1,h2,real_inner_self_eq_norm_sq,forward_norm_sq,norm_smul,Real.norm_eq_abs,hf,mul_one,sq_abs]
  ring

theorem residual_inner (f : Space) (hf : ‖f‖=1) (n : ℕ) :
    inner ℝ (backward n f-moment f n • f) (forward f-moment f 1 • f)=
      moment f (n+1)-moment f 1*moment f n := by
  simp only [inner_sub_left,inner_sub_right,real_inner_smul_left,real_inner_smul_right]
  rw [forward_adjoint,backward_add, Nat.add_comm 1 n,← moment_eq_inner,
    ← moment_eq_inner,forward_adjoint,← moment_eq_inner,real_inner_self_eq_norm_sq,hf]
  ring

theorem residual_norm (f : Space) (hf : ‖f‖=1) (n : ℕ) :
    ‖backward n f-moment f n • f‖^2=‖backward n f‖^2-(moment f n)^2 := by
  have h1 : inner ℝ (backward n f) f=moment f n := (moment_eq_inner f n).symm
  have h2 : inner ℝ f (backward n f)=moment f n := by rw [real_inner_comm,h1]
  rw [← real_inner_self_eq_norm_sq]
  simp only [inner_sub_left,inner_sub_right,real_inner_smul_left,real_inner_smul_right,
    h1,h2,real_inner_self_eq_norm_sq,norm_smul,Real.norm_eq_abs,hf,mul_one,sq_abs]
  ring

theorem consecutive_moment_bound (f : Space) (hf : ‖f‖=1) (n : ℕ) :
    (moment f (n+1)-moment f 1*moment f n)^2≤
      (‖backward n f‖^2-(moment f n)^2)*(1-(moment f 1)^2) := by
  have h := abs_real_inner_le_norm (backward n f-moment f n • f)
    (forward f-moment f 1 • f)
  have hsq := mul_self_le_mul_self (abs_nonneg _) h
  simp only [← sq, sq_abs, mul_pow] at hsq
  rw [residual_inner f hf n] at hsq
  simpa only [← sq, mul_pow, residual_norm f hf n, forward_residual_norm f hf] using hsq

theorem first_moment_sq_lt_one (f : Space) (hf : ‖f‖=1) : (moment f 1)^2<1 := by
  have hnonneg : 0≤1-(moment f 1)^2 := by
    rw [← forward_residual_norm f hf]
    positivity
  by_contra h
  have he : (moment f 1)^2=1 := by linarith
  have ht : moment f 1≠0 := by intro hz; simp [hz] at he
  have hz : forward f-moment f 1 • f=0 := by
    apply norm_eq_zero.mp
    apply sq_eq_zero_iff.mp
    rw [forward_residual_norm f hf,he,sub_self]
  have heq := sub_eq_zero.mp hz
  have hm (m : ℕ) : forward f m=moment f 1*f m := by
    have h := congrArg (fun g : Space => g m) heq
    simpa using h
  have hc (m : ℕ) : f m=0 := by
    induction m with
    | zero => exact (mul_eq_zero.mp (by simpa using (hm 0).symm)).resolve_left ht
    | succ m ih =>
      exact (mul_eq_zero.mp (by simpa [ih] using (hm (m+1)).symm)).resolve_left ht
  have hzero : f=0 := by ext m; exact hc m
  rw [hzero,norm_zero] at hf
  norm_num at hf

#print axioms consecutive_moment_bound
#print axioms first_moment_sq_lt_one
end BecknerOnofri.HighDim.CircleHardy
