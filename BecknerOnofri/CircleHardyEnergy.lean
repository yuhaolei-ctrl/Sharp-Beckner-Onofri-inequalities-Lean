module

public import BecknerOnofri.CircleHardyShift
public import Mathlib.Algebra.BigOperators.NatAntidiagonal
public import Mathlib.Topology.Algebra.InfiniteSum.Real

@[expose] public section

/-! Summation of the Hardy-space shift estimates.  The weighted coefficient
energy is finite for the smooth outer functions used in the manuscript. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
namespace BecknerOnofri.HighDim.CircleHardy

theorem backward_norm_sq (f : Space) (n : ℕ) :
    ‖backward n f‖^2=∑' m,(f (m+n))^2 := by
  rw [← real_inner_self_eq_norm_sq,lp.inner_eq_tsum]
  simp [pow_two]

private theorem diagonal_sum (f : Space) (n : ℕ) :
    (∑' p : ↥(Finset.antidiagonal n),(f (p.val.1+p.val.2+1))^2)=
      (n+1:ℝ)*(f (n+1))^2 := by
  have he (p : ↥(Finset.antidiagonal n)) : p.val.1+p.val.2=n :=
    Finset.mem_antidiagonal.mp p.property
  simp only [he,tsum_fintype,Finset.sum_const,Finset.card_univ,
    Fintype.card_coe,Finset.Nat.card_antidiagonal,nsmul_eq_mul,Nat.cast_add,Nat.cast_one]

theorem backward_energy (f : Space) (hE : Summable (fun m : ℕ => (m:ℝ)*(f m)^2)) :
    Summable (fun n => ‖backward (n+1) f‖^2) ∧
    (∑' n,‖backward (n+1) f‖^2)=∑' m : ℕ,(m:ℝ)*(f m)^2 := by
  let g : ℕ × ℕ → ℝ := fun p => (f (p.1+p.2+1))^2
  let e := Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd (A:=ℕ)
  have hdiag : Summable (g ∘ e) := by
    apply (summable_sigma_of_nonneg (fun p => sq_nonneg _)).mpr
    constructor
    · intro n; exact (hasSum_fintype _).summable
    · change Summable (fun n => ∑' p : ↥(Finset.antidiagonal n),
        (f (p.val.1+p.val.2+1))^2)
      simp_rw [diagonal_sum]
      simpa using (summable_nat_add_iff 1).mpr hE
  have hg : Summable g := e.summable_iff.mp hdiag
  have hpoint (n : ℕ) : (∑' m,g (n,m))=‖backward (n+1) f‖^2 := by
    rw [backward_norm_sq]
    apply tsum_congr
    intro m
    dsimp only [g]
    exact congrArg (fun k : ℕ => (f k)^2) (by omega)
  constructor
  · simpa only [hpoint] using hg.prod
  · calc
      (∑' n,‖backward (n+1) f‖^2) = ∑' p,g p := by
        rw [hg.tsum_prod]; simp only [hpoint]
      _ = ∑' p,g (e p) := (e.tsum_eq g).symm
      _ = ∑' n : ℕ, (n+1:ℝ)*(f (n+1))^2 := by
        calc
          _ = ∑' n, ∑' p : ↥(Finset.antidiagonal n), (f (p.val.1+p.val.2+1))^2 := hdiag.tsum_sigma
          _ = _ := tsum_congr (diagonal_sum f)
      _ = ∑' m : ℕ,(m:ℝ)*(f m)^2 := by
        simpa using hE.tsum_eq_zero_add.symm

theorem residual_summable (f : Space) (hf : ‖f‖=1)
    (hE : Summable (fun m : ℕ => (m:ℝ)*(f m)^2)) :
    Summable (fun n => ‖backward (n+1) f-moment f (n+1) • f‖^2) := by
  apply Summable.of_nonneg_of_le (fun n => sq_nonneg _) _ (backward_energy f hE).1
  intro n
  rw [residual_norm f hf]
  exact sub_le_self _ (sq_nonneg _)

theorem moment_squares_summable (f : Space) (hf : ‖f‖=1)
    (hE : Summable (fun m : ℕ => (m:ℝ)*(f m)^2)) :
    Summable (fun n => (moment f (n+1))^2) := by
  apply Summable.of_nonneg_of_le (fun n => sq_nonneg _) _ (backward_energy f hE).1
  intro n
  have h := sq_nonneg ‖backward (n+1) f-moment f (n+1) • f‖
  rw [residual_norm f hf] at h
  linarith

theorem fisher_shift_identity (f : Space) (hf : ‖f‖=1)
    (hE : Summable (fun m : ℕ => (m:ℝ)*(f m)^2)) :
    (∑' n,‖backward (n+1) f-moment f (n+1) • f‖^2)=
      (∑' m : ℕ,(m:ℝ)*(f m)^2)-(∑' n,(moment f (n+1))^2) := by
  simp_rw [residual_norm f hf]
  rw [((backward_energy f hE).1).tsum_sub (moment_squares_summable f hf hE),
    (backward_energy f hE).2]

theorem fisher_lower_bound (f : Space) (hf : ‖f‖=1)
    (hE : Summable (fun m : ℕ => (m:ℝ)*(f m)^2)) :
    2/(1-(moment f 1)^2)*
      (∑' n,(moment f (n+2)-moment f 1*moment f (n+1))^2) ≤
    2*((∑' m : ℕ,(m:ℝ)*(f m)^2)-(∑' n,(moment f (n+1))^2)) := by
  have ht2 := first_moment_sq_lt_one f hf
  have hden : 0<1-(moment f 1)^2 := by linarith
  have hres := residual_summable f hf hE
  have hbound (n : ℕ) :
      (moment f (n+2)-moment f 1*moment f (n+1))^2≤
      ‖backward (n+1) f-moment f (n+1) • f‖^2*(1-(moment f 1)^2) := by
    rw [residual_norm f hf]
    exact consecutive_moment_bound f hf (n+1)
  have hsum : Summable (fun n => (moment f (n+2)-moment f 1*moment f (n+1))^2) :=
    Summable.of_nonneg_of_le (fun n => sq_nonneg _) hbound (hres.mul_right _)
  have h := hsum.tsum_le_tsum hbound (hres.mul_right _)
  rw [tsum_mul_right,fisher_shift_identity f hf hE] at h
  have hdiv := (div_le_iff₀ hden).mpr h
  calc
    _ = 2*((∑' n,(moment f (n+2)-moment f 1*moment f (n+1))^2)/(1-(moment f 1)^2)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hdiv (by norm_num)

#print axioms fisher_shift_identity
#print axioms fisher_lower_bound
end BecknerOnofri.HighDim.CircleHardy
