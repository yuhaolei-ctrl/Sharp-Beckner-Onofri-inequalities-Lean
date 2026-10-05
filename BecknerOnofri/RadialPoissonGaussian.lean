module

public import BecknerOnofri.RadialE1
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import Mathlib.Analysis.SpecificLimits.Normed

@[expose] public section

/-! Shifted one-dimensional Gaussian bounds for the nonzero Poisson image tail. -/
noncomputable section
set_option maxHeartbeats 800000
open scoped BigOperators
namespace BecknerOnofri.HighDim.RadialPoissonGaussian

def gaussian (p y : ℝ) (n : ℤ) : ℝ := Real.exp (-p*((n:ℝ)+y)^2)
def majorant (p : ℝ) (N n : ℕ) : ℝ :=
  Real.exp (-p*((N:ℝ)-1/2)^2)*Real.exp (-2*p*N)^n

theorem majorant_summable {p : ℝ} (hp : 0<p) {N : ℕ} (hN : 0<N) :
    Summable (majorant p N) := by
  apply Summable.mul_left
  apply summable_geometric_of_lt_one (Real.exp_pos _).le
  apply Real.exp_lt_one_iff.mpr
  have hNr : (0:ℝ)<N := by exact_mod_cast hN
  nlinarith

theorem majorant_tsum {p : ℝ} (hp : 0<p) {N : ℕ} (hN : 0<N) :
    (∑'n,majorant p N n)=Real.exp (-p*((N:ℝ)-1/2)^2)/(1-Real.exp (-2*p*N)) := by
  unfold majorant
  rw [tsum_mul_left,tsum_geometric_of_lt_one (Real.exp_pos _).le]
  · simp only [div_eq_mul_inv]
  · apply Real.exp_lt_one_iff.mpr
    have hNr : (0:ℝ)<N := by exact_mod_cast hN
    nlinarith

theorem square_bound (n : ℕ) {N : ℕ} (hN : 0<N) {y : ℝ}
    (hy : 0≤y) (hy' : y≤1/2) :
    ((N:ℝ)-1/2)^2+2*N*n ≤ (((n+N:ℕ):ℝ)+y)^2 ∧
    ((N:ℝ)-1/2)^2+2*N*n ≤ (-((n+N:ℕ):ℝ)+y)^2 := by
  have hNr : (1:ℝ)≤N := by exact_mod_cast hN
  have hn : (0:ℝ)≤n := Nat.cast_nonneg n
  have hn2 : (n:ℝ)≤(n:ℝ)^2 := by
    rcases Nat.eq_zero_or_pos n with h | h
    · simp [h]
    · have hn1 : (1:ℝ)≤n := by exact_mod_cast h
      nlinarith [mul_nonneg hn (show 0≤(n:ℝ)-1 by linarith)]
  have hs := sq_nonneg (y-1/2)
  push_cast
  constructor <;> nlinarith [mul_nonneg hn hy,mul_nonneg hn (show 0≤1/2-y by linarith),
    mul_nonneg (show 0≤(N:ℝ)-1 by linarith) hy,
    mul_nonneg (show 0≤(N:ℝ)-1 by linarith) (show 0≤1/2-y by linarith)]

theorem gaussian_tail_bound {p y : ℝ} (hp : 0<p) (hy : 0≤y) (hy' : y≤1/2)
    {N : ℕ} (hN : 0<N) (n : ℕ) :
    gaussian p y (n+N)≤majorant p N n ∧ gaussian p y (-(n+N:ℤ))≤majorant p N n := by
  have he : majorant p N n=Real.exp (-p*(((N:ℝ)-1/2)^2+2*N*n)) := by
    rw [majorant,← Real.exp_nat_mul,← Real.exp_add]
    congr 1
    ring
  rw [he]
  have hs:=square_bound n hN hy hy'
  constructor
  · apply Real.exp_le_exp.mpr
    push_cast at *
    exact mul_le_mul_of_nonpos_left hs.1 (by linarith)
  · apply Real.exp_le_exp.mpr
    push_cast at *
    exact mul_le_mul_of_nonpos_left hs.2 (by linarith)

theorem positive_tail_summable {p y : ℝ} (hp : 0<p) (hy : 0≤y) (hy' : y≤1/2)
    {N : ℕ} (hN : 0<N) : Summable (fun n : ℕ=>gaussian p y (n+N)) :=
  (majorant_summable hp hN).of_nonneg_of_le (fun n=>(Real.exp_pos _).le)
    (fun n=>(gaussian_tail_bound hp hy hy' hN n).1)

theorem negative_tail_summable {p y : ℝ} (hp : 0<p) (hy : 0≤y) (hy' : y≤1/2)
    {N : ℕ} (hN : 0<N) : Summable (fun n : ℕ=>gaussian p y (-(n+N:ℤ))) :=
  (majorant_summable hp hN).of_nonneg_of_le (fun n=>(Real.exp_pos _).le)
    (fun n=>(gaussian_tail_bound hp hy hy' hN n).2)

theorem positive_tail_tsum_le {p y : ℝ} (hp : 0<p) (hy : 0≤y) (hy' : y≤1/2)
    {N : ℕ} (hN : 0<N) :
    (∑'n : ℕ,gaussian p y (n+N))≤Real.exp (-p*((N:ℝ)-1/2)^2)/(1-Real.exp (-2*p*N)) := by
  rw [← majorant_tsum hp hN]
  exact (positive_tail_summable hp hy hy' hN).tsum_le_tsum
    (fun n=>(gaussian_tail_bound hp hy hy' hN n).1) (majorant_summable hp hN)

theorem negative_tail_tsum_le {p y : ℝ} (hp : 0<p) (hy : 0≤y) (hy' : y≤1/2)
    {N : ℕ} (hN : 0<N) :
    (∑'n : ℕ,gaussian p y (-(n+N:ℤ)))≤Real.exp (-p*((N:ℝ)-1/2)^2)/(1-Real.exp (-2*p*N)) := by
  rw [← majorant_tsum hp hN]
  exact (negative_tail_summable hp hy hy' hN).tsum_le_tsum
    (fun n=>(gaussian_tail_bound hp hy hy' hN n).2) (majorant_summable hp hN)

theorem gaussian_summable {p y : ℝ} (hp : 0<p) (hy : 0≤y) (hy' : y≤1/2) :
    Summable (gaussian p y) := by
  apply Summable.of_nat_of_neg_add_one
  · exact (summable_nat_add_iff 1).mp (by simpa only [Nat.cast_add,Nat.cast_one]
      using (positive_tail_summable (N:=1) hp hy hy' (by omega)))
  · exact negative_tail_summable hp hy hy' (N:=1) (by omega)

/-- The source's unrestricted shifted Gaussian bound, valid uniformly on [0,1/2]. -/
theorem gaussian_tsum_le {p y : ℝ} (hp : 0<p) (hy : 0≤y) (hy' : y≤1/2) :
    (∑'n,gaussian p y n) ≤ 1+2*Real.exp (-p/4)/(1-Real.exp (-2*p)) := by
  have hpos : Summable (fun n : ℕ=>gaussian p y n) :=
    (summable_nat_add_iff 1).mp (by simpa only [Nat.cast_add,Nat.cast_one]
      using (positive_tail_summable (N:=1) hp hy hy' (by omega)))
  rw [tsum_of_nat_of_neg_add_one hpos (negative_tail_summable hp hy hy' (N:=1) (by omega)),
    hpos.tsum_eq_zero_add]
  have h0 : gaussian p y 0≤1 := by
    unfold gaussian
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _)
  have harg : -p*((1:ℝ)-1/2)^2= -p/4 := by ring
  have h1 := positive_tail_tsum_le (N:=1) hp hy hy' (by omega)
  have h2 := negative_tail_tsum_le (N:=1) hp hy hy' (by omega)
  simp only [Nat.cast_one,mul_one,harg] at h1 h2
  simp only [Nat.cast_zero,Nat.cast_add,Nat.cast_one] at *
  rw [mul_div_assoc]
  linarith

#print axioms gaussian_tsum_le
end BecknerOnofri.HighDim.RadialPoissonGaussian
