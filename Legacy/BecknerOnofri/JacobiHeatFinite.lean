import Legacy.BecknerOnofri.JacobiCompleteness
import Legacy.BecknerOnofri.ParabolicComparison
import Legacy.BecknerOnofri.SpectralHeatInverse

/-! Positivity for actual finite Jacobi spectral heat evolutions.
Every regularity, PDE, endpoint and initial-value assertion used by the maximum principle
is proved from the concrete normalized Jacobi eigenfunctions. -/
noncomputable section
open Set MeasureTheory Filter Polynomial Classical
open scoped ContDiff Topology BigOperators
namespace Legacy.BecknerOnofri.JacobiHeatPositivity
open JacobiEigenfunctions

def potential (m : ℕ) (x : ℝ) : ℝ := (m:ℝ)*((m:ℝ)-1)/Real.sin x^2

def finiteHeat (m : ℕ) (F : Finset ℕ) (c : ℕ→ℝ) (t x : ℝ) : ℝ :=
  ∑ n∈F, c n*Real.exp (-t*eigenvalue m n)*normalizedFunction m n x

def finiteTime (m : ℕ) (F : Finset ℕ) (c : ℕ→ℝ) (t x : ℝ) : ℝ :=
  ∑ n∈F, c n*(-eigenvalue m n*Real.exp (-t*eigenvalue m n))*normalizedFunction m n x

def finiteSpace (m : ℕ) (F : Finset ℕ) (c : ℕ→ℝ) (t x : ℝ) : ℝ :=
  ∑ n∈F, c n*Real.exp (-t*eigenvalue m n)*deriv (normalizedFunction m n) x

def finiteSecond (m : ℕ) (F : Finset ℕ) (c : ℕ→ℝ) (t x : ℝ) : ℝ :=
  ∑ n∈F, c n*Real.exp (-t*eigenvalue m n)*deriv (deriv (normalizedFunction m n)) x

theorem finiteHeat_continuous (m : ℕ) (F : Finset ℕ) (c : ℕ→ℝ) :
    Continuous (fun z : ℝ×ℝ => finiteHeat m F c z.1 z.2) := by
  apply continuous_finset_sum
  intro n hn
  exact (continuous_const.mul (Real.continuous_exp.comp
    (continuous_fst.neg.mul continuous_const))).mul
    ((normalizedFunction_contDiff m n).continuous.comp continuous_snd)

theorem finiteHeat_time (m : ℕ) (F : Finset ℕ) (c : ℕ→ℝ) (t x : ℝ) :
    HasDerivAt (fun r => finiteHeat m F c r x) (finiteTime m F c t x) t := by
  apply HasDerivAt.fun_sum
  intro n hn
  convert! (((((hasDerivAt_id t).neg.mul_const (eigenvalue m n)).exp).const_mul (c n)).mul_const
    (normalizedFunction m n x)) using 1 <;> simp only [Pi.neg_apply,id_eq] <;> ring

theorem finiteHeat_space (m : ℕ) (F : Finset ℕ) (c : ℕ→ℝ) (t x : ℝ) :
    HasDerivAt (finiteHeat m F c t) (finiteSpace m F c t x) x := by
  apply HasDerivAt.fun_sum
  intro n hn
  exact (((normalizedFunction_contDiff m n).differentiable (by simp) x).hasDerivAt).const_mul _

theorem finiteHeat_second (m : ℕ) (F : Finset ℕ) (c : ℕ→ℝ) (t x : ℝ) :
    HasDerivAt (finiteSpace m F c t) (finiteSecond m F c t x) x := by
  apply HasDerivAt.fun_sum
  intro n hn
  exact ((((contDiff_infty_iff_deriv.mp (normalizedFunction_contDiff m n)).2).differentiable
    (by simp) x).hasDerivAt).const_mul _

theorem finiteHeat_equation (m : ℕ) (F : Finset ℕ) (c : ℕ→ℝ) (t : ℝ)
    {x : ℝ} (hx : x∈Ioo 0 Real.pi) :
    finiteTime m F c t x - finiteSecond m F c t x + potential m x*finiteHeat m F c t x = 0 := by
  unfold finiteTime finiteSecond finiteHeat
  rw [Finset.mul_sum,← Finset.sum_sub_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro n hn
  have h := normalizedFunction_equation m n hx
  unfold JacobiAngular.angularOperator at h
  unfold potential
  linear_combination (c n*Real.exp (-t*eigenvalue m n))*h

theorem potential_nonnegative {m : ℕ} (hm : 0<m) (x : ℝ) : 0≤potential m x := by
  have hm' : (1:ℝ)≤m := by exact_mod_cast hm
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr hm')) (sq_nonneg _)

@[simp] theorem finiteHeat_zero_time (m : ℕ) (F : Finset ℕ) (c : ℕ→ℝ) (x : ℝ) :
    finiteHeat m F c 0 x = ∑ n∈F,c n*normalizedFunction m n x := by simp [finiteHeat]

@[simp] theorem finiteHeat_left {m : ℕ} (hm : 0<m) (F : Finset ℕ) (c : ℕ→ℝ) (t : ℝ) :
    finiteHeat m F c t 0=0 := by simp [finiteHeat,normalizedFunction_zero hm]

@[simp] theorem finiteHeat_right {m : ℕ} (hm : 0<m) (F : Finset ℕ) (c : ℕ→ℝ) (t : ℝ) :
    finiteHeat m F c t Real.pi=0 := by simp [finiteHeat,normalizedFunction_pi hm]

/-- A nonnegative finite spectral initial function has nonnegative actual heat evolution.
The coefficients themselves may have either sign. -/
theorem finiteHeat_nonnegative {m : ℕ} (hm : 0<m) (F : Finset ℕ) (c : ℕ→ℝ)
    (hinitial : ∀x∈Icc 0 Real.pi, 0≤∑n∈F,c n*normalizedFunction m n x)
    {t x : ℝ} (ht : 0≤t) (hx : x∈Icc 0 Real.pi) : 0≤finiteHeat m F c t x := by
  apply ParabolicComparison.nonnegative (finiteHeat m F c) (finiteTime m F c)
    (finiteSpace m F c) (finiteSecond m F c) (potential m) t 0 Real.pi
    (finiteHeat_continuous m F c).continuousOn
    (fun r _ y _ => (finiteHeat_time m F c r y).hasDerivWithinAt)
    (fun r _ y _ => finiteHeat_space m F c r y)
    (fun r _ y _ => finiteHeat_second m F c r y)
    (fun y _ => potential_nonnegative hm y)
    (fun r _ y hy => (finiteHeat_equation m F c r hy).ge)
    (by simpa only [finiteHeat_zero_time] using hinitial)
    (by intro r hr; simp [finiteHeat_left hm])
    (by intro r hr; simp [finiteHeat_right hm])
    t ⟨ht,le_rfl⟩ x hx

/-- Coefficients in the actual normalized Jacobi basis of an angular polynomial. -/
def polynomialCoefficients (m : ℕ) (p : Polynomial ℝ) (n : ℕ) : ℝ :=
  (polynomialBasis m).repr p n * Real.sqrt (normSquared m n)

def polynomialHeat (m : ℕ) (p : Polynomial ℝ) (t x : ℝ) : ℝ :=
  finiteHeat m ((polynomialBasis m).repr p).support (polynomialCoefficients m p) t x

/-- The spectral initial value is exactly the prescribed actual angular polynomial. -/
theorem polynomialHeat_initial (m : ℕ) (p : Polynomial ℝ) (x : ℝ) :
    polynomialHeat m p 0 x = angularPolynomial m p x := by
  have hr := congrArg (fun q : Polynomial ℝ => q.eval (Real.cos x))
    ((polynomialBasis m).linearCombination_repr p)
  simp only [Finsupp.linearCombination_apply,Finsupp.sum,eval_finset_sum,eval_smul,
    smul_eq_mul,polynomialBasis_apply] at hr
  rw [polynomialHeat,finiteHeat_zero_time,angularPolynomial,← hr,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  unfold polynomialCoefficients normalizedFunction eigenfunction JacobiAngular.angular
  have hs : Real.sqrt (normSquared m n) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (normSquared_pos m n))
  field_simp

/-- Positivity starts from an actual nonnegative polynomial on the cosine interval.
Its finite spectral coefficients need not be nonnegative. -/
theorem polynomialHeat_nonnegative {m : ℕ} (hm : 0<m) (p : Polynomial ℝ)
    (hp : ∀y∈Icc (-1:ℝ) 1, 0≤p.eval y) {t x : ℝ} (ht : 0≤t)
    (hx : x∈Icc 0 Real.pi) : 0≤polynomialHeat m p t x := by
  apply finiteHeat_nonnegative hm _ _ _ ht hx
  intro y hy
  rw [← finiteHeat_zero_time]
  change 0≤polynomialHeat m p 0 y
  rw [polynomialHeat_initial]
  exact mul_nonneg (pow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hy.1 hy.2) m)
    (hp _ ⟨Real.neg_one_le_cos y,Real.cos_le_one y⟩)

#print axioms polynomialHeat_initial
#print axioms polynomialHeat_nonnegative
#print axioms finiteHeat_nonnegative
end Legacy.BecknerOnofri.JacobiHeatPositivity
