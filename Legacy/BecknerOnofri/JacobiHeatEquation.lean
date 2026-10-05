import Legacy.BecknerOnofri.JacobiHeatSmooth
import Legacy.BecknerOnofri.JacobiNeumann

/-! The genuine, complete Jacobi heat kernel satisfies its heat equation and
Dirichlet or Neumann boundary conditions. All series derivatives are justified
by explicit summable polynomial Gaussian bounds. -/
set_option maxHeartbeats 800000
noncomputable section
open Set Filter
open scoped BigOperators ContDiff Topology
namespace Legacy.BecknerOnofri.JacobiHeatBounds
open JacobiEigenfunctions

def spatialTerm (m n k : ℕ) (t x y : ℝ) : ℝ :=
  Real.exp (-t * eigenvalue m n) * iteratedDeriv k (normalizedFunction m n) x * normalizedFunction m n y

def spatialMajorant (m k : ℕ) (t : ℝ) (n : ℕ) : ℝ :=
  (derivativeConstant m k * derivativeConstant m 0) *
    (degreeBase m n ^ (derivativeDegree m k + derivativeDegree m 0) * Real.exp (-t * eigenvalue m n))

theorem scalar_derivative_bound (m n k : ℕ) (x : ℝ) :
    ‖iteratedDeriv k (normalizedFunction m n) x‖ ≤ derivativeConstant m k * degreeBase m n ^ derivativeDegree m k := by
  simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv] using normalizedFunction_derivative_bound m n k x

theorem spatialTerm_bound (m n k : ℕ) (t x y : ℝ) :
    ‖spatialTerm m n k t x y‖ ≤ spatialMajorant m k t n := by
  have h0 := scalar_derivative_bound m n 0 y
  simp only [iteratedDeriv_zero] at h0
  have h := mul_le_mul (scalar_derivative_bound m n k x) h0 (norm_nonneg _) (mul_nonneg (derivativeConstant_nonneg m k) (pow_nonneg (degreeBase_pos m n).le _))
  have he := mul_le_mul_of_nonneg_left h (Real.exp_pos (-t*eigenvalue m n)).le
  simpa only [spatialTerm, norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), spatialMajorant, pow_add,
    mul_assoc, mul_left_comm, mul_comm] using he

theorem spatialMajorant_summable (m k : ℕ) {t : ℝ} (ht : 0 < t) : Summable (spatialMajorant m k t) :=
  (shifted_polynomial_gaussian_summable ht m _).mul_left _

theorem spatialTerm_summable (m k : ℕ) {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    Summable (fun n => spatialTerm m n k t x y) :=
  (spatialMajorant_summable m k ht).of_norm_bounded (fun n => spatialTerm_bound m n k t x y)

theorem spatialTerm_hasDerivAt (m n k : ℕ) (t x y : ℝ) :
    HasDerivAt (fun z => spatialTerm m n k t z y) (spatialTerm m n (k+1) t x y) x := by
  have hd := ((normalizedFunction_contDiff m n).differentiable_iteratedDeriv k (by exact_mod_cast (show (k : ℕ∞) < ⊤ by simp)) x).hasDerivAt
  simpa only [spatialTerm, iteratedDeriv_succ] using (hd.const_mul (Real.exp (-t*eigenvalue m n))).mul_const (normalizedFunction m n y)

theorem spatialSeries_hasDerivAt (m k : ℕ) {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    HasDerivAt (fun z => ∑' n : ℕ, spatialTerm m n k t z y)
      (∑' n : ℕ, spatialTerm m n (k+1) t x y) x :=
  hasDerivAt_tsum_of_isPreconnected (spatialMajorant_summable m (k+1) ht)
    isOpen_univ isPreconnected_univ (fun n z _ => spatialTerm_hasDerivAt m n k t z y)
    (fun n z _ => spatialTerm_bound m n (k+1) t z y) (mem_univ x)
    (spatialTerm_summable m k ht x y) (mem_univ x)

theorem heatKernel_eq_spatialSeries (m : ℕ) (t x y : ℝ) :
    heatKernel m t x y = ∑' n : ℕ, spatialTerm m n 0 t x y := by
  simp only [heatKernel,spatialTerm,iteratedDeriv_zero]

theorem heatKernel_hasDerivAt_space (m : ℕ) {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    HasDerivAt (fun z => heatKernel m t z y) (∑' n : ℕ, spatialTerm m n 1 t x y) x := by
  simpa only [heatKernel_eq_spatialSeries] using spatialSeries_hasDerivAt m 0 ht x y

theorem heatKernel_deriv_space (m : ℕ) {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    deriv (fun z => heatKernel m t z y) x = ∑' n : ℕ, spatialTerm m n 1 t x y :=
  (heatKernel_hasDerivAt_space m ht x y).deriv

theorem heatKernel_second_space (m : ℕ) {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    deriv (deriv (fun z => heatKernel m t z y)) x = ∑' n : ℕ, spatialTerm m n 2 t x y := by
  have he : deriv (fun z => heatKernel m t z y) = fun z => ∑' n : ℕ, spatialTerm m n 1 t z y :=
    funext (fun z => heatKernel_deriv_space m ht z y)
  rw [he]
  exact (spatialSeries_hasDerivAt m 1 ht x y).deriv

@[simp] theorem heatKernel_zero_left {m : ℕ} (hm : 0 < m) (t y : ℝ) : heatKernel m t 0 y = 0 := by
  simp only [heatKernel, normalizedFunction_zero hm, mul_zero, zero_mul, tsum_zero]

@[simp] theorem heatKernel_pi_left {m : ℕ} (hm : 0 < m) (t y : ℝ) : heatKernel m t Real.pi y = 0 := by
  simp only [heatKernel, normalizedFunction_pi hm, mul_zero, zero_mul, tsum_zero]

theorem heatKernel_symmetric (m : ℕ) (t x y : ℝ) : heatKernel m t x y = heatKernel m t y x := by
  unfold heatKernel
  apply tsum_congr
  intro n
  ring

@[simp] theorem heatKernel_neumann_zero {t : ℝ} (ht : 0 < t) (y : ℝ) :
    deriv (fun z => heatKernel 0 t z y) 0 = 0 := by
  rw [heatKernel_deriv_space 0 ht]
  simp [spatialTerm,iteratedDeriv_succ,normalizedFunction_neumann_deriv_zero]

@[simp] theorem heatKernel_neumann_pi {t : ℝ} (ht : 0 < t) (y : ℝ) :
    deriv (fun z => heatKernel 0 t z y) Real.pi = 0 := by
  rw [heatKernel_deriv_space 0 ht]
  simp [spatialTerm,iteratedDeriv_succ,normalizedFunction_neumann_deriv_pi]


theorem heatKernel_summable (m : ℕ) {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    Summable (fun n : ℕ => Real.exp (-t*eigenvalue m n)*normalizedFunction m n x*normalizedFunction m n y) := by
  simpa only [spatialTerm,iteratedDeriv_zero] using spatialTerm_summable m 0 ht x y

def timeDerivativeTerm (m n : ℕ) (t x y : ℝ) : ℝ :=
  -(eigenvalue m n) * Real.exp (-t*eigenvalue m n) * normalizedFunction m n x * normalizedFunction m n y

def timeDerivativeMajorant (m : ℕ) (ε : ℝ) (n : ℕ) : ℝ :=
  (derivativeConstant m 0)^2 * (degreeBase m n^(2+2*derivativeDegree m 0)*Real.exp (-ε*eigenvalue m n))

theorem timeDerivativeMajorant_summable (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    Summable (timeDerivativeMajorant m ε) :=
  (shifted_polynomial_gaussian_summable hε m _).mul_left _

theorem timeDerivativeTerm_bound (m n : ℕ) {ε t : ℝ} (ht : ε ≤ t) (x y : ℝ) :
    ‖timeDerivativeTerm m n t x y‖ ≤ timeDerivativeMajorant m ε n := by
  have hl : 0 ≤ eigenvalue m n := by unfold eigenvalue; positivity
  have hb : eigenvalue m n ≤ degreeBase m n^2 := by
    apply pow_le_pow_left₀ (by positivity)
    dsimp [degreeBase]
    push_cast
    linarith
  have he : Real.exp (-t*eigenvalue m n) ≤ Real.exp (-ε*eigenvalue m n) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hx := scalar_derivative_bound m n 0 x
  have hy := scalar_derivative_bound m n 0 y
  simp only [iteratedDeriv_zero] at hx hy
  have hc : 0 ≤ derivativeConstant m 0 * degreeBase m n^derivativeDegree m 0 :=
    mul_nonneg (derivativeConstant_nonneg m 0) (pow_nonneg (degreeBase_pos m n).le _)
  have h := mul_le_mul (mul_le_mul (mul_le_mul hb he (Real.exp_pos _).le (sq_nonneg _)) hx
    (norm_nonneg _) (mul_nonneg (sq_nonneg _) (Real.exp_nonneg _))) hy (norm_nonneg _)
    (mul_nonneg (mul_nonneg (sq_nonneg _) (Real.exp_nonneg _)) hc)
  calc
    ‖timeDerivativeTerm m n t x y‖ =
      eigenvalue m n * Real.exp (-t*eigenvalue m n) * ‖normalizedFunction m n x‖ * ‖normalizedFunction m n y‖ := by
        simp only [timeDerivativeTerm,norm_mul,norm_neg,Real.norm_eq_abs,
          abs_of_nonneg hl,abs_of_pos (Real.exp_pos _)]
    _ ≤ degreeBase m n^2 * Real.exp (-ε*eigenvalue m n) *
        (derivativeConstant m 0 * degreeBase m n^derivativeDegree m 0) *
        (derivativeConstant m 0 * degreeBase m n^derivativeDegree m 0) := h
    _ = timeDerivativeMajorant m ε n := by
      unfold timeDerivativeMajorant
      rw [show 2+2*derivativeDegree m 0 = 2+derivativeDegree m 0+derivativeDegree m 0 by omega,
        pow_add,pow_add]
      ring

theorem timeDerivativeTerm_summable (m : ℕ) {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    Summable (fun n => timeDerivativeTerm m n t x y) :=
  (timeDerivativeMajorant_summable m ht).of_norm_bounded (fun n => timeDerivativeTerm_bound m n (le_refl t) x y)

theorem heatKernel_hasDerivAt_time (m : ℕ) {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    HasDerivAt (fun u => heatKernel m u x y) (∑' n : ℕ, timeDerivativeTerm m n t x y) t := by
  have hε : 0 < t/2 := by linarith
  have hm : t ∈ Ioi (t/2) := by change t/2 < t; linarith
  change HasDerivAt (fun u => ∑' n : ℕ, Real.exp (-u*eigenvalue m n)*normalizedFunction m n x*normalizedFunction m n y) _ t
  apply hasDerivAt_tsum_of_isPreconnected (g' := fun n u => timeDerivativeTerm m n u x y)
    (timeDerivativeMajorant_summable m hε) isOpen_Ioi (convex_Ioi (t/2)).isPreconnected _ _ hm (heatKernel_summable m ht x y) hm
  · intro n u _
    have h := (((hasDerivAt_id u).neg.mul_const (eigenvalue m n)).exp.mul_const
      (normalizedFunction m n x)).mul_const (normalizedFunction m n y)
    simpa only [timeDerivativeTerm,Pi.neg_apply,id_eq,neg_mul,mul_neg,one_mul,mul_assoc,mul_left_comm,mul_comm] using h
  · intro n u hu
    exact timeDerivativeTerm_bound m n hu.le x y

theorem heatKernel_deriv_time (m : ℕ) {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    deriv (fun u => heatKernel m u x y) t = ∑' n : ℕ, timeDerivativeTerm m n t x y :=
  (heatKernel_hasDerivAt_time m ht x y).deriv

/-- The complete normalized kernel solves ∂t H = ∂x² H - m(m-1)csc²(x) H
at every positive time and every interior spatial point. -/
theorem heatKernel_equation (m : ℕ) {t x : ℝ} (ht : 0 < t) (hx : x ∈ Ioo 0 Real.pi) (y : ℝ) :
    deriv (fun u => heatKernel m u x y) t =
      deriv (deriv (fun z => heatKernel m t z y)) x -
        ((m:ℝ)*((m:ℝ)-1)/(Real.sin x)^2)*heatKernel m t x y := by
  rw [heatKernel_deriv_time m ht,heatKernel_second_space m ht,heatKernel_eq_spatialSeries,
    ← tsum_mul_left,← (spatialTerm_summable m 2 ht x y).tsum_sub
      ((spatialTerm_summable m 0 ht x y).mul_left _)]
  apply tsum_congr
  intro n
  have h := normalizedFunction_equation m n hx
  dsimp [JacobiAngular.angularOperator] at h
  simp only [timeDerivativeTerm,spatialTerm,iteratedDeriv_succ,iteratedDeriv_zero]
  linear_combination (Real.exp (-t*eigenvalue m n)*normalizedFunction m n y)*h


theorem heatKernel_contDiff_space (m : ℕ) {t : ℝ} (ht : 0 < t) (y : ℝ) :
    ContDiff ℝ ∞ (fun x => heatKernel m t x y) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  have he : (fun z : ℝ => jointHeat m ![t,z,y]) = (fun z => heatKernel m t z y) := by
    funext z
    simp [jointHeat_eq_heatKernel]
  rw [← he]
  exact (jointHeat_contDiffAt m (z := ![t,x,y]) ht).comp (f := fun z : ℝ => ![t,z,y]) x
    (by apply contDiffAt_pi.2; intro i; fin_cases i <;> simp <;> fun_prop)

theorem heatKernel_contDiff_right (m : ℕ) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    ContDiff ℝ ∞ (fun y => heatKernel m t x y) := by
  have he : (fun y => heatKernel m t x y) = (fun y => heatKernel m t y x) :=
    funext (fun y => heatKernel_symmetric m t x y)
  rw [he]
  exact heatKernel_contDiff_space m ht x

theorem heatKernel_angular_equation (m : ℕ) {t x : ℝ} (ht : 0 < t)
    (hx : x ∈ Ioo 0 Real.pi) (y : ℝ) :
    deriv (fun u => heatKernel m u x y) t =
      -JacobiAngular.angularOperator m (fun z => heatKernel m t z y) x := by
  rw [heatKernel_equation m ht hx]
  unfold JacobiAngular.angularOperator
  ring

@[simp] theorem heatKernel_zero_right {m : ℕ} (hm : 0 < m) (t x : ℝ) : heatKernel m t x 0 = 0 := by
  rw [heatKernel_symmetric,heatKernel_zero_left hm]

@[simp] theorem heatKernel_pi_right {m : ℕ} (hm : 0 < m) (t x : ℝ) : heatKernel m t x Real.pi = 0 := by
  rw [heatKernel_symmetric,heatKernel_pi_left hm]

#print axioms heatKernel_equation
#print axioms heatKernel_neumann_zero
#print axioms heatKernel_zero_left
end Legacy.BecknerOnofri.JacobiHeatBounds
