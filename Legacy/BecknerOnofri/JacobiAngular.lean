module

public import Legacy.BecknerOnofri.JacobiPolynomial
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Calculus.ContDiff.Deriv

@[expose] public section

/-! Actual one-variable angular conjugation of the Jacobi differential expression.
This is a pointwise identity; no closed-operator or Friedrichs-domain identification is asserted.
-/
noncomputable section
open Filter
open scoped ContDiff Topology
namespace Legacy.BecknerOnofri.JacobiAngular

def angular (m : ℕ) (f : ℝ → ℝ) (t : ℝ) : ℝ := Real.sin t ^ m * f (Real.cos t)

def jacobi (m : ℕ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  -(1-x^2) * deriv (deriv f) x + (2*(m:ℝ)+1)*x*deriv f x

def angularOperator (m : ℕ) (g : ℝ → ℝ) (t : ℝ) : ℝ :=
  -deriv (deriv g) t + (m:ℝ)*((m:ℝ)-1)/(Real.sin t)^2*g t

def first (m : ℕ) (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.sin t ^ m * ((m:ℝ)*(Real.cos t/Real.sin t)*f (Real.cos t) - Real.sin t*deriv f (Real.cos t))

theorem angular_hasDerivAt (m : ℕ) {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    {t : ℝ} (hs : Real.sin t ≠ 0) : HasDerivAt (angular m f) (first m f t) t := by
  induction m with
  | zero =>
    convert! (hf (Real.cos t)).hasDerivAt.comp t (Real.hasDerivAt_cos t) using 1
    · funext x; simp [angular]
    · simp [first]; ring
  | succ m ih =>
    have h := (Real.hasDerivAt_sin t).mul ih
    convert! h using 1
    · funext x; simp [angular, pow_succ]; ring
    · simp only [first, angular, Nat.cast_add, Nat.cast_one, pow_succ]
      field_simp
      ring

theorem angular_deriv (m : ℕ) {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    {t : ℝ} (hs : Real.sin t ≠ 0) : deriv (angular m f) t = first m f t :=
  (angular_hasDerivAt m hf hs).deriv

theorem sin_pow_hasDerivAt (m : ℕ) {t : ℝ} (hs : Real.sin t ≠ 0) :
    HasDerivAt (fun x : ℝ => Real.sin x^m)
      (Real.sin t^m*((m:ℝ)*(Real.cos t/Real.sin t))) t := by
  convert! angular_hasDerivAt m (f := fun _ => (1 : ℝ)) (differentiable_const 1) hs using 1
  · funext x; simp [angular]
  · simp [first]

theorem cot_hasDerivAt {t : ℝ} (hs : Real.sin t ≠ 0) :
    HasDerivAt (fun x : ℝ => Real.cos x/Real.sin x) (-1/(Real.sin t)^2) t := by
  convert! (Real.hasDerivAt_cos t).div (Real.hasDerivAt_sin t) hs using 1
  field_simp
  nlinarith [Real.sin_sq_add_cos_sq t]

theorem first_hasDerivAt (m : ℕ) {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    {t : ℝ} (hs : Real.sin t ≠ 0) :
    HasDerivAt (first m f)
      (Real.sin t^m * ((m:ℝ)*(Real.cos t/Real.sin t)*
        ((m:ℝ)*(Real.cos t/Real.sin t)*f (Real.cos t) - Real.sin t*deriv f (Real.cos t)) +
        (-(m:ℝ)/(Real.sin t)^2*f (Real.cos t) - ((m:ℝ)+1)*Real.cos t*deriv f (Real.cos t) +
          Real.sin t^2*deriv (deriv f) (Real.cos t)))) t := by
  have hfd : Differentiable ℝ f := hf.differentiable (by simp)
  have hfdd : Differentiable ℝ (deriv f) := ((contDiff_infty_iff_deriv.mp hf).2).differentiable (by simp)
  have hfc := (hfd (Real.cos t)).hasDerivAt.comp t (Real.hasDerivAt_cos t)
  have hfdc := (hfdd (Real.cos t)).hasDerivAt.comp t (Real.hasDerivAt_cos t)
  have hb := (((cot_hasDerivAt hs).const_mul (m:ℝ)).mul hfc).sub
    ((Real.hasDerivAt_sin t).mul hfdc)
  have h := (sin_pow_hasDerivAt m hs).mul hb
  convert! h using 1
  dsimp only [Pi.mul_apply, Pi.sub_apply, Function.comp_apply]
  field_simp
  ring

theorem angular_second_deriv (m : ℕ) {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    {t : ℝ} (hs : Real.sin t ≠ 0) :
    deriv (deriv (angular m f)) t =
      Real.sin t^m * ((m:ℝ)*(Real.cos t/Real.sin t)*
        ((m:ℝ)*(Real.cos t/Real.sin t)*f (Real.cos t) - Real.sin t*deriv f (Real.cos t)) +
        (-(m:ℝ)/(Real.sin t)^2*f (Real.cos t) - ((m:ℝ)+1)*Real.cos t*deriv f (Real.cos t) +
          Real.sin t^2*deriv (deriv f) (Real.cos t))) := by
  have he : deriv (angular m f) =ᶠ[𝓝 t] first m f := by
    filter_upwards [Real.continuous_sin.continuousAt.eventually_ne hs] with y hy
    exact angular_deriv m (hf.differentiable (by simp)) hy
  rw [he.deriv_eq]
  exact (first_hasDerivAt m hf hs).deriv

/-- The conjugation identity holds for the actual twice-differentiated angular function. -/
theorem angular_conjugation (m : ℕ) {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    {t : ℝ} (hs : Real.sin t ≠ 0) :
    angularOperator m (angular m f) t =
      Real.sin t^m * (jacobi m f (Real.cos t) + (m:ℝ)^2*f (Real.cos t)) := by
  rw [angularOperator, angular_second_deriv m hf hs]
  unfold angular jacobi
  have hc : Real.cos t^2 = 1-Real.sin t^2 := by nlinarith [Real.sin_sq_add_cos_sq t]
  field_simp
  ring_nf
  rw [hc]
  ring

/-- The actual Jacobi differential expression agrees with the already-proved formal polynomial one. -/
theorem jacobi_eval (m : ℕ) (p : Polynomial ℝ) (x : ℝ) :
    jacobi m (fun y => p.eval y) x = (JacobiPolynomial.jacobi m p).eval x := by
  have hd : deriv (fun y => p.eval y) = fun y => p.derivative.eval y := funext (fun y => p.deriv (x := y))
  unfold jacobi
  rw [hd, p.derivative.deriv]
  simp [JacobiPolynomial.jacobi]

theorem polynomial_contDiff (p : Polynomial ℝ) : ContDiff ℝ ∞ (fun y => p.eval y) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa using hp.add hq
  | monomial n a =>
    simpa using (contDiff_const.mul (contDiff_id.pow n) : ContDiff ℝ ∞ (fun x : ℝ => a * x^n))

theorem angular_conjugation_polynomial (m : ℕ) (p : Polynomial ℝ)
    {t : ℝ} (hs : Real.sin t ≠ 0) :
    angularOperator m (angular m (fun y => p.eval y)) t =
      Real.sin t^m * (JacobiPolynomial.shifted m p).eval (Real.cos t) := by
  have h := angular_conjugation m (f := fun y => p.eval y) (polynomial_contDiff p) hs
  rw [jacobi_eval] at h
  simpa [JacobiPolynomial.shifted] using h

#print axioms angular_conjugation
#print axioms angular_conjugation_polynomial
end Legacy.BecknerOnofri.JacobiAngular
