module

public import BecknerOnofri.BesselQuartic
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.Normed.Ring.InfiniteSum

@[expose] public section

/-! Identification of the positive Bessel series with its actual circle Haar integral. -/

noncomputable section
open MeasureTheory
open scoped ComplexConjugate

namespace BecknerOnofri.HighDim

def circleCosine (x : UnitAddCircle) : ℝ := (fourier 1 x).re

theorem circleCosine_coe (x : ℝ) :
    circleCosine (x : UnitAddCircle) = Real.cos (2 * Real.pi * x) := by
  unfold circleCosine
  rw [fourier_coe_apply]
  simp [Complex.exp_re]

def circleExpCoefficient (t : ℝ) (n : ℕ) : ℂ := (t ^ n / (n.factorial : ℝ) : ℝ)

theorem circle_fourier_norm (k : ℤ) (x : UnitAddCircle) : ‖fourier k x‖ = 1 := by
  rw [fourier_apply, Circle.norm_coe]

theorem circle_fourier_nat_mul (k : ℤ) (n : ℕ) (x : UnitAddCircle) :
    fourier ((n : ℤ) * k) x = (fourier k x) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.cast_succ, add_mul, one_mul, fourier_add, ih, pow_succ]

theorem circle_fourier_integral (k : ℤ) :
    (∫ x : UnitAddCircle, fourier k x ∂AddCircle.haarAddCircle) = if k = 0 then 1 else 0 := by
  have h := (orthonormal_iff_ite.mp (orthonormal_fourier (T := 1))) 0 k
  simpa [ContinuousMap.inner_toLp, fourier_zero, eq_comm] using h

theorem circle_exponential_hasSum (t : ℝ) (k : ℤ) (x : UnitAddCircle) :
    HasSum (fun n : ℕ => circleExpCoefficient t n * fourier ((n : ℤ) * k) x)
      (Complex.exp ((t : ℂ) * fourier k x)) := by
  have h := NormedSpace.expSeries_div_hasSum_exp ((t : ℂ) * fourier k x)
  rw [← Complex.exp_eq_exp_ℂ] at h
  apply h.congr_fun
  intro n
  rw [circle_fourier_nat_mul, mul_pow]
  unfold circleExpCoefficient
  push_cast
  ring

theorem circle_coefficient_fourier_norm (t : ℝ) (n : ℕ) (k : ℤ) (x : UnitAddCircle) :
    ‖circleExpCoefficient t n * fourier k x‖ = |t| ^ n / (n.factorial : ℝ) := by
  simp [circleExpCoefficient, Complex.norm_real, Real.norm_eq_abs]

def circleBesselTerm (t : ℝ) (p : ℕ × ℕ) (x : UnitAddCircle) : ℂ :=
  circleExpCoefficient t p.1 * circleExpCoefficient t p.2 *
    fourier ((p.1 : ℤ) - (p.2 : ℤ)) x

theorem circleBesselTerm_as_product (t : ℝ) (p : ℕ × ℕ) (x : UnitAddCircle) :
    circleBesselTerm t p x =
      (circleExpCoefficient t p.1 * fourier ((p.1 : ℤ) * 1) x) *
      (circleExpCoefficient t p.2 * fourier ((p.2 : ℤ) * (-1)) x) := by
  unfold circleBesselTerm
  simp only [mul_one, mul_neg_one]
  rw [sub_eq_add_neg, fourier_add]
  ring

theorem circleBesselTerm_hasSum (t : ℝ) (x : UnitAddCircle) :
    HasSum (fun p : ℕ × ℕ => circleBesselTerm t p x)
      (Real.exp (2 * t * circleCosine x) : ℂ) := by
  have hf := circle_exponential_hasSum t 1 x
  have hg := circle_exponential_hasSum t (-1) x
  have hfg : Summable (fun p : ℕ × ℕ =>
      (circleExpCoefficient t p.1 * fourier ((p.1 : ℤ) * 1) x) *
      (circleExpCoefficient t p.2 * fourier ((p.2 : ℤ) * (-1)) x)) := by
    apply Summable.of_norm
    simpa [circleExpCoefficient, Complex.norm_real, Real.norm_eq_abs] using
      (Real.summable_pow_div_factorial |t|).mul_of_nonneg
        (Real.summable_pow_div_factorial |t|) (fun n => by positivity) (fun n => by positivity)
  have h := hf.mul hg hfg
  have he : Complex.exp ((t : ℂ) * fourier 1 x) * Complex.exp ((t : ℂ) * fourier (-1) x) =
      (Real.exp (2 * t * circleCosine x) : ℂ) := by
    rw [← Complex.exp_add, fourier_neg, ← mul_add, Complex.add_conj]
    rw [← Complex.ofReal_mul, ← Complex.ofReal_exp]
    congr 2
    dsimp [circleCosine]
    ring
  rw [he] at h
  apply h.congr_fun
  intro p
  exact circleBesselTerm_as_product t p x

theorem circleBesselTerm_norm (t : ℝ) (p : ℕ × ℕ) (x : UnitAddCircle) :
    ‖circleBesselTerm t p x‖ =
      (|t| ^ p.1 / (p.1.factorial : ℝ)) * (|t| ^ p.2 / (p.2.factorial : ℝ)) := by
  rw [circleBesselTerm_as_product, norm_mul]
  rw [circle_coefficient_fourier_norm, circle_coefficient_fourier_norm]

theorem circleBesselTerm_integrable (t : ℝ) (p : ℕ × ℕ) :
    Integrable (circleBesselTerm t p) AddCircle.haarAddCircle := by
  apply Integrable.of_bound
    (by unfold circleBesselTerm; fun_prop)
    ((|t| ^ p.1 / (p.1.factorial : ℝ)) * (|t| ^ p.2 / (p.2.factorial : ℝ)))
  exact Filter.Eventually.of_forall (fun x => (circleBesselTerm_norm t p x).le)

theorem circleBesselTerm_summable_integral_norm (t : ℝ) :
    Summable (fun p : ℕ × ℕ => ∫ x : UnitAddCircle, ‖circleBesselTerm t p x‖
      ∂AddCircle.haarAddCircle) := by
  simp_rw [circleBesselTerm_norm]
  simp only [integral_const, probReal_univ, one_smul]
  exact (Real.summable_pow_div_factorial |t|).mul_of_nonneg
    (Real.summable_pow_div_factorial |t|) (fun n => by positivity) (fun n => by positivity)

theorem circleBesselTerm_integral (t : ℝ) (p : ℕ × ℕ) :
    (∫ x : UnitAddCircle, circleBesselTerm t p x ∂AddCircle.haarAddCircle) =
      if p.1 = p.2 then (besselSeriesTerm (t ^ 2) p.1 : ℂ) else 0 := by
  rcases p with ⟨n, m⟩
  unfold circleBesselTerm
  rw [integral_const_mul, circle_fourier_integral]
  simp only [sub_eq_zero, Int.natCast_inj]
  by_cases h : n = m
  · subst m
    simp only [↓reduceIte, mul_one]
    unfold circleExpCoefficient besselSeriesTerm
    push_cast
    rw [← pow_mul, Nat.mul_comm 2 n, pow_mul]
    ring
  · simp [h]

theorem besselI0Two_eq_circle_integral (t : ℝ) :
    besselI0Two t = ∫ x : UnitAddCircle, Real.exp (2 * t * circleCosine x)
      ∂AddCircle.haarAddCircle := by
  have hi := hasSum_integral_of_summable_integral_norm
    (circleBesselTerm_integrable t) (circleBesselTerm_summable_integral_norm t)
  have hint : (∫ x : UnitAddCircle, ∑' p : ℕ × ℕ, circleBesselTerm t p x
      ∂AddCircle.haarAddCircle) =
      (∫ x : UnitAddCircle, Real.exp (2 * t * circleCosine x) ∂AddCircle.haarAddCircle : ℝ) := by
    rw [← integral_complex_ofReal]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun x => (circleBesselTerm_hasSum t x).tsum_eq)
  rw [hint] at hi
  simp_rw [circleBesselTerm_integral] at hi
  have hdiag := hi.prod_fiberwise (fun n : ℕ => by
    simpa only [eq_comm] using hasSum_ite_eq n (besselSeriesTerm (t ^ 2) n : ℂ))
  have hreal : HasSum (fun n : ℕ => (besselSeriesTerm (t ^ 2) n : ℂ)) (besselI0Two t : ℂ) := by
    apply Complex.hasSum_ofReal.mpr
    rw [besselI0Two_eq_series]
    exact (besselSeries_summable (sq_nonneg t)).hasSum
  exact Complex.ofReal_injective (hreal.unique hdiag)

theorem circle_log_partition_quartic {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1 / 5) :
    Real.log (∫ x : UnitAddCircle, Real.exp (2 * t * circleCosine x)
      ∂AddCircle.haarAddCircle) ≤ t ^ 2 - (6 / 25 : ℝ) * t ^ 4 := by
  rw [← besselI0Two_eq_circle_integral]
  exact log_besselI0Two_quartic ht ht'

end BecknerOnofri.HighDim
