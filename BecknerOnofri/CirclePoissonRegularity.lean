import BecknerOnofri.CircleSeriesSmooth
import BecknerOnofri.CircleTorusFlow
import Mathlib.Analysis.SpecialFunctions.Exp

/-! Positive-time Poisson flow has arbitrarily many spatial derivatives.
Polynomially weighted exponential multipliers give absolute convergence
of every differentiated Fourier series. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
namespace BecknerOnofri.HighDim.CirclePoisson
open CircleOuter CircleFisher CircleRegularity Legacy.TorusEndpoint Legacy.BecknerOnofri.WeightedWiener

theorem poisson_polynomial_summable (m : ℕ) (s : ℝ) (hs : 0<s) :
    Summable (fun n : ℤ => |(n:ℝ)|^m*Real.exp (-|(n:ℝ)| *s)) := by
  apply summable_int_iff_summable_nat_and_neg.mpr
  have h := Real.summable_pow_mul_exp_neg_nat_mul m hs
  constructor <;> simpa only [Int.cast_natCast,Int.cast_neg,abs_neg,
    abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) _),mul_comm (-s),neg_mul,mul_neg] using h

theorem torus_flow_contDiff (p : Torus 1 → ℝ) (hp : Continuous p)
    (hw : Summable (fun k => linearWeight k*‖UnitAddTorus.mFourierCoeff (fun x => (p x:ℂ)) k‖))
    (s : ℝ) (hs : 0<s) (N : ℕ) :
    ContDiff ℝ N (fun x : ℝ => torusFlow s p (fun _ => (x:UnitAddCircle))) := by
  let a : Frequency 1 → ℂ := UnitAddTorus.mFourierCoeff (fun x => (p x:ℂ))
  let b : ℤ → ℂ := fun n => (Real.exp (-|(n:ℝ)| *s):ℂ)*a (fun _ => n)
  have h₀ : Summable (fun k => ‖a k‖) := summable_norm linearWeight_isWeight hw
  let C : ℝ := ∑' k,‖a k‖
  have hc (n : ℤ) : ‖a (fun _ => n)‖≤C := h₀.le_tsum (fun _ => n) (fun _ _ => norm_nonneg _)
  have hb (m : ℕ) : Summable (fun n : ℤ => |(n:ℝ)|^m*‖b n‖) := by
    apply Summable.of_nonneg_of_le (fun n => mul_nonneg (pow_nonneg (abs_nonneg _) _) (norm_nonneg _))
      (fun n => ?_) ((poisson_polynomial_summable m s hs).mul_right C)
    dsimp only [b]
    simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    calc
      _ = (|(n:ℝ)|^m*Real.exp (-|(n:ℝ)| *s))*‖a (fun _ => n)‖ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hc n) (by positivity)
  have hseries := contDiff_series N b (fun m _ => hb m)
  have hrep (x : ℝ) : (torusFlow s p (fun _ => (x:UnitAddCircle)):ℂ)=
      ∑' n : ℤ,b n*fourier n (x:UnitAddCircle) := by
    have h := torus_flow_series s hs p hp hw (fun _ => (x:UnitAddCircle))
    change (torusFlow s p (fun _ => (x:UnitAddCircle)):ℂ)=
      absoluteFourierSeries (fun k => (Real.exp (-|(k (0:Fin 1):ℝ)| *s):ℂ)*a k) (fun _ => (x:UnitAddCircle)) at h
    simpa only [series_eq_circle,b] using h
  have hreal := Complex.reCLM.contDiff.comp hseries
  convert hreal using 1
  funext x
  exact congrArg Complex.re (hrep x)

#print axioms torus_flow_contDiff
end BecknerOnofri.HighDim.CirclePoisson
