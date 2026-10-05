module

public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

@[expose] public section

/-! Integrating out variables preserves convexity and monotonicity of the
logarithmic profile. This is the integral form of the conditional Hessian
identity in the manuscript, proved by normalized exponential convexity. -/

noncomputable section
open MeasureTheory Set

namespace BecknerOnofri.HighDim.ConditionalEntropy

theorem log_integral_exp_convex {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [NeZero μ] {s : Set ℝ} (hs : Convex ℝ s)
    (V : ℝ → X → ℝ) (hV : ∀ y, ConvexOn ℝ s (fun t => V t y))
    (hI : ∀ t ∈ s, Integrable (fun y => Real.exp (V t y)) μ) :
    ConvexOn ℝ s (fun t => Real.log (∫ y, Real.exp (V t y) ∂μ)) := by
  refine ⟨hs, ?_⟩
  intro x hx z hz a b ha hb hab
  simp only [smul_eq_mul]
  let A := ∫ y, Real.exp (V x y) ∂μ
  let B := ∫ y, Real.exp (V z y) ∂μ
  let C := a * Real.log A + b * Real.log B
  have hA : 0 < A := integral_exp_pos (hI x hx)
  have hB : 0 < B := integral_exp_pos (hI z hz)
  have hxz : a * x + b * z ∈ s := hs hx hz ha hb hab
  have hpoint (y : X) : Real.exp (V (a * x + b * z) y) / Real.exp C ≤
      a * (Real.exp (V x y) / A) + b * (Real.exp (V z y) / B) := by
    rw [← Real.exp_sub]
    calc
      _ ≤ Real.exp (a * (V x y - Real.log A) + b * (V z y - Real.log B)) := by
        apply Real.exp_le_exp.mpr
        have hv := (hV y).2 hx hz ha hb hab
        simp only [smul_eq_mul] at hv
        dsimp only [C]
        nlinarith
      _ ≤ a * Real.exp (V x y - Real.log A) + b * Real.exp (V z y - Real.log B) := by
        exact convexOn_exp.2 (mem_univ _) (mem_univ _) ha hb hab
      _ = _ := by rw [Real.exp_sub, Real.exp_sub, Real.exp_log hA, Real.exp_log hB]
  have hint := integral_mono ((hI _ hxz).div_const (Real.exp C))
    (((hI x hx).div_const A).const_mul a |>.add (((hI z hz).div_const B).const_mul b)) hpoint
  simp only [Pi.add_apply] at hint
  rw [integral_add (((hI x hx).div_const A).const_mul a)
      (((hI z hz).div_const B).const_mul b), integral_const_mul, integral_const_mul,
      integral_div, integral_div, integral_div] at hint
  change (∫ y, Real.exp (V (a * x + b * z) y) ∂μ) / Real.exp C ≤
    a * (A / A) + b * (B / B) at hint
  rw [div_self hA.ne', div_self hB.ne', mul_one, mul_one, hab] at hint
  apply (Real.log_le_iff_le_exp (integral_exp_pos (hI _ hxz))).mpr
  exact (div_le_one (Real.exp_pos C)).mp hint

theorem log_integral_exp_monotone {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [NeZero μ] {s : Set ℝ} (V : ℝ → X → ℝ)
    (hV : ∀ y, MonotoneOn (fun t => V t y) s)
    (hI : ∀ t ∈ s, Integrable (fun y => Real.exp (V t y)) μ) :
    MonotoneOn (fun t => Real.log (∫ y, Real.exp (V t y) ∂μ)) s := by
  intro x hx z hz hxz
  apply Real.log_le_log (integral_exp_pos (hI x hx))
  exact integral_mono (hI x hx) (hI z hz) (fun y => Real.exp_le_exp.mpr (hV y hx hz hxz))

#print axioms log_integral_exp_convex
#print axioms log_integral_exp_monotone

end BecknerOnofri.HighDim.ConditionalEntropy
