import Legacy.BecknerOnofri.FiniteDifferenceSmooth
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.FDeriv.Congr

/-! Actual coordinate differentiation rules on the closed cube, including its boundary. -/
noncomputable section
open Set
open scoped ContDiff
namespace Legacy.BecknerOnofri.MixedExponentialDerivatives
open FiniteDifferences

theorem coordinateDerivative_congr {d : ℕ} (i : Fin d) {f g : Space d → ℝ}
    (he : EqOn f g (closedCube d)) {x : Space d} (hx : x ∈ closedCube d) :
    coordinateDerivative i f x = coordinateDerivative i g x := by
  unfold coordinateDerivative
  rw [fderivWithin_congr' he hx]

theorem coordinateDerivative_const {d : ℕ} (i : Fin d) (c : ℝ) (x : Space d) :
    coordinateDerivative i (fun _ => c) x = 0 := by
  simp [coordinateDerivative]

theorem coordinateDerivative_add {d : ℕ} (i : Fin d) {f g : Space d → ℝ}
    (hf : ContDiffOn ℝ ∞ f (closedCube d)) (hg : ContDiffOn ℝ ∞ g (closedCube d))
    {x : Space d} (hx : x ∈ closedCube d) :
    coordinateDerivative i (fun y => f y + g y) x =
      coordinateDerivative i f x + coordinateDerivative i g x := by
  unfold coordinateDerivative
  change (fderivWithin ℝ (f + g) (closedCube d) x) (basis i) = _
  rw [fderivWithin_add (uniqueDiffOn_closedCube d x hx)
    (hf.differentiableOn (by simp) x hx) (hg.differentiableOn (by simp) x hx)]
  rfl

theorem coordinateDerivative_mul {d : ℕ} (i : Fin d) {f g : Space d → ℝ}
    (hf : ContDiffOn ℝ ∞ f (closedCube d)) (hg : ContDiffOn ℝ ∞ g (closedCube d))
    {x : Space d} (hx : x ∈ closedCube d) :
    coordinateDerivative i (fun y => f y * g y) x =
      coordinateDerivative i f x * g x + f x * coordinateDerivative i g x := by
  unfold coordinateDerivative
  change (fderivWithin ℝ (f * g) (closedCube d) x) (basis i) = _
  rw [fderivWithin_mul (uniqueDiffOn_closedCube d x hx)
    (hf.differentiableOn (by simp) x hx) (hg.differentiableOn (by simp) x hx)]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem coordinateDerivative_exp {d : ℕ} (i : Fin d) {u : Space d → ℝ}
    (hu : ContDiffOn ℝ ∞ u (closedCube d)) {x : Space d} (hx : x ∈ closedCube d) :
    coordinateDerivative i (fun y => Real.exp (u y)) x =
      Real.exp (u x) * coordinateDerivative i u x := by
  unfold coordinateDerivative
  rw [fderivWithin_exp (hu.differentiableOn (by simp) x hx) (uniqueDiffOn_closedCube d x hx)]
  rfl

theorem mixedPartial_exp_one {d : ℕ} (i : Fin d) {u : Space d → ℝ}
    (hu : ContDiffOn ℝ ∞ u (closedCube d)) {x : Space d} (hx : x ∈ closedCube d) :
    mixedPartial [i] (fun y => Real.exp (u y)) x = Real.exp (u x) * mixedPartial [i] u x :=
  coordinateDerivative_exp i hu hx

#print axioms mixedPartial_exp_one
end Legacy.BecknerOnofri.MixedExponentialDerivatives
