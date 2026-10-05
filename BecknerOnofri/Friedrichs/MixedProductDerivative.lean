import BecknerOnofri.Friedrichs.MixedCutoffL2
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Comp

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped ContDiff BigOperators
namespace BecknerOnofri.Friedrichs.MixedSpatial

lemma partialDerivative_productProfile {d : ℕ} (f : Fin d → ℝ → ℝ)
    (hf : ∀ i,Differentiable ℝ (f i)) (i : Fin d) (x : Space d) :
    partialDerivative i (productProfile f) x=
      (∏ j∈Finset.univ.erase i,f j (x j))*deriv (f i) (x i) := by
  have h (j : Fin d) : HasFDerivAt (fun y : Space d => f j (y j))
      (deriv (f j) (x j) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) j) x := by
    exact ((hf j (x j)).hasDerivAt).comp_hasFDerivAt (f := fun y : Space d => y j) x
      (hasFDerivAt_apply (𝕜 := ℝ) j x)
  have he := (HasFDerivAt.finsetProd (u := Finset.univ) (fun j _ => h j)).fderiv
  change fderiv ℝ (productProfile f) x=_ at he
  unfold partialDerivative
  rw [he]
  simp only [ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.proj_apply,smul_eq_mul]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j hj hji
    simp [Pi.single_eq_of_ne hji]
  · simp

#print axioms partialDerivative_productProfile
end BecknerOnofri.Friedrichs.MixedSpatial
