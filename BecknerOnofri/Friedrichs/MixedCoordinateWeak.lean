import BecknerOnofri.Friedrichs.PeriodicAngularWeak
import BecknerOnofri.Friedrichs.MixedProductDerivative
import Mathlib.Analysis.Calculus.FDeriv.Pi

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped ContDiff BigOperators
namespace BecknerOnofri.Friedrichs.MixedSpatial
open Legacy.BecknerOnofri.JacobiAngular

lemma coordinate_angular_weak (m : ℕ) {f φ : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hφ : ContDiff ℝ ∞ φ)
    (hend : m≠0 → φ 0=0 ∧ φ Real.pi=0) :
    (∫ t,deriv (angular m f) t*deriv φ t+
      ((m:ℝ)*((m:ℝ)-1)/(Real.sin t)^2)*angular m f t*φ t ∂coordinateMeasure m)=
      ∫ t,angularImage m f t*φ t ∂coordinateMeasure m := by
  by_cases hm : m=0
  · subst m
    simpa [coordinateMeasure] using periodic_angular_weak hf hφ
  · simpa [coordinateMeasure,hm] using angular_weak_conjugation m hf hφ (hend hm).1 (hend hm).2

lemma fiber_smooth {d : ℕ} {φ : Space d → ℝ} (hφ : ContDiff ℝ ∞ φ) (x : Space d) (i : Fin d) :
    ContDiff ℝ ∞ (fun t => φ (Function.update x i t)) :=
  hφ.comp (contDiff_update ∞ x i)

lemma fiber_deriv {d : ℕ} {φ : Space d → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (x : Space d) (i : Fin d) (t : ℝ) :
    deriv (fun s => φ (Function.update x i s)) t=
      partialDerivative i φ (Function.update x i t) := by
  have h := ((hφ.differentiable (by simp) (Function.update x i t)).hasFDerivAt.comp t
    (hasFDerivAt_update (𝕜 := ℝ) x (i := i) t)).hasDerivAt.deriv
  have hv : (ContinuousLinearMap.pi (Pi.single i (ContinuousLinearMap.id ℝ ℝ)) : ℝ →L[ℝ] Space d) 1=(Pi.single i (1:ℝ) : Space d) := by
    ext j
    by_cases hj : j=i <;> simp [hj]
  simpa only [partialDerivative,ContinuousLinearMap.comp_apply,hv,Function.comp_def] using h

lemma core_fiber_endpoints {d : ℕ} {α : MultiIndex d} {φ : Space d → ℝ}
    (hφ : interiorSupport α φ) (x : Space d) (i : Fin d) (hi : α i≠0) :
    φ (Function.update x i 0)=0 ∧ φ (Function.update x i Real.pi)=0 := by
  obtain ⟨δ,hδ,hs⟩ := hφ
  constructor
  · apply hs
    exact ⟨i,Nat.pos_of_ne_zero hi,Or.inl (by simpa using hδ.le)⟩
  · apply hs
    exact ⟨i,Nat.pos_of_ne_zero hi,Or.inr (by simpa using hδ.le)⟩

#print axioms coordinate_angular_weak
#print axioms fiber_deriv
end BecknerOnofri.Friedrichs.MixedSpatial
