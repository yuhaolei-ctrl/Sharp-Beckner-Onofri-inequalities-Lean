import BecknerOnofri.CompactParameterDifferentiation
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-! Smooth compact-parameter integrals, derived from the actual smooth
integrand rather than an assumed derivative family. -/
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace BecknerOnofri.CompactParameter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def timeDerivative (F : ℝ × E → ℝ) : ℕ → ℝ × E → ℝ
  | 0 => F
  | n+1 => fun p => fderiv ℝ (timeDerivative F n) p (1,0)

lemma timeDerivative_smooth (F : ℝ × E → ℝ) (hF : ContDiff ℝ ∞ F) :
    ∀ n,ContDiff ℝ ∞ (timeDerivative F n) := by
  intro n
  induction n with
  | zero => exact hF
  | succ n ih => exact (ih.fderiv_right (by simp)).clm_apply contDiff_const

lemma timeDerivative_hasDerivAt (F : ℝ × E → ℝ) (hF : ContDiff ℝ ∞ F)
    (n : ℕ) (t : ℝ) (y : E) :
    HasDerivAt (fun x => timeDerivative F n (x,y)) (timeDerivative F (n+1) (t,y)) t := by
  have h := ((timeDerivative_smooth F hF n).differentiable (by simp)).differentiableAt (x := (t,y)) |>.hasFDerivAt
  exact h.comp_hasDerivAt t ((hasDerivAt_id t).prodMk (hasDerivAt_const t y))

/-- Integrating a jointly smooth Euclidean function against any continuous
compact parameterization preserves smoothness in the free real variable. -/
theorem integral_contDiff_of_compact_parameter
    {Y : Type*} [TopologicalSpace Y] [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (μ : Measure Y) [IsFiniteMeasure μ] (φ : Y → E) (hφ : Continuous φ)
    (F : ℝ × E → ℝ) (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (fun t => ∫ y,F (t,φ y) ∂μ) := by
  let G : ℕ → ℝ → Y → ℝ := fun n t y => timeDerivative F n (t,φ y)
  have hGc : ∀ n,Continuous (G n).uncurry := by
    intro n
    exact (timeDerivative_smooth F hF n).continuous.comp
      (continuous_fst.prodMk (hφ.comp continuous_snd))
  have hGd : ∀ n t y,HasDerivAt (fun x => G n x y) (G (n+1) t y) t :=
    fun n t y => timeDerivative_hasDerivAt F hF n t (φ y)
  exact integral_contDiff_family μ G hGc hGd 0

#print axioms integral_contDiff_of_compact_parameter
end BecknerOnofri.CompactParameter
