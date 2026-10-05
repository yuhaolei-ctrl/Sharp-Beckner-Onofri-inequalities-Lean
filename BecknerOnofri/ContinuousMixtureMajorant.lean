import BecknerOnofri.CountableMixtureL1
import BecknerOnofri.CosineMixtureStatementDefinitions
import BecknerOnofri.UniformFourierHessian

/-! A continuous density represented almost everywhere by a normalized
cosine-power mixture automatically has the required summable spatial majorant.
No pointwise convergence at the origin is assumed. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators
namespace BecknerOnofri.CosineMixtureTransfer
open Legacy.TorusEndpoint Legacy.BecknerOnofri

lemma mixture_majorant_of_continuous {d : ℕ} (f : Torus d → ℝ) (hf : Continuous f)
    (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ) (hw : ∀ n,0≤w n) (hs : Summable w)
    (he : f =ᵐ[torusMeasure d] CosineMixtureApproximation.rho w N) :
    Summable (fun n => w n*CosineMixture.tensor (N n) 0) := by
  haveI : (torusMeasure d).IsOpenPosMeasure := by
    change (HighDim.torusMeasure d).IsOpenPosMeasure
    unfold HighDim.torusMeasure
    infer_instance
  apply summable_of_sum_le (fun n => mul_nonneg (hw n) (CosineMixture.tensor_nonneg _ _))
    (c := f 0)
  intro s
  have hle : CosineMixture.mixture s w N ≤ᵐ[torusMeasure d] f := by
    filter_upwards [rho_summable_ae w N hw hs,he] with x hx hfx
    rw [hfx]
    exact hx.sum_le_tsum s (fun n _ => mul_nonneg (hw n) (CosineMixture.tensor_nonneg _ _))
  have hclosed := isClosed_le (CosineMixture.mixture_continuous s w N) hf
  have hset : {x | CosineMixture.mixture s w N x ≤ f x}=Set.univ :=
    hclosed.ae_eq_univ_iff_eq.mp (ae_eq_univ.mpr hle)
  have hzero : (0 : Torus d)∈{x | CosineMixture.mixture s w N x ≤ f x} := by
    rw [hset]
    trivial
  exact hzero

/-- Under continuity the series representation also holds pointwise. -/
lemma mixture_eq_of_continuous {d : ℕ} (f : Torus d → ℝ) (hf : Continuous f)
    (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ) (hw : ∀ n,0≤w n) (hs : Summable w)
    (he : f =ᵐ[torusMeasure d] CosineMixtureApproximation.rho w N) :
    f=CosineMixtureApproximation.rho w N := by
  haveI : (torusMeasure d).IsOpenPosMeasure := by
    change (HighDim.torusMeasure d).IsOpenPosMeasure
    unfold HighDim.torusMeasure
    infer_instance
  exact Measure.eq_of_ae_eq he hf (CosineMixtureApproximation.rho_continuous w N hw
    (mixture_majorant_of_continuous f hf w N hw hs he))

#print axioms mixture_majorant_of_continuous
#print axioms mixture_eq_of_continuous
end BecknerOnofri.CosineMixtureTransfer
