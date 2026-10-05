module

public import BecknerOnofri.CircleMeanBounds
public import BecknerOnofri.CircleMomentComparison
public import BecknerOnofri.CircleRateEntropy

@[expose] public section

/-! The manuscript's full von Mises comparison for a normalized increasing
convex exponential cosine profile: mean domain, moments, and entropy. -/
noncomputable section
open MeasureTheory Set
namespace BecknerOnofri.HighDim.CircleScalar

theorem circle_comparison (F : ℝ → ℝ) (t : ℝ)
    (hcF : Continuous F) (hF : ConvexOn ℝ (Icc (-1:ℝ) 1) F)
    (hinc : MonotoneOn F (Icc (-1:ℝ) 1))
    (hmass : (∫ x : UnitAddCircle,Real.exp (F ((fourier 1 x).re)) ∂AddCircle.haarAddCircle)=1)
    (hm : (∫ x : UnitAddCircle,Real.exp (F ((fourier 1 x).re))*(fourier 1 x).re
      ∂AddCircle.haarAddCircle)=t) :
    0≤t ∧ t<1 ∧
    besselMoment 2 (parameter t)≤
      (∫ x : UnitAddCircle,Real.exp (F ((fourier 1 x).re))*(fourier 2 x).re ∂AddCircle.haarAddCircle) ∧
    |(∫ x : UnitAddCircle,Real.exp (F ((fourier 1 x).re))*(fourier 3 x).re ∂AddCircle.haarAddCircle)-
      besselMoment 3 (parameter t)|≤
      6*((∫ x : UnitAddCircle,Real.exp (F ((fourier 1 x).re))*(fourier 2 x).re ∂AddCircle.haarAddCircle)-
        besselMoment 2 (parameter t)) ∧
    rate t≤∫ x : UnitAddCircle,Real.exp (F ((fourier 1 x).re))*
      Real.log (Real.exp (F ((fourier 1 x).re))) ∂AddCircle.haarAddCircle := by
  have ht : 0≤t := by rw [← hm]; exact circle_mean_nonneg F hcF hinc
  have ht1 : t<1 := by rw [← hm]; exact circle_mean_lt_one F hcF hmass
  obtain ⟨h2,h3⟩ := circle_second_third_comparison F t hcF hF hmass hm ht ht1
  refine ⟨ht,ht1,h2,h3,?_⟩
  have hcp : Continuous (fun x : UnitAddCircle => Real.exp (F ((fourier 1 x).re))) :=
    Real.continuous_exp.comp (hcF.comp (Complex.continuous_re.comp (fourier 1).continuous))
  apply rate_le_circle_entropy _ t (Filter.Eventually.of_forall (fun _ => (Real.exp_pos _).le)) hmass
    (hcp.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) _ hm
  exact (Real.continuous_mul_log.comp hcp).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

#print axioms circle_comparison
end BecknerOnofri.HighDim.CircleScalar
