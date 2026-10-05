import BecknerOnofri.GeneralShapeEntropyGap
import BecknerOnofri.CosineShapeCalculus
import BecknerOnofri.ContinuousMixtureMajorant

/-! The standalone nonstationary global entropy estimate with the manuscript's
actual closed-cube first and second partial derivative hypotheses. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped ContDiff
namespace BecknerOnofri.HighDim.ShapeEntropy
open ConditionalEntropy Legacy.BecknerOnofri

/-- Convert only the manuscript hypotheses into analytic assembly data. -/
def paperData (ρ : ProbabilityDensity 12) (hs : SmoothOnTorus ρ.value)
    (hp : ∀ x,0<ρ.value x)
    (hperm : ∀ (π : Equiv.Perm (Fin 12)) (x : Torus 12),ρ.value (fun i => x (π i))=ρ.value x)
    (hmix : IsCountableCosineMixture ρ)
    (V : (Fin 12 → ℝ) → ℝ) (hV : ContDiffOn ℝ ∞ V (cosineCube 12))
    (hlog : ∀ x,Real.log (ρ.value x)=V (cosineVector x))
    (h1 : ∀ v∈cosineCube 12,∀ i : Fin 12,0≤cosinePartial i V v)
    (h2 : ∀ v∈cosineCube 12,∀ i : Fin 12,0≤cosinePartial i (cosinePartial i V) v) : Data ρ where
  smooth := hs
  symmetric := by
    intro π x
    have he : ContinuousSymmetry.pointPermutation π x=(fun i => x (π.symm i)) := by
      funext i
      exact ContinuousSymmetry.pointPermutation_apply π x i
    rw [he]
    exact hperm π.symm x
  mixture := by
    obtain ⟨w,N,hw,hm,he⟩ := hmix
    have hc := UniformFourier.smooth_continuous hs
    have he' : ρ.value =ᵐ[torusMeasure 12] CosineMixtureApproximation.rho w N := he
    exact ⟨w,N,hw,hm,CosineMixtureTransfer.mixture_majorant_of_continuous ρ.value hc w N hw hm.summable he',
      CosineMixtureTransfer.mixture_eq_of_continuous ρ.value hc w N hw hm.summable he'⟩
  profile := V
  continuous_profile := hV.continuousOn
  convex_profile := fun v hv i => CosineShape.coordinate_convex hV i (fun y hy => h2 y hy i) hv
  monotone_profile := fun v hv i => CosineShape.coordinate_monotone hV i (fun y hy => h1 y hy i) hv
  representation := by intro x; rw [← hlog x,Real.exp_log (hp x)]

/-- The full standalone estimate, including reality, nonnegativity and rigidity
of its first Fourier coefficient, for every source-admissible density. -/
theorem global_shape_entropy (ρ : ProbabilityDensity 12) (hs : SmoothOnTorus ρ.value)
    (hp : ∀ x,0<ρ.value x)
    (hperm : ∀ (π : Equiv.Perm (Fin 12)) (x : Torus 12),ρ.value (fun i => x (π i))=ρ.value x)
    (hmix : IsCountableCosineMixture ρ)
    (V : (Fin 12 → ℝ) → ℝ) (hV : ContDiffOn ℝ ∞ V (cosineCube 12))
    (hlog : ∀ x,Real.log (ρ.value x)=V (cosineVector x))
    (h1 : ∀ v∈cosineCube 12,∀ i : Fin 12,0≤cosinePartial i V v)
    (h2 : ∀ v∈cosineCube 12,∀ i : Fin 12,0≤cosinePartial i (cosinePartial i V) v) :
    (fourierCoeff ρ.value (Pi.single (0 : Fin 12) (1 : ℤ))).im=0 ∧
    0≤(fourierCoeff ρ.value (Pi.single (0 : Fin 12) (1 : ℤ))).re ∧
    (fourierCoeff ρ.value (Pi.single (0 : Fin 12) (1 : ℤ))).re^4/250≤
      entropy ρ-(1/2 : ℝ)*EntropyTail.fullFourierEnergy ρ.value ∧
    ((fourierCoeff ρ.value (Pi.single (0 : Fin 12) (1 : ℤ))).re=0 → ρ.value=(fun _ => 1)) := by
  let D := paperData ρ hs hp hperm hmix V hV hlog h1 h2
  exact ⟨density_coefficient_real D _,first_mode_nonnegative D,global_gap D,first_mode_zero_uniform D⟩

#print axioms global_shape_entropy
end BecknerOnofri.HighDim.ShapeEntropy
