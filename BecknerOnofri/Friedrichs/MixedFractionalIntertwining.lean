import BecknerOnofri.Friedrichs.MixedAngularPowers
import BecknerOnofri.Friedrichs.SmoothCosinePower

/-! The smooth-profile real-power intertwining on the manuscript's actual
mixed periodic/Dirichlet space, with genuine derivatives on [-1,1]^d. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped ContDiff BigOperators
namespace BecknerOnofri.Friedrichs.MixedFractional
open Legacy.BecknerOnofri Legacy.TorusEndpoint
open HighDim.SmoothEulerStatement
open AngularMixedTerms MixedSpatial

lemma scaled_vector_ae {d : ℕ} (a : Frequency d → ℂ)
    (ha : ∀ m : ℕ,RadialWiener.RadialSummable a m) {U : (Fin d → ℝ) → ℝ}
    (hU : ContDiffOn ℝ ∞ U (cosineCube d))
    (he : EqOn (ChebyshevProfile.profile a) U (cosineCube d)) (is : List (Fin d)) :
    (((2^is.length:ℝ)⁻¹ • MixedAngularSeries.vector a is : H (countIndex is)) : Space d → ℝ)=ᵐ[spatialMeasure (countIndex is)]
      (fun x => weight is x*mixedPartial is U (fun i => Real.cos (x i))) := by
  have hpoint (x : Space d) : FiniteDifferences.mixedPartial is
      (fun z => ChebyshevProfile.profile a (CubeProfileMonotone.fromUnitCube z)) (angularCube x)=
      2^is.length*mixedPartial is U (fun i => Real.cos (x i)) := by
    rw [NormalizedExponentialPartials.mixedPartial_congr is
      (fun y hy => he (CubeProfileMonotone.fromUnitCube_mapsTo d hy)) (angularCube_mem x),
      GeneralEuler.CubeAffine.mixed_affine hU is (angularCube_mem x)]
    congr 2
    ext i
    exact angularCube_coordinate x i
  filter_upwards [Lp.coeFn_smul (2^is.length:ℝ)⁻¹ (MixedAngularSeries.vector a is),
    MixedAngularSeries.vector_ae a ha is] with x hs hx
  rw [hs]
  simp only [Pi.smul_apply,smul_eq_mul,hx,hpoint]
  have hn : (2^is.length:ℝ)≠0 := by positivity
  field_simp

theorem smooth_profile_intertwining {d : ℕ} {U : (Fin d → ℝ) → ℝ} {u : HighDim.Torus d → ℝ}
    (hU : ContDiffOn ℝ ∞ U (cosineCube d))
    (hrep : ∀ x : Fin d → ℝ,u (SmoothFourier.quotient x)=U (ChebyshevProfile.cosinePoint x))
    (s : ℝ) (hs : 0<s) (is : List (Fin d)) :
    ∃ Us : (Fin d → ℝ) → ℝ,
      ContDiffOn ℝ ∞ Us (cosineCube d) ∧
      (∀ x : Fin d → ℝ,SmoothTorus.angularPower s u (SmoothFourier.quotient x)=Us (ChebyshevProfile.cosinePoint x)) ∧
      ∃ f g : H (countIndex is),
        (f : Space d → ℝ)=ᵐ[spatialMeasure (countIndex is)]
          (fun x => weight is x*mixedPartial is U (fun i => Real.cos (x i))) ∧
        (g : Space d → ℝ)=ᵐ[spatialMeasure (countIndex is)]
          (fun x => weight is x*mixedPartial is Us (fun i => Real.cos (x i))) ∧
        SpectralPowerGraph (countIndex is) s f g := by
  have hu := SmoothCosine.smooth_of_representation hU hrep
  have hpu := SmoothTorus.angularPower_smooth hu s hs.le
  let a := HighDim.fourierCoeff u
  let b := MixedAngularSeries.powerCoefficients s a
  let Us := ChebyshevProfile.profile b
  have hb : HighDim.fourierCoeff (SmoothTorus.angularPower s u)=b :=
    funext (SmoothTorus.angularPower_fourier hu s hs.le)
  have ha := SmoothTorus.smooth_fourier_moments hu
  have hbm : ∀ m : ℕ,RadialWiener.RadialSummable b m :=
    AngularRealPower.real_power_radialSummable (2*s) (by positivity) a ha
  have hfact := ChebyshevProfile.continuous_profile_factorization (SmoothTorus.angularPower s u)
    (SmoothTorus.real_continuous hpu) (SmoothTorus.smooth_fourier_moments hpu)
    (SmoothCosine.angularPower_even (SmoothCosine.even_of_representation hrep) s)
  have hb' : densityFourier (SmoothTorus.angularPower s u)=b := hb
  rw [hb'] at hfact
  refine ⟨Us,hfact.1,hfact.2,(2^is.length:ℝ)⁻¹ • MixedAngularSeries.vector a is,
    (2^is.length:ℝ)⁻¹ • MixedAngularSeries.vector b is,?_,?_,?_⟩
  · exact scaled_vector_ae a ha hU (SmoothCosine.profile_eq_of_representation hU hrep) is
  · exact scaled_vector_ae b hbm hfact.1 (fun _ _ => rfl) is
  · exact spectralPowerGraph_smul (MixedAngularSeries.positive_intertwining s hs.le a ha is) _

#print axioms smooth_profile_intertwining
end BecknerOnofri.Friedrichs.MixedFractional
