module

public import BecknerOnofri.SmoothAngularPowerFourier
public import BecknerOnofri.GeneralCoefficientReflections
public import BecknerOnofri.GeneralEuler.CubeAffineDerivatives

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped ContDiff
namespace BecknerOnofri.Friedrichs.SmoothCosine
open HighDim Legacy.TorusEndpoint Legacy.BecknerOnofri
open CosineCoefficientLattice ChebyshevProfile

lemma reflection_zero_eq_update {d : ℕ} (i : Fin d) (x : HighDim.Torus d) :
    CoordinatePolarization.reflection i 0 x=Function.update x i (-x i) := by
  ext j
  by_cases hj : j=i <;>
    simp [CoordinatePolarization.reflection,CoordinatePolarization.circleReflection,hj]

lemma smooth_of_representation {d : ℕ} {u : HighDim.Torus d → ℝ} {U : (Fin d → ℝ) → ℝ}
    (hU : ContDiffOn ℝ ∞ U (HighDim.SmoothEulerStatement.cosineCube d))
    (hrep : ∀ x : Fin d → ℝ,u (SmoothFourier.quotient x)=U (cosinePoint x)) : SmoothOnTorus u := by
  change ContDiff ℝ ∞ (fun x : Fin d → ℝ => u (SmoothFourier.quotient x))
  simp_rw [hrep]
  apply hU.comp_contDiff
  · apply contDiff_pi.mpr
    intro i
    exact Real.contDiff_cos.comp (contDiff_const.mul (contDiff_apply ℝ ℝ i))
  · intro x
    constructor <;> intro i
    · exact Real.neg_one_le_cos _
    · exact Real.cos_le_one _

lemma even_of_representation {d : ℕ} {u : HighDim.Torus d → ℝ} {U : (Fin d → ℝ) → ℝ}
    (hrep : ∀ x : Fin d → ℝ,u (SmoothFourier.quotient x)=U (cosinePoint x)) :
    ∀ (i : Fin d) (x : HighDim.Torus d),u (Function.update x i (-x i))=u x := by
  intro i x
  choose y hy using fun j => QuotientAddGroup.mk_surjective (x j)
  have he : SmoothFourier.quotient y=x := funext hy
  have hu : SmoothFourier.quotient (Function.update y i (-y i))=Function.update x i (-x i) := by
    ext j
    by_cases hj : j=i <;> simp [SmoothFourier.quotient,hj,hy]
  rw [← hu,← he,hrep,hrep]
  congr 1
  ext j
  by_cases hj : j=i <;> simp [cosinePoint,hj]

lemma coefficient_even {d : ℕ} {u : HighDim.Torus d → ℝ}
    (heven : ∀ (i : Fin d) (x : HighDim.Torus d),u (Function.update x i (-x i))=u x)
    (i : Fin d) (k : HighDim.Frequency d) : fourierCoeff u (frequencyFlip i k)=fourierCoeff u k := by
  have h := (CoordinatePolarization.reflection_measurePreserving i 0).integral_comp
    (CoordinatePolarization.reflectionEquiv i 0).measurableEmbedding
    (fun x => UnitAddTorus.mFourier (-k) x*(u x:ℂ))
  have hu (x : HighDim.Torus d) : u (CoordinatePolarization.reflection i 0 x)=u x := by
    rw [reflection_zero_eq_update,heven]
  simp only [hu] at h
  simp_rw [mFourier_coordinate_reflection,map_neg] at h
  rw [Legacy.TorusEndpoint.torusMeasure_explicit] at h
  simpa only [HighDim.fourierCoeff,UnitAddTorus.mFourierCoeff,HighDim.torusMeasure] using h

lemma angularPower_even {d : ℕ} {u : HighDim.Torus d → ℝ}
    (heven : ∀ (i : Fin d) (x : HighDim.Torus d),u (Function.update x i (-x i))=u x) (s : ℝ) :
    ∀ (i : Fin d) (x : HighDim.Torus d),SmoothTorus.angularPower s u (Function.update x i (-x i))=
      SmoothTorus.angularPower s u x := by
  intro i x
  have he := (frequencyFlip i).toEquiv.tsum_eq
    (fun k => ((frequencyLength k^(2*s):ℝ):ℂ)*fourierCoeff u k*UnitAddTorus.mFourier k x)
  have hr (k : HighDim.Frequency d) : frequencyLength (frequencyFlip i k)=frequencyLength k := radius_flip i k
  have hs : absoluteFourierSeries
      (fun k => ((frequencyLength k^(2*s):ℝ):ℂ)*fourierCoeff u k) (Function.update x i (-x i))=
      absoluteFourierSeries (fun k => ((frequencyLength k^(2*s):ℝ):ℂ)*fourierCoeff u k) x := by
    rw [← reflection_zero_eq_update]
    unfold absoluteFourierSeries
    simp_rw [mFourier_coordinate_reflection]
    simpa only [frequencyFlip_toEquiv_apply,hr,coefficient_even heven] using he
  exact congrArg Complex.re hs

theorem profile_eq_of_representation {d : ℕ} {u : HighDim.Torus d → ℝ} {U : (Fin d → ℝ) → ℝ}
    (hU : ContDiffOn ℝ ∞ U (HighDim.SmoothEulerStatement.cosineCube d))
    (hrep : ∀ x : Fin d → ℝ,u (SmoothFourier.quotient x)=U (cosinePoint x)) :
    EqOn (profile (fourierCoeff u)) U (HighDim.SmoothEulerStatement.cosineCube d) := by
  have hs := smooth_of_representation hU hrep
  have hf := continuous_profile_factorization u (SmoothTorus.real_continuous hs)
    (SmoothTorus.smooth_fourier_moments hs) (even_of_representation hrep)
  intro z hz
  have he := hf.2 (CubeProfileMonotone.inverseCos z)
  rw [hrep,CubeProfileMonotone.cosinePoint_inverseCos hz] at he
  exact he.symm

#print axioms profile_eq_of_representation
#print axioms angularPower_even
end BecknerOnofri.Friedrichs.SmoothCosine
