module

public import BecknerOnofri.V2.Reaudit.HeatKernel.CriticalWiring
public import BecknerOnofri.GeneralEuler.Paper

@[expose] public section

/-! # Raw smooth Euler-pair cosine representation on the new heat-kernel inputs (U05/S015)

Copies of `GeneralEuler.mixedPartials`, `GeneralEuler.mixture` and
`HighDim.GeneralEulerBridge.cosine_representation` in which the two operator inputs
(`criticalInverse_positive`, `higher_norm_lt_one`) are the re-proved versions of `CriticalWiring`.
Statements are identical (certified by `type_of%` equalities).  A consumer of
`GeneralEulerBridge.cosine_representation` can be pointed at `cosine_representation_V2`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Legacy.TorusEndpoint Legacy.BecknerOnofri
open scoped ContDiff
namespace BecknerOnofri.V2.Reaudit.HeatKernel.Wiring
open TorusSobolev SubcriticalAttainment SubcriticalEuler WienerFourier SmoothFourier
open SteinerSelection FiniteDifferences AngularMixedTerms JacobiTensorSpectrum
open BecknerOnofri.GeneralEuler

theorem mixedPartials_V2 {d : ℕ} (hd : 0 < d) {A : ℝ} (hA : 0 < A)
    {u : TorusL2 d} (hu : Admissible u) (hE : Regularity.Data A u)
    (hStR : Steiner (smoothGibbsValue u))
    (hStU : Steiner (fun x => (representative u x).re))
    (is : List (Fin d)) (his : is ≠ []) :
    ∀ y ∈ closedCube d, 0 ≤ mixedPartial is (UnitProfiles.potential u) y :=
  HigherPartialSigns.mixedPartials_nonnegative hd (rough hd) hA hu hE hStR hStU
    (fun js hjs => criticalInverse_positive_V2 (countIndex js)
      (SpectralIntertwining.countIndex_ne_zero js hjs))
    (higher_norm_lt_one_V2 hd (rough hd) hA hu hE hStR hStU) is his

theorem mixture_V2 {d : ℕ} (hd : 0 < d) {A : ℝ} (hA : 0 < A)
    {u : TorusL2 d} (hu : Admissible u) (hE : Regularity.Data A u)
    (hStR : Steiner (smoothGibbsValue u))
    (hStU : Steiner (fun x => (representative u x).re)) :
    GenericCosineRepresentation.HasPositiveCosineMixture (smoothGibbsValue u) := by
  have hs := Regularity.fourier_summable hd (rough hd) hA hu hE
  have hnon : BernsteinPositiveCoefficients.NonnegativeMixedPartials (UnitProfiles.density u) :=
    NormalizedExponentialPartials.normalized_exp_nonnegative_mixed (partition_pos (rough hd) hu)
      (UnitProfiles.potential_contDiffOn hd (rough hd) hA hu hE hStU)
      (fun _ hx => UnitProfiles.density_eq_exp hd (rough hd) hA hu hE hStU hStR hx)
      (mixedPartials_V2 hd hA hu hE hStR hStU)
  exact GenericCosineRepresentation.positive_profile_mixture hd (smoothGibbsDensity (rough hd) hu hs)
    (UnitProfiles.density_contDiffOn hd (rough hd) hA hu hE hStR) hnon
    (UnitProfiles.density_representation hd (rough hd) hA hu hE hStR)


end BecknerOnofri.V2.Reaudit.HeatKernel.Wiring

namespace BecknerOnofri.V2.Reaudit.HeatKernel.Wiring
open BecknerOnofri.HighDim BecknerOnofri.HighDim.GeneralEulerBridge
open ContinuousGibbs ContinuousFirstShell ContinuousOptimizers OptimizerDuality
open Legacy.BecknerOnofri.TorusSobolev Legacy.BecknerOnofri.SubcriticalEuler
open Legacy.BecknerOnofri.WienerFourier Legacy.BecknerOnofri.SmoothFourier
open PrescribedSelection

theorem cosine_representation_V2 {d : ℕ} (hd : 0 < d) : SmoothEulerStatement.CosineRepresentation d := by
  intro β hβ u ρ hus hm hstu hρ he
  let v : ContinuousGibbs.Space d := ⟨u,SmoothTorus.real_continuous hus⟩
  have hv : InCriticalSobolev v := SmoothTorus.smooth_mem_critical hus
  have hV := OnsetContinuous.toL2_admissible hd v hv hm
  have hA : 0 < spectralThreshold d/(2*β) := div_pos (spectralThreshold_pos hd) (by positivity)
  have hE := regularity_data hd hβ v hus (by simpa only [v,ContinuousMap.coe_mk,hρ] using he)
  have hs := BecknerOnofri.GeneralEuler.Regularity.fourier_summable hd
    (BecknerOnofri.GeneralEuler.rough hd) hA hV hE
  haveI : (BecknerOnofri.HighDim.torusMeasure d).IsOpenPosMeasure := by
    unfold BecknerOnofri.HighDim.torusMeasure; infer_instance
  haveI : (Legacy.TorusEndpoint.torusMeasure d).IsOpenPosMeasure := by
    rw [Legacy.TorusEndpoint.torusMeasure_explicit]
    infer_instance
  have hrep : representative (toL2 d v) = fun x => (v x : ℂ) :=
    Measure.eq_of_ae_eq ((representative_ae_eq (toL2 d v) hs).trans (toL2_ae v))
      (representative_continuous (toL2 d v) hs) (Complex.continuous_ofReal.comp v.continuous)
  have hg : smoothGibbsValue (toL2 d v)=normalizedGibbs v := by
    funext x
    simp only [smoothGibbsValue,hrep,Complex.ofReal_re,partition_toL2,
      normalizedGibbs,ContinuousGibbs.partition,mean_apply,exponential_apply]
  have hStV : Legacy.BecknerOnofri.SteinerSelection.Steiner
      (fun x => (representative (toL2 d v) x).re) := by rw [hrep]; exact hstu
  have hStR : Legacy.BecknerOnofri.SteinerSelection.Steiner (smoothGibbsValue (toL2 d v)) := by
    rw [hg]; exact normalized_steiner v hstu
  obtain ⟨hUs,hUfactor⟩ := BecknerOnofri.GeneralEuler.CosineProfile.potential_profile hd
    (BecknerOnofri.GeneralEuler.rough hd) hA hV hE hStV
  let U := Legacy.BecknerOnofri.ChebyshevProfile.profile (fourierIsometry d (toL2 d v))
  refine ⟨U,hUs,?_,?_,?_⟩
  · intro x
    have hh := hUfactor x
    rw [hrep] at hh
    exact hh
  · intro is his z hz
    let y : Fin d → ℝ := fun i => (z i+1)/2
    have hy : y∈Legacy.BecknerOnofri.FiniteDifferences.closedCube d := by
      constructor <;> intro i
      · change 0≤(z i+1)/2
        have h0 : -1≤z i := hz.1 i
        linarith
      · change (z i+1)/2≤1
        have h1 : z i≤1 := hz.2 i
        linarith
    have hzy : Legacy.BecknerOnofri.CubeProfileMonotone.fromUnitCube y=z := by
      ext i
      dsimp [Legacy.BecknerOnofri.CubeProfileMonotone.fromUnitCube,y]
      ring
    have hpos := mixedPartials_V2 hd hA hV hE hStR hStV is his y hy
    have hid := BecknerOnofri.GeneralEuler.CubeAffine.mixed_affine hUs is hy
    change Legacy.BecknerOnofri.FiniteDifferences.mixedPartial is
      (fun y => U (Legacy.BecknerOnofri.CubeProfileMonotone.fromUnitCube y)) y ≥ 0 at hpos
    rw [hid,hzy] at hpos
    exact nonneg_of_mul_nonneg_right hpos (by positivity : (0:ℝ)<2^is.length)
  · obtain ⟨w,N,hw,hsw,_,hEq⟩ := mixture_V2 hd hA hV hE hStR hStV
    rw [hg] at hEq
    refine ⟨w,N,hw,hsw,?_⟩
    exact Filter.Eventually.of_forall (fun x => (congrFun hρ x).trans (congrFun hEq x))


theorem mixedPartials_V2_type :
    (type_of% @mixedPartials_V2) = (type_of% @BecknerOnofri.GeneralEuler.mixedPartials) := rfl

theorem mixture_V2_type :
    (type_of% @mixture_V2) = (type_of% @BecknerOnofri.GeneralEuler.mixture) := rfl

theorem cosine_representation_V2_type :
    (type_of% @cosine_representation_V2) =
      (type_of% @BecknerOnofri.HighDim.GeneralEulerBridge.cosine_representation) := rfl

#print axioms mixedPartials_V2
#print axioms mixture_V2
#print axioms cosine_representation_V2

end BecknerOnofri.V2.Reaudit.HeatKernel.Wiring
