import BecknerOnofri.GeneralEuler.Mixture
import BecknerOnofri.GeneralEuler.RawData
import BecknerOnofri.GeneralEuler.CubeAffineDerivatives

/-! The full raw smooth Euler-pair proposition, with actual derivatives on the
closed cosine cube and no variational maximality assumption. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
namespace BecknerOnofri.HighDim.GeneralEulerBridge
open ContinuousGibbs ContinuousFirstShell ContinuousOptimizers OptimizerDuality
open Legacy.BecknerOnofri.TorusSobolev Legacy.BecknerOnofri.SubcriticalEuler
open Legacy.BecknerOnofri.WienerFourier Legacy.BecknerOnofri.SmoothFourier
open PrescribedSelection

lemma normalized_steiner {d : ℕ} (u : ContinuousGibbs.Space d) (hSt : CoordinateSteiner u) :
    CoordinateSteiner (normalizedGibbs u) := by
  constructor
  · intro i x
    simp only [normalizedGibbs,hSt.1 i x]
  · intro x i s hs t ht hst
    exact div_le_div_of_nonneg_right (Real.exp_le_exp.mpr (hSt.2 x i hs ht hst))
      (by simpa only [ContinuousGibbs.partition,mean_apply,exponential_apply] using
        (ContinuousGibbs.partition_pos u).le)

theorem cosine_representation {d : ℕ} (hd : 0 < d) : SmoothEulerStatement.CosineRepresentation d := by
  intro β hβ u ρ hus hm hstu hρ he
  let v : ContinuousGibbs.Space d := ⟨u,SmoothTorus.real_continuous hus⟩
  have hv : InCriticalSobolev v := SmoothTorus.smooth_mem_critical hus
  have hV := OnsetContinuous.toL2_admissible hd v hv hm
  have hA : 0 < spectralThreshold d/(2*β) := div_pos (spectralThreshold_pos hd) (by positivity)
  have hE := regularity_data hd hβ v hus (by simpa only [v,ContinuousMap.coe_mk,hρ] using he)
  have hs := BecknerOnofri.GeneralEuler.Regularity.fourier_summable hd
    (BecknerOnofri.GeneralEuler.rough hd) hA hV hE
  haveI : (torusMeasure d).IsOpenPosMeasure := by unfold torusMeasure; infer_instance
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
    have hpos := BecknerOnofri.GeneralEuler.mixedPartials hd hA hV hE hStR hStV is his y hy
    have hid := BecknerOnofri.GeneralEuler.CubeAffine.mixed_affine hUs is hy
    change Legacy.BecknerOnofri.FiniteDifferences.mixedPartial is
      (fun y => U (Legacy.BecknerOnofri.CubeProfileMonotone.fromUnitCube y)) y ≥ 0 at hpos
    rw [hid,hzy] at hpos
    exact nonneg_of_mul_nonneg_right hpos (by positivity : (0:ℝ)<2^is.length)
  · obtain ⟨w,N,hw,hsw,_,hEq⟩ := BecknerOnofri.GeneralEuler.mixture hd hA hV hE hStR hStV
    rw [hg] at hEq
    refine ⟨w,N,hw,hsw,?_⟩
    exact Filter.Eventually.of_forall (fun x => (congrFun hρ x).trans (congrFun hEq x))

#print axioms cosine_representation
end BecknerOnofri.HighDim.GeneralEulerBridge
