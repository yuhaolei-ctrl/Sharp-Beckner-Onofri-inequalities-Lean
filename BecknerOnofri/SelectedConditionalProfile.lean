module

public import BecknerOnofri.SelectedConditionalRegularity
public import BecknerOnofri.CoordinateConvexity
public import BecknerOnofri.ConditionalGamma

@[expose] public section

/-! The actual selected Euler potential supplies the increasing convex joint
cosine profile needed by every conditional circle. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Function
open scoped ContDiff
namespace BecknerOnofri.HighDim.SelectedNumericalModel
open Legacy.TorusEndpoint Legacy.BecknerOnofri
open TorusSobolev SubcriticalAttainment SmoothFourier WienerFourier
open ConditionalEntropy

def logarithmicCosineProfile (u : TorusL2 12) (v : Fin 12 → ℝ) : ℝ :=
  ChebyshevProfile.profile (fourierIsometry 12 u) v - Real.log (partition u)

def toUnit (v : Fin 12 → ℝ) : Fin 12 → ℝ := fun j => (1 + v j)/2

theorem from_toUnit (v : Fin 12 → ℝ) : CubeProfileMonotone.fromUnitCube (toUnit v) = v := by
  funext j
  dsimp [CubeProfileMonotone.fromUnitCube, toUnit]
  ring

theorem toUnit_mem {v : Fin 12 → ℝ} (hv : v ∈ cosineCube 12) :
    toUnit v ∈ FiniteDifferences.closedCube 12 := by
  constructor <;> intro j
  · change 0 ≤ (1 + v j)/2
    linarith [hv.1 j]
  · change (1 + v j)/2 ≤ 1
    linarith [hv.2 j]

theorem toUnit_interval {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    (1+t)/2 ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [ht.1, ht.2]

theorem selected_log_profile_shape {u : TorusL2 12} (hu : Selected u) :
    ContinuousOn (logarithmicCosineProfile u) (cosineCube 12) ∧
    (∀ v ∈ cosineCube 12, ∀ i : Fin 12,
      ConvexOn ℝ (Icc (-1 : ℝ) 1) (fun t => logarithmicCosineProfile u (update v i t))) ∧
    (∀ v ∈ cosineCube 12, ∀ i : Fin 12,
      MonotoneOn (fun t => logarithmicCosineProfile u (update v i t)) (Icc (-1 : ℝ) 1)) := by
  have hprof := EulerCosineProfile.potential_profile (by norm_num : 0 < 12) rough
    (by norm_num : (0 : ℝ) < 1/2) hu.1 hu.2.1 hu.2.2.2
  have hsmooth := EulerUnitProfiles.potential_contDiffOn (by norm_num : 0 < 12) rough
    (by norm_num : (0 : ℝ) < 1/2) hu.1 hu.2.1 hu.2.2.2
  refine ⟨hprof.1.continuousOn.sub continuousOn_const, ?_, ?_⟩
  · intro v hv i
    have h2 := GenericCosineRepresentation.steiner_maximizer_mixedPartials
      (by norm_num : 0 < 12) (by norm_num : (0 : ℝ) < 1/2)
      hu.1 hu.2.1 hu.2.2.1 hu.2.2.2 [i,i] (by simp)
    have hcv := FiniteDifferences.coordinate_convex hsmooth i h2 (toUnit_mem hv)
    have hid (t : ℝ) : logarithmicCosineProfile u (update v i t) =
        EulerUnitProfiles.potential u (update (toUnit v) i ((1+t)/2)) - Real.log (partition u) := by
      unfold logarithmicCosineProfile EulerUnitProfiles.potential
      rw [CubeProfileMonotone.fromUnitCube_update, from_toUnit]
      congr 2
      ring
    refine ⟨convex_Icc _ _, ?_⟩
    intro s hs t ht a b ha hb hab
    have h := hcv.2 (toUnit_interval hs) (toUnit_interval ht) ha hb hab
    simp only [smul_eq_mul] at h ⊢
    have hc : a*((1+s)/2)+b*((1+t)/2)=(1+(a*s+b*t))/2 := by nlinarith
    rw [hc] at h
    simp only [hid]
    nlinarith [congrArg (fun r : ℝ => r * Real.log (partition u)) hab]
  · intro v hv i s hs t ht hst
    have h := CubeProfileMonotone.coordinate_monotone_of_steiner hu.2.2.2 hprof.2 hv i hs ht hst
    exact sub_le_sub_right h _

theorem selected_log_profile_representation {u : TorusL2 12} (hu : Selected u)
    (x : HighDim.Torus 12) :
    (spinDensity hu).value x = Real.exp (logarithmicCosineProfile u (cosineVector x)) := by
  obtain ⟨z, rfl⟩ := EulerUnitProfiles.quotient_surjective 12 x
  have hc : cosineVector (quotient z) = ChebyshevProfile.cosinePoint z := by
    funext j
    exact CosineMomentWeight.circleCos_coe (z j)
  have hp := (EulerCosineProfile.potential_profile (by norm_num : 0 < 12) rough
    (by norm_num : (0 : ℝ) < 1/2) hu.1 hu.2.1 hu.2.2.2).2 z
  change smoothGibbsValue u (quotient z) = _
  rw [logarithmicCosineProfile, hc, ← hp, Real.exp_sub,
    Real.exp_log (partition_pos rough hu.1)]
  rfl

theorem selected_conditional_gamma {u : TorusL2 12} (hu : Selected u)
    (i : Fin 12) (x : HighDim.Torus 12) :
    2 * Spin.binaryCost (conditionalCosineMoment (spinDensity hu).value i 1 x) +
      CircleScalar.gamma (conditionalCosineMoment (spinDensity hu).value i 1 x) +
      (21/1000) * (conditionalCosineMoment (spinDensity hu).value i 2 x)^2 +
      (27/40) * (∑' n : ℕ, (conditionalCosineMoment (spinDensity hu).value i (n+3) x)^2 / (n+3 : ℝ)) ≤
        conditionalEntropy (spinDensity hu).value i x := by
  obtain ⟨hc,hcv,hm⟩ := selected_log_profile_shape hu
  exact conditional_gamma (logarithmicCosineProfile u) hc hcv hm _
    (selected_log_profile_representation hu) _ (spinDensity_radialSummable hu)
    (spinDensity_fourierSeries hu) i x

#print axioms selected_log_profile_shape
#print axioms selected_conditional_gamma
end BecknerOnofri.HighDim.SelectedNumericalModel
