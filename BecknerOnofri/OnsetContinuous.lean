import BecknerOnofri.OnsetWienerConvergence
import BecknerOnofri.GraphRegularity

/-! Global continuous optimizers converge in the actual uniform norm, from
endpoint rigidity and the proved quantitative Wiener bounds. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped Topology BigOperators
namespace BecknerOnofri.HighDim.OnsetContinuous
open ContinuousGibbs ContinuousFirstShell GraphRegularity
open Legacy.BecknerOnofri.TorusSobolev Legacy.BecknerOnofri.SubcriticalAttainment
open Legacy.BecknerOnofri.SobolevCentering
open BecknerOnofri.OnsetWienerBounds

/-- The uniform norm is controlled by the actual absolutely convergent Fourier series. -/
theorem norm_le_wiener {d : ℕ} (u : Space d)
    (hu : Summable (fun k => ‖coefficient k u‖)) :
    ‖u‖ ≤ radialSize 0 (fun k => coefficient k u) := by
  haveI : (Legacy.TorusEndpoint.torusMeasure d).IsOpenPosMeasure := by
    rw [Legacy.TorusEndpoint.torusMeasure_explicit]
    infer_instance
  have he : Legacy.BecknerOnofri.WienerFourier.representative (toL2 d u) = fun x => (u x : ℂ) :=
    Measure.eq_of_ae_eq
      ((Legacy.BecknerOnofri.WienerFourier.representative_ae_eq (toL2 d u) hu).trans (toL2_ae u))
      (Legacy.BecknerOnofri.WienerFourier.representative_continuous (toL2 d u) hu)
      (Complex.continuous_ofReal.comp u.continuous)
  apply (ContinuousMap.norm_le _ (radialSize_nonneg _ _)).mpr
  intro x
  have hs : Summable (fun k => ‖coefficient k u * UnitAddTorus.mFourier k x‖) := by
    simpa only [norm_mul, Legacy.TorusEndpoint.mFourier_norm_apply, mul_one] using hu
  calc
    ‖u x‖ = ‖Legacy.BecknerOnofri.WienerFourier.representative (toL2 d u) x‖ := by
      rw [he, Complex.norm_real]
    _ ≤ ∑' k, ‖coefficient k u * UnitAddTorus.mFourier k x‖ := norm_tsum_le_tsum_norm hs
    _ = _ := by simp [radialSize, Legacy.BecknerOnofri.RadialWiener.radialWeight,
      norm_mul, Legacy.TorusEndpoint.mFourier_norm_apply]

theorem toL2_eq_potentialLp {d : ℕ} (u : Space d) (hu : InCriticalSobolev u) :
    toL2 d u = Bridge.potentialLp u hu.1 :=
  Lp.ext ((toL2_ae u).trans (Bridge.potentialLp_ae u hu.1).symm)

theorem toL2_admissible {d : ℕ} (hd : 0 < d) (u : Space d)
    (hu : InCriticalSobolev u) (hm : MeanZero u) : Admissible (toL2 d u) := by
  refine ⟨toL2_real u, ?_, ?_⟩
  · change coefficient 0 u = 0
    rw [coefficient_zero, show mean d u = 0 from hm]
    rfl
  · rw [toL2_eq_potentialLp u hu]
    exact Bridge.potentialLp_summable hd u hu

theorem center_toL2 {d : ℕ} (u : Space d) (hm : MeanZero u) :
    Legacy.BecknerOnofri.SobolevCentering.center (toL2 d u) = toL2 d u := by
  have hz : fourierIsometry d (toL2 d u) 0 = 0 := by
    change coefficient 0 u = 0
    rw [coefficient_zero, show mean d u = 0 from hm]
    rfl
  simp [Legacy.BecknerOnofri.SobolevCentering.center, hz, constant]

/-- No unproved compact embedding is assumed: this is uniform convergence of
actual continuous mean-zero optimizers, deduced from their Fourier series. -/
theorem optimizers_tendsto_zero {d : ℕ} (hd : 12 ≤ d)
    (hEndpoint : BecknerOnofri.EndpointRigidity.CoefficientEndpoint d (1/2))
    (hRigidity : BecknerOnofri.OnsetCompactness.DensityRigidity d)
    {β : ℕ → ℝ} (hβ : Tendsto β atTop (𝓝 (spectralThreshold d)))
    (u : ℕ → Space d) (hu : ∀ n, InCriticalSobolev (u n))
    (hmean : ∀ n, MeanZero (u n))
    (hmax : ∀ n (v : Torus d → ℝ), InCriticalSobolev v →
      dualFunctional (β n) v ≤ dualFunctional (β n) (u n)) :
    Tendsto u atTop (𝓝 0) := by
  have hd0 : 0 < d := by omega
  let U : ℕ → TorusL2 d := fun n => toL2 d (u n)
  have hU (n : ℕ) : Admissible (U n) := toL2_admissible hd0 (u n) (hu n) (hmean n)
  have hmaxU (n : ℕ) (v : TorusL2 d) (hv : Admissible v) :
      functional (spectralThreshold d/(2*β n)) v ≤
        functional (spectralThreshold d/(2*β n)) (U n) := by
    have hh := hmax n (RawAttainment.realValue v) (RawAttainment.realValue_sobolev v hv)
    rw [OnsetRaw.dualFunctional_eq_normalized hd0 _ _ (RawAttainment.realValue_sobolev v hv),
      OnsetRaw.dualFunctional_eq_normalized hd0 _ _ (hu n),
      RawAttainment.center_potentialLp_realValue v hv,
      ← toL2_eq_potentialLp (u n) (hu n), center_toL2 (u n) (hmean n)] at hh
    exact_mod_cast hh
  have hSigma : spectralThreshold d ≠ 0 := (Legacy.TorusEndpoint.endpointSigma_pos hd0).ne'
  have hA : Tendsto (fun n => spectralThreshold d/(2*β n)) atTop (𝓝 (1/2)) := by
    have hh := (tendsto_const_nhds (x := spectralThreshold d)).div
      (hβ.const_mul 2) (mul_ne_zero (by norm_num) hSigma)
    convert hh using 1
    congr 1
    field_simp
  have hw := maximizers_wiener_tendsto_zero hd hEndpoint hRigidity hA U hU hmaxU
  obtain ⟨b,Ab,hb,hR,hgap⟩ := BecknerOnofri.OnsetCompactness.exists_rough_gap hd
  have hApos : ∀ᶠ n in atTop, 0 < spectralThreshold d/(2*β n) :=
    hA.eventually (lt_mem_nhds (by norm_num : (0:ℝ)<1/2))
  have hbound : ∀ᶠ n in atTop, ‖u n‖ ≤ radialSize 0 (fourierIsometry d (U n)) := by
    filter_upwards [hApos] with n hn
    exact norm_le_wiener (u n) ((Legacy.BecknerOnofri.RadialWiener.radialSummable_zero _).mp
      (Legacy.BecknerOnofri.SubcriticalEuler.maximizer_radialSummable hd0 hR hn (hU n) (hmaxU n) 0))
  exact tendsto_zero_iff_norm_tendsto_zero.mpr
    (squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) hbound hw)

/-- All global optimizers enter any prescribed joint parameter/potential
neighborhood; the conclusion is uniform over the entire optimizer set. -/
theorem optimizers_eventually_near {d : ℕ} (hd : 12 ≤ d)
    (hEndpoint : BecknerOnofri.EndpointRigidity.CoefficientEndpoint d (1/2))
    (hRigidity : BecknerOnofri.OnsetCompactness.DensityRigidity d)
    {S : Set (ℝ × Space d)} (hS : S ∈ 𝓝 (spectralThreshold d,0)) :
    ∀ᶠ β in 𝓝 (spectralThreshold d), ∀ u : Space d,
      InCriticalSobolev u → MeanZero u →
      (∀ v : Torus d → ℝ, InCriticalSobolev v → dualFunctional β v ≤ dualFunctional β u) →
      (β,u) ∈ S := by
  classical
  by_contra hn
  have hf : ∃ᶠ β in 𝓝 (spectralThreshold d), ∃ u : Space d,
      InCriticalSobolev u ∧ MeanZero u ∧
      (∀ v : Torus d → ℝ, InCriticalSobolev v → dualFunctional β v ≤ dualFunctional β u) ∧
      (β,u) ∉ S := by
    simpa only [Filter.Frequently, not_exists, not_and, not_forall, Classical.not_imp,
      not_not] using hn
  obtain ⟨β,hβ,hbad⟩ := exists_seq_forall_of_frequently hf
  choose u hu hm hmax houtside using hbad
  have ht := hβ.prodMk_nhds (optimizers_tendsto_zero hd hEndpoint hRigidity hβ u hu hm hmax)
  obtain ⟨n,hn⟩ := (ht.eventually hS).exists
  exact houtside n hn

theorem optimizers_eventually_near_normalized {d : ℕ} (hd : 12 ≤ d)
    (hEndpoint : BecknerOnofri.EndpointRigidity.CoefficientEndpoint d (1/2))
    (hRigidity : BecknerOnofri.OnsetCompactness.DensityRigidity d)
    {S : Set (ℝ × Space d)} (hS : S ∈ 𝓝 (1,0)) :
    ∀ᶠ μ in 𝓝 (1:ℝ), ∀ u : Space d,
      InCriticalSobolev u → MeanZero u →
      (∀ v : Torus d → ℝ, InCriticalSobolev v →
        dualFunctional (μ*spectralThreshold d) v ≤ dualFunctional (μ*spectralThreshold d) u) →
      (μ,u) ∈ S := by
  have hσ : spectralThreshold d ≠ 0 := (Legacy.TorusEndpoint.endpointSigma_pos (by omega : 0<d)).ne'
  have ht : Tendsto (fun x : ℝ × Space d => (x.1/spectralThreshold d,x.2))
      (𝓝 (spectralThreshold d,0)) (𝓝 (1,0)) := by
    simpa only [div_self hσ] using
      ((continuous_fst.div_const (spectralThreshold d)).prodMk continuous_snd).tendsto (spectralThreshold d,(0:Space d))
  have hβ : Tendsto (fun μ : ℝ => μ*spectralThreshold d) (𝓝 1) (𝓝 (spectralThreshold d)) := by
    simpa only [id_eq, one_mul] using (continuous_id.mul_const (spectralThreshold d)).tendsto (1:ℝ)
  have he := hβ.eventually (optimizers_eventually_near hd hEndpoint hRigidity (ht.eventually hS))
  filter_upwards [he] with μ hμ u hu hm hmax
  have hh := hμ u hu hm hmax
  change (μ*spectralThreshold d/spectralThreshold d,u) ∈ S at hh
  rwa [mul_div_cancel_right₀ _ hσ] at hh

#print axioms optimizers_eventually_near
#print axioms norm_le_wiener
#print axioms optimizers_tendsto_zero
end BecknerOnofri.HighDim.OnsetContinuous
