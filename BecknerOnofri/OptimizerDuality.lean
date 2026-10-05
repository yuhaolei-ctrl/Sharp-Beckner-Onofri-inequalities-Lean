module

public import BecknerOnofri.ContinuousOptimizers
public import BecknerOnofri.OptimizerGibbsLimit
public import BecknerOnofri.PressureDuality

@[expose] public section

/-! Primal-dual optimizer correspondence on the full actual finite-entropy
and critical-Sobolev domains. Regularity of a density optimizer is a conclusion. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped Topology BigOperators
namespace BecknerOnofri.HighDim.OptimizerDuality
open ContinuousGibbs ContinuousFirstShell ContinuousOptimizers OnsetContinuous GraphRegularity
open Legacy.BecknerOnofri.TorusSobolev
open Legacy.BecknerOnofri.SubcriticalAttainment Legacy.BecknerOnofri.SubcriticalEuler
open Legacy.BecknerOnofri.SubcriticalPrimalDual

/-- Actual Gibbs probability density of a continuous potential. -/
def continuousGibbsDensity {d : ℕ} (u : Space d) : ProbabilityDensity d where
  value := normalizedGibbs u
  nonneg := Eventually.of_forall (fun x => by
    rw [← normalized_apply]; exact (normalized_pos u x).le)
  integrable := by
    exact (ContinuousGibbs.integrable d (normalized u)).congr
      (Eventually.of_forall (normalized_apply u))
  mass := by
    have he : (normalized u : Torus d → ℝ) = normalizedGibbs u := funext (normalized_apply u)
    rw [← he]
    exact mean_normalized u

theorem finiteEntropy_congr_ae {d : ℕ} {ρ η : ProbabilityDensity d}
    (he : ρ.value =ᵐ[torusMeasure d] η.value) : ρ.FiniteEntropy ↔ η.FiniteEntropy := by
  apply integrable_congr
  filter_upwards [he] with x hx
  rw [hx]

theorem pressureValue_congr_ae {d : ℕ} {ρ η : ProbabilityDensity d}
    (he : ρ.value =ᵐ[torusMeasure d] η.value) (β : ℝ) :
    pressureValue β ρ = pressureValue β η := by
  have hEnt : entropy ρ = entropy η := by
    apply integral_congr_ae
    filter_upwards [he] with x hx
    rw [hx]
  have hc (k : Frequency d) : fourierCoeff ρ.value k = fourierCoeff η.value k := by
    apply integral_congr_ae
    filter_upwards [he] with x hx
    rw [hx]
  have hQ : spectralEnergy ρ = spectralEnergy η := by
    apply tsum_congr
    intro k
    simp only [spectralTerm, hc]
  simp only [pressureValue, hEnt, hQ]

theorem minimizer_congr_ae {d : ℕ} {ρ η : ProbabilityDensity d}
    (he : ρ.value =ᵐ[torusMeasure d] η.value) (β : ℝ) :
    IsGlobalMinimizer β ρ ↔ IsGlobalMinimizer β η := by
  simp only [IsGlobalMinimizer, finiteEntropy_congr_ae he, pressureValue_congr_ae he β]

theorem pressureValue_eq_legacy {d : ℕ} (hd : 0 < d) {β : ℝ} (hβ : 0 < β)
    (ρ : ProbabilityDensity d) (hρ : ρ.FiniteEntropy) :
    pressureValue β ρ = (densityFunctional (spectralThreshold d/(2*β)) (Bridge.density ρ) : EReal) := by
  have hσ := spectralThreshold_pos hd
  have hcoef : 1/(4*(spectralThreshold d/(2*β))) = β/(2*spectralThreshold d) := by
    field_simp
    <;> ring
  have hterms : Legacy.BecknerOnofri.fourierEnergy (Bridge.density ρ) = ∑' k, spectralTerm ρ k :=
    tsum_congr (Bridge.densitySpectralTerm_eq ρ)
  rw [pressureValue, spectralEnergy_coe_eq_tsum hd ρ hρ, densityFunctional, hcoef, hterms]
  norm_cast

/-- The primal pressure agrees with the value of any actual global dual optimizer. -/
theorem pressure_eq_dual {d : ℕ} (hd : 0 < d) {β : ℝ} (hβ : 0 < β)
    (u : Torus d → ℝ) (hu : InCriticalSobolev u)
    (hmax : ∀ v : Torus d → ℝ, InCriticalSobolev v → dualFunctional β v ≤ dualFunctional β u) :
    pressure d β = dualFunctional β u := by
  rw [pressure_eq_coefficientDefect hd hβ]
  change (⨆ v : Torus d → ℝ, ⨆ _hv : InCriticalSobolev v,
    RawAttainment.rawFunctional (spectralThreshold d/(2*β*(2*Real.pi)^d)) v) = _
  simp_rw [← RawAttainment.dualFunctional_eq_raw]
  exact le_antisymm (iSup_le (fun v => iSup_le (hmax v)))
    (le_iSup_of_le u (le_iSup_of_le hu le_rfl))

/-- Every finite-entropy primal optimizer has an actual smooth, mean-zero
continuous Gibbs potential which maximizes the full dual functional. -/
theorem continuous_optimizer_of_minimizer {d : ℕ} (hd : 0 < d) {β : ℝ} (hβ : 0 < β)
    (ρ : ProbabilityDensity d) (hρ : IsGlobalMinimizer β ρ) :
    ∃ u : Space d, InCriticalSobolev u ∧ MeanZero u ∧ SmoothOnTorus u ∧
      (∀ s : ℝ, InSobolev s u) ∧
      (∀ v : Torus d → ℝ, InCriticalSobolev v → dualFunctional β v ≤ dualFunctional β u) ∧
      ρ.value =ᵐ[torusMeasure d] normalizedGibbs u := by
  have hσ : 0 < spectralThreshold d := spectralThreshold_pos hd
  have hA : 0 < spectralThreshold d/(2*β) := by positivity
  have hC : 0 < Legacy.BecknerOnofri.endpointConstant d :=
    div_pos (Nat.cast_pos.mpr hd) (Legacy.TorusEndpoint.endpointSigma_pos hd)
  have hb : 0 < Legacy.BecknerOnofri.endpointConstant d/2 := by positivity
  have hbC : Legacy.BecknerOnofri.endpointConstant d/2 < Legacy.BecknerOnofri.endpointConstant d := by linarith
  have hR := GenericAttainment.rough_bound hd hb hbC
  have hQ := (legacy_rough_finite_entropy hd (Bridge.density ρ) hρ.1 hb hbC).1
  have hcoef : 1/(4*(β/(2*spectralThreshold d))) = spectralThreshold d/(2*β) := by
    field_simp
    <;> ring
  have hinv : 1/(4*(spectralThreshold d/(2*β))) = β/(2*spectralThreshold d) := by
    field_simp
    <;> ring
  have hBound (v : TorusL2 d) (hv : Admissible v) :
      functional (1/(4*(β/(2*spectralThreshold d)))) v ≤
        (β/(2*spectralThreshold d))*Legacy.BecknerOnofri.fourierEnergy (Bridge.density ρ)-
          Legacy.TorusEndpoint.densityEntropy ρ.value := by
    have hh := hρ.2 (Bridge.rawDensity (gibbsDensity hR hv)) (gibbsDensity_finiteEntropy hR hv)
    rw [pressureValue_eq_legacy hd hβ (Bridge.rawDensity (gibbsDensity hR hv)) (gibbsDensity_finiteEntropy hR hv),
      pressureValue_eq_legacy hd hβ ρ hρ.1] at hh
    have hh' : densityFunctional (spectralThreshold d/(2*β)) (gibbsDensity hR hv) ≤
        densityFunctional (spectralThreshold d/(2*β)) (Bridge.density ρ) := by exact_mod_cast hh
    have hh'' := (dual_le_gibbs hd hR hA hv).trans hh'
    rwa [densityFunctional, hinv, ← hcoef] at hh''
  obtain ⟨U,hU,hg,hvalue,hmax⟩ := BecknerOnofri.OptimizerGibbsLimit.exists_gibbs_optimizer hd hb hR
    (by positivity : 0 < β/(2*spectralThreshold d)) (Bridge.density ρ) hρ.1 hQ hBound
  rw [hcoef] at hvalue hmax
  have hs := maximizer_fourier_summable hd hR hA hU hmax
  let u := realRepresentative U hs
  have huL : toL2 d u = U := toL2_realRepresentative U hs hU.1
  have huadm : Admissible (toL2 d u) := by rw [huL]; exact hU
  have hu := inCriticalSobolev_of_toL2 u huadm
  have hm := meanZero_of_toL2 u huadm
  have huradial (m : ℕ) : Radial m u := by
    have hh := maximizer_radialSummable hd hR hA hU hmax m
    simpa only [Radial, Legacy.BecknerOnofri.RadialWiener.RadialSummable, coefficient_apply, huL] using hh
  refine ⟨u,hu,hm,smooth_of_radial u huradial,inSobolev_of_radial u huradial,?_,?_⟩
  · intro v hv
    rw [OnsetRaw.dualFunctional_eq_normalized hd β v hv, dualFunctional_eq_toL2 hd β u hu hm, huL]
    have hadm := Legacy.BecknerOnofri.SobolevCentering.center_admissible hd
      (Bridge.potentialLp_real v hv.1) (Bridge.potentialLp_summable hd v hv)
    exact_mod_cast hmax _ hadm
  · have hZ : Legacy.BecknerOnofri.SubcriticalAttainment.partition U = ContinuousGibbs.partition u := by
      rw [← huL, partition_toL2]
    filter_upwards [hg, realRepresentative_ae U hs] with x hx he
    change u x = (U x).re at he
    change ρ.value x = _ at hx
    rw [hx]
    change Real.exp (U x).re / Legacy.BecknerOnofri.SubcriticalAttainment.partition U = _
    rw [hZ, ← he]
    simp only [normalizedGibbs, ContinuousGibbs.partition, mean_apply, exponential_apply]

theorem gibbsValue_toL2_ae {d : ℕ} (u : Space d) :
    gibbsValue (toL2 d u) =ᵐ[torusMeasure d] normalizedGibbs u := by
  filter_upwards [toL2_ae u] with x hx
  simp only [gibbsValue, hx, Complex.ofReal_re, partition_toL2,
    normalizedGibbs, ContinuousGibbs.partition, mean_apply, exponential_apply]

/-- The Gibbs density of an actual continuous global dual optimizer is a
finite-entropy optimizer over the entire density domain. -/
theorem gibbs_minimizer_of_continuous_optimizer {d : ℕ} (hd : 0 < d) {β : ℝ} (hβ : 0 < β)
    (u : Space d) (hu : InCriticalSobolev u) (hm : MeanZero u)
    (hmax : ∀ v : Torus d → ℝ, InCriticalSobolev v → dualFunctional β v ≤ dualFunctional β u) :
    IsGlobalMinimizer β (continuousGibbsDensity u) := by
  have hσ : 0 < spectralThreshold d := spectralThreshold_pos hd
  have hA : 0 < spectralThreshold d/(2*β) := by positivity
  have hC : 0 < Legacy.BecknerOnofri.endpointConstant d :=
    div_pos (Nat.cast_pos.mpr hd) (Legacy.TorusEndpoint.endpointSigma_pos hd)
  have hR := GenericAttainment.rough_bound hd
    (by positivity : 0 < Legacy.BecknerOnofri.endpointConstant d/2)
    (by linarith : Legacy.BecknerOnofri.endpointConstant d/2 < Legacy.BecknerOnofri.endpointConstant d)
  have hadm := toL2_admissible hd u hu hm
  let r := Bridge.rawDensity (gibbsDensity hR hadm)
  have hr : r.FiniteEntropy := gibbsDensity_finiteEntropy hR hadm
  have he : r.value =ᵐ[torusMeasure d] (continuousGibbsDensity u).value := gibbsValue_toL2_ae u
  apply (minimizer_congr_ae he β).mp
  refine ⟨hr,?_⟩
  intro ρ hρ
  have hle : pressureValue β ρ ≤ pressure d β :=
    le_iSup_of_le ρ (le_iSup_of_le hρ le_rfl)
  have hv := maximizer_functional_eq_density hd hR hA hadm (toL2_optimizer hd β u hu hm hmax)
  rw [pressure_eq_dual hd hβ u hu hmax, dualFunctional_eq_toL2 hd β u hu hm, hv] at hle
  rwa [pressureValue_eq_legacy hd hβ r hr]

/-- Exact actual primal-dual correspondence, with full domains. -/
theorem minimizer_iff_continuous_optimizer {d : ℕ} (hd : 0 < d) {β : ℝ} (hβ : 0 < β)
    (ρ : ProbabilityDensity d) :
    IsGlobalMinimizer β ρ ↔
      ∃ u : Space d, InCriticalSobolev u ∧ MeanZero u ∧
        (∀ v : Torus d → ℝ, InCriticalSobolev v → dualFunctional β v ≤ dualFunctional β u) ∧
        ρ.value =ᵐ[torusMeasure d] normalizedGibbs u := by
  constructor
  · intro hρ
    obtain ⟨u,hu,hm,_,_,hmax,hg⟩ := continuous_optimizer_of_minimizer hd hβ ρ hρ
    exact ⟨u,hu,hm,hmax,hg⟩
  · rintro ⟨u,hu,hm,hmax,hg⟩
    exact (minimizer_congr_ae hg β).mpr (gibbs_minimizer_of_continuous_optimizer hd hβ u hu hm hmax)

/-- Actual global density minimizers exist throughout the physical subcritical range. -/
theorem exists_minimizer {d : ℕ} (hd : 0 < d) {β : ℝ}
    (hβ : 0 < β) (hβd : β < 2*(d:ℝ)) : ∃ ρ : ProbabilityDensity d, IsGlobalMinimizer β ρ := by
  obtain ⟨u,hu,hm,_,_,_,hmax,_⟩ := exists_continuous_optimizer hd hβ hβd
  exact ⟨continuousGibbsDensity u, gibbs_minimizer_of_continuous_optimizer hd hβ u hu hm hmax⟩

/-- Normalization and zero mean uniquely fix the continuous Gibbs potential. -/
theorem meanZero_gibbs_injective {d : ℕ} {u v : Space d}
    (hu : MeanZero u) (hv : MeanZero v)
    (he : normalizedGibbs u =ᵐ[torusMeasure d] normalizedGibbs v) : u = v := by
  haveI : (torusMeasure d).IsOpenPosMeasure := by
    unfold torusMeasure
    infer_instance
  have he' : (normalized u : Torus d → ℝ) =ᵐ[torusMeasure d] (normalized v : Torus d → ℝ) := by
    filter_upwards [he] with x hx
    simpa only [normalized_apply] using hx
  have hn := Measure.eq_of_ae_eq he' (normalized u).continuous (normalized v).continuous
  have hlog (x : Torus d) :
      u x-Real.log (ContinuousGibbs.partition u) = v x-Real.log (ContinuousGibbs.partition v) := by
    apply Real.exp_injective
    have hx := congrFun hn x
    simpa only [Real.exp_sub, Real.exp_log (ContinuousGibbs.partition_pos u),
      Real.exp_log (ContinuousGibbs.partition_pos v), normalized, ContinuousMap.smul_apply,
      smul_eq_mul, exponential_apply, div_eq_mul_inv, mul_comm] using hx
  have hc : u-v = ContinuousMap.const (Torus d)
      (Real.log (ContinuousGibbs.partition u)-Real.log (ContinuousGibbs.partition v)) := by
    ext x
    simp only [ContinuousMap.sub_apply, ContinuousMap.const_apply]
    linarith [hlog x]
  have hm := congrArg (mean d) hc
  rw [map_sub, mean_const, show mean d u=0 from hu, show mean d v=0 from hv] at hm
  apply ContinuousMap.ext
  intro x
  have hh := hlog x
  linarith

theorem minimizer_value_eq_pressure {d : ℕ} {β : ℝ} {ρ : ProbabilityDensity d}
    (hρ : IsGlobalMinimizer β ρ) : pressureValue β ρ = pressure d β := by
  apply le_antisymm
  · exact le_iSup_of_le ρ (le_iSup_of_le hρ.1 le_rfl)
  · exact iSup_le (fun η => iSup_le (hρ.2 η))

/-- The correspondence preserves the actual extended-real objective values. -/
theorem gibbs_optimizer_value {d : ℕ} (hd : 0 < d) {β : ℝ} (hβ : 0 < β)
    {ρ : ProbabilityDensity d} (u : Space d) (hu : InCriticalSobolev u) (hm : MeanZero u)
    (hmax : ∀ v : Torus d → ℝ, InCriticalSobolev v → dualFunctional β v ≤ dualFunctional β u)
    (hg : ρ.value =ᵐ[torusMeasure d] normalizedGibbs u) :
    pressureValue β ρ = dualFunctional β u := by
  have hρ := (minimizer_iff_continuous_optimizer hd hβ ρ).mpr ⟨u,hu,hm,hmax,hg⟩
  rw [minimizer_value_eq_pressure hρ, pressure_eq_dual hd hβ u hu hmax]

#print axioms meanZero_gibbs_injective
#print axioms continuous_optimizer_of_minimizer
#print axioms gibbs_minimizer_of_continuous_optimizer
#print axioms minimizer_iff_continuous_optimizer
#print axioms exists_minimizer
end BecknerOnofri.HighDim.OptimizerDuality
