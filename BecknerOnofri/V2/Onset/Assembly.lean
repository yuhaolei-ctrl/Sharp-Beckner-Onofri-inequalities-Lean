module

public import BecknerOnofri.V2.Onset.Orbit
public import BecknerOnofri.LocalElevenCore.FullModeLocalBranch
public import BecknerOnofri.LocalElevenCore.DiagonalSobolevProfile
public import BecknerOnofri.OptimizerDuality
public import BecknerOnofri.ContinuousOptimizers

@[expose] public section

/-! # Assembly of `FullBranchOnset d` (manuscript route)

From the orbit classification `optimizers_eventually_branch_orbit_v2` (Sobolev smallness,
`H^s` classification, exclusion of proper-support branches), the explicit branch is itself a
global optimizer (translation invariance), the free-energy minimizers are exactly its translates,
and the Morse--Bott and profile estimates are those of `LocalEleven.fullmode_local_branch`.
The only conditional hypothesis is `OnsetEndpointInputs d`. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped Topology

namespace BecknerOnofri.V2.Onset
open BecknerOnofri.HighDim ContinuousGibbs ContinuousSymmetry
open BecknerOnofri.HighDim.LocalEleven

/-- The explicit symmetric branch itself attains the raw dual maximum. -/
theorem branch_eventually_optimizer_v2 {d : ℕ} (hd : 12 ≤ d) (E : OnsetEndpointInputs d) :
    ∀ᶠ μ in 𝓝[>] (1 : ℝ),
      let U := LocalEleven.DiagonalScalarBranch.branchPotential (by omega : 11 ≤ d)
        (LocalEleven.DiagonalScalarBranch.amplitude (by omega : 11 ≤ d) μ)
      InCriticalSobolev U ∧ MeanZero U ∧
        ∀ v : Torus d → ℝ, InCriticalSobolev v →
          dualFunctional (μ * spectralThreshold d) v ≤ dualFunctional (μ * spectralThreshold d) U := by
  have hgap : ∀ᶠ μ in 𝓝 (1 : ℝ), μ * spectralThreshold d < 2 * (d : ℝ) := by
    simpa using ((continuous_id.mul_const (spectralThreshold d)).tendsto (1 : ℝ)).eventually
      (gt_mem_nhds (by simpa using spectral_subcritical_gap hd))
  filter_upwards [optimizers_eventually_branch_orbit_v2 hd E,
    hgap.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with μ horbit hg hp
  have hβ : 0 < μ * spectralThreshold d :=
    mul_pos (by change 1 < μ at hp; linarith) (spectralThreshold_pos (by omega))
  obtain ⟨u, hu, hm, hs, hreg, hzero, hmax, hfull⟩ :=
    ContinuousOptimizers.exists_continuous_optimizer (by omega) hβ hg
  obtain ⟨a, ha⟩ := horbit u hu hm hmax
  apply (OptimizerTranslation.continuous_optimizer_translation_iff (μ * spectralThreshold d)
    (LocalEleven.DiagonalScalarBranch.branchPotential (by omega : 11 ≤ d)
      (LocalEleven.DiagonalScalarBranch.amplitude (by omega : 11 ≤ d) μ)) a).mp
  rw [← ha]
  exact ⟨hu, hm, hmax⟩

/-- Complete finite-entropy minimizer classification near onset (coupling `μ β_s`). -/
theorem density_minimizers_eventually_v2 {d : ℕ} (hd : 12 ≤ d) (E : OnsetEndpointInputs d) :
    ∀ᶠ μ in 𝓝[>] (1 : ℝ),
      let U := LocalEleven.DiagonalScalarBranch.branchPotential (by omega : 11 ≤ d)
        (LocalEleven.DiagonalScalarBranch.amplitude (by omega : 11 ≤ d) μ)
      (∃ ρ : ProbabilityDensity d, IsGlobalMinimizer (μ * spectralThreshold d) ρ) ∧
      (∀ ρ : ProbabilityDensity d, IsGlobalMinimizer (μ * spectralThreshold d) ρ ↔
        ∃ a : Torus d, ρ.value =ᵐ[torusMeasure d] normalizedGibbs (translate U a)) := by
  filter_upwards [optimizers_eventually_branch_orbit_v2 hd E,
    branch_eventually_optimizer_v2 hd E, self_mem_nhdsWithin] with μ horbit hopt hp
  have hβ : 0 < μ * spectralThreshold d :=
    mul_pos (by change 1 < μ at hp; linarith) (spectralThreshold_pos (by omega))
  let U := LocalEleven.DiagonalScalarBranch.branchPotential (by omega : 11 ≤ d)
    (LocalEleven.DiagonalScalarBranch.amplitude (by omega : 11 ≤ d) μ)
  refine ⟨⟨OptimizerDuality.continuousGibbsDensity U,
    OptimizerDuality.gibbs_minimizer_of_continuous_optimizer (by omega) hβ U hopt.1 hopt.2.1
      hopt.2.2⟩, ?_⟩
  intro ρ
  rw [OptimizerDuality.minimizer_iff_continuous_optimizer (by omega) hβ ρ]
  constructor
  · rintro ⟨u, hu, hm, hmax, hg⟩
    obtain ⟨a, ha⟩ := horbit u hu hm hmax
    refine ⟨a, ?_⟩
    rw [ha] at hg
    exact hg
  · rintro ⟨a, ha⟩
    have ht := OptimizerTranslation.continuous_optimizer_translation
      (μ * spectralThreshold d) U hopt.1 hopt.2.1 hopt.2.2 a
    exact ⟨translation a U, ht.1, ht.2.1, ht.2.2, ha⟩

/-- The same classification in the coupling variable `β`, for the physical branch. -/
theorem physical_density_classification_v2 {d : ℕ} (hd : 12 ≤ d) (E : OnsetEndpointInputs d) :
    ∀ᶠ β in 𝓝[>] (spectralThreshold d),
      (∃ ρ : ProbabilityDensity d, IsGlobalMinimizer β ρ) ∧
      (∀ ρ : ProbabilityDensity d, IsGlobalMinimizer β ρ ↔
        ∃ a : Torus d, ρ.value =ᵐ[torusMeasure d]
          normalizedGibbs (translate (LocalEleven.DiagonalScalarBranch.physicalPotential (by omega : 11 ≤ d) β) a)) := by
  have hσ := (spectralThreshold_pos (by omega : 0 < d)).ne'
  have hh := (LocalEleven.DiagonalScalarBranch.normalized_parameter_tendsto (by omega : 11 ≤ d)).eventually
    (density_minimizers_eventually_v2 hd E)
  simpa only [div_mul_cancel₀ _ hσ, LocalEleven.DiagonalScalarBranch.physicalPotential] using hh

/-- **Full branch onset (Theorem 1.3 packaging of the branch assertions).**  For `d ≥ 12`, the
endpoint inputs imply `FullBranchOnset d`: a Morse--Bott family of full-mode branches, existence
and exact translation-orbit classification of the free-energy minimizers, and the `H^s` profile
estimate with `O(δ)` remainder uniformly over translations. -/
theorem full_branch_onset_of_inputs {d : ℕ} (hd : 12 ≤ d) (E : OnsetEndpointInputs d) :
    FullBranchOnset d := by
  have hd11 : 11 ≤ d := by omega
  have hAll : ∀ᶠ β in 𝓝[>] (spectralThreshold d),
      FullModeMorseBott β (LocalEleven.DiagonalScalarBranch.physicalPotential hd11 β) ∧
      (∃ ρ : ProbabilityDensity d, IsGlobalMinimizer β ρ) ∧
      (∀ ρ : ProbabilityDensity d, IsGlobalMinimizer β ρ ↔
        ∃ a : Torus d, ρ.value =ᵐ[torusMeasure d]
          normalizedGibbs (translate (LocalEleven.DiagonalScalarBranch.physicalPotential hd11 β) a)) := by
    filter_upwards [PhysicalBranchProperties.physical_branch_properties hd11,
      FullBranchHessian.physical_hessian_nonpos_kernel hd11,
      PhysicalNormalCoercivity.physical_normalCoercivity hd11,
      physical_sobolev_local_maximum hd11,
      physical_density_classification_v2 hd E] with β hb hh hn hmax hc
    exact ⟨⟨hb.smooth, fun s _ => hb.sobolev s, hb.criticalSobolev, hb.meanZero, hb.stationary,
      hb.fullModes, hb.tangentIndependent,
      fun h hc hm => (hh h hc hm).1, fun h hc hm => (hh h hc hm).2, hn, hmax⟩, hc⟩
  obtain ⟨r, hr, hBall⟩ := Metric.mem_nhdsWithin_iff.mp hAll
  refine ⟨r, hr, (fun β => (LocalEleven.DiagonalScalarBranch.physicalPotential hd11 β : Torus d → ℝ)), ?_, ?_⟩
  · intro β hβ hupper
    apply hBall
    refine ⟨?_, hβ⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (sub_pos.mpr hβ)]
    linarith
  · intro s _
    exact LocalEleven.DiagonalScalarBranch.physical_profile_sobolev_interval hd11 s hr

#print axioms full_branch_onset_of_inputs
#print axioms optimizers_eventually_branch_orbit_v2

end BecknerOnofri.V2.Onset
