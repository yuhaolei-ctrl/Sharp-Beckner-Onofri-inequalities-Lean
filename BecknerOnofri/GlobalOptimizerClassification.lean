import BecknerOnofri.GlobalPressureOnset
import BecknerOnofri.LocalOrbitClassification
import BecknerOnofri.PressureRegularity
import BecknerOnofri.OptimizerTranslation
import BecknerOnofri.OptimizerDuality

/-! Global optimizer classification through genuine uniform compactness and
actual stationary, near-optimal local orbit selection. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter
open scoped Topology
namespace BecknerOnofri.HighDim.GlobalOptimizerClassification
open ContinuousGibbs ContinuousFirstShell ContinuousSymmetry ReducedEquation
open ReducedEnergyGradient LocalReducedEnergyUpper GlobalPressureOnset

/-- The actual graph energy of a global optimizer is exactly the full pressure. -/
theorem graph_optimizer_pressure {d : ℕ} (hd : 12 ≤ d) {μ : ℝ} (hμ : 0 < μ)
    (u : Space d) (hu : InCriticalSobolev u) (hm : MeanZero u)
    (hmax : ∀ v : Torus d → ℝ, InCriticalSobolev v →
      dualFunctional (μ*spectralThreshold d) v ≤ dualFunctional (μ*spectralThreshold d) u)
    (hg : u = potential hd (μ,coordinates d u)) :
    pressure d (μ*spectralThreshold d) = (physicalReducedEnergy hd (μ,coordinates d u) : EReal) := by
  rw [optimizer_pressure (by omega) (mul_pos hμ (spectralThreshold_pos (by omega))) u hu hmax,
    continuous_dual_coe (by omega) _ u hu hm]
  congr 1
  unfold physicalReducedEnergy
  rw [← hg]

/-- Along any approaching family of actual global optimizers, the exact local
coordinates satisfy all the hypotheses of the local branch-selection theorem. -/
theorem optimizer_family_local_data {d : ℕ} (hd : 12 ≤ d)
    (hEndpoint : BecknerOnofri.EndpointRigidity.CoefficientEndpoint d (1/2))
    (hRigidity : BecknerOnofri.OnsetCompactness.DensityRigidity d)
    {α : Type*} {l : Filter α} {μ : α → ℝ} {u : α → Space d}
    (hμ : Tendsto μ l (𝓝 1)) (hμpos : ∀ᶠ n in l, 1 < μ n)
    (hu : ∀ᶠ n in l, InCriticalSobolev (u n)) (hm : ∀ᶠ n in l, MeanZero (u n))
    (hmax : ∀ᶠ n in l, ∀ v : Torus d → ℝ, InCriticalSobolev v →
      dualFunctional (μ n*spectralThreshold d) v ≤ dualFunctional (μ n*spectralThreshold d) (u n)) :
    Tendsto (fun n => coordinates d (u n)) l (𝓝 0) ∧
      ∃ C : ℝ, 0 < C ∧ ∀ᶠ n in l,
        u n = potential hd (μ n,coordinates d (u n)) ∧
        reduced hd (μ n,coordinates d (u n)) = 0 ∧
        0 ≤ physicalReducedEnergy hd (μ n,coordinates d (u n)) ∧
        (d:ℝ)/(2*kappa d)*(onsetParameter (μ n))^2-C*(onsetParameter (μ n))^3 ≤
          physicalReducedEnergy hd (μ n,coordinates d (u n)) := by
  have hjoint := optimizer_family_tendsto hd hEndpoint hRigidity hμ hu hm hmax
  have hz : Tendsto (fun n => coordinates d (u n)) l (𝓝 0) := by
    have hc := ((coordinates d).continuous.tendsto (0:Space d)).comp ((continuous_snd.tendsto ((1:ℝ),(0:Space d))).comp hjoint)
    convert! hc using 1
    simp only [map_zero]
  have hμright : Tendsto μ l (𝓝[>] (1:ℝ)) := tendsto_nhdsWithin_iff.mpr ⟨hμ,hμpos⟩
  obtain ⟨C,hC,hlo⟩ := DiagonalScalarBranch.pressure_onset_lower_bound hd
  refine ⟨hz,C,hC,?_⟩
  filter_upwards [hμ.eventually (optimizers_eventually_on_graph hd hEndpoint hRigidity),
    hμright.eventually hlo, hμpos, hu,hm,hmax] with n hgraph hlo hp hu hm hmax
  obtain ⟨hg,hr⟩ := hgraph (u n) hu hm hmax
  have hpeq := graph_optimizer_pressure hd (by linarith) (u n) hu hm hmax hg
  rw [hpeq] at hlo
  have hnonneg := pressure_nonneg d (μ n*spectralThreshold d)
  rw [hpeq] at hnonneg
  exact ⟨hg,hr,by exact_mod_cast hnonneg,EReal.coe_le_coe_iff.mp hlo⟩

theorem optimizer_family_branch_orbit {d : ℕ} (hd : 12 ≤ d)
    (hEndpoint : BecknerOnofri.EndpointRigidity.CoefficientEndpoint d (1/2))
    (hRigidity : BecknerOnofri.OnsetCompactness.DensityRigidity d)
    {α : Type*} {l : Filter α} {μ : α → ℝ} {u : α → Space d}
    (hμ : Tendsto μ l (𝓝 1)) (hμpos : ∀ᶠ n in l, 1 < μ n)
    (hu : ∀ᶠ n in l, InCriticalSobolev (u n)) (hm : ∀ᶠ n in l, MeanZero (u n))
    (hmax : ∀ᶠ n in l, ∀ v : Torus d → ℝ, InCriticalSobolev v →
      dualFunctional (μ n*spectralThreshold d) v ≤ dualFunctional (μ n*spectralThreshold d) (u n)) :
    ∀ᶠ n in l, ∃ a : Torus d, u n = translation a
      (DiagonalScalarBranch.branchPotential hd (DiagonalScalarBranch.amplitude hd (μ n))) := by
  obtain ⟨hz,C,hC,hdata⟩ := optimizer_family_local_data hd hEndpoint hRigidity hμ hμpos hu hm hmax
  have horbit := LocalOrbitClassification.stationary_branch_orbit hd hμ hz hμpos C hC.le
    (hdata.mono (fun _ h => h.2.2.1)) (hdata.mono (fun _ h => h.2.2.2))
    (hdata.mono (fun _ h => h.2.1))
  filter_upwards [hdata,horbit] with n hn ho
  obtain ⟨a,ha⟩ := ho
  exact ⟨a,hn.1.trans ha⟩

/-- Every continuous global optimizer, uniformly near the threshold, lies on
the one actually constructed translation orbit. -/
theorem optimizers_eventually_branch_orbit {d : ℕ} (hd : 12 ≤ d)
    (hEndpoint : BecknerOnofri.EndpointRigidity.CoefficientEndpoint d (1/2))
    (hRigidity : BecknerOnofri.OnsetCompactness.DensityRigidity d) :
    ∀ᶠ μ in 𝓝[>] (1:ℝ), ∀ u : Space d, InCriticalSobolev u → MeanZero u →
      (∀ v : Torus d → ℝ, InCriticalSobolev v →
        dualFunctional (μ*spectralThreshold d) v ≤ dualFunctional (μ*spectralThreshold d) u) →
      ∃ a : Torus d, u = translation a
        (DiagonalScalarBranch.branchPotential hd (DiagonalScalarBranch.amplitude hd μ)) := by
  classical
  by_contra hn
  have hf : ∃ᶠ μ in 𝓝[>] (1:ℝ), ∃ u : Space d,
      InCriticalSobolev u ∧ MeanZero u ∧
      (∀ v : Torus d → ℝ, InCriticalSobolev v →
        dualFunctional (μ*spectralThreshold d) v ≤ dualFunctional (μ*spectralThreshold d) u) ∧
      ¬∃ a : Torus d, u = translation a
        (DiagonalScalarBranch.branchPotential hd (DiagonalScalarBranch.amplitude hd μ)) := by
    simpa only [Filter.Frequently,not_exists,not_and,not_forall,Classical.not_imp,not_not] using hn
  obtain ⟨μ,hμ,hbad⟩ := exists_seq_forall_of_frequently hf
  choose u hu hm hmax houtside using hbad
  have horbit := optimizer_family_branch_orbit hd hEndpoint hRigidity
    (hμ.mono_right nhdsWithin_le_nhds) (hμ.eventually self_mem_nhdsWithin)
    (Eventually.of_forall hu) (Eventually.of_forall hm) (Eventually.of_forall hmax)
  obtain ⟨n,hn⟩ := horbit.exists
  exact houtside n hn

/-- The explicit symmetric branch itself attains the full raw dual maximum. -/
theorem branch_eventually_optimizer {d : ℕ} (hd : 12 ≤ d)
    (hEndpoint : BecknerOnofri.EndpointRigidity.CoefficientEndpoint d (1/2))
    (hRigidity : BecknerOnofri.OnsetCompactness.DensityRigidity d) :
    ∀ᶠ μ in 𝓝[>] (1:ℝ),
      let U := DiagonalScalarBranch.branchPotential hd (DiagonalScalarBranch.amplitude hd μ)
      InCriticalSobolev U ∧ MeanZero U ∧
        ∀ v : Torus d → ℝ, InCriticalSobolev v →
          dualFunctional (μ*spectralThreshold d) v ≤ dualFunctional (μ*spectralThreshold d) U := by
  have hgap : ∀ᶠ μ in 𝓝 (1:ℝ), μ*spectralThreshold d < 2*(d:ℝ) := by
    simpa using ((continuous_id.mul_const (spectralThreshold d)).tendsto (1:ℝ)).eventually
      (gt_mem_nhds (by simpa using spectral_subcritical_gap hd))
  filter_upwards [optimizers_eventually_branch_orbit hd hEndpoint hRigidity,
    hgap.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with μ horbit hg hp
  have hβ : 0 < μ*spectralThreshold d :=
    mul_pos (by change 1<μ at hp; linarith) (spectralThreshold_pos (by omega))
  obtain ⟨u,hu,hm,hs,hreg,hzero,hmax,hfull⟩ := ContinuousOptimizers.exists_continuous_optimizer (by omega) hβ hg
  obtain ⟨a,ha⟩ := horbit u hu hm hmax
  apply (OptimizerTranslation.continuous_optimizer_translation_iff (μ*spectralThreshold d)
    (DiagonalScalarBranch.branchPotential hd (DiagonalScalarBranch.amplitude hd μ)) a).mp
  rw [← ha]
  exact ⟨hu,hm,hmax⟩

/-- Complete finite-entropy minimizer classification near onset, with no
smoothness or L² hypothesis on the classified densities. -/
theorem density_minimizers_eventually {d : ℕ} (hd : 12 ≤ d)
    (hEndpoint : BecknerOnofri.EndpointRigidity.CoefficientEndpoint d (1/2))
    (hRigidity : BecknerOnofri.OnsetCompactness.DensityRigidity d) :
    ∀ᶠ μ in 𝓝[>] (1:ℝ),
      let U := DiagonalScalarBranch.branchPotential hd (DiagonalScalarBranch.amplitude hd μ)
      (∃ ρ : ProbabilityDensity d, IsGlobalMinimizer (μ*spectralThreshold d) ρ) ∧
      (∀ ρ : ProbabilityDensity d, IsGlobalMinimizer (μ*spectralThreshold d) ρ ↔
        ∃ a : Torus d, ρ.value =ᵐ[torusMeasure d] normalizedGibbs (translate U a)) := by
  filter_upwards [optimizers_eventually_branch_orbit hd hEndpoint hRigidity,
    branch_eventually_optimizer hd hEndpoint hRigidity,self_mem_nhdsWithin] with μ horbit hopt hp
  have hβ : 0 < μ*spectralThreshold d :=
    mul_pos (by change 1<μ at hp; linarith) (spectralThreshold_pos (by omega))
  let U := DiagonalScalarBranch.branchPotential hd (DiagonalScalarBranch.amplitude hd μ)
  refine ⟨⟨OptimizerDuality.continuousGibbsDensity U,
    OptimizerDuality.gibbs_minimizer_of_continuous_optimizer (by omega) hβ U hopt.1 hopt.2.1 hopt.2.2⟩,?_⟩
  intro ρ
  rw [OptimizerDuality.minimizer_iff_continuous_optimizer (by omega) hβ ρ]
  constructor
  · rintro ⟨u,hu,hm,hmax,hg⟩
    obtain ⟨a,ha⟩ := horbit u hu hm hmax
    refine ⟨a,?_⟩
    rw [ha] at hg
    exact hg
  · rintro ⟨a,ha⟩
    have ht := OptimizerTranslation.continuous_optimizer_translation
      (μ*spectralThreshold d) U hopt.1 hopt.2.1 hopt.2.2 a
    exact ⟨translation a U,ht.1,ht.2.1,ht.2.2,ha⟩

theorem physical_branch_optimizer {d : ℕ} (hd : 12 ≤ d)
    (hEndpoint : BecknerOnofri.EndpointRigidity.CoefficientEndpoint d (1/2))
    (hRigidity : BecknerOnofri.OnsetCompactness.DensityRigidity d) :
    ∀ᶠ β in 𝓝[>] (spectralThreshold d),
      InCriticalSobolev (DiagonalScalarBranch.physicalPotential hd β) ∧
      MeanZero (DiagonalScalarBranch.physicalPotential hd β) ∧
      ∀ v : Torus d → ℝ, InCriticalSobolev v →
        dualFunctional β v ≤ dualFunctional β (DiagonalScalarBranch.physicalPotential hd β) := by
  have hσ := (spectralThreshold_pos (by omega : 0<d)).ne'
  have hh := (DiagonalScalarBranch.normalized_parameter_tendsto hd).eventually
    (branch_eventually_optimizer hd hEndpoint hRigidity)
  simpa only [div_mul_cancel₀ _ hσ,DiagonalScalarBranch.physicalPotential] using hh

theorem physical_density_classification {d : ℕ} (hd : 12 ≤ d)
    (hEndpoint : BecknerOnofri.EndpointRigidity.CoefficientEndpoint d (1/2))
    (hRigidity : BecknerOnofri.OnsetCompactness.DensityRigidity d) :
    ∀ᶠ β in 𝓝[>] (spectralThreshold d),
      (∃ ρ : ProbabilityDensity d, IsGlobalMinimizer β ρ) ∧
      (∀ ρ : ProbabilityDensity d, IsGlobalMinimizer β ρ ↔
        ∃ a : Torus d, ρ.value =ᵐ[torusMeasure d]
          normalizedGibbs (translate (DiagonalScalarBranch.physicalPotential hd β) a)) := by
  have hσ := (spectralThreshold_pos (by omega : 0<d)).ne'
  have hh := (DiagonalScalarBranch.normalized_parameter_tendsto hd).eventually
    (density_minimizers_eventually hd hEndpoint hRigidity)
  simpa only [div_mul_cancel₀ _ hσ,DiagonalScalarBranch.physicalPotential] using hh

#print axioms physical_density_classification
#print axioms physical_branch_optimizer
#print axioms optimizers_eventually_branch_orbit
#print axioms optimizer_family_local_data
end BecknerOnofri.HighDim.GlobalOptimizerClassification
