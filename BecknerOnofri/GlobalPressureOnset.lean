module

public import BecknerOnofri.ContinuousOptimizers
public import BecknerOnofri.ContinuousLocalReduction
public import BecknerOnofri.LocalAmplitudeSelection
public import BecknerOnofri.SupercriticalBranchEnergy
public import BecknerOnofri.DiagonalProfile

@[expose] public section

/-! The sharp pressure onset from the exact endpoint and its rigidity. These
premises are explicit; no numerical certificate is assumed as an axiom. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter MeasureTheory
open scoped Topology
namespace BecknerOnofri.HighDim.GlobalPressureOnset
open ContinuousGibbs ContinuousFirstShell ContinuousComplement GreenLocalBranch ReducedEquation
open ContinuousOptimizers OnsetContinuous ReducedEnergyGradient LocalReducedEnergyUpper

/-- A global optimizer realizes the actual full finite-entropy pressure. -/
theorem optimizer_pressure {d : ℕ} (hd : 0 < d) {β : ℝ} (hβ : 0 < β)
    (u : Torus d → ℝ) (hu : InCriticalSobolev u)
    (hmax : ∀ v : Torus d → ℝ, InCriticalSobolev v → dualFunctional β v ≤ dualFunctional β u) :
    pressure d β = dualFunctional β u := by
  rw [pressure_eq_coefficientDefect hd hβ]
  change (⨆ v : Torus d → ℝ, ⨆ _hv : InCriticalSobolev v,
    RawAttainment.rawFunctional (spectralThreshold d/(2*β*(2*Real.pi)^d)) v) = _
  simp_rw [← RawAttainment.dualFunctional_eq_raw]
  exact le_antisymm (iSup_le (fun v => iSup_le (hmax v)))
    (le_iSup_of_le u (le_iSup_of_le hu le_rfl))

theorem continuous_dual_coe {d : ℕ} (hd : 0 < d) (β : ℝ)
    (u : Space d) (hu : InCriticalSobolev u) (hm : MeanZero u) :
    dualFunctional β u = ((dualFunctional β u).toReal : EReal) := by
  rw [dualFunctional_eq_toL2 hd β u hu hm, EReal.toReal_coe]

/-- Uniform optimizer compactness along any parameter filter. -/
theorem optimizer_family_tendsto {d : ℕ} (hd : 12 ≤ d)
    (hEndpoint : BecknerOnofri.EndpointRigidity.CoefficientEndpoint d (1/2))
    (hRigidity : BecknerOnofri.OnsetCompactness.DensityRigidity d)
    {α : Type*} {l : Filter α} {μ : α → ℝ} {u : α → Space d}
    (hμ : Tendsto μ l (𝓝 1))
    (hu : ∀ᶠ n in l, InCriticalSobolev (u n)) (hm : ∀ᶠ n in l, MeanZero (u n))
    (hmax : ∀ᶠ n in l, ∀ v : Torus d → ℝ, InCriticalSobolev v →
      dualFunctional (μ n*spectralThreshold d) v ≤ dualFunctional (μ n*spectralThreshold d) (u n)) :
    Tendsto (fun n => (μ n,u n)) l (𝓝 (1,0)) := by
  apply tendsto_def.mpr
  intro S hS
  filter_upwards [hμ.eventually (optimizers_eventually_near_normalized hd hEndpoint hRigidity hS),
    hu,hm,hmax] with n hn hu hm hx
  exact hn (u n) hu hm hx

theorem optimizers_eventually_on_graph {d : ℕ} (hd : 12 ≤ d)
    (hEndpoint : BecknerOnofri.EndpointRigidity.CoefficientEndpoint d (1/2))
    (hRigidity : BecknerOnofri.OnsetCompactness.DensityRigidity d) :
    ∀ᶠ μ in 𝓝 (1:ℝ), ∀ u : Space d, InCriticalSobolev u → MeanZero u →
      (∀ v : Torus d → ℝ, InCriticalSobolev v →
        dualFunctional (μ*spectralThreshold d) v ≤ dualFunctional (μ*spectralThreshold d) u) →
      u = potential hd (μ,coordinates d u) ∧ reduced hd (μ,coordinates d u) = 0 := by
  filter_upwards [optimizers_eventually_near_normalized hd hEndpoint hRigidity
    (small_full_solution_on_graph hd), lt_mem_nhds (by norm_num : (0:ℝ)<1)] with μ hnear hμ u hu hm hmax
  exact hnear u hu hm hmax hm (continuous_optimizer_full (by omega) hμ u hu hm hmax)

theorem pressure_upper {d : ℕ} (hd : 12 ≤ d)
    (hEndpoint : BecknerOnofri.EndpointRigidity.CoefficientEndpoint d (1/2))
    (hRigidity : BecknerOnofri.OnsetCompactness.DensityRigidity d) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ μ in 𝓝[>] (1:ℝ),
      ∃ p : ℝ, pressure d (μ*spectralThreshold d) = (p : EReal) ∧
        p ≤ (d:ℝ)/(2*kappa d)*(onsetParameter μ)^2+C*(onsetParameter μ)^3 := by
  obtain ⟨C,hC,hupper⟩ := nonnegative_energy_upper hd
  have ht : Tendsto (fun x : ℝ × Space d => (x.1,coordinates d x.2))
      (𝓝 (1,0)) (𝓝 (1,(0:Coordinates d))) := by
    simpa only [Function.comp_apply, map_zero] using
      (continuous_fst.prodMk ((coordinates d).continuous.comp continuous_snd)).tendsto ((1:ℝ),(0:Space d))
  have hnear := optimizers_eventually_near_normalized hd hEndpoint hRigidity (ht.eventually hupper)
  have hσ : 0 < spectralThreshold d := spectralThreshold_pos (by omega)
  have hgap : ∀ᶠ μ in 𝓝 (1:ℝ), μ*spectralThreshold d < 2*(d:ℝ) := by
    have hh := ((continuous_id.mul_const (spectralThreshold d)).tendsto (1:ℝ)).eventually
      (gt_mem_nhds (by simpa using spectral_subcritical_gap hd))
    simpa using hh
  refine ⟨C,hC,?_⟩
  filter_upwards [self_mem_nhdsWithin, hgap.filter_mono nhdsWithin_le_nhds,
    hnear.filter_mono nhdsWithin_le_nhds,
    (optimizers_eventually_on_graph hd hEndpoint hRigidity).filter_mono nhdsWithin_le_nhds]
    with μ hμ hg hn hon
  have hμ0 : 0 < μ := by change 1<μ at hμ; linarith
  obtain ⟨u,hu,hm,hs,hreg,hzero,hmax,hfull⟩ := exists_continuous_optimizer (by omega)
    (mul_pos hμ0 hσ) hg
  have hug := (hon u hu hm hmax).1
  have he : dualFunctional (μ*spectralThreshold d) u =
      (physicalReducedEnergy hd (μ,coordinates d u) : EReal) := by
    rw [continuous_dual_coe (by omega) _ u hu hm]
    congr 1
    unfold physicalReducedEnergy
    rw [← hug]
  have hE : 0 ≤ physicalReducedEnergy hd (μ,coordinates d u) := by
    rw [he] at hzero
    exact_mod_cast hzero
  refine ⟨physicalReducedEnergy hd (μ,coordinates d u),?_,hn u hu hm hmax hμ hE⟩
  exact (optimizer_pressure (by omega) (mul_pos hμ0 hσ) u hu hmax).trans he

theorem pressure_asymptotic_normalized {d : ℕ} (hd : 12 ≤ d)
    (hEndpoint : BecknerOnofri.EndpointRigidity.CoefficientEndpoint d (1/2))
    (hRigidity : BecknerOnofri.OnsetCompactness.DensityRigidity d) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ μ in 𝓝[>] (1:ℝ),
      ∃ p : ℝ, pressure d (μ*spectralThreshold d) = (p : EReal) ∧
        |p-(d:ℝ)/(2*kappa d)*(onsetParameter μ)^2| ≤ C*(onsetParameter μ)^3 := by
  obtain ⟨C,hC,hu⟩ := pressure_upper hd hEndpoint hRigidity
  obtain ⟨B,hB,hl⟩ := DiagonalScalarBranch.pressure_onset_lower_bound hd
  refine ⟨C+B,by positivity,?_⟩
  filter_upwards [hu,hl,self_mem_nhdsWithin] with μ hupper hlower hμ
  obtain ⟨p,hp,hub⟩ := hupper
  rw [hp] at hlower
  have hlb : (d:ℝ)/(2*kappa d)*(onsetParameter μ)^2-B*(onsetParameter μ)^3 ≤ p :=
    EReal.coe_le_coe_iff.mp hlower
  have hδ := onsetParameter_pos hμ
  refine ⟨p,hp,abs_le.mpr ⟨?_,?_⟩⟩ <;> nlinarith [pow_pos hδ 3]

/-- Exactly the scalar pressure-onset conclusion in Challenge, conditional on
only the genuine endpoint inequality and its finite-entropy rigidity. -/
theorem pressure_onset_of_endpoint {d : ℕ} (hd : 12 ≤ d)
    (hEndpoint : BecknerOnofri.EndpointRigidity.CoefficientEndpoint d (1/2))
    (hRigidity : BecknerOnofri.OnsetCompactness.DensityRigidity d) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 ≤ C ∧
      ∀ β : ℝ, spectralThreshold d < β → β < spectralThreshold d+ε →
        ∃ p : ℝ, pressure d β = (p : EReal) ∧
          |p-(d:ℝ)/(2*kappa d)*(1-spectralThreshold d/β)^2| ≤
            C*(β-spectralThreshold d)^3 := by
  obtain ⟨C,hC,hB⟩ := pressure_asymptotic_normalized hd hEndpoint hRigidity
  have hσ : 0 < spectralThreshold d := spectralThreshold_pos (by omega)
  have he := (DiagonalScalarBranch.normalized_parameter_tendsto hd).eventually hB
  obtain ⟨r,hr,hBall⟩ := Metric.mem_nhdsWithin_iff.mp he
  refine ⟨r,C/(spectralThreshold d)^3,hr,by positivity,?_⟩
  intro β hβ hupper
  have hβ0 : 0 < β := hσ.trans hβ
  have hdist : β ∈ Metric.ball (spectralThreshold d) r ∩ Set.Ioi (spectralThreshold d) := by
    refine ⟨?_,hβ⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (sub_pos.mpr hβ)]
    linarith
  obtain ⟨p,hp,herr⟩ := hBall hdist
  rw [div_mul_cancel₀ _ hσ.ne'] at hp
  have heq : onsetParameter (β/spectralThreshold d) = 1-spectralThreshold d/β := by
    unfold onsetParameter
    field_simp
  rw [heq] at herr
  refine ⟨p,hp,herr.trans ?_⟩
  have hδ0 : 0 ≤ 1-spectralThreshold d/β := by
    have hh := (div_lt_one hβ0).mpr hβ
    linarith
  have hδ : 1-spectralThreshold d/β ≤ (β-spectralThreshold d)/spectralThreshold d := by
    calc
      _ = (β-spectralThreshold d)/β := by field_simp <;> ring
      _ ≤ _ := div_le_div_of_nonneg_left (sub_nonneg.mpr hβ.le) hσ hβ.le
  calc
    _ ≤ C*((β-spectralThreshold d)/spectralThreshold d)^3 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hδ0 hδ 3) hC.le
    _ = _ := by rw [div_pow]; ring

#print axioms pressure_onset_of_endpoint
#print axioms optimizers_eventually_on_graph
#print axioms pressure_upper
end BecknerOnofri.HighDim.GlobalPressureOnset
