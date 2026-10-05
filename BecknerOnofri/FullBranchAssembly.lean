module

public import BecknerOnofri.PhysicalBranchProperties
public import BecknerOnofri.GlobalOptimizerClassification
public import BecknerOnofri.DiagonalSobolevProfile

@[expose] public section

/-! Assembly of the exact trusted branch statement. All raw Hessian
conditions remain explicit until supplied by the full-domain Hessian proof. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace BecknerOnofri.HighDim.FullBranchAssembly
open DiagonalScalarBranch PhysicalBranchProperties GlobalOptimizerClassification

/-- The three full-domain Hessian fields, in precisely the trusted formulation. -/
structure HessianProperties {d : ℕ} (β : ℝ) (u : Torus d → ℝ) : Prop where
  nonpos : ∀ h : Torus d → ℝ, InCriticalSobolev h → MeanZero h → secondVariation β u h ≤ 0
  kernel : ∀ h : Torus d → ℝ, InCriticalSobolev h → MeanZero h →
    (secondVariation β u h = 0 ↔ ∃ a : Fin d → ℝ,
      h =ᵐ[torusMeasure d] tangentCombination u a)
  normal : ∃ c : ℝ, 0 < c ∧ ∀ h : Torus d → ℝ,
    InCriticalSobolev h → InSobolev ((d:ℝ)/2) h → MeanZero h →
    (∀ j : Fin d, (∫ x, h x*coordinateDerivative u j x ∂torusMeasure d)=0) →
    secondVariation β u h ≤ -c*sobolevNorm ((d:ℝ)/2) h^2

theorem morseBott_of_global {d : ℕ} {β : ℝ} {u : Torus d → ℝ}
    (hb : BasicProperties β u) (hh : HessianProperties β u)
    (hmax : ∀ v : Torus d → ℝ, InCriticalSobolev v → dualFunctional β v ≤ dualFunctional β u) :
    FullModeMorseBott β u where
  smooth := hb.smooth
  sobolev := fun s _ => hb.sobolev s
  criticalSobolev := hb.criticalSobolev
  meanZero := hb.meanZero
  stationary := hb.stationary
  fullModes := hb.fullModes
  tangentIndependent := hb.tangentIndependent
  hessianNonpos := hh.nonpos
  hessianKernel := hh.kernel
  normalCoercivity := hh.normal
  localMaximum := fun _ _ => ⟨1,by norm_num,fun v _ hv _ _ _ => hmax v hv⟩

/-- All quantifiers of the original branch assertion, including one family
for every Sobolev index and all translations, are preserved in this assembly. -/
theorem full_branch_onset_of_hessian {d : ℕ} (hd : 12 ≤ d)
    (hEndpoint : BecknerOnofri.EndpointRigidity.CoefficientEndpoint d (1/2))
    (hRigidity : BecknerOnofri.OnsetCompactness.DensityRigidity d)
    (hH : ∀ᶠ β in 𝓝[>] (spectralThreshold d), HessianProperties β (physicalPotential hd β)) :
    FullBranchOnset d := by
  have hAll : ∀ᶠ β in 𝓝[>] (spectralThreshold d),
      FullModeMorseBott β (physicalPotential hd β) ∧
      (∃ ρ : ProbabilityDensity d, IsGlobalMinimizer β ρ) ∧
      (∀ ρ : ProbabilityDensity d, IsGlobalMinimizer β ρ ↔
        ∃ a : Torus d, ρ.value =ᵐ[torusMeasure d]
          normalizedGibbs (translate (physicalPotential hd β) a)) := by
    filter_upwards [physical_branch_properties hd,hH,
      physical_branch_optimizer hd hEndpoint hRigidity,
      physical_density_classification hd hEndpoint hRigidity] with β hb hh ho hc
    exact ⟨morseBott_of_global hb hh ho.2.2,hc⟩
  obtain ⟨r,hr,hBall⟩ := Metric.mem_nhdsWithin_iff.mp hAll
  refine ⟨r,hr,(fun β => (physicalPotential hd β : Torus d → ℝ)),?_,?_⟩
  · intro β hβ hupper
    apply hBall
    refine ⟨?_,hβ⟩
    rw [Metric.mem_ball,Real.dist_eq,abs_of_pos (sub_pos.mpr hβ)]
    linarith
  · intro s _
    exact physical_profile_sobolev_interval hd s hr

#print axioms full_branch_onset_of_hessian
end BecknerOnofri.HighDim.FullBranchAssembly
