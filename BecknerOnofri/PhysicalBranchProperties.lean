import BecknerOnofri.DiagonalProfile
import BecknerOnofri.GraphTranslationTangents
import BecknerOnofri.GraphCritical
import BecknerOnofri.EulerEquation

/-! All non-Hessian fields of the actual physical full-mode branch, including
its exact Fourier stationarity and actual raw translation tangent independence. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter MeasureTheory
open scoped Topology
namespace BecknerOnofri.HighDim.PhysicalBranchProperties
open ContinuousGibbs ContinuousFirstShell ContinuousSymmetry ReducedCubicExpansion
open DiagonalScalarBranch ReducedEquation

/-- The first seven fields of the trusted Morse--Bott statement, with Sobolev
membership proved for every real index. Hessian conclusions are separate. -/
structure BasicProperties {d : ℕ} (β : ℝ) (u : Torus d → ℝ) : Prop where
  smooth : SmoothOnTorus u
  sobolev : ∀ s : ℝ, InSobolev s u
  criticalSobolev : InCriticalSobolev u
  meanZero : MeanZero u
  stationary : ∀ k : NonzeroFrequency d,
    (frequencyLength k.val ^ d : ℂ) * fourierCoeff u k.val =
      (β / spectralThreshold d : ℝ) * fourierCoeff (normalizedGibbs u) k.val
  fullModes : ∀ j : Fin d, fourierCoeff u (axisFrequency j) ≠ 0
  tangentIndependent : ∀ a : Fin d → ℝ,
    tangentCombination u a =ᵐ[torusMeasure d] (fun _ => 0) → a = 0

@[simp] theorem physical_meanZero {d : ℕ} (hd : 12 ≤ d) (β : ℝ) :
    MeanZero (physicalPotential hd β) := branchPotential_mean hd _

@[simp] theorem physical_coordinates {d : ℕ} (hd : 12 ≤ d) (β : ℝ) :
    coordinates d (physicalPotential hd β) =
      realDiagonal d (amplitude hd (β/spectralThreshold d)) :=
  branchPotential_coordinates hd _

@[simp] theorem physical_axis_coefficient {d : ℕ} (hd : 12 ≤ d) (β : ℝ) (j : Fin d) :
    fourierCoeff (physicalPotential hd β) (axisFrequency j) =
      (amplitude hd (β/spectralThreshold d) : ℂ) := by
  rw [← coefficient_eq_fourierCoeff]
  exact congrFun (physical_coordinates hd β) j

/-- The coordinates at which the physical branch evaluates the genuine graph
converge to its analytic base point. -/
theorem physical_graph_tendsto {d : ℕ} (hd : 12 ≤ d) :
    Tendsto (fun β : ℝ =>
      (parameter hd (amplitude hd (β/spectralThreshold d)),
        realDiagonal d (amplitude hd (β/spectralThreshold d))))
      (𝓝[>] (spectralThreshold d)) (𝓝 (1,(0 : Coordinates d))) :=
  (branch_coordinates_tendsto hd).comp ((amplitude_tendsto hd).comp (normalized_parameter_tendsto hd))

/-- The actual inverse diagonal branch satisfies the exact continuous Euler
operator at its physical normalized parameter. -/
theorem physical_full_zero {d : ℕ} (hd : 12 ≤ d) :
    ∀ᶠ β in 𝓝[>] (spectralThreshold d),
      full d (β/spectralThreshold d) (physicalPotential hd β)=0 := by
  filter_upwards [(normalized_parameter_tendsto hd).eventually self_mem_nhdsWithin,
    (normalized_parameter_tendsto hd).eventually (eventually_parameter_interval hd)] with β hp hi
  exact (amplitude_stationary hd hp hi.2).2.2.2.2

theorem physical_branch_properties {d : ℕ} (hd : 12 ≤ d) :
    ∀ᶠ β in 𝓝[>] (spectralThreshold d), BasicProperties β (physicalPotential hd β) := by
  have ht := physical_graph_tendsto hd
  filter_upwards [(normalized_parameter_tendsto hd).eventually self_mem_nhdsWithin,
    (normalized_parameter_tendsto hd).eventually (eventually_parameter_interval hd),
    ht.eventually (GraphCritical.potential_inCriticalSobolev hd),
    ht.eventually (GraphTranslationTangents.tangentIndependent hd)] with β hp hi hcrit htangent
  have hs := amplitude_stationary hd hp hi.2
  have hfull : ∀ j : Fin d, realDiagonal d (amplitude hd (β/spectralThreshold d)) j ≠ 0 := by
    intro j
    exact Complex.ofReal_ne_zero.mpr (amplitude_pos hd hp hi.2).ne'
  refine ⟨hs.2.2.1,hs.2.2.2.1,hcrit,physical_meanZero hd β,?_,?_,htangent hfull⟩
  · simpa only [physicalPotential,Complex.ofReal_pow] using
      ((full_zero_iff_stationary (by omega) _ _).mp hs.2.2.2.2).2
  · intro j
    rw [physical_axis_coefficient]
    exact Complex.ofReal_ne_zero.mpr (amplitude_pos hd hp hi.2).ne'

#print axioms physical_full_zero
#print axioms physical_branch_properties
end BecknerOnofri.HighDim.PhysicalBranchProperties
