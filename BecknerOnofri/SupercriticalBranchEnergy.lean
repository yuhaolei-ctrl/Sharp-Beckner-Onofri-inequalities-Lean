import BecknerOnofri.DiagonalEnergyExpansion
import BecknerOnofri.DiagonalAmplitude
import BecknerOnofri.PressureDuality

/-! Actual supercritical branch pressure, with the manuscript's cubic onset
error and its unconditional lower bound for the full variational pressure. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter Asymptotics
open scoped Topology
namespace BecknerOnofri.HighDim.DiagonalScalarBranch
open ContinuousGibbs ContinuousFirstShell ContinuousComplement GreenLocalBranch ReducedEquation
open ReducedCubicExpansion GraphEnergy

def supercriticalEnergy {d : ℕ} (hd : 12 ≤ d) (μ : ℝ) : ℝ := branchEnergy hd (amplitude hd μ)

theorem supercriticalEnergy_expansion {d : ℕ} (hd : 12 ≤ d) :
    (fun μ => supercriticalEnergy hd μ-(d:ℝ)/(2*kappa d)*(onset μ)^2)
      =O[𝓝[>] (1:ℝ)] (fun μ => (onset μ)^3) := by
  have ht : (fun μ : ℝ => ‖amplitude hd μ‖^6)
      =O[𝓝[>] (1:ℝ)] (fun μ => (onset μ)^3) := by
    simpa only [norm_pow, ← pow_mul, show 2*3=6 from rfl] using
      ((amplitude_square_bound hd).pow 3).norm_left
  have hh := ((branchEnergy_delta_expansion hd).comp_tendsto (amplitude_tendsto hd)).trans ht
  apply hh.congr'
  · filter_upwards [amplitude_eventually_inverse hd] with μ hμ
    simp only [Function.comp_apply, branchDelta, hμ, supercriticalEnergy, onset]
  · rfl

theorem supercriticalEnergy_coe {d : ℕ} (hd : 12 ≤ d) :
    ∀ᶠ μ in 𝓝[>] (1:ℝ),
      dualFunctional (μ*spectralThreshold d) (branchPotential hd (amplitude hd μ)) =
        (supercriticalEnergy hd μ : EReal) := by
  have ht := (branch_coordinates_tendsto hd).comp (amplitude_tendsto hd)
  filter_upwards [ht.eventually (correction_solves hd), amplitude_eventually_inverse hd,
    self_mem_nhdsWithin] with μ he hi hμ
  have hμpos : 0 < μ := by change 1 < μ at hμ; linarith
  change projectedEquation (greenContinuous d)
    ((parameter hd (amplitude hd μ),realDiagonal d (amplitude hd μ)),
      correction hd (parameter hd (amplitude hd μ),realDiagonal d (amplitude hd μ))) = 0 at he
  rw [hi] at he
  have hh := graph_dualFunctional (by omega : 0 < d) hμpos
    (realDiagonal d (amplitude hd μ)) (correction hd (μ,realDiagonal d (amplitude hd μ))) he
  unfold supercriticalEnergy branchEnergy branchPotential potential
  rw [hi, hh, EReal.toReal_coe]

theorem supercriticalEnergy_le_pressure {d : ℕ} (hd : 12 ≤ d) :
    ∀ᶠ μ in 𝓝[>] (1:ℝ),
      (supercriticalEnergy hd μ : EReal) ≤ pressure d (μ*spectralThreshold d) := by
  have ht := (branch_coordinates_tendsto hd).comp (amplitude_tendsto hd)
  filter_upwards [supercriticalEnergy_coe hd,
    ht.eventually (GraphCritical.potential_inCriticalSobolev hd), self_mem_nhdsWithin] with μ he hu hμ
  have hβ : 0 < μ*spectralThreshold d :=
    mul_pos (by change 1 < μ at hμ; linarith) (spectralThreshold_pos (by omega))
  rw [← he, RawAttainment.dualFunctional_eq_raw]
  apply le_trans _ (coefficientDefect_le_pressure (by omega) hβ)
  exact le_iSup_of_le (branchPotential hd (amplitude hd μ)) (le_iSup_of_le hu le_rfl)

/-- An unconditional lower onset bound for the exact full pressure.
The matching global upper bound is a separate theorem, not assumed here. -/
theorem pressure_onset_lower_bound {d : ℕ} (hd : 12 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ μ in 𝓝[>] (1:ℝ),
      (((d:ℝ)/(2*kappa d)*(onset μ)^2-C*(onset μ)^3 : ℝ) : EReal) ≤
        pressure d (μ*spectralThreshold d) := by
  obtain ⟨C,hC,hbound⟩ := (supercriticalEnergy_expansion hd).exists_pos
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound.bound, supercriticalEnergy_le_pressure hd, self_mem_nhdsWithin] with μ hb hp hμ
  have ho : 0 < onset μ := onset_pos hμ
  have hab : |supercriticalEnergy hd μ-(d:ℝ)/(2*kappa d)*(onset μ)^2| ≤ C*(onset μ)^3 := by
    simpa only [Real.norm_eq_abs, abs_of_pos (pow_pos ho 3)] using hb
  have hl : (d:ℝ)/(2*kappa d)*(onset μ)^2-C*(onset μ)^3 ≤ supercriticalEnergy hd μ := by
    linarith [(neg_abs_le (supercriticalEnergy hd μ-(d:ℝ)/(2*kappa d)*(onset μ)^2))]
  exact (EReal.coe_le_coe_iff.mpr hl).trans hp

#print axioms supercriticalEnergy_expansion
#print axioms pressure_onset_lower_bound
end BecknerOnofri.HighDim.DiagonalScalarBranch
