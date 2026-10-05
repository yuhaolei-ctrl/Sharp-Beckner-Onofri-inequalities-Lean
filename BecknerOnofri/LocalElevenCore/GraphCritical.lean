import BecknerOnofri.LocalElevenContinuousInverse
import BecknerOnofri.GraphCritical
import BecknerOnofri.LocalElevenCore.GreenCritical
import BecknerOnofri.QuadraticModes

/-! The actual local complementary graph belongs to the trusted critical
Sobolev domain, as follows from its genuine projected Euler equation. -/
noncomputable section

open MeasureTheory Filter
open scoped Topology
namespace BecknerOnofri.HighDim.LocalEleven.GraphCritical

open BecknerOnofri.HighDim.GraphCritical hiding critical_of_same_complement critical_smul firstShell_finite potential_inCriticalSobolev reconstruction_critical_of_projected
open BecknerOnofri.HighDim.GreenLocalBranch hiding correction correction_analytic correction_axis correction_base correction_derivative_zero correction_quadratic correction_solves correction_unique exists_analytic_complement green_assembly green_first_complement_zero linearPart_eq zero_axis_of_unique
open BecknerOnofri.HighDim.ReducedEquation hiding complementMap_assembly complementMap_reconstruction coordinates_complement coordinates_green coordinates_one coordinates_reconstruction full full_complement full_coordinates full_mean full_zero_iff graph_full_iff_reduced local_full_iff_reduced meanZero_zero_iff mean_green potential potential_analytic reduced reduced_analytic
open ContinuousGibbs ContinuousFirstShell ContinuousComplement GreenLocalBranch ReducedEquation
open BecknerOnofri.HighDim.GreenCritical hiding coefficient_square_summable green_inCriticalSobolev nonzero_eigenvalue_ge_one potentialTerm_green
open BecknerOnofri.HighDim.QuadraticModes
open GreenCritical QuadraticModes

theorem firstShell_finite (d : ℕ) : Set.Finite {k : Frequency d | InFirstShell k} := by
  have hs : {k : Frequency d | InFirstShell k} =
      Set.range (@axisFrequency d) ∪ Set.range (fun i : Fin d => -axisFrequency i) := by
    ext k
    simp only [Set.mem_setOf_eq, InFirstShell, Set.mem_union, Set.mem_range]
    aesop
  rw [hs]
  exact (Set.finite_range _).union (Set.finite_range _)

/-- Changing finitely many first-shell coefficients preserves the actual
critical Sobolev membership, without invoking a totalized divergent sum. -/
theorem critical_of_same_complement {d : ℕ} (f g : Space d) (hg : InCriticalSobolev g)
    (he : ∀ k : Frequency d, ComplementFrequency k → coefficient k g = coefficient k f) :
    InCriticalSobolev f := by
  refine ⟨f.continuous.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _), ?_⟩
  apply hg.2.congr_cofinite
  have hs : Set.Finite {k : NonzeroFrequency d | InFirstShell k.val} :=
    (firstShell_finite d).preimage (f := fun k : NonzeroFrequency d => k.val)
      (fun _ _ _ _ h => Subtype.val_injective h)
  filter_upwards [hs.compl_mem_cofinite] with k hk
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq] at hk
  simp only [potentialTerm, ← coefficient_eq_fourierCoeff, he k.val ⟨k.property,hk⟩]

theorem critical_smul {d : ℕ} (c : ℝ) (f : Space d) (hf : InCriticalSobolev f) :
    InCriticalSobolev (c • f) := by
  refine ⟨(c • f).continuous.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _), ?_⟩
  apply (hf.2.mul_left (c^2)).congr
  intro k
  simp only [potentialTerm, ← coefficient_eq_fourierCoeff, map_smul, norm_smul,
    mul_pow, Real.norm_eq_abs, sq_abs]
  ring

theorem reconstruction_critical_of_projected {d : ℕ} (hd : 0 < d)
    (μ : ℝ) (z : Coordinates d) (w : complement d)
    (he : projectedEquation (greenContinuous d) ((μ,z),w) = 0) :
    InCriticalSobolev (reconstruction d (z,w)) := by
  let f := normalized (reconstruction d (z,w)) - 1
  have hw : w = μ • complementMap d (greenContinuous d f) := sub_eq_zero.mp he
  apply critical_of_same_complement _ (μ • greenContinuous d f)
    (critical_smul μ _ (green_inCriticalSobolev hd f))
  intro k hk
  have hz : coefficient k (assembly d z) = 0 := by
    rw [← projection_assembly z]
    exact coefficient_projection_off_shell _ k hk.2
  have hwc : coefficient k (w : Space d) = μ • coefficient k (greenContinuous d f) := by
    have h := congrArg (fun v : complement d => coefficient k (v : Space d)) hw
    simpa only [Submodule.coe_smul, map_smul, complementMap_coefficient, if_pos hk] using h
  simp only [map_smul, reconstruction_apply, map_add, hz, zero_add, hwc]

/-- All nearby points of the constructed graph are actual critical-Sobolev
potentials, including points not satisfying the finite-dimensional equation. -/
theorem potential_inCriticalSobolev {d : ℕ} (hd : 11 ≤ d) :
    ∀ᶠ x in 𝓝 (1, (0 : Coordinates d)), InCriticalSobolev (potential hd x) := by
  filter_upwards [correction_solves hd] with x hx
  exact reconstruction_critical_of_projected (by omega) x.1 x.2 (correction hd x) hx

#print axioms potential_inCriticalSobolev
end BecknerOnofri.HighDim.LocalEleven.GraphCritical
