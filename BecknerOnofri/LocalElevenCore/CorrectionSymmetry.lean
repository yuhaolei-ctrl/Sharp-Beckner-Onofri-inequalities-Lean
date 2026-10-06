module

public import BecknerOnofri.LocalElevenContinuousInverse
public import BecknerOnofri.CorrectionSymmetry
public import BecknerOnofri.ContinuousSymmetry
public import BecknerOnofri.LocalElevenCore.GreenLocalBranch

@[expose] public section

/-! Translation equivariance of the actual local analytic correction, with a
single parameter neighbourhood valid for every torus translation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Topology
namespace BecknerOnofri.HighDim.LocalEleven.ContinuousSymmetry

open BecknerOnofri.HighDim.ContinuousSymmetry hiding correction_translation green_translation reconstructed_correction_translation
open BecknerOnofri.HighDim.GreenLocalBranch hiding correction correction_analytic correction_axis correction_base correction_derivative_zero correction_quadratic correction_solves correction_unique exists_analytic_complement green_assembly green_first_complement_zero linearPart_eq zero_axis_of_unique
open ContinuousGibbs ContinuousFirstShell ContinuousComplement GreenLocalBranch

/-- The actual torus Green operator commutes with translations. -/
theorem green_translation {d : ℕ} (hd : 0 < d) (a : Torus d) (u : Space d) :
    greenContinuous d (translation a u) = translation a (greenContinuous d u) := by
  apply coefficient_ext
  intro k
  rw [coefficient_green hd, coefficient_translation, coefficient_translation, coefficient_green hd]
  ring

theorem translated_graph_dist {d : ℕ} (a : Torus d)
    (x : ℝ × Coordinates d) (w : complement d) :
    dist ((x.1, phaseCoordinates a x.2), complementTranslation a w)
        ((1, (0 : Coordinates d)), (0 : complement d)) =
      dist (x,w) ((1, (0 : Coordinates d)), (0 : complement d)) := by
  simp only [Prod.dist_eq, dist_zero_right, phaseCoordinates_norm,
    (complementTranslation a).norm_map]

/-- Local uniqueness and norm-preserving translations give a common
neighbourhood on which every actual character rotation commutes with ψ. -/
theorem correction_translation {d : ℕ} (hd : 11 ≤ d) :
    ∀ᶠ x in 𝓝 (1, (0 : Coordinates d)), ∀ a : Torus d,
      correction hd (x.1, phaseCoordinates a x.2) =
        complementTranslation a (correction hd x) := by
  obtain ⟨ε, hε, hUnique⟩ := Metric.eventually_nhds_iff.mp (correction_unique hd)
  have ht : Filter.Tendsto (fun x : ℝ × Coordinates d => (x, correction hd x))
      (𝓝 (1, (0 : Coordinates d)))
      (𝓝 ((1, (0 : Coordinates d)), (0 : complement d))) := by
    simpa only [correction_base, id_eq] using
      (continuousAt_id.prodMk (correction_analytic hd).continuousAt).tendsto
  have hNear : ∀ᶠ x in 𝓝 (1, (0 : Coordinates d)),
      dist (x, correction hd x) ((1, (0 : Coordinates d)), (0 : complement d)) < ε :=
    ht.eventually (Metric.ball_mem_nhds _ hε)
  filter_upwards [correction_solves hd, hNear] with x hx hdist
  intro a
  have hdist' : dist ((x.1, phaseCoordinates a x.2), complementTranslation a (correction hd x))
      ((1, (0 : Coordinates d)), (0 : complement d)) < ε := by
    rw [translated_graph_dist]
    exact hdist
  apply (hUnique hdist').mp
  rw [projectedEquation_translation a (greenContinuous d) (green_translation (by omega) a)]
  change complementTranslation a (projectedEquation (greenContinuous d) (x, correction hd x)) = 0
  rw [hx, map_zero]

/-- The actual reconstructed local potentials have the same uniform covariance. -/
theorem reconstructed_correction_translation {d : ℕ} (hd : 11 ≤ d) :
    ∀ᶠ x in 𝓝 (1, (0 : Coordinates d)), ∀ a : Torus d,
      reconstruction d (phaseCoordinates a x.2,
          correction hd (x.1, phaseCoordinates a x.2)) =
        translation a (reconstruction d (x.2, correction hd x)) := by
  filter_upwards [correction_translation hd] with x hx
  intro a
  rw [hx a, reconstruction_translation]

#print axioms green_translation
#print axioms correction_translation
#print axioms reconstructed_correction_translation
end BecknerOnofri.HighDim.LocalEleven.ContinuousSymmetry
