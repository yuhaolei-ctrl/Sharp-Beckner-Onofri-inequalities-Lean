import BecknerOnofri.CorrectionSymmetry
import BecknerOnofri.ReducedEquation

/-! Exact translation covariance of the actual, non-polynomial reduced equation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Topology
namespace BecknerOnofri.HighDim.ContinuousSymmetry
open ContinuousGibbs ContinuousFirstShell ContinuousComplement GreenLocalBranch ReducedEquation

theorem full_translation {d : ℕ} (hd : 0 < d) (a : Torus d) (μ : ℝ) (u : Space d) :
    full d μ (translation a u) = translation a (full d μ u) := by
  unfold full
  rw [normalized_translation]
  have he : translation a (normalized u) - 1 = translation a (normalized u - 1) := by
    rw [map_sub, translation_one]
  rw [he, green_translation hd]
  simp only [map_sub, map_smul]

theorem potential_translation {d : ℕ} (hd : 12 ≤ d) :
    ∀ᶠ x in 𝓝 (1, (0 : Coordinates d)), ∀ a : Torus d,
      potential hd (x.1, phaseCoordinates a x.2) = translation a (potential hd x) :=
  reconstructed_correction_translation hd

/-- All complex first-shell components transform with their exact character
phase, on one common neighbourhood for all translations. -/
theorem reduced_translation {d : ℕ} (hd : 12 ≤ d) :
    ∀ᶠ x in 𝓝 (1, (0 : Coordinates d)), ∀ a : Torus d,
      reduced hd (x.1, phaseCoordinates a x.2) = phaseCoordinates a (reduced hd x) := by
  filter_upwards [potential_translation hd] with x hx
  intro a
  simp only [reduced, hx a, normalized_translation, coordinates_translation]
  change coordinateTranslation a x.2 - x.1 •
      coordinateTranslation a (coordinates d (normalized (potential hd x))) =
    coordinateTranslation a (x.2 - x.1 • coordinates d (normalized (potential hd x)))
  simp only [map_sub, map_smul]

/-- Translation preserves the exact local zero set of the reduced equation. -/
theorem reduced_zero_translation_iff {d : ℕ} (hd : 12 ≤ d) :
    ∀ᶠ x in 𝓝 (1, (0 : Coordinates d)), ∀ a : Torus d,
      reduced hd (x.1, phaseCoordinates a x.2) = 0 ↔ reduced hd x = 0 := by
  filter_upwards [reduced_translation hd] with x hx
  intro a
  rw [hx a]
  exact (coordinateTranslation a).map_eq_zero_iff

#print axioms full_translation
#print axioms reduced_translation
#print axioms reduced_zero_translation_iff
end BecknerOnofri.HighDim.ContinuousSymmetry
