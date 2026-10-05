import Legacy.BecknerOnofri.PolarizationPairing

/-! Order preservation and L1 nonexpansiveness of the actual coordinate
polarization. These are the local sorting steps used in circle rearrangement. -/
noncomputable section
open MeasureTheory Set Legacy.TorusEndpoint
namespace BecknerOnofri.PolarizationL1
open Legacy.BecknerOnofri.CoordinatePolarization
attribute [local instance] Classical.propDecidable

lemma sorted_distance_le (a b c d : ℝ) :
    |max a b-max c d|+|min a b-min c d|≤|a-c|+|b-d| := by
  rcases le_total a b with hab | hab <;> rcases le_total c d with hcd | hcd <;>
    simp only [max_eq_left, max_eq_right, min_eq_left, min_eq_right, hab, hcd]
  all_goals
    rcases le_total a c with hac | hac <;> rcases le_total b d with hbd | hbd <;>
      rcases le_total a d with had | had <;> rcases le_total b c with hbc | hbc <;>
      simp_all only [max_eq_left, max_eq_right, min_eq_left, min_eq_right,
        abs_of_nonneg, abs_of_nonpos, sub_nonneg, sub_nonpos]
    all_goals linarith

end BecknerOnofri.PolarizationL1
