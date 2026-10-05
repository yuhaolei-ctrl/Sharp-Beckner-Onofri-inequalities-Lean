import BecknerOnofri.MixtureSubsetComparison

noncomputable section
open scoped BigOperators ENNReal
open Finset MeasureTheory
namespace BecknerOnofri.CosineMixtureTransfer
open RectangleLattice Legacy.TorusEndpoint Legacy.BecknerOnofri

/-- Exact coefficient from the manuscript's general r-subset energy formula. -/
theorem countable_mixture_subset_comparison {d r : ℕ} (hr : 12 ≤ r) (hrd : r ≤ d)
    (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ) (hw : ∀ n, 0 ≤ w n) (hs : Summable w) :
    weightedEnergyENN (weight (d:ℝ)) (CosineMixtureApproximation.rho w N) ≤
      ENNReal.ofReal ((d:ℝ)/((r:ℝ)*(d.choose r:ℝ))) *
        ∑ I ∈ (univ : Finset (Fin d)).powersetCard r,
          coordinateEnergy I (r:ℝ) (CosineMixtureApproximation.rho w N) := by
  have hd : 1 ≤ d := by omega
  have hr1 : 1 ≤ r := by omega
  have hr0 : (0:ℝ)<(r:ℝ) := by exact_mod_cast (show 0 < r by omega)
  have hc0 : (0:ℝ)<(d.choose r:ℝ) := by exact_mod_cast Nat.choose_pos hrd
  have hcomb : (d:ℝ)*((d-1).choose (r-1):ℝ) = (d.choose r:ℝ)*(r:ℝ) := by
    exact_mod_cast (show d*((d-1).choose (r-1)) = d.choose r*r from by
      simpa only [Nat.sub_add_cancel hd, Nat.sub_add_cancel hr1] using
        Nat.add_one_mul_choose_eq (d-1) (r-1))
  have hcancel : (d:ℝ)/((r:ℝ)*(d.choose r:ℝ))*((d-1).choose (r-1):ℝ) = 1 := by
    field_simp [ne_of_gt hr0, ne_of_gt hc0]
    nlinarith [hcomb]
  have he : ENNReal.ofReal ((d:ℝ)/((r:ℝ)*(d.choose r:ℝ))) *
      (((d-1).choose (r-1):ℕ):ℝ≥0∞) = 1 := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity), hcancel, ENNReal.ofReal_one]
  have h := mul_le_mul_right (countable_mixture_subset_unnormalized hr hrd w N hw hs)
    (ENNReal.ofReal ((d:ℝ)/((r:ℝ)*(d.choose r:ℝ))))
  simpa only [← mul_assoc, he, one_mul] using h

#print axioms countable_mixture_subset_comparison
end BecknerOnofri.CosineMixtureTransfer
