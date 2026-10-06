module

public import BecknerOnofri.MixtureSubsetEnergy

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators ENNReal
open Finset MeasureTheory
namespace BecknerOnofri.CosineMixtureTransfer
open RectangleLattice RandomRectangles Legacy.TorusEndpoint
open Legacy.BecknerOnofri Legacy.D10

lemma coordinateEnergy_deletion {d : ℕ} (I : Finset (Fin d)) (hI : 12 ≤ I.card)
    (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ) (hw : ∀ n, 0 ≤ w n) (hs : Summable w) :
    ((I.card-1:ℕ):ℝ≥0∞) * coordinateEnergy I (I.card:ℝ) (CosineMixtureApproximation.rho w N) ≤
      ∑ i ∈ I, coordinateEnergy (I.erase i) ((I.erase i).card:ℝ) (CosineMixtureApproximation.rho w N) := by
  have h := countable_mixture_comparison_enn hI w (fun n j => N n (coordinateEmbedding I j)) hw hs
  rw [← coordinateEnergy_embedding I (I.card:ℝ) w N hw hs] at h
  have hsum : (∑ j : Fin I.card,
      weightedEnergyENN (fun k => if k j = 0 then weight ((I.card:ℝ)-1) k else 0)
        (CosineMixtureApproximation.rho w (fun n l => N n (coordinateEmbedding I l)))) =
      ∑ i ∈ I, coordinateEnergy (I.erase i) ((I.erase i).card:ℝ)
        (CosineMixtureApproximation.rho w N) := by
    simp_rw [← coordinateEnergy_erase_embedding I _ w N hw hs]
    have hmap : (univ : Finset (Fin I.card)).map (coordinateEmbedding I) = I :=
      I.map_orderEmbOfFin_univ rfl
    calc
      _ = ∑ j : Fin I.card, coordinateEnergy (I.erase (coordinateEmbedding I j))
          ((I.erase (coordinateEmbedding I j)).card:ℝ) (CosineMixtureApproximation.rho w N) := by
        apply sum_congr rfl
        intro j hj
        congr 2
        rw [card_erase_of_mem (coordinateEmbedding_mem I j), Nat.cast_sub (by omega), Nat.cast_one]
      _ = _ := by
        have hh := sum_map (univ : Finset (Fin I.card)) (coordinateEmbedding I)
          (fun i => coordinateEnergy (I.erase i) ((I.erase i).card:ℝ) (CosineMixtureApproximation.rho w N))
        rw [hmap] at hh
        exact hh.symm
  rw [hsum] at h
  have hpos : 0 < (I.card:ℝ)-1 := by
    have : (12:ℝ) ≤ I.card := by exact_mod_cast hI
    linarith
  have hc : ((I.card-1:ℕ):ℝ≥0∞) * ENNReal.ofReal (1/((I.card:ℝ)-1)) = 1 := by
    have he : ((I.card-1:ℕ):ℝ≥0∞) = ENNReal.ofReal ((I.card:ℝ)-1) := by
      have he' : ((I.card-1:ℕ):ℝ) = (I.card:ℝ)-1 := by
        rw [Nat.cast_sub (show 1 ≤ I.card by omega), Nat.cast_one]
      rw [← he', ENNReal.ofReal_natCast]
    rw [he, ← ENNReal.ofReal_mul hpos.le, mul_one_div_cancel hpos.ne', ENNReal.ofReal_one]
  calc
    _ ≤ ((I.card-1:ℕ):ℝ≥0∞) * (ENNReal.ofReal (1/((I.card:ℝ)-1)) *
        ∑ i ∈ I, coordinateEnergy (I.erase i) ((I.erase i).card:ℝ)
          (CosineMixtureApproximation.rho w N)) := mul_le_mul_right h _
    _ = _ := by rw [← mul_assoc, hc, one_mul]

theorem countable_mixture_subset_unnormalized {d r : ℕ} (hr : 12 ≤ r) (hrd : r ≤ d)
    (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ) (hw : ∀ n, 0 ≤ w n) (hs : Summable w) :
    (((d-1).choose (r-1):ℕ):ℝ≥0∞) * weightedEnergyENN (weight (d:ℝ))
      (CosineMixtureApproximation.rho w N) ≤
    ∑ I ∈ (univ : Finset (Fin d)).powersetCard r,
      coordinateEnergy I (r:ℝ) (CosineMixtureApproximation.rho w N) := by
  have h := subset_energy_iteration
    (fun I : Finset (Fin d) => coordinateEnergy I (I.card:ℝ) (CosineMixtureApproximation.rho w N))
    r (by omega) (fun I hi => coordinateEnergy_deletion I (by omega) w N hw hs)
    univ (by simpa using hrd)
  simp only [card_univ, Fintype.card_fin] at h
  have hu : coordinateEnergy (univ : Finset (Fin d)) (d:ℝ) (CosineMixtureApproximation.rho w N) =
      weightedEnergyENN (weight (d:ℝ)) (CosineMixtureApproximation.rho w N) := by
    simp [coordinateEnergy]
  rw [hu] at h
  convert h using 1
  apply sum_congr rfl
  intro I hI
  rw [(mem_powersetCard.mp hI).2]

#print axioms coordinateEnergy_deletion
#print axioms countable_mixture_subset_unnormalized
end BecknerOnofri.CosineMixtureTransfer
