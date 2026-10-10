module

public import BecknerOnofri.V2.Reaudit.Mixtures.DirectRectangle
public import BecknerOnofri.MixtureMarginalEnergyPaper

@[expose] public section

/-! # `prop:spectral-marginal-energy` (Proposition 5.5), printed statements, direct argument (S037)

The deletion step (`eq:spectral-energy-main`) is
`DirectRectangle.countable_mixture_comparison_enn_direct`.  The iteration to `r`-subsets
(`eq:spectral-energy-r`) is the manuscript's: marginals of a mixture are mixtures, each `r`-subset
is counted `d - r` times in the induction step, and
`1/(d-1) * (d-1)/(r C(d-1,r)) * (d-r) = d/(r C(d,r))`.  The bookkeeping lemmas below are the
repository's `coordinateEnergy_deletion`, `countable_mixture_subset_unnormalized` and
`cosine_mixture_{deletion,subset}_energy` with the single appeal to the truncation-based deletion
bound replaced by the direct one; `subset_energy_iteration` and the Haar-marginal bridges are reused
unchanged.  The final two theorems have exactly the types of
`V2.Transfer.spectral_marginal_energy_deletion` and `..._subset`. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators ENNReal
open Finset MeasureTheory

namespace BecknerOnofri.V2.Reaudit.Mixtures
open BecknerOnofri.CosineMixtureTransfer BecknerOnofri.RectangleLattice
  BecknerOnofri.RandomRectangles Legacy.TorusEndpoint Legacy.BecknerOnofri Legacy.D10

lemma coordinateEnergy_deletion_direct {d : ℕ} (I : Finset (Fin d)) (hI : 12 ≤ I.card)
    (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ) (hw : ∀ n, 0 ≤ w n) (hs : Summable w) :
    ((I.card-1:ℕ):ℝ≥0∞) * coordinateEnergy I (I.card:ℝ) (CosineMixtureApproximation.rho w N) ≤
      ∑ i ∈ I, coordinateEnergy (I.erase i) ((I.erase i).card:ℝ)
        (CosineMixtureApproximation.rho w N) := by
  have h := countable_mixture_comparison_enn_direct hI w (fun n j => N n (coordinateEmbedding I j)) hw hs
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
          (fun i => coordinateEnergy (I.erase i) ((I.erase i).card:ℝ)
            (CosineMixtureApproximation.rho w N))
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

theorem countable_mixture_subset_unnormalized_direct {d r : ℕ} (hr : 12 ≤ r) (hrd : r ≤ d)
    (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ) (hw : ∀ n, 0 ≤ w n) (hs : Summable w) :
    (((d-1).choose (r-1):ℕ):ℝ≥0∞) * weightedEnergyENN (weight (d:ℝ))
      (CosineMixtureApproximation.rho w N) ≤
    ∑ I ∈ (univ : Finset (Fin d)).powersetCard r,
      coordinateEnergy I (r:ℝ) (CosineMixtureApproximation.rho w N) := by
  have h := subset_energy_iteration
    (fun I : Finset (Fin d) => coordinateEnergy I (I.card:ℝ) (CosineMixtureApproximation.rho w N))
    r (by omega) (fun I hi => coordinateEnergy_deletion_direct I (by omega) w N hw hs)
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

/-- Exact coefficient from the manuscript's general `r`-subset energy formula. -/
theorem countable_mixture_subset_comparison_direct {d r : ℕ} (hr : 12 ≤ r) (hrd : r ≤ d)
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
  have h := mul_le_mul_right (countable_mixture_subset_unnormalized_direct hr hrd w N hw hs)
    (ENNReal.ofReal ((d:ℝ)/((r:ℝ)*(d.choose r:ℝ))))
  simpa only [← mul_assoc, he, one_mul] using h

/-- **Proposition 5.5**, first display (`eq:spectral-energy-main`), direct argument.  Same type as
`V2.Transfer.spectral_marginal_energy_deletion`. -/
theorem spectral_marginal_energy_deletion_direct {d : ℕ} (hd : 12 ≤ d)
    (ρ : HighDim.ProbabilityDensity d) (hρ : HighDim.IsCountableCosineMixture ρ) :
    HighDim.spectralEnergy ρ ≤ ENNReal.ofReal (1 / ((d : ℝ) - 1)) *
      ∑ i : Fin d, HighDim.inversePowerEnergy (d - 1)
        (HighDim.coordinateMarginal ρ (Finset.univ.erase i)) := by
  obtain ⟨w, N, hw, hm, he⟩ := hρ
  rw [countableCosineMixture_eq] at he
  have h := countable_mixture_comparison_enn_direct hd w N hw hm.summable
  have hd0 : 0 < d := by omega
  have hr0 : 0 < d-1 := by omega
  have hleft : weightedEnergyENN (weight (d:ℝ)) (CosineMixtureApproximation.rho w N) =
      HighDim.spectralEnergy ρ := by
    rw [weightedEnergyENN_eq_inversePowerEnergy hd0]
    exact (inversePowerEnergy_congr_ae hd0 he).symm
  rw [hleft] at h
  have hdel (i : Fin d) : weightedEnergyENN
      (fun k => if k i = 0 then weight ((d:ℝ)-1) k else 0) (CosineMixtureApproximation.rho w N) =
      HighDim.inversePowerEnergy (d-1) (HighDim.coordinateMarginal ρ (univ.erase i)) := by
    have hc := coordinateEnergy_eq_inversePower_marginal hr0 ρ (univ.erase i) w N hw hm he
    simpa [coordinateEnergy, Nat.cast_sub (show 1 ≤ d by omega)] using hc
  simpa only [hdel] using h

/-- **Proposition 5.5**, second display (`eq:spectral-energy-r`), by iteration of the direct
deletion step.  Same type as `V2.Transfer.spectral_marginal_energy_subset`. -/
theorem spectral_marginal_energy_subset_direct {d r : ℕ} (hr : 12 ≤ r) (hrd : r ≤ d)
    (ρ : HighDim.ProbabilityDensity d) (hρ : HighDim.IsCountableCosineMixture ρ) :
    HighDim.spectralEnergy ρ ≤ ENNReal.ofReal ((d : ℝ) / ((r : ℝ) * (d.choose r : ℝ))) *
      ∑ I ∈ (Finset.univ : Finset (Fin d)).powersetCard r,
        HighDim.inversePowerEnergy r (HighDim.coordinateMarginal ρ I) := by
  obtain ⟨w, N, hw, hm, he⟩ := hρ
  rw [countableCosineMixture_eq] at he
  have h := countable_mixture_subset_comparison_direct hr hrd w N hw hm.summable
  have hd0 : 0 < d := by omega
  have hr0 : 0 < r := by omega
  have hleft : weightedEnergyENN (weight (d:ℝ)) (CosineMixtureApproximation.rho w N) =
      HighDim.spectralEnergy ρ := by
    rw [weightedEnergyENN_eq_inversePowerEnergy hd0]
    exact (inversePowerEnergy_congr_ae hd0 he).symm
  rw [hleft] at h
  simpa only [coordinateEnergy_eq_inversePower_marginal hr0 ρ _ w N hw hm he] using h

#print axioms spectral_marginal_energy_deletion_direct
#print axioms spectral_marginal_energy_subset_direct

end BecknerOnofri.V2.Reaudit.Mixtures
