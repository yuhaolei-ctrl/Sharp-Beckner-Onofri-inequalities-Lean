module

public import BecknerOnofri.EntropyShearer.FiniteEntropy
public import BecknerOnofri.CoordinateMarginalDefinitions

@[expose] public section

/-! The precise normalization and full finite-entropy domain of the manuscript's
Lemma `spectral-subset-entropy`. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped BigOperators
namespace BecknerOnofri.HighDim.EntropyShearer

lemma coordinateMarginal_eq {d : ℕ} (ρ : ProbabilityDensity d) (I : Finset (Fin d)) :
    coordinateMarginal ρ I = (fullMarginalDensity Iᶜ ρ).value := by
  funext x
  change (∫ y, ρ.value (fun i => if i ∈ I then x i else y i) ∂torusMeasure d) =
    ∫ y, ρ.value (EntropyShearer.mix Iᶜ (x,y)) ∂torusMeasure d
  apply integral_congr_ae
  exact ae_of_all _ (fun y => by
    change ρ.value (fun i => if i ∈ I then x i else y i) =
      ρ.value (fun i => if i ∈ Iᶜ then y i else x i)
    simp only [Finset.mem_compl, ite_not])

lemma coordinateMarginalEntropy_eq {d : ℕ} (ρ : ProbabilityDensity d) (I : Finset (Fin d)) :
    coordinateMarginalEntropy ρ I = entropy (fullMarginalDensity Iᶜ ρ) := by
  simp only [coordinateMarginalEntropy, coordinateMarginal_eq, entropy]

theorem coordinateMarginal_finiteEntropy {d : ℕ} (ρ : ProbabilityDensity d)
    (hρ : ρ.FiniteEntropy) (I : Finset (Fin d)) :
    Integrable (fun x => coordinateMarginal ρ I x * Real.log (coordinateMarginal ρ I x))
      (torusMeasure d) ∧ coordinateMarginalEntropy ρ I ≤ entropy ρ := by
  rw [coordinateMarginal_eq, coordinateMarginalEntropy_eq]
  exact marginal_finiteEntropy ρ hρ Iᶜ

theorem subset_entropy {d r : ℕ} (hr : 1 ≤ r) (hrd : r ≤ d)
    (ρ : ProbabilityDensity d) (hρ : ρ.FiniteEntropy) :
    (d:ℝ) / ((r:ℝ)*(d.choose r:ℝ)) *
      (∑ I ∈ (Finset.univ : Finset (Fin d)).powersetCard r, coordinateMarginalEntropy ρ I)
      ≤ entropy ρ := by
  have hd : 1 ≤ d := hr.trans hrd
  have hr0 : (0:ℝ)<(r:ℝ) := by exact_mod_cast (show 0 < r by omega)
  have hc0 : (0:ℝ)<(d.choose r:ℝ) := by exact_mod_cast Nat.choose_pos hrd
  have hcomb : (d:ℝ)*((d-1).choose (r-1):ℝ) = (d.choose r:ℝ)*(r:ℝ) := by
    exact_mod_cast (show d*((d-1).choose (r-1)) = d.choose r*r from by
      simpa only [Nat.sub_add_cancel hd, Nat.sub_add_cancel hr] using
        Nat.add_one_mul_choose_eq (d-1) (r-1))
  have hcancel : (d:ℝ)/((r:ℝ)*(d.choose r:ℝ))*((d-1).choose (r-1):ℝ) = 1 := by
    field_simp [ne_of_gt hr0, ne_of_gt hc0]
    nlinarith [hcomb]
  simp_rw [coordinateMarginalEntropy_eq]
  calc
    _ ≤ (d:ℝ)/((r:ℝ)*(d.choose r:ℝ))*(((d-1).choose (r-1):ℝ)*entropy ρ) :=
      mul_le_mul_of_nonneg_left (all_subsets_finiteEntropy (by omega) ρ hρ) (by positivity)
    _ = _ := by rw [← mul_assoc, hcancel, one_mul]

#print axioms coordinateMarginal_finiteEntropy
#print axioms subset_entropy
end BecknerOnofri.HighDim.EntropyShearer
