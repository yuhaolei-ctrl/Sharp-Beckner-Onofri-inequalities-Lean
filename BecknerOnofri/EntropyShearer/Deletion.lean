module

public import BecknerOnofri.EntropyShearer.Contraction

@[expose] public section

/-! Haar-marginal deletion Shearer inequality from proved entropy contraction. -/

noncomputable section
open MeasureTheory Function
open scoped BigOperators

namespace BecknerOnofri.HighDim.EntropyShearer

theorem entropy_loss_avg_le {d : ℕ} {f : Torus d → ℝ}
    (hf : PositiveBounded f) (s : Finset (Fin d)) (i : Fin d) (hi : i ∉ s) :
    entropyIntegral (avg s f) - entropyIntegral (avg (insert i s) f) ≤
      entropyIntegral f - entropyIntegral (avg {i} f) := by
  have h := relativeEntropy_avg_le hf (hf.avg {i}) s
  rw [entropy_difference hf {i}] at h
  have he : avg s (avg {i} f) = avg {i} (avg s f) := by
    rw [← avg_union (Finset.disjoint_singleton_right.mpr hi) hf.bounded,
      ← avg_union (Finset.disjoint_singleton_left.mpr hi) hf.bounded,
      Finset.union_comm]
  rw [he, entropy_difference (hf.avg s) {i}] at h
  rwa [← avg_union (Finset.disjoint_singleton_left.mpr hi) hf.bounded,
    ← Finset.insert_eq] at h

theorem entropy_loss_le_sum {d : ℕ} {f : Torus d → ℝ}
    (hf : PositiveBounded f) (s : Finset (Fin d)) :
    entropyIntegral f - entropyIntegral (avg s f) ≤
      ∑ i ∈ s, (entropyIntegral f - entropyIntegral (avg {i} f)) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    have h := entropy_loss_avg_le hf s i hi
    linarith

/-- The same entropy inequality before normalizing the total mass. -/
theorem deletion_of_bounds_general_mass {d : ℕ} {f : Torus d → ℝ}
    (hf : PositiveBounded f) :
    (∑ i : Fin d, entropyIntegral (avg {i} f)) ≤
      ((d : ℝ) - 1) * entropyIntegral f +
        (∫ x, f x ∂torusMeasure d) * Real.log (∫ x, f x ∂torusMeasure d) := by
  have h := entropy_loss_le_sum hf Finset.univ
  have he : entropyIntegral (avg Finset.univ f) =
      (∫ x, f x ∂torusMeasure d) * Real.log (∫ x, f x ∂torusMeasure d) := by
    rw [avg_univ]
    simp [entropyIntegral]
  rw [he, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at h
  linarith

/-- Deleting each coordinate once loses enough relative entropy to cover the
full joint entropy. Every marginal in this statement is the actual Haar integral. -/
theorem deletion_of_bounds {d : ℕ} {f : Torus d → ℝ}
    (hf : PositiveBounded f) (hmass : (∫ x, f x ∂torusMeasure d) = 1) :
    (∑ i : Fin d, entropyIntegral (avg {i} f)) ≤
      ((d : ℝ) - 1) * entropyIntegral f := by
  have h := entropy_loss_le_sum hf Finset.univ
  have he : entropyIntegral (avg Finset.univ f) = 0 := by
    rw [avg_univ, hmass]
    simp [entropyIntegral]
  rw [he, sub_zero, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at h
  linarith

/-- The deletion Shearer inequality for every continuous strictly positive
probability density on the actual normalized Haar torus. -/
theorem deletion_of_continuous_pos {d : ℕ} (ρ : ProbabilityDensity d)
    (hρ : Continuous ρ.value) (hpos : ∀ x, 0 < ρ.value x) :
    (∑ i : Fin d, entropyIntegral (avg {i} ρ.value)) ≤ ((d : ℝ) - 1) * entropy ρ :=
  deletion_of_bounds (positiveBounded_of_continuous_pos hρ hpos) ρ.mass

#print axioms deletion_of_continuous_pos

end BecknerOnofri.HighDim.EntropyShearer
