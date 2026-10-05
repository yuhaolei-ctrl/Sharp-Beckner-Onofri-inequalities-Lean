import BecknerOnofri.EntropyShearer.Chain

/-! Shearer's inequality for all coordinate subsets of a fixed size, initially
for positive bounded densities. The marginal is the actual Haar integral. -/
noncomputable section
open MeasureTheory Function
open scoped BigOperators
namespace BecknerOnofri.HighDim.EntropyShearer

lemma chain_increments_sum {d : ℕ} {f : Torus d → ℝ}
    (hmass : (∫ x, f x ∂torusMeasure d) = 1) :
    (∑ i : Fin d, (entropyIntegral (avg (coordinatePrefix d i.val) f) -
      entropyIntegral (avg (coordinatePrefix d (i.val+1)) f))) = entropyIntegral f := by
  have h := chain_sum hmass ∅
  rw [← Fin.sum_univ_eq_sum_range] at h
  simpa using h

lemma sum_subset_weights (d r : ℕ) (hr : 0 < r) (c : Fin d → ℝ) :
    (∑ s ∈ (Finset.univ : Finset (Fin d)).powersetCard r,
      ∑ i : Fin d, if i ∈ s then c i else 0) =
    ((d-1).choose (r-1):ℝ) * ∑ i : Fin d, c i := by
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_filter]
  have hc : ((Finset.univ.powersetCard r).filter (fun s : Finset (Fin d) => i ∈ s)).card =
      (d-1).choose (r-1) := by
    simpa only [Finset.singleton_subset_iff, Finset.card_univ, Fintype.card_fin,
      Finset.card_singleton] using
      Finset.card_filter_powersetCard_subset {i} Finset.univ r
        (Finset.subset_univ _) (by simpa only [Finset.card_singleton] using (Nat.succ_le_iff.mpr hr))
  simp only [Finset.sum_const, nsmul_eq_mul, hc]

/-- The unnormalized all-subsets form, before dividing by the number of subsets. -/
theorem all_subsets_of_bounds {d r : ℕ} (hr : 0 < r)
    {f : Torus d → ℝ} (hf : PositiveBounded f)
    (hmass : (∫ x, f x ∂torusMeasure d) = 1) :
    (∑ s ∈ (Finset.univ : Finset (Fin d)).powersetCard r,
      entropyIntegral (avg sᶜ f)) ≤ ((d-1).choose (r-1):ℝ) * entropyIntegral f := by
  calc
    _ ≤ ∑ s ∈ (Finset.univ : Finset (Fin d)).powersetCard r,
        ∑ i : Fin d, if i ∈ s then
          entropyIntegral (avg (coordinatePrefix d i.val) f) -
            entropyIntegral (avg (coordinatePrefix d (i.val+1)) f) else 0 := by
      apply Finset.sum_le_sum
      intro s _
      simpa only [Finset.mem_compl, ite_not] using marginal_chain_bound hf hmass sᶜ
    _ = _ := by rw [sum_subset_weights d r hr, chain_increments_sum hmass]

#print axioms all_subsets_of_bounds
end BecknerOnofri.HighDim.EntropyShearer
