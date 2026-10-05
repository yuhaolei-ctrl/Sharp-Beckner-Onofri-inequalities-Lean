module

public import BecknerOnofri.EntropyShearer.Deletion
public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

@[expose] public section

/-! Coordinate-chain entropy bounds for actual Haar marginals. -/
noncomputable section
open MeasureTheory Function
open scoped BigOperators
namespace BecknerOnofri.HighDim.EntropyShearer

lemma avg_absorb {d : ℕ} {s t : Finset (Fin d)} (hst : s ⊆ t)
    (f : Torus d → ℝ) : avg s (avg t f) = avg t f := by
  funext x
  have h (y : s → UnitAddCircle) : avg t f (updateFinset x s y) = avg t f x := by
    simp only [avg, updateFinset_updateFinset_of_subset hst]
  change (∫ y : s → UnitAddCircle, avg t f (updateFinset x s y)
    ∂Measure.pi (fun _ : s => AddCircle.haarAddCircle)) = avg t f x
  simp only [h, integral_const, probReal_univ, smul_eq_mul, one_mul]

lemma avg_union_general {d : ℕ} (s t : Finset (Fin d)) {f : Torus d → ℝ}
    (hf : BoundedMeasurable f) : avg (s ∪ t) f = avg s (avg t f) := by
  have hs : s = (s \ t) ∪ (s ∩ t) := by ext i; simp <;> tauto
  have hd : Disjoint (s \ t) (s ∩ t) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_inter.mp hj).2
  calc
    _ = avg ((s \ t) ∪ t) f := by congr 1; ext i; simp <;> tauto
    _ = avg (s \ t) (avg t f) := avg_union Finset.sdiff_disjoint hf
    _ = avg (s \ t) (avg (s ∩ t) (avg t f)) := by
      rw [avg_absorb Finset.inter_subset_right]
    _ = avg ((s \ t) ∪ (s ∩ t)) (avg t f) := (avg_union hd (hf.avg t)).symm
    _ = _ := by rw [← hs]

/-- The coordinates deleted before stage `n` of the canonical order. -/
def coordinatePrefix (d n : ℕ) : Finset (Fin d) := Finset.univ.filter (fun i => i.val < n)

@[simp] lemma coordinatePrefix_zero (d : ℕ) : coordinatePrefix d 0 = ∅ := by ext i; simp [coordinatePrefix]
@[simp] lemma coordinatePrefix_end (d : ℕ) : coordinatePrefix d d = Finset.univ := by
  ext i; simp [coordinatePrefix, i.isLt]
lemma coordinatePrefix_succ {d n : ℕ} (hn : n < d) :
    coordinatePrefix d (n+1) = insert ⟨n,hn⟩ (coordinatePrefix d n) := by
  ext i
  simp only [coordinatePrefix, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
  constructor
  · intro h
    by_cases hi : i.val = n
    · exact Or.inl (Fin.ext hi)
    · exact Or.inr (by omega)
  · rintro (rfl | h) <;> simp_all <;> omega

/-- Each retained coordinate contributes at most its original chain increment. -/
lemma marginal_chain_step {d : ℕ} {f : Torus d → ℝ} (hf : PositiveBounded f)
    (s : Finset (Fin d)) {n : ℕ} (hn : n < d) :
    entropyIntegral (avg (s ∪ coordinatePrefix d n) f) -
      entropyIntegral (avg (s ∪ coordinatePrefix d (n+1)) f) ≤
    if (⟨n,hn⟩ : Fin d) ∈ s then 0 else
      entropyIntegral (avg (coordinatePrefix d n) f) - entropyIntegral (avg (coordinatePrefix d (n+1)) f) := by
  rw [coordinatePrefix_succ hn]
  by_cases hi : (⟨n,hn⟩ : Fin d) ∈ s
  · have he : s ∪ insert ⟨n,hn⟩ (coordinatePrefix d n) = s ∪ coordinatePrefix d n := by
      ext i; simp; aesop
    rw [he, sub_self, if_pos hi]
  · rw [if_neg hi]
    have h := entropy_loss_avg_le (hf.avg (coordinatePrefix d n)) s ⟨n,hn⟩ hi
    rw [← avg_union_general _ _ hf.bounded,
      ← avg_union_general _ _ hf.bounded,
      ← avg_union_general _ _ hf.bounded] at h
    have he : insert ⟨n,hn⟩ s ∪ coordinatePrefix d n = s ∪ insert ⟨n,hn⟩ (coordinatePrefix d n) := by
      ext i; simp <;> tauto
    simpa only [he, Finset.singleton_union] using h

lemma chain_sum {d : ℕ} {f : Torus d → ℝ}
    (hmass : (∫ x, f x ∂torusMeasure d) = 1) (s : Finset (Fin d)) :
    (∑ n ∈ Finset.range d, (entropyIntegral (avg (s ∪ coordinatePrefix d n) f) -
      entropyIntegral (avg (s ∪ coordinatePrefix d (n+1)) f))) = entropyIntegral (avg s f) := by
  rw [Finset.sum_range_sub']
  have he : s ∪ (Finset.univ : Finset (Fin d)) = Finset.univ := by ext i; simp
  simp [he, entropyIntegral, hmass]

lemma marginal_chain_bound {d : ℕ} {f : Torus d → ℝ} (hf : PositiveBounded f)
    (hmass : (∫ x, f x ∂torusMeasure d) = 1) (s : Finset (Fin d)) :
    entropyIntegral (avg s f) ≤ ∑ i : Fin d,
      if i ∈ s then 0 else
        entropyIntegral (avg (coordinatePrefix d i.val) f) -
          entropyIntegral (avg (coordinatePrefix d (i.val+1)) f) := by
  rw [← chain_sum hmass s, ← Fin.sum_univ_eq_sum_range]
  exact Finset.sum_le_sum (fun i _ => marginal_chain_step hf s i.isLt)

#print axioms marginal_chain_bound
end BecknerOnofri.HighDim.EntropyShearer
