module

public import BecknerOnofri.SpinPressureCertificateCells

@[expose] public section

/-!
# Lemma 5.20 on `[1/16, 0.99]` from the cell certificate

The cells of `SpinPressureCertificateCells` are consecutive and cover `[1/16, 99/100]`; on each
of them `checkCell_sound` gives `t⁴/200 < 𝓑(t)`.
-/

namespace BecknerOnofri.HighDim.Spin.PressureCertificate

open Set

/-- `chain a cs b`: the cells `cs` are consecutive, start at `a` and end at `b`. -/
def chain : ℤ → List (ℤ × ℤ) → ℤ → Bool
  | a, [], b => decide (a = b)
  | a, c :: cs, b => decide (c.1 = a) && decide (c.1 ≤ c.2) && chain c.2 cs b

theorem chain_cover {d : ℤ} :
    ∀ (cs : List (ℤ × ℤ)) (a b : ℤ), chain a cs b = true → ∀ t : ℝ,
      (a : ℝ) / d < t → t ≤ (b : ℝ) / d →
        ∃ c ∈ cs, (c.1 : ℝ) / d ≤ t ∧ t ≤ (c.2 : ℝ) / d := by
  intro cs
  induction cs with
  | nil =>
    intro a b h t h1 h2
    simp only [chain, decide_eq_true_eq] at h
    subst h
    exact absurd h1 (not_lt.mpr h2)
  | cons c cs ih =>
    intro a b h t h1 h2
    simp only [chain, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hca, -⟩, hrest⟩ := h
    by_cases ht : t ≤ (c.2 : ℝ) / d
    · exact ⟨c, List.mem_cons_self .., by rw [hca]; exact h1.le, ht⟩
    · push Not at ht
      obtain ⟨c', hc', h'⟩ := ih c.2 b hrest t ht h2
      exact ⟨c', List.mem_cons_of_mem _ hc', h'⟩

theorem cells_chain : chain 204800 cells 3244032 = true := by decide +kernel

theorem cells_all : (cells.all fun c => checkCell c.1 c.2 cellDen) = true := by
  simp only [cells, List.all_append, cells00_check, cells01_check, cells02_check, cells03_check, cells04_check, cells05_check, cells06_check, cells07_check, cells08_check, cells09_check, cells10_check, cells11_check, cells12_check, cells13_check, cells14_check, cells15_check, Bool.and_self]

/-- **Lemma 5.20** (lem:section5-scalar-pressure) on `[1/16, 0.99]`: `𝓑(t) > t⁴/200`. -/
theorem pressureScalar_gt_cells (t : ℝ) (ht : t ∈ Icc (1 / 16 : ℝ) (99 / 100)) :
    t ^ 4 / 200 < pressureScalar t := by
  have hd : (0 : ℤ) < cellDen := by decide
  have h1 : ((204800 : ℤ) : ℝ) / (cellDen : ℝ) ≤ t := by
    have := ht.1; norm_num [cellDen]; linarith
  have h2 : t ≤ ((3244032 : ℤ) : ℝ) / (cellDen : ℝ) := by
    have := ht.2; norm_num [cellDen]; linarith
  rcases lt_or_eq_of_le h1 with h1 | h1
  · obtain ⟨c, hc, hc1, hc2⟩ := chain_cover cells 204800 3244032 cells_chain t h1 h2
    exact checkCell_sound (List.all_eq_true.mp cells_all c hc) ⟨hc1, hc2⟩
      (by linarith [ht.1]) (by linarith [ht.2])
  · have hc : ((204800 : ℤ), (211394 : ℤ)) ∈ cells := by simp [cells, cells00]
    refine checkCell_sound (List.all_eq_true.mp cells_all _ hc) ⟨h1.le, ?_⟩
      (by linarith [ht.1]) (by linarith [ht.2])
    rw [← h1]
    norm_num [cellDen]

end BecknerOnofri.HighDim.Spin.PressureCertificate
