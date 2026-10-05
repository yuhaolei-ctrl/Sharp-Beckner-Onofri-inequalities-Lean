import BecknerOnofri.EntropyTailPermutationComparison

noncomputable section
open scoped BigOperators
namespace BecknerOnofri.HighDim.EntropyTail.DiscreteLayers

def nonemptyChoices (d : ℕ) : Finset (Fin d → Bool) :=
  Finset.univ.erase (fun _ => false)

def choiceTerm {d : ℕ} (g h : ℕ → ℝ) (b : Fin d → Bool) (L : Fin d → ℕ) : ℝ :=
  ∏ i, if b i then h (L i) else g (L i)

theorem choice_sum_deficit {d : ℕ} (g h : ℕ → ℝ) (L : Fin d → ℕ) :
    (∑ b ∈ nonemptyChoices d, choiceTerm g h b L) =
      (∏ i, (g (L i)+h (L i)))-(∏ i, g (L i)) := by
  classical
  have he : (∏ i, (g (L i)+h (L i))) = ∑ b : Fin d → Bool, choiceTerm g h b L := by
    calc
      _ = ∏ i, ∑ b : Bool, if b then h (L i) else g (L i) := by
        apply Finset.prod_congr rfl
        intro i _
        simp [Fintype.sum_bool, add_comm]
      _ = _ := Fintype.prod_sum _
  have hh := Finset.sum_erase_add Finset.univ
    (fun b : Fin d → Bool => choiceTerm g h b L) (Finset.mem_univ (fun _ => false))
  have hz : choiceTerm g h (fun _ : Fin d => false) L = ∏ i, g (L i) := by simp [choiceTerm]
  rw [hz, ← he] at hh
  change (∑ b ∈ Finset.univ.erase (fun _ : Fin d => false), choiceTerm g h b L) = _
  linarith

theorem permutation_deficit_identity {d : ℕ} (g h : ℕ → ℝ) (L : Fin d → ℕ) :
    (∑ b ∈ nonemptyChoices d, (Fintype.card (Equiv.Perm (Fin d)) : ℝ)⁻¹*
      (∑ σ : Equiv.Perm (Fin d), choiceTerm g h b (fun i => L (σ i)))) =
      (∏ i, (g (L i)+h (L i)))-(∏ i, g (L i)) := by
  classical
  have hp : (Fintype.card (Equiv.Perm (Fin d)) : ℝ) ≠ 0 := by positivity
  rw [← Finset.mul_sum, Finset.sum_comm]
  have he (σ : Equiv.Perm (Fin d)) :
      (∑ b ∈ nonemptyChoices d, choiceTerm g h b (fun i => L (σ i))) =
        (∏ i, (g (L i)+h (L i)))-(∏ i, g (L i)) := by
    rw [choice_sum_deficit]
    rw [Equiv.prod_comp σ (fun i => g (L i)+h (L i)), Equiv.prod_comp σ (fun i => g (L i))]
  simp_rw [he]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hp, one_mul]

theorem diagonal_deficit_identity {d : ℕ} (g h : ℕ → ℝ) (L : Fin d → ℕ) :
    (∑ b ∈ nonemptyChoices d, (d : ℝ)⁻¹*(∑ j : Fin d,
      choiceTerm g h b (fun _ => L j))) =
        (d : ℝ)⁻¹*(∑ j : Fin d, ((g (L j)+h (L j))^d-(g (L j))^d)) := by
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp only [choice_sum_deficit, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- The source's subset expansion and permutation averaging, before the Mellin integral. -/
theorem product_deficit_comparison {d : ℕ} (hd : 0 < d) (g h : ℕ → ℝ)
    (hg : ∀ n, 0 ≤ g n) (hh : ∀ n, 0 ≤ h n) (hgm : Monotone g) (hhm : Monotone h)
    (L : Fin d → ℕ) :
    (∏ i, (g (L i)+h (L i)))-(∏ i, g (L i)) ≤
      (d : ℝ)⁻¹*(∑ j : Fin d, ((g (L j)+h (L j))^d-(g (L j))^d)) := by
  classical
  rw [← permutation_deficit_identity, ← diagonal_deficit_identity]
  apply Finset.sum_le_sum
  intro b _
  apply permutation_product_comparison hd (fun i n => if b i then h n else g n) _ _ L
  · intro i n
    split_ifs
    · exact hh n
    · exact hg n
  · intro i
    cases hb : b i <;> simpa only [hb, Bool.false_eq_true, if_false, if_true] using
      (show Monotone (if b i then h else g) from by cases hc : b i <;> simp [hc, hgm, hhm])

#print axioms product_deficit_comparison
end BecknerOnofri.HighDim.EntropyTail.DiscreteLayers
