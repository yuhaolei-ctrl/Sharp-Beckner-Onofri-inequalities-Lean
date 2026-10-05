import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-! Exact multiplicity used when iterating the marginal-energy comparison. -/
noncomputable section
open Finset
open scoped BigOperators
namespace BecknerOnofri

lemma powersetCard_erase_eq_filter {α : Type*} [DecidableEq α]
    (s : Finset α) (i : α) (r : ℕ) :
    (s.erase i).powersetCard r = (s.powersetCard r).filter (fun t => i ∉ t) := by
  ext t
  simp only [mem_powersetCard, mem_filter]
  constructor
  · rintro ⟨ht, hc⟩
    exact ⟨⟨ht.trans (erase_subset _ _), hc⟩, fun hi => (mem_erase.mp (ht hi)).1 rfl⟩
  · rintro ⟨⟨ht, hc⟩, hi⟩
    exact ⟨fun j hj => mem_erase.mpr ⟨fun h => hi (h ▸ hj), ht hj⟩, hc⟩

theorem sum_erase_powersetCard {α M : Type*} [DecidableEq α] [AddCommMonoid M]
    (s : Finset α) (r : ℕ) (f : Finset α → M) :
    (∑ i ∈ s, ∑ t ∈ (s.erase i).powersetCard r, f t) =
      (s.card-r) • ∑ t ∈ s.powersetCard r, f t := by
  simp_rw [powersetCard_erase_eq_filter, sum_filter]
  rw [sum_comm, smul_sum]
  apply sum_congr rfl
  intro t ht
  rw [← sum_filter]
  have he : s.filter (fun i => i ∉ t) = s \ t := by ext i; simp
  rw [he, sum_const, card_sdiff_of_subset (mem_powersetCard.mp ht).1, (mem_powersetCard.mp ht).2]

#print axioms sum_erase_powersetCard
end BecknerOnofri
