module

public import BecknerOnofri.RectangleTwelve
public import BecknerOnofri.SpectralSliceBound

@[expose] public section

/-! # Lemmas 5.3 and 5.4 (`lem:spectral-slice`, `lem:spectral-rectangle`)

Lemma 5.3 is `BecknerOnofri.SpectralSlice.spectral_slice_bound` (type matches).

Lemma 5.4 is `BecknerOnofri.RectangleLattice.rectangle_comparison_ge12`, whose deleted-coordinate
sums are written on the ambient lattice `ℤ^d` with the `i`th radius set to `0`.  The manuscript's
`𝒮_{d-1}(R_{-i})` is a sum over `ℤ^{d-1}`; `latticeSum_update_zero_eq_succAbove` identifies the two
(for `d = n+1`) and `spectral_rectangle` is the literal reduced-coordinate form. -/

noncomputable section
open scoped BigOperators
open Finset

namespace BecknerOnofri.V2.Transfer
open BecknerOnofri.RectangleLattice

/-- Lemma 5.3, literally. -/
theorem spectral_slice {p a : ℝ} (hp : 12 ≤ p) (ha : Real.sqrt 2 ≤ a) :
    a ^ (p - 1) * (∑' n : ℤ, (a ^ 2 + (n : ℝ) ^ 2) ^ (-p / 2)) ≤ 311141 / 342144 ∧
      (311141 / 342144 : ℝ) < 1 :=
  ⟨BecknerOnofri.SpectralSlice.spectral_slice_bound hp ha, by norm_num⟩

/-- Deleting a coordinate: the sum over the ambient lattice with the `i`th radius `0` equals the
sum over the `n`-dimensional lattice of the remaining coordinates. -/
theorem latticeSum_update_zero_eq_succAbove {n : ℕ} (p : ℝ) (R : Fin (n + 1) → ℕ)
    (i : Fin (n + 1)) :
    latticeSum p (Function.update R i 0) = latticeSum p (fun j : Fin n => R (i.succAbove j)) := by
  unfold latticeSum puncturedBox box
  refine Finset.sum_nbij' (fun k j => k (i.succAbove j)) (fun m => Fin.insertNth i 0 m) ?_ ?_ ?_ ?_ ?_
  · intro k hk
    simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Icc] at hk ⊢
    obtain ⟨hb, hne⟩ := hk
    have hki : k i = 0 := by
      have := hb i
      simp only [Function.update_self, Nat.cast_zero, neg_zero] at this
      omega
    refine ⟨fun j => ?_, ?_⟩
    · have := hb (i.succAbove j)
      rwa [Function.update_of_ne (Fin.succAbove_ne i j)] at this
    · intro h0
      apply hne
      funext l
      rcases Fin.eq_self_or_eq_succAbove i l with rfl | ⟨j, rfl⟩
      · simpa using hki
      · exact congrFun h0 j
  · intro m hm
    simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Icc] at hm ⊢
    obtain ⟨hb, hne⟩ := hm
    refine ⟨fun l => ?_, ?_⟩
    · rcases Fin.eq_self_or_eq_succAbove i l with rfl | ⟨j, rfl⟩
      · simp
      · rw [Function.update_of_ne (Fin.succAbove_ne i j)]
        simpa using hb j
    · intro h0
      apply hne
      funext j
      have := congrFun h0 (i.succAbove j)
      simpa using this
  · intro k hk
    simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Icc] at hk
    funext l
    rcases Fin.eq_self_or_eq_succAbove i l with rfl | ⟨j, rfl⟩
    · have := hk.1 l
      simp only [Function.update_self, Nat.cast_zero, neg_zero] at this
      simp only [Fin.insertNth_apply_same]
      omega
    · simp
  · intro m _
    funext j
    simp
  · intro k hk
    simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Icc] at hk
    have hki : k i = 0 := by
      have := hk.1 i
      simp only [Function.update_self, Nat.cast_zero, neg_zero] at this
      omega
    unfold weight normSq
    rw [Fin.sum_univ_succAbove _ i, hki]
    simp

/-- Lemma 5.4 in reduced coordinates: for every `n ≥ 11` (that is, `d = n + 1 ≥ 12`) and every
`R ∈ ℕ₀^{n+1}`, `𝒮_{n+1}(R) ≤ (1/n) ∑_i 𝒮_n(R_{-i})`. -/
theorem spectral_rectangle {n : ℕ} (hn : 11 ≤ n) (R : Fin (n + 1) → ℕ) :
    latticeSum ((n + 1 : ℕ) : ℝ) R ≤
      1 / (n : ℝ) * ∑ i : Fin (n + 1), latticeSum (n : ℝ) (fun j : Fin n => R (i.succAbove j)) := by
  have h := rectangle_comparison_ge12 (d := n + 1) (by omega) R
  have hc : (((n + 1 : ℕ) : ℝ) - 1) = (n : ℝ) := by push_cast; ring
  rw [hc] at h
  simpa only [latticeSum_update_zero_eq_succAbove] using h

end BecknerOnofri.V2.Transfer
