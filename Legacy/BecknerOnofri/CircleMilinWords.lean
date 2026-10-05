import Legacy.TorusEndpoint.FiniteAtomCoefficients
import Mathlib.Analysis.Complex.Basic

/-! Complete positive-integer words for the equality-sensitive circle
exponential-coefficient argument. -/
noncomputable section
open scoped BigOperators
namespace Legacy.BecknerOnofri.CircleMilin
open Legacy.TorusEndpoint.FiniteCone Legacy.TorusEndpoint.FiniteAtomCoefficients

def words (n : ℕ) : Finset (List ℕ) :=
  ((wordsAtMost (List.range' 1 n) n).toFinset).filter (fun xs => xs.sum = n)

def complexWord (a : ℕ → ℂ) (xs : List ℕ) : ℂ :=
  ((xs.length.factorial : ℕ) : ℂ)⁻¹ * (xs.map a).prod

def pWord (a : ℕ → ℂ) (xs : List ℕ) : ℝ :=
  ((xs.length.factorial : ℕ) : ℝ)⁻¹ * (xs.map (fun j : ℕ => (j : ℝ)*‖a j‖^2)).prod

def qWord (xs : List ℕ) : ℝ :=
  ((xs.length.factorial : ℕ) : ℝ)⁻¹ * (xs.map (fun j : ℕ => (j : ℝ)⁻¹)).prod

def wordValue (a : ℕ → ℂ) (xs : List ℕ) : ℂ :=
  (xs.map (fun j : ℕ => (j : ℂ)*a j)).prod

def bCoeff (a : ℕ → ℂ) (n : ℕ) : ℂ := ∑ xs ∈ words n, complexWord a xs
def pCoeff (a : ℕ → ℂ) (n : ℕ) : ℝ := ∑ xs ∈ words n, pWord a xs
def qCoeff (n : ℕ) : ℝ := ∑ xs ∈ words n, qWord xs

private theorem length_le_sum {xs : List ℕ} (h : ∀ j ∈ xs, 0 < j) :
    xs.length ≤ xs.sum := by
  induction xs with
  | nil => simp
  | cons j xs ih =>
    have hj := h j (by simp)
    have ht := ih (fun k hk => h k (by simp [hk]))
    simp only [List.length_cons, List.sum_cons]
    omega

private theorem le_sum_of_mem {xs : List ℕ} {j : ℕ} (h : j ∈ xs) : j ≤ xs.sum := by
  induction xs with
  | nil => simp at h
  | cons k xs ih =>
    simp only [List.mem_cons] at h
    rcases h with rfl | ht
    · simp
    · have := ih ht
      simp only [List.sum_cons]
      omega

theorem mem_words_iff (n : ℕ) (xs : List ℕ) :
    xs ∈ words n ↔ (∀ j ∈ xs, 0 < j) ∧ xs.sum = n := by
  rw [words, Finset.mem_filter, List.mem_toFinset]
  constructor
  · rintro ⟨hx, hs⟩
    refine ⟨?_, hs⟩
    intro j hj
    have hmem := (mem_wordsAtMost_properties _ _ hx).2 j hj
    have := List.left_le_of_mem_range' hmem
    omega
  · rintro ⟨hp, hs⟩
    refine ⟨mem_wordsAtMost _ _ _ ?_ ?_, hs⟩
    · simpa [hs] using length_le_sum hp
    · intro j hj
      have hjp := hp j hj
      have hjn := le_sum_of_mem hj
      rw [hs] at hjn
      exact List.mem_range'.mpr ⟨j-1, by omega, by omega⟩

@[simp] theorem words_zero : words 0 = {[]} := by
  ext xs
  rw [mem_words_iff, Finset.mem_singleton]
  constructor
  · rintro ⟨hp, hs⟩
    exact List.eq_nil_of_length_eq_zero (by have := length_le_sum hp; omega)
  · rintro rfl
    simp

theorem singleton_mem_words {n : ℕ} (hn : 0 < n) : [n] ∈ words n := by
  rw [mem_words_iff]
  simp [hn]

theorem replicate_mem_words (n : ℕ) : List.replicate n 1 ∈ words n := by
  rw [mem_words_iff]
  constructor
  · intro j hj
    have := List.eq_of_mem_replicate hj
    omega
  · simp

theorem qWord_pos {n : ℕ} {xs : List ℕ} (hx : xs ∈ words n) : 0 < qWord xs := by
  apply mul_pos (inv_pos.mpr (Nat.cast_pos.mpr (Nat.factorial_pos _)))
  apply List.prod_pos
  intro b hb
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hb
  exact inv_pos.mpr (Nat.cast_pos.mpr (((mem_words_iff _ _).mp hx).1 j hj))

theorem pWord_nonneg (a : ℕ → ℂ) (xs : List ℕ) : 0 ≤ pWord a xs := by
  apply mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
  apply List.prod_nonneg
  intro b hb
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hb
  positivity

@[simp] theorem bCoeff_zero (a : ℕ → ℂ) : bCoeff a 0 = 1 := by
  simp [bCoeff, complexWord]
@[simp] theorem pCoeff_zero (a : ℕ → ℂ) : pCoeff a 0 = 1 := by
  simp [pCoeff, pWord]
@[simp] theorem qCoeff_zero : qCoeff 0 = 1 := by
  simp [qCoeff, qWord]

end Legacy.BecknerOnofri.CircleMilin
