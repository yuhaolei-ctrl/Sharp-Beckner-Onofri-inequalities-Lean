import Legacy.TorusEndpoint.FiniteCone
import Legacy.TorusEndpoint.ScalarExponentialCoefficients
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List

/-!
# Complete finite-atom exponential coefficients

The coefficient is a sum over all distinct ordered words in a finite atom
alphabet with the prescribed output frequency. Positive integer weights
provide a finite cover; the membership theorem proves that this is not an
arbitrary truncation. The chosen positive weights do not affect the result.
-/

open scoped BigOperators
open Legacy.TorusEndpoint.FiniteCone

namespace Legacy.TorusEndpoint.FiniteAtomCoefficients

set_option maxHeartbeats 800000

theorem mem_wordsAtMost_properties {α : Type} (atoms : List α) (n : ℕ)
    {xs : List α} (hx : xs ∈ wordsAtMost atoms n) :
    xs.length ≤ n ∧ ∀ x ∈ xs, x ∈ atoms := by
  induction n generalizing xs with
  | zero =>
    have he : xs = [] := by simpa [wordsAtMost] using hx
    subst xs
    simp
  | succ n ih =>
    rcases List.mem_cons.mp hx with he | ht
    · subst xs
      simp
    · rcases List.mem_flatMap.mp ht with ⟨x, hxa, hm⟩
      rcases List.mem_map.mp hm with ⟨ys, hy, he⟩
      subst xs
      obtain ⟨hlen, hmem⟩ := ih hy
      constructor
      · simp only [List.length_cons]
        omega
      · intro z hz
        rcases List.mem_cons.mp hz with hzx | hzy
        · simpa [hzx] using hxa
        · exact hmem z hzy

noncomputable def decompositions {d : ℕ} (atoms : List (Vec d)) (w k : Vec d) :
    Finset (List (Vec d)) := by
  classical
  exact ((wordsAtMost atoms (eval w k).toNat).toFinset).filter (fun xs => sumVec xs = k)

/-- Exact membership: all words with the right atoms and sum, without a cutoff premise. -/
theorem mem_decompositions_iff {d : ℕ} (atoms : List (Vec d)) (w k : Vec d)
    (hw : ∀ x ∈ atoms, 0 < eval w x) (xs : List (Vec d)) :
    xs ∈ decompositions atoms w k ↔ (∀ x ∈ xs, x ∈ atoms) ∧ sumVec xs = k := by
  classical
  rw [decompositions, Finset.mem_filter, List.mem_toFinset]
  constructor
  · rintro ⟨hx, hs⟩
    exact ⟨(mem_wordsAtMost_properties atoms _ hx).2, hs⟩
  · rintro ⟨hm, hs⟩
    refine ⟨?_, hs⟩
    have hb := length_le_eval_sum w xs (fun x hx => hw x (hm x hx))
    rw [hs] at hb
    exact mem_wordsAtMost atoms (eval w k).toNat xs (by omega) hm

theorem decompositions_independent_weights {d : ℕ}
    (atoms : List (Vec d)) (w v k : Vec d)
    (hw : ∀ x ∈ atoms, 0 < eval w x) (hv : ∀ x ∈ atoms, 0 < eval v x) :
    decompositions atoms w k = decompositions atoms v k := by
  classical
  ext xs
  rw [mem_decompositions_iff atoms w k hw, mem_decompositions_iff atoms v k hv]

theorem sumVec_singleton {d : ℕ} (k : Vec d) : sumVec [k] = k := by
  funext i
  simp [sumVec, add, zero]

theorem sumVec_append {d : ℕ} (xs ys : List (Vec d)) :
    sumVec (xs ++ ys) = add (sumVec xs) (sumVec ys) := by
  induction xs with
  | nil =>
    funext i
    simp [sumVec, add, zero]
  | cons x xs ih =>
    rw [List.cons_append]
    change add x (sumVec (xs ++ ys)) = add (add x (sumVec xs)) (sumVec ys)
    rw [ih]
    funext i
    simp [add, Int.add_assoc]

theorem decompositions_zero {d : ℕ} (atoms : List (Vec d)) (w : Vec d)
    (hw : ∀ x ∈ atoms, 0 < eval w x) : decompositions atoms w zero = {[]} := by
  classical
  ext xs
  rw [mem_decompositions_iff atoms w zero hw, Finset.mem_singleton]
  constructor
  · rintro ⟨hm, hs⟩
    have hb := length_le_eval_sum w xs (fun x hx => hw x (hm x hx))
    rw [hs, eval_zero] at hb
    exact List.eq_nil_of_length_eq_zero (by omega)
  · rintro rfl
    exact ⟨by simp, rfl⟩

theorem singleton_mem_decompositions {d : ℕ} (atoms : List (Vec d)) (w k : Vec d)
    (hw : ∀ x ∈ atoms, 0 < eval w x) (hk : k ∈ atoms) :
    [k] ∈ decompositions atoms w k := by
  rw [mem_decompositions_iff atoms w k hw]
  exact ⟨by simpa using hk, sumVec_singleton k⟩

noncomputable def wordWeight {d : ℕ} (a : Vec d → ℝ) (q : ℝ)
    (xs : List (Vec d)) : ℝ := scalarExpTerm q xs.length * (xs.map a).prod

@[simp] theorem wordWeight_nil {d : ℕ} (a : Vec d → ℝ) (q : ℝ) :
    wordWeight a q [] = 1 := by simp [wordWeight]

@[simp] theorem wordWeight_singleton {d : ℕ} (a : Vec d → ℝ) (q : ℝ) (k : Vec d) :
    wordWeight a q [k] = q * a k := by simp [wordWeight]

theorem wordWeight_nonneg {d : ℕ} (a : Vec d → ℝ) {q : ℝ} (hq : 0 ≤ q)
    (xs : List (Vec d)) (ha : ∀ x ∈ xs, 0 ≤ a x) : 0 ≤ wordWeight a q xs := by
  apply mul_nonneg (scalarExpTerm_nonneg hq _)
  apply List.prod_nonneg
  intro b hb
  rcases List.mem_map.mp hb with ⟨x, hx, rfl⟩
  exact ha x hx

theorem wordWeight_pos {d : ℕ} (a : Vec d → ℝ) {q : ℝ} (hq : 0 < q)
    (xs : List (Vec d)) (ha : ∀ x ∈ xs, 0 < a x) : 0 < wordWeight a q xs := by
  apply mul_pos
  · unfold scalarExpTerm
    exact div_pos (pow_pos hq _) (Nat.cast_pos.mpr (Nat.factorial_pos _))
  · apply List.prod_pos
    intro b hb
    rcases List.mem_map.mp hb with ⟨x, hx, rfl⟩
    exact ha x hx

noncomputable def coefficient {d : ℕ} (atoms : List (Vec d)) (w : Vec d)
    (a : Vec d → ℝ) (q : ℝ) (k : Vec d) : ℝ :=
  ∑ xs ∈ decompositions atoms w k, wordWeight a q xs

theorem coefficient_independent_weights {d : ℕ}
    (atoms : List (Vec d)) (w v : Vec d) (a : Vec d → ℝ) (q : ℝ) (k : Vec d)
    (hw : ∀ x ∈ atoms, 0 < eval w x) (hv : ∀ x ∈ atoms, 0 < eval v x) :
    coefficient atoms w a q k = coefficient atoms v a q k := by
  unfold coefficient
  rw [decompositions_independent_weights atoms w v k hw hv]

theorem coefficient_nonneg {d : ℕ} (atoms : List (Vec d)) (w : Vec d)
    (a : Vec d → ℝ) {q : ℝ} (k : Vec d)
    (hw : ∀ x ∈ atoms, 0 < eval w x)
    (ha : ∀ x ∈ atoms, 0 ≤ a x) (hq : 0 ≤ q) :
    0 ≤ coefficient atoms w a q k := by
  apply Finset.sum_nonneg
  intro xs hx
  have hm := ((mem_decompositions_iff atoms w k hw xs).mp hx).1
  exact wordWeight_nonneg a hq xs (fun x hx => ha x (hm x hx))

theorem coefficient_zero {d : ℕ} (atoms : List (Vec d)) (w : Vec d)
    (a : Vec d → ℝ) (q : ℝ) (hw : ∀ x ∈ atoms, 0 < eval w x) :
    coefficient atoms w a q zero = 1 := by
  classical
  simp [coefficient, decompositions_zero atoms w hw]

theorem single_atom_lower_bound {d : ℕ} (atoms : List (Vec d)) (w : Vec d)
    (a : Vec d → ℝ) {q : ℝ} (k : Vec d)
    (hw : ∀ x ∈ atoms, 0 < eval w x)
    (ha : ∀ x ∈ atoms, 0 ≤ a x) (hq : 0 ≤ q) (hk : k ∈ atoms) :
    q * a k ≤ coefficient atoms w a q k := by
  classical
  have hs := singleton_mem_decompositions atoms w k hw hk
  have hnonneg : ∀ xs ∈ decompositions atoms w k, 0 ≤ wordWeight a q xs := by
    intro xs hx
    have hm := ((mem_decompositions_iff atoms w k hw xs).mp hx).1
    exact wordWeight_nonneg a hq xs (fun x hx => ha x (hm x hx))
  simpa [coefficient] using (Finset.single_le_sum hnonneg hs)

/-- Strict positivity on every frequency admitting a word with positive atom weights. -/
theorem coefficient_pos_of_decomposition {d : ℕ}
    (atoms : List (Vec d)) (w : Vec d) (a : Vec d → ℝ) {q : ℝ} (k : Vec d)
    (hw : ∀ x ∈ atoms, 0 < eval w x) (ha : ∀ x ∈ atoms, 0 < a x) (hq : 0 < q)
    (xs : List (Vec d)) (hm : ∀ x ∈ xs, x ∈ atoms) (hs : sumVec xs = k) :
    0 < coefficient atoms w a q k := by
  classical
  have hx : xs ∈ decompositions atoms w k :=
    (mem_decompositions_iff atoms w k hw xs).mpr ⟨hm, hs⟩
  have hnonneg : ∀ ys ∈ decompositions atoms w k, 0 ≤ wordWeight a q ys := by
    intro ys hy
    have hmy := ((mem_decompositions_iff atoms w k hw ys).mp hy).1
    exact wordWeight_nonneg a hq.le ys (fun x hx => (ha x (hmy x hx)).le)
  exact (wordWeight_pos a hq xs (fun x hx => ha x (hm x hx))).trans_le
    (Finset.single_le_sum hnonneg hx)

/--
The scalar factorial convolution accounts for the binomial multiplicities.
Each term is an ordered prefix/suffix cut, including both empty-word cuts.
-/
theorem wordWeight_add_parameter {d : ℕ} (a : Vec d → ℝ) (p q : ℝ)
    (xs : List (Vec d)) :
    wordWeight a (p + q) xs =
      ∑ j ∈ Finset.range (xs.length + 1),
        wordWeight a p (xs.take j) * wordWeight a q (xs.drop j) := by
  rw [wordWeight, scalarExpTerm_convolution_range, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  have hjle : j ≤ xs.length := by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have hprod : ((xs.take j).map a).prod * ((xs.drop j).map a).prod = (xs.map a).prod := by
    rw [← List.prod_append, ← List.map_append, List.take_append_drop]
  simp only [wordWeight, List.length_take, List.length_drop, Nat.min_eq_left hjle]
  rw [← hprod]
  ring

/-- A complete finite convolution identity at the word-and-cut level. -/
theorem coefficient_add_parameter_word_cuts {d : ℕ}
    (atoms : List (Vec d)) (w : Vec d) (a : Vec d → ℝ) (p q : ℝ) (k : Vec d) :
    coefficient atoms w a (p + q) k =
      ∑ xs ∈ decompositions atoms w k,
        ∑ j ∈ Finset.range (xs.length + 1),
          wordWeight a p (xs.take j) * wordWeight a q (xs.drop j) := by
  unfold coefficient
  apply Finset.sum_congr rfl
  intro xs _
  exact wordWeight_add_parameter a p q xs

abbrev Cut (d : ℕ) := Σ _ : List (Vec d), ℕ

def cutPair {d : ℕ} (c : Cut d) : List (Vec d) × List (Vec d) :=
  (c.1.take c.2, c.1.drop c.2)

def joinPair {d : ℕ} (uv : List (Vec d) × List (Vec d)) : Cut d :=
  ⟨uv.1 ++ uv.2, uv.1.length⟩

theorem cutPair_joinPair {d : ℕ} (uv : List (Vec d) × List (Vec d)) :
    cutPair (joinPair uv) = uv := by
  rcases uv with ⟨xs, ys⟩
  simp [cutPair, joinPair]

theorem joinPair_cutPair {d : ℕ} (c : Cut d) (hj : c.2 ≤ c.1.length) :
    joinPair (cutPair c) = c := by
  rcases c with ⟨xs, j⟩
  simp only [joinPair, cutPair, List.take_append_drop, List.length_take,
    Nat.min_eq_left hj]

noncomputable def cuts {d : ℕ} (atoms : List (Vec d)) (w k : Vec d) : Finset (Cut d) :=
  (decompositions atoms w k).sigma (fun xs => Finset.range (xs.length + 1))

noncomputable def splitPairs {d : ℕ} (atoms : List (Vec d)) (w k : Vec d) :
    Finset (List (Vec d) × List (Vec d)) := by
  classical
  exact (cuts atoms w k).image cutPair

theorem cutPair_injOn_cuts {d : ℕ} (atoms : List (Vec d)) (w k : Vec d)
    {c e : Cut d} (hc : c ∈ cuts atoms w k) (he : e ∈ cuts atoms w k)
    (hce : cutPair c = cutPair e) : c = e := by
  have hcj : c.2 ≤ c.1.length := by
    have h := (Finset.mem_sigma.mp hc).2
    have := Finset.mem_range.mp h
    omega
  have hej : e.2 ≤ e.1.length := by
    have h := (Finset.mem_sigma.mp he).2
    have := Finset.mem_range.mp h
    omega
  calc
    c = joinPair (cutPair c) := (joinPair_cutPair c hcj).symm
    _ = joinPair (cutPair e) := congrArg joinPair hce
    _ = e := joinPair_cutPair e hej

/-- The finite pair set is exactly all two-word decompositions of the target. -/
theorem mem_splitPairs_iff {d : ℕ} (atoms : List (Vec d)) (w k : Vec d)
    (hw : ∀ x ∈ atoms, 0 < eval w x) (uv : List (Vec d) × List (Vec d)) :
    uv ∈ splitPairs atoms w k ↔
      (∀ x ∈ uv.1, x ∈ atoms) ∧ (∀ x ∈ uv.2, x ∈ atoms) ∧
        add (sumVec uv.1) (sumVec uv.2) = k := by
  classical
  rw [splitPairs, Finset.mem_image]
  constructor
  · rintro ⟨c, hc, rfl⟩
    have hD := (Finset.mem_sigma.mp hc).1
    obtain ⟨hm, hs⟩ := (mem_decompositions_iff atoms w k hw c.1).mp hD
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      exact hm x (List.mem_of_mem_take hx)
    · intro x hx
      exact hm x (List.mem_of_mem_drop hx)
    · change add (sumVec (c.1.take c.2)) (sumVec (c.1.drop c.2)) = k
      rw [← sumVec_append, List.take_append_drop]
      exact hs
  · rintro ⟨hu, hv, hs⟩
    refine ⟨joinPair uv, ?_, cutPair_joinPair uv⟩
    apply Finset.mem_sigma.mpr
    constructor
    · rw [mem_decompositions_iff atoms w k hw]
      constructor
      · intro x hx
        rcases List.mem_append.mp hx with hxu | hxv
        · exact hu x hxu
        · exact hv x hxv
      · exact (sumVec_append uv.1 uv.2).trans hs
    · apply Finset.mem_range.mpr
      change uv.1.length < (uv.1 ++ uv.2).length + 1
      simp only [List.length_append]
      omega

/--
Exact finite word-pair convolution. The cut-to-pair map is injective, so
passing from cuts to the image finset neither loses nor duplicates a term.
-/
theorem coefficient_add_parameter_word_pairs {d : ℕ}
    (atoms : List (Vec d)) (w : Vec d) (a : Vec d → ℝ) (p q : ℝ) (k : Vec d) :
    coefficient atoms w a (p + q) k =
      ∑ uv ∈ splitPairs atoms w k, wordWeight a p uv.1 * wordWeight a q uv.2 := by
  classical
  rw [coefficient_add_parameter_word_cuts, splitPairs, Finset.sum_image]
  · simp only [cuts, Finset.sum_sigma, cutPair]
  · intro c hc e he hce
    exact cutPair_injOn_cuts atoms w k hc he hce

def remainder {d : ℕ} (k i : Vec d) : Vec d := fun j => k j - i j

noncomputable def splitFrequencies {d : ℕ} (atoms : List (Vec d)) (w k : Vec d) :
    Finset (Vec d) := by
  classical
  exact (splitPairs atoms w k).image (fun uv => sumVec uv.1)

/-- Each frequency fiber is exactly the product of the two complete word sets. -/
theorem splitPairs_fiber {d : ℕ} (atoms : List (Vec d)) (w k i : Vec d)
    (hw : ∀ x ∈ atoms, 0 < eval w x) :
    (splitPairs atoms w k).filter (fun uv => sumVec uv.1 = i) =
      (decompositions atoms w i) ×ˢ (decompositions atoms w (remainder k i)) := by
  classical
  ext uv
  rw [Finset.mem_filter, mem_splitPairs_iff atoms w k hw, Finset.mem_product,
    mem_decompositions_iff atoms w i hw,
    mem_decompositions_iff atoms w (remainder k i) hw]
  constructor
  · rintro ⟨⟨hu, hv, hs⟩, hi⟩
    refine ⟨⟨hu, hi⟩, ⟨hv, ?_⟩⟩
    funext j
    have hsj := congrFun hs j
    have hij := congrFun hi j
    dsimp [add, remainder] at *
    omega
  · rintro ⟨⟨hu, hi⟩, ⟨hv, hj⟩⟩
    refine ⟨⟨hu, hv, ?_⟩, hi⟩
    rw [hi, hj]
    funext j
    dsimp [add, remainder]
    omega

theorem mem_splitFrequencies_iff {d : ℕ} (atoms : List (Vec d)) (w k i : Vec d)
    (hw : ∀ x ∈ atoms, 0 < eval w x) :
    i ∈ splitFrequencies atoms w k ↔
      (decompositions atoms w i).Nonempty ∧
        (decompositions atoms w (remainder k i)).Nonempty := by
  classical
  rw [splitFrequencies, Finset.mem_image]
  constructor
  · rintro ⟨uv, huv, hi⟩
    have hf : uv ∈ (splitPairs atoms w k).filter (fun uv => sumVec uv.1 = i) :=
      Finset.mem_filter.mpr ⟨huv, hi⟩
    rw [splitPairs_fiber atoms w k i hw] at hf
    obtain ⟨hu, hv⟩ := Finset.mem_product.mp hf
    exact ⟨⟨uv.1, hu⟩, ⟨uv.2, hv⟩⟩
  · rintro ⟨⟨xs, hxs⟩, ⟨ys, hys⟩⟩
    have hf : (xs, ys) ∈
        (decompositions atoms w i) ×ˢ (decompositions atoms w (remainder k i)) :=
      Finset.mem_product.mpr ⟨hxs, hys⟩
    rw [← splitPairs_fiber atoms w k i hw] at hf
    exact ⟨(xs, ys), (Finset.mem_filter.mp hf).1, (Finset.mem_filter.mp hf).2⟩

/-- Every term outside the stated finite convolution index set vanishes. -/
theorem coefficient_product_zero_outside {d : ℕ}
    (atoms : List (Vec d)) (w : Vec d) (a : Vec d → ℝ) (p q : ℝ) (k i : Vec d)
    (hw : ∀ x ∈ atoms, 0 < eval w x) (hi : i ∉ splitFrequencies atoms w k) :
    coefficient atoms w a p i * coefficient atoms w a q (remainder k i) = 0 := by
  classical
  have hn := (mem_splitFrequencies_iff atoms w k i hw).not.mp hi
  rcases not_and_or.mp hn with hl | hr
  · have he := Finset.not_nonempty_iff_eq_empty.mp hl
    simp [coefficient, he]
  · have he := Finset.not_nonempty_iff_eq_empty.mp hr
    simp [coefficient, he]

/--
The complete finite frequency-convolution identity. The finite outer set is
the set of all possible left frequencies of a two-word decomposition of `k`.
It is not a rectangular or externally imposed frequency cutoff.
-/
theorem coefficient_convolution {d : ℕ}
    (atoms : List (Vec d)) (w : Vec d) (a : Vec d → ℝ) (p q : ℝ) (k : Vec d)
    (hw : ∀ x ∈ atoms, 0 < eval w x) :
    coefficient atoms w a (p + q) k =
      ∑ i ∈ splitFrequencies atoms w k,
        coefficient atoms w a p i * coefficient atoms w a q (remainder k i) := by
  classical
  have hgroup := Finset.sum_fiberwise_of_maps_to
    (s := splitPairs atoms w k) (t := splitFrequencies atoms w k)
    (g := fun uv => sumVec uv.1)
    (fun uv huv => Finset.mem_image_of_mem (fun uv => sumVec uv.1) huv)
    (fun uv => wordWeight a p uv.1 * wordWeight a q uv.2)
  calc
    coefficient atoms w a (p + q) k =
        ∑ uv ∈ splitPairs atoms w k, wordWeight a p uv.1 * wordWeight a q uv.2 :=
      coefficient_add_parameter_word_pairs atoms w a p q k
    _ = ∑ i ∈ splitFrequencies atoms w k,
        ∑ uv ∈ (splitPairs atoms w k).filter (fun uv => sumVec uv.1 = i),
          wordWeight a p uv.1 * wordWeight a q uv.2 := hgroup.symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [splitPairs_fiber atoms w k i hw, Finset.sum_product]
      simp only [coefficient, Finset.sum_mul_sum]

end Legacy.TorusEndpoint.FiniteAtomCoefficients

#print axioms Legacy.TorusEndpoint.FiniteAtomCoefficients.mem_decompositions_iff
#print axioms Legacy.TorusEndpoint.FiniteAtomCoefficients.coefficient_independent_weights
#print axioms Legacy.TorusEndpoint.FiniteAtomCoefficients.coefficient_nonneg
#print axioms Legacy.TorusEndpoint.FiniteAtomCoefficients.coefficient_zero
#print axioms Legacy.TorusEndpoint.FiniteAtomCoefficients.single_atom_lower_bound
#print axioms Legacy.TorusEndpoint.FiniteAtomCoefficients.coefficient_add_parameter_word_cuts
#print axioms Legacy.TorusEndpoint.FiniteAtomCoefficients.mem_splitPairs_iff
#print axioms Legacy.TorusEndpoint.FiniteAtomCoefficients.coefficient_add_parameter_word_pairs
#print axioms Legacy.TorusEndpoint.FiniteAtomCoefficients.coefficient_convolution
#print axioms Legacy.TorusEndpoint.FiniteAtomCoefficients.coefficient_product_zero_outside
#print axioms Legacy.TorusEndpoint.FiniteAtomCoefficients.coefficient_pos_of_decomposition
