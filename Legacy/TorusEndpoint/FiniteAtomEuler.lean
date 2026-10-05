import Legacy.TorusEndpoint.D3AxisCoefficient
import Mathlib.Data.List.InsertIdx

/-! The Euler recurrence for the actual finite-atom exponential coefficient.
Marked letters are erased and reinserted bijectively; no recurrence is assumed
for a freely supplied coefficient family. -/

open scoped BigOperators
open Legacy.TorusEndpoint.FiniteCone Legacy.TorusEndpoint.FiniteAtomCoefficients
open Legacy.TorusEndpoint.D3AxisCoefficient

namespace Legacy.TorusEndpoint.FiniteAtomEuler

def markedLetter {d : ℕ} (p : Cut d) : Vec d := p.1[p.2]?.getD zero

abbrev Erasure (d : ℕ) := Σ _ : Vec d, Cut d

def eraseMark {d : ℕ} (p : Cut d) : Erasure d :=
  ⟨markedLetter p, ⟨p.1.eraseIdx p.2, p.2⟩⟩

def insertMark {d : ℕ} (e : Erasure d) : Cut d :=
  ⟨e.2.1.insertIdx e.2.2 e.1, e.2.2⟩

noncomputable def markedDecompositions {d : ℕ}
    (atoms : List (Vec d)) (w k : Vec d) : Finset (Cut d) :=
  (decompositions atoms w k).sigma (fun xs => Finset.range xs.length)

noncomputable def erasedDecompositions {d : ℕ}
    (atoms : List (Vec d)) (w k : Vec d) : Finset (Erasure d) :=
  atoms.toFinset.sigma (fun x =>
    (decompositions atoms w (remainder k x)).sigma
      (fun ys => Finset.range (ys.length + 1)))

theorem insertMark_eraseMark {d : ℕ} (p : Cut d) (hp : p.2 < p.1.length) :
    insertMark (eraseMark p) = p := by
  rcases p with ⟨xs, i⟩
  simp only [insertMark, eraseMark, markedLetter, List.getElem?_eq_getElem hp,
    Option.getD_some, List.insertIdx_eraseIdx_getElem hp]

theorem eraseMark_insertMark {d : ℕ} (e : Erasure d) (he : e.2.2 ≤ e.2.1.length) :
    eraseMark (insertMark e) = e := by
  rcases e with ⟨x, ys, i⟩
  simp [eraseMark, insertMark, markedLetter, List.getElem?_insertIdx_self, he]

theorem sumVec_insertIdx {d : ℕ} (xs : List (Vec d)) (x : Vec d) (i : ℕ)
    (hi : i ≤ xs.length) : sumVec (xs.insertIdx i x) = add x (sumVec xs) := by
  funext j
  simp only [sumVec_coordinate, List.map_insertIdx, add]
  exact List.sum_insertIdx (by simpa using hi) (fun a _ => AddCommute.all _ a)

theorem sumVec_eraseMark {d : ℕ} (p : Cut d) (hp : p.2 < p.1.length) :
    add (markedLetter p) (sumVec (p.1.eraseIdx p.2)) = sumVec p.1 := by
  have hi : p.2 ≤ (p.1.eraseIdx p.2).length := by
    rw [List.length_eraseIdx_of_lt hp]
    omega
  have h := sumVec_insertIdx (p.1.eraseIdx p.2) (markedLetter p) p.2 hi
  have he := congrArg Sigma.fst (insertMark_eraseMark p hp)
  change (p.1.eraseIdx p.2).insertIdx p.2 (markedLetter p) = p.1 at he
  rw [he] at h
  exact h.symm

theorem eraseMark_mem {d : ℕ} (atoms : List (Vec d)) (w k : Vec d)
    (hw : ∀ x ∈ atoms, 0 < eval w x) (p : Cut d)
    (hp : p ∈ markedDecompositions atoms w k) :
    eraseMark p ∈ erasedDecompositions atoms w k := by
  classical
  obtain ⟨hxs, hi⟩ := Finset.mem_sigma.mp hp
  have hil := Finset.mem_range.mp hi
  obtain ⟨hm, hs⟩ := (mem_decompositions_iff atoms w k hw p.1).mp hxs
  have hx : markedLetter p ∈ atoms := by
    unfold markedLetter
    rw [List.getElem?_eq_getElem hil]
    exact hm _ (List.getElem_mem hil)
  apply Finset.mem_sigma.mpr
  refine ⟨List.mem_toFinset.mpr hx, Finset.mem_sigma.mpr ⟨?_, ?_⟩⟩
  · apply (mem_decompositions_iff atoms w _ hw _).mpr
    refine ⟨fun x hx => hm x (List.eraseIdx_subset hx), ?_⟩
    have h := (sumVec_eraseMark p hil).trans hs
    funext j
    have hj := congrFun h j
    dsimp [add, remainder, eraseMark] at *
    omega
  · apply Finset.mem_range.mpr
    dsimp [eraseMark]
    rw [List.length_eraseIdx_of_lt hil]
    omega

theorem insertMark_mem {d : ℕ} (atoms : List (Vec d)) (w k : Vec d)
    (hw : ∀ x ∈ atoms, 0 < eval w x) (e : Erasure d)
    (he : e ∈ erasedDecompositions atoms w k) :
    insertMark e ∈ markedDecompositions atoms w k := by
  classical
  obtain ⟨hx, hrest⟩ := Finset.mem_sigma.mp he
  obtain ⟨hys, hi⟩ := Finset.mem_sigma.mp hrest
  have hil : e.2.2 ≤ e.2.1.length := by
    have h := Finset.mem_range.mp hi
    omega
  obtain ⟨hm, hs⟩ := (mem_decompositions_iff atoms w _ hw e.2.1).mp hys
  apply Finset.mem_sigma.mpr
  refine ⟨?_, Finset.mem_range.mpr ?_⟩
  · apply (mem_decompositions_iff atoms w k hw _).mpr
    refine ⟨?_, ?_⟩
    · intro x hmem
      rcases List.eq_or_mem_of_mem_insertIdx hmem with rfl | hr
      · exact List.mem_toFinset.mp hx
      · exact hm x hr
    · change sumVec (e.2.1.insertIdx e.2.2 e.1) = k
      rw [sumVec_insertIdx _ _ _ hil, hs]
      funext j
      simp [add, remainder]
  · dsimp [insertMark]
    rw [List.length_insertIdx_of_le_length hil]
    omega

theorem wordWeight_insertIdx {d : ℕ} (a : Vec d → ℝ) (x : Vec d)
    (ys : List (Vec d)) (i : ℕ) (hi : i ≤ ys.length) :
    wordWeight a 1 (ys.insertIdx i x) = a x * wordWeight a 1 ys / (ys.length + 1) := by
  have hp : ((ys.insertIdx i x).map a).prod = a x * (ys.map a).prod := by
    rw [List.map_insertIdx]
    exact List.prod_insertIdx (by simpa using hi) (fun b _ => Commute.all _ b)
  rw [wordWeight, List.length_insertIdx_of_le_length hi, hp, wordWeight]
  simp only [scalarExpTerm, one_pow, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
    Nat.cast_one]
  field_simp

theorem sum_coordinate_marks {d : ℕ} (xs : List (Vec d)) (j : Fin d) :
    (∑ i ∈ Finset.range xs.length, ((xs[i]?.getD zero) j : ℝ)) =
      (sumVec xs j : ℝ) := by
  induction xs with
  | nil => simp [sumVec, zero]
  | cons x xs ih =>
    simp only [List.length_cons, Finset.sum_range_succ', List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some, sumVec, add, Int.cast_add]
    rw [ih]
    ring

theorem coefficient_marked_coordinate {d : ℕ}
    (atoms : List (Vec d)) (w k : Vec d) (a : Vec d → ℝ) (j : Fin d)
    (hw : ∀ x ∈ atoms, 0 < eval w x) :
    (k j : ℝ) * coefficient atoms w a 1 k =
      ∑ p ∈ markedDecompositions atoms w k,
        (markedLetter p j : ℝ) * wordWeight a 1 p.1 := by
  simp only [coefficient, markedDecompositions, Finset.sum_sigma, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro xs hx
  have hs := ((mem_decompositions_iff atoms w k hw xs).mp hx).2
  rw [← hs, ← sum_coordinate_marks xs j, Finset.sum_mul]
  rfl

theorem marked_coordinate_reindex {d : ℕ}
    (atoms : List (Vec d)) (w k : Vec d) (a : Vec d → ℝ) (j : Fin d)
    (hw : ∀ x ∈ atoms, 0 < eval w x) :
    (∑ p ∈ markedDecompositions atoms w k,
      (markedLetter p j : ℝ) * wordWeight a 1 p.1) =
    ∑ e ∈ erasedDecompositions atoms w k,
      (e.1 j : ℝ) * a e.1 * wordWeight a 1 e.2.1 / (e.2.1.length + 1) := by
  classical
  apply Finset.sum_bij (fun p _ => eraseMark p)
  · exact fun p hp => eraseMark_mem atoms w k hw p hp
  · intro p hp q hq heq
    have hp' := Finset.mem_range.mp (Finset.mem_sigma.mp hp).2
    have hq' := Finset.mem_range.mp (Finset.mem_sigma.mp hq).2
    exact (insertMark_eraseMark p hp').symm.trans
      ((congrArg insertMark heq).trans (insertMark_eraseMark q hq'))
  · intro e he
    refine ⟨insertMark e, insertMark_mem atoms w k hw e he, ?_⟩
    have hi := Finset.mem_range.mp (Finset.mem_sigma.mp (Finset.mem_sigma.mp he).2).2
    exact eraseMark_insertMark e (by omega)
  · intro p hp
    have hi := Finset.mem_range.mp (Finset.mem_sigma.mp hp).2
    have hle : p.2 ≤ (p.1.eraseIdx p.2).length := by
      rw [List.length_eraseIdx_of_lt hi]
      omega
    have he := congrArg Sigma.fst (insertMark_eraseMark p hi)
    have hweight := wordWeight_insertIdx a (markedLetter p) (p.1.eraseIdx p.2) p.2 hle
    change (p.1.eraseIdx p.2).insertIdx p.2 (markedLetter p) = p.1 at he
    rw [he] at hweight
    change (markedLetter p j : ℝ) * wordWeight a 1 p.1 =
      (markedLetter p j : ℝ) * a (markedLetter p) *
        wordWeight a 1 (p.1.eraseIdx p.2) / ((p.1.eraseIdx p.2).length + 1)
    rw [hweight]
    ring

/-- Exact Euler recurrence, for the complete finite-atom coefficient.
Every atom is counted once even when the original list has repetitions.
The atom weights may be arbitrary real numbers; no positivity premise is
needed for this algebraic identity beyond the separator that ensures finiteness. -/
theorem coefficient_euler_coordinate {d : ℕ}
    (atoms : List (Vec d)) (w k : Vec d) (a : Vec d → ℝ) (j : Fin d)
    (hw : ∀ x ∈ atoms, 0 < eval w x) :
    (k j : ℝ) * coefficient atoms w a 1 k =
      ∑ x ∈ atoms.toFinset, (x j : ℝ) * a x *
        coefficient atoms w a 1 (remainder k x) := by
  rw [coefficient_marked_coordinate atoms w k a j hw,
    marked_coordinate_reindex atoms w k a j hw]
  simp only [erasedDecompositions, Finset.sum_sigma, coefficient, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro ys hy
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  field_simp

/-- Any finite collection of actual coefficients has total mass at most
the exponential of the deduplicated alphabet mass. This is a sum bound,
not a pointwise bound multiplied by the number of output frequencies. -/
theorem coefficient_finite_sum_le_exp_mass {d : ℕ}
    (atoms : List (Vec d)) (w : Vec d) (a : Vec d → ℝ) (s : Finset (Vec d))
    (hw : ∀ x ∈ atoms, 0 < eval w x) (ha : ∀ x ∈ atoms, 0 ≤ a x) :
    (∑ k ∈ s, coefficient atoms w a 1 k) ≤
      Real.exp (∑ x ∈ atoms.toFinset, a x) := by
  classical
  let N := s.sup (fun k => (eval w k).toNat)
  let allWords := (Finset.range (N + 1)).biUnion (exactWords atoms.toFinset)
  have hdisj : Set.PairwiseDisjoint (↑s) (decompositions atoms w) := by
    intro k _ l _ hkl
    apply Finset.disjoint_left.mpr
    intro xs hx hy
    have hk := ((mem_decompositions_iff atoms w k hw xs).mp hx).2
    have hl := ((mem_decompositions_iff atoms w l hw xs).mp hy).2
    exact hkl (hk.symm.trans hl)
  have hsub : s.biUnion (decompositions atoms w) ⊆ allWords := by
    intro xs hx
    obtain ⟨k, hk, hxs⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨hm, hs⟩ := (mem_decompositions_iff atoms w k hw xs).mp hxs
    have hb := length_le_eval_sum w xs (fun x hx => hw x (hm x hx))
    rw [hs] at hb
    have hN : (eval w k).toNat ≤ N := Finset.le_sup (f := fun k => (eval w k).toNat) hk
    apply Finset.mem_biUnion.mpr
    refine ⟨xs.length, Finset.mem_range.mpr (by omega), ?_⟩
    exact (mem_exactWords atoms.toFinset xs.length xs).mpr
      ⟨rfl, fun x hx => List.mem_toFinset.mpr (hm x hx)⟩
  have htotal : (∑ xs ∈ allWords, wordWeight a 1 xs) =
      ∑ n ∈ Finset.range (N + 1), scalarExpTerm (∑ x ∈ atoms.toFinset, a x) n := by
    rw [show allWords = (Finset.range (N + 1)).biUnion (exactWords atoms.toFinset) from rfl,
      Finset.sum_biUnion (exactWords_disjoint_lengths atoms.toFinset (N + 1))]
    exact Finset.sum_congr rfl (fun n _ => exactWords_weight_sum atoms.toFinset a n)
  calc
    _ = ∑ xs ∈ s.biUnion (decompositions atoms w), wordWeight a 1 xs := by
      rw [Finset.sum_biUnion hdisj]
      rfl
    _ ≤ ∑ xs ∈ allWords, wordWeight a 1 xs := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro xs hx _
      obtain ⟨n, _, hxs⟩ := Finset.mem_biUnion.mp hx
      have hm := ((mem_exactWords atoms.toFinset n xs).mp hxs).2
      exact wordWeight_nonneg a (by norm_num) xs
        (fun x hx => ha x (List.mem_toFinset.mp (hm x hx)))
    _ = _ := htotal
    _ ≤ _ := scalarExpTerm_partial_sum_le_exp
      (Finset.sum_nonneg (fun x hx => ha x (List.mem_toFinset.mp hx))) (N + 1)

end Legacy.TorusEndpoint.FiniteAtomEuler
