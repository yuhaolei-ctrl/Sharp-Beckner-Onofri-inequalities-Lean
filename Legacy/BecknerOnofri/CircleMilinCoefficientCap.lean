module

public import Legacy.BecknerOnofri.CircleMilinWords
public import Legacy.D10.CircleEntropy

@[expose] public section

noncomputable section
open scoped BigOperators
namespace Legacy.BecknerOnofri.CircleMilin
open Legacy.TorusEndpoint Legacy.TorusEndpoint.FiniteCone Legacy.TorusEndpoint.FiniteAtomCoefficients

private def frequency (j : ℕ) : Vec 1 := fun _ => j
private def alphabet (n : ℕ) : List (Vec 1) := (List.range' 1 n).map frequency

private theorem frequency_injective : Function.Injective frequency := by
  intro j k he
  have := congrFun he 0
  change (j : ℤ) = k at this
  exact_mod_cast this

private theorem alphabet_pos (n : ℕ) : ∀ x ∈ alphabet n, LexPositive x := by
  intro x hx
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hx
  have hp := List.left_le_of_mem_range' hj
  refine ⟨0, ?_, ?_⟩
  · change (0 : ℤ) < j
    omega
  · intro i hi
    exact False.elim (by omega)

private theorem alphabet_weight (n : ℕ) : ∀ x ∈ alphabet n, 0 < eval (frequency 1) x := by
  intro x hx
  have := Legacy.D10.CircleEntropy.positive_coordinate x (alphabet_pos n x hx)
  simpa [eval,frequency] using this

private theorem sum_frequency (xs : List ℕ) : sumVec (xs.map frequency) = frequency xs.sum := by
  induction xs with
  | nil => rfl
  | cons j xs ih =>
    simp only [List.map_cons,sumVec,List.sum_cons,ih]
    funext i
    simp [add,frequency]

private theorem map_word_mem (n : ℕ) (xs : List ℕ) (hx : xs ∈ words n) :
    xs.map frequency ∈ decompositions (alphabet n) (frequency 1) (frequency n) := by
  rw [mem_decompositions_iff _ _ _ (alphabet_weight n)]
  obtain ⟨hp, hs⟩ := (mem_words_iff _ _).mp hx
  constructor
  · intro x hx
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hx
    apply List.mem_map.mpr
    refine ⟨j,?_,rfl⟩
    have hbound : j ≤ n := by
      have := List.single_le_sum (fun k hk => Nat.zero_le k) j hj
      simpa [hs] using this
    exact List.mem_range'.mpr ⟨j-1,by have := hp j hj; omega,by have := hp j hj; omega⟩
  · rw [sum_frequency,hs]

private theorem words_surjective (n : ℕ) (ys : List (Vec 1))
    (hy : ys ∈ decompositions (alphabet n) (frequency 1) (frequency n)) :
    ∃ xs, xs ∈ words n ∧ xs.map frequency = ys := by
  obtain ⟨hm, hs⟩ := (mem_decompositions_iff _ _ _ (alphabet_weight n) _).mp hy
  let xs := ys.map (fun k => (k 0).toNat)
  have he : xs.map frequency = ys := by
    dsimp [xs]
    rw [List.map_map]
    conv_rhs => rw [← List.map_id ys]
    apply List.map_congr_left
    intro k hk
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp (hm k hk)
    simp [frequency]
  refine ⟨xs,?_,he⟩
  rw [mem_words_iff]
  constructor
  · intro j hj
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hj
    have hp := Legacy.D10.CircleEntropy.positive_coordinate k (alphabet_pos n k (hm k hk))
    omega
  · have hsum := sum_frequency xs
    rw [he,hs] at hsum
    exact (frequency_injective hsum).symm

private theorem wordWeight_map (xs : List ℕ) :
    wordWeight Legacy.D10.CircleEntropy.weight 1 (xs.map frequency) = qWord xs := by
  unfold wordWeight qWord
  simp only [List.length_map,Legacy.TorusEndpoint.scalarExpTerm,one_pow,one_div]
  congr 1
  rw [List.map_map]
  apply congrArg List.prod
  apply List.map_congr_left
  intro j hj
  simp [Legacy.D10.CircleEntropy.weight,frequency]

/-- The reciprocal-letter coefficient is the actual circle exponential
coefficient, so the previously checked circle coefficient cap applies. -/
theorem qCoeff_le_one (n : ℕ) : qCoeff n ≤ 1 := by
  have he : qCoeff n = coefficient (alphabet n) (frequency 1) Legacy.D10.CircleEntropy.weight 1 (frequency n) := by
    unfold qCoeff coefficient
    apply Finset.sum_bij (fun xs _ => xs.map frequency)
    · exact map_word_mem n
    · intro xs hx ys hy he
      exact (List.map_injective_iff.mpr frequency_injective) he
    · intro ys hy
      obtain ⟨xs,hx,he⟩ := words_surjective n ys hy
      exact ⟨xs,hx,he⟩
    · intro xs hx
      exact (wordWeight_map xs).symm
  rw [he]
  exact Legacy.D10.CircleEntropy.coefficient_cap _ _ (alphabet_pos n) (alphabet_weight n) n _ rfl

end Legacy.BecknerOnofri.CircleMilin
