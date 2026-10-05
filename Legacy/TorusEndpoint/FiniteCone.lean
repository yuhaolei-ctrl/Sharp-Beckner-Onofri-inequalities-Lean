import Std

/-!
# Finite atoms in the lexicographic positive cone

The lattice is `Fin d → Int`. Positivity means that the first nonzero
coordinate is positive. The finite-atom hypotheses in the final theorems are
essential; no local-finiteness claim is made about the whole infinite cone.
This module contains algebra only, with no Fourier or analytic premises.
-/

namespace Legacy.TorusEndpoint.FiniteCone

set_option maxRecDepth 2000
set_option maxHeartbeats 800000

abbrev Vec (d : Nat) := Fin d → Int

def zero {d : Nat} : Vec d := fun _ => 0
def add {d : Nat} (x y : Vec d) : Vec d := fun i => x i + y i
def neg {d : Nat} (x : Vec d) : Vec d := fun i => -(x i)
def smul {d : Nat} (n : Int) (x : Vec d) : Vec d := fun i => n * x i

/-- Coordinates are inspected in increasing order, starting at index zero. -/
def LexPositive {d : Nat} (x : Vec d) : Prop :=
  ∃ j : Fin d, 0 < x j ∧ ∀ i : Fin d, i < j → x i = 0

theorem not_positive_zero (d : Nat) : ¬ LexPositive (zero : Vec d) := by
  rintro ⟨j, hj, _⟩
  simp [zero] at hj

theorem positive_ne_zero {d : Nat} {x : Vec d} (hx : LexPositive x) : x ≠ zero := by
  intro h
  exact not_positive_zero d (h ▸ hx)

theorem positive_add {d : Nat} {x y : Vec d}
    (hx : LexPositive x) (hy : LexPositive y) : LexPositive (add x y) := by
  rcases hx with ⟨i, hi, hiz⟩
  rcases hy with ⟨j, hj, hjz⟩
  by_cases hij : i < j
  · refine ⟨i, ?_, ?_⟩
    · have h := hjz i hij
      dsimp [add]
      omega
    · intro k hk
      have h1 := hiz k hk
      have h2 := hjz k (by omega)
      simp [add, h1, h2]
  · by_cases hji : j < i
    · refine ⟨j, ?_, ?_⟩
      · have h := hiz j hji
        dsimp [add]
        omega
      · intro k hk
        have h1 := hiz k (by omega)
        have h2 := hjz k hk
        simp [add, h1, h2]
    · have he : i = j := Fin.ext (by omega)
      subst j
      refine ⟨i, ?_, ?_⟩
      · dsimp [add]
        omega
      · intro k hk
        simp [add, hiz k hk, hjz k hk]

theorem positive_not_neg {d : Nat} {x : Vec d} (hx : LexPositive x) :
    ¬ LexPositive (neg x) := by
  intro hn
  have hp := positive_add hx hn
  have hz : add x (neg x) = zero := by
    funext i
    dsimp [add, neg, zero]
    omega
  exact not_positive_zero d (hz ▸ hp)

def sumVec {d : Nat} : List (Vec d) → Vec d
  | [] => zero
  | x :: xs => add x (sumVec xs)

theorem positive_sum {d : Nat} (xs : List (Vec d))
    (hne : xs ≠ []) (hpos : ∀ x ∈ xs, LexPositive x) : LexPositive (sumVec xs) := by
  induction xs with
  | nil => exact False.elim (hne rfl)
  | cons x xs ih =>
    have hx : LexPositive x := hpos x (by simp)
    cases xs with
    | nil =>
      have he : sumVec [x] = x := by
        funext i
        dsimp [sumVec, add, zero]
        omega
      rw [he]
      exact hx
    | cons y ys =>
      apply positive_add hx
      exact ih (by simp) (by
        intro z hz
        exact hpos z (by simp [hz]))

theorem nonempty_positive_sum_ne_zero {d : Nat} (xs : List (Vec d))
    (hne : xs ≠ []) (hpos : ∀ x ∈ xs, LexPositive x) : sumVec xs ≠ zero :=
  positive_ne_zero (positive_sum xs hne hpos)

def tail {d : Nat} (x : Vec (d + 1)) : Vec d := fun i => x i.succ
def cons {d : Nat} (a : Int) (x : Vec d) : Vec (d + 1) := Fin.cases a x

theorem positive_head_nonneg {d : Nat} {x : Vec (d + 1)}
    (hx : LexPositive x) : 0 ≤ x 0 := by
  rcases hx with ⟨j, hj, hz⟩
  by_cases hj0 : j = 0
  · subst j
    omega
  · have hlt : (0 : Fin (d + 1)) < j := by
      have : j.val ≠ 0 := by
        intro h
        exact hj0 (Fin.ext h)
      change 0 < j.val
      omega
    have := hz 0 hlt
    omega

theorem positive_tail_of_head_zero {d : Nat} {x : Vec (d + 1)}
    (hx : LexPositive x) (hzero : x 0 = 0) : LexPositive (tail x) := by
  rcases hx with ⟨j, hj, hz⟩
  have jpos : 0 < j.val := by
    by_cases h : 0 < j.val
    · exact h
    · have he : j = 0 := Fin.ext (by change j.val = 0; omega)
      subst j
      omega
  let k : Fin d := ⟨j.val - 1, by omega⟩
  have hk : k.succ = j := Fin.ext (by dsimp [k]; omega)
  refine ⟨k, ?_, ?_⟩
  · simpa [tail, hk] using hj
  · intro i hi
    apply hz i.succ
    have hival : i.val < j.val - 1 := hi
    change i.val + 1 < j.val
    omega

/-- The ordinary integer dot product, recursively in the dimension. -/
def eval : {d : Nat} → Vec d → Vec d → Int
  | 0, _, _ => 0
  | _ + 1, w, x => w 0 * x 0 + eval (tail w) (tail x)

theorem eval_zero {d : Nat} (w : Vec d) : eval w zero = 0 := by
  induction d with
  | zero => rfl
  | succ d ih =>
    change w 0 * 0 + eval (tail w) zero = 0
    rw [ih]
    omega

theorem eval_add {d : Nat} (w x y : Vec d) :
    eval w (add x y) = eval w x + eval w y := by
  induction d with
  | zero => rfl
  | succ d ih =>
    have ht : tail (add x y) = add (tail x) (tail y) := rfl
    simp only [eval, add, ht, ih, Int.mul_add]
    omega

theorem eval_smul {d : Nat} (w x : Vec d) (n : Int) :
    eval w (smul n x) = n * eval w x := by
  induction d with
  | zero => simp [eval]
  | succ d ih =>
    have ht : tail (smul n x) = smul n (tail x) := rfl
    simp only [eval, smul, ht, ih, Int.mul_add]
    rw [← Int.mul_assoc, Int.mul_comm (w 0) n, Int.mul_assoc]

/-- A finite, nonnegative integer budget for the values of a function. -/
def absBudget {α : Type} (f : α → Int) (xs : List α) : Nat :=
  (xs.map (fun x => (f x).natAbs)).sum

theorem natAbs_le_budget {α : Type} (f : α → Int) (xs : List α)
    {x : α} (hx : x ∈ xs) : (f x).natAbs ≤ absBudget f xs := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
    rcases List.mem_cons.mp hx with hxy | hxs
    · subst y
      simp only [absBudget, List.map_cons, List.sum_cons]
      omega
    · have h := ih hxs
      change (f x).natAbs ≤ (f y).natAbs + absBudget f ys
      omega

theorem neg_budget_le {α : Type} (f : α → Int) (xs : List α)
    {x : α} (hx : x ∈ xs) : -(absBudget f xs : Int) ≤ f x := by
  have hb := natAbs_le_budget f xs hx
  have ha : -(f x) ≤ ((f x).natAbs : Int) := by
    simpa only [Int.natAbs_neg] using (Int.le_natAbs (a := -(f x)))
  omega

/--
Every finite list of lexicographically positive atoms admits an integer-valued
linear functional strictly positive on all its atoms. There is no assumption
of local finiteness for the entire infinite cone.
-/
theorem exists_positive_weights (d : Nat) (atoms : List (Vec d))
    (hpos : ∀ x ∈ atoms, LexPositive x) :
    ∃ w : Vec d, ∀ x ∈ atoms, 0 < eval w x := by
  induction d with
  | zero =>
    refine ⟨zero, ?_⟩
    intro x hx
    rcases hpos x hx with ⟨j, _, _⟩
    exact Fin.elim0 j
  | succ d ih =>
    let small : List (Vec d) :=
      (atoms.filter (fun x => decide (x 0 = 0))).map tail
    have hsmall : ∀ y ∈ small, LexPositive y := by
      intro y hy
      rcases List.mem_map.mp hy with ⟨x, hx, hxy⟩
      rcases List.mem_filter.mp hx with ⟨hxa, hxzero⟩
      have hzero : x 0 = 0 := by simpa using hxzero
      subst y
      exact positive_tail_of_head_zero (hpos x hxa) hzero
    obtain ⟨w, hw⟩ := ih small hsmall
    let f : Vec (d + 1) → Int := fun x => eval w (tail x)
    let B : Nat := absBudget f atoms
    let W : Int := (B : Int) + 1
    refine ⟨cons W w, ?_⟩
    intro x hx
    change 0 < W * x 0 + eval w (tail x)
    by_cases hzero : x 0 = 0
    · have hmem : tail x ∈ small := by
        apply List.mem_map.mpr
        refine ⟨x, ?_, rfl⟩
        apply List.mem_filter.mpr
        exact ⟨hx, by simpa using hzero⟩
      have h := hw (tail x) hmem
      rw [hzero]
      omega
    · have hhead := positive_head_nonneg (hpos x hx)
      have hone : (1 : Int) ≤ x 0 := by omega
      have hW : 0 ≤ W := by dsimp [W]; omega
      have hmul : W ≤ W * x 0 := by
        simpa using Int.mul_le_mul_of_nonneg_left hone hW
      have htail : -(B : Int) ≤ eval w (tail x) := neg_budget_le f atoms hx
      dsimp [W] at hmul
      dsimp [W]
      omega

theorem eval_sum {d : Nat} (w : Vec d) (xs : List (Vec d)) :
    eval w (sumVec xs) = (xs.map (eval w)).sum := by
  induction xs with
  | nil => exact eval_zero w
  | cons x xs ih =>
    change eval w (add x (sumVec xs)) = eval w x + (xs.map (eval w)).sum
    rw [eval_add, ih]

/-- Integer-valued strict positivity supplies the uniform atom lower bound 1. -/
theorem length_le_eval_sum {d : Nat} (w : Vec d) (xs : List (Vec d))
    (hpos : ∀ x ∈ xs, 0 < eval w x) :
    (xs.length : Int) ≤ eval w (sumVec xs) := by
  induction xs with
  | nil => simp [sumVec, eval_zero]
  | cons x xs ih =>
    have hx : 0 < eval w x := hpos x (by simp)
    have ht : (xs.length : Int) ≤ eval w (sumVec xs) := ih (by
      intro y hy
      exact hpos y (by simp [hy]))
    change ((xs.length + 1 : Nat) : Int) ≤ eval w (add x (sumVec xs))
    rw [eval_add]
    omega

/--
For a fixed finite atom list, a single functional bounds the length of every
decomposition of every output vector. The bound depends on the finite list.
-/
theorem finite_atom_decomposition_bound (d : Nat) (atoms : List (Vec d))
    (hpos : ∀ x ∈ atoms, LexPositive x) :
    ∃ w : Vec d, (∀ x ∈ atoms, 0 < eval w x) ∧
      ∀ (k : Vec d) (xs : List (Vec d)),
        (∀ x ∈ xs, x ∈ atoms) → sumVec xs = k → (xs.length : Int) ≤ eval w k := by
  obtain ⟨w, hw⟩ := exists_positive_weights d atoms hpos
  refine ⟨w, hw, ?_⟩
  intro k xs hmem hsum
  have hb := length_le_eval_sum w xs (fun x hx => hw x (hmem x hx))
  rw [hsum] at hb
  exact hb

/-- All words of length at most `n` in a finite alphabet (repetitions allowed). -/
def wordsAtMost {α : Type} (atoms : List α) : Nat → List (List α)
  | 0 => [[]]
  | n + 1 => [] :: atoms.flatMap
      (fun a => (wordsAtMost atoms n).map (fun xs => a :: xs))

theorem mem_wordsAtMost {α : Type} (atoms : List α) (n : Nat) (xs : List α)
    (hlen : xs.length ≤ n) (hmem : ∀ x ∈ xs, x ∈ atoms) :
    xs ∈ wordsAtMost atoms n := by
  induction n generalizing xs with
  | zero =>
    have he : xs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst xs
    simp [wordsAtMost]
  | succ n ih =>
    cases xs with
    | nil => simp [wordsAtMost]
    | cons x xs =>
      apply List.mem_cons.mpr
      right
      apply List.mem_flatMap.mpr
      refine ⟨x, hmem x (by simp), ?_⟩
      apply List.mem_map.mpr
      refine ⟨xs, ?_, rfl⟩
      apply ih
      · simp only [List.length_cons] at hlen
        omega
      · intro y hy
        exact hmem y (by simp [hy])

/--
Literal finite local-finiteness statement: for each fixed output there is a
finite list containing every ordered decomposition using the given finite
positive atom list. Extra candidates in this list are harmless; the statement
is an explicit finite cover, not a claim about the whole lexicographic cone.
-/
theorem finite_atom_decomposition_candidates (d : Nat) (atoms : List (Vec d))
    (hpos : ∀ x ∈ atoms, LexPositive x) (k : Vec d) :
    ∃ candidates : List (List (Vec d)),
      ∀ xs : List (Vec d), (∀ x ∈ xs, x ∈ atoms) → sumVec xs = k → xs ∈ candidates := by
  obtain ⟨w, _, hbound⟩ := finite_atom_decomposition_bound d atoms hpos
  refine ⟨wordsAtMost atoms (eval w k).toNat, ?_⟩
  intro xs hmem hsum
  have hb := hbound k xs hmem hsum
  apply mem_wordsAtMost atoms (eval w k).toNat xs (by omega) hmem

end Legacy.TorusEndpoint.FiniteCone

#print axioms Legacy.TorusEndpoint.FiniteCone.positive_add
#print axioms Legacy.TorusEndpoint.FiniteCone.nonempty_positive_sum_ne_zero
#print axioms Legacy.TorusEndpoint.FiniteCone.eval_add
#print axioms Legacy.TorusEndpoint.FiniteCone.eval_smul
#print axioms Legacy.TorusEndpoint.FiniteCone.exists_positive_weights
#print axioms Legacy.TorusEndpoint.FiniteCone.finite_atom_decomposition_bound
#print axioms Legacy.TorusEndpoint.FiniteCone.finite_atom_decomposition_candidates
