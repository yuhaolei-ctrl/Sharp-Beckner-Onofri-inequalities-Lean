import Legacy.TorusEndpoint.FiniteCone

/-! The lexicographic positive cone partitions the nonzero lattice into two halves. -/

namespace Legacy.TorusEndpoint.FiniteCone

theorem positive_of_head_zero {d : Nat} {x : Vec (d + 1)}
    (hz : x 0 = 0) (ht : LexPositive (tail x)) : LexPositive x := by
  rcases ht with ⟨j, hj, hprior⟩
  refine ⟨j.succ, hj, ?_⟩
  intro i
  refine Fin.cases ?_ (fun l => ?_) i
  · intro _
    exact hz
  · intro hl
    exact hprior l (by
      change l.val + 1 < j.val + 1 at hl
      change l.val < j.val
      omega)

theorem zero_or_positive_or_negative (d : Nat) (x : Vec d) :
    x = zero ∨ LexPositive x ∨ LexPositive (neg x) := by
  induction d with
  | zero =>
    exact Or.inl (funext fun i => Fin.elim0 i)
  | succ d ih =>
    by_cases hpos : 0 < x 0
    · exact Or.inr (Or.inl ⟨0, hpos, by
        intro i hi
        change i.val < 0 at hi
        omega⟩)
    · by_cases hneg : x 0 < 0
      · refine Or.inr (Or.inr ⟨0, ?_, ?_⟩)
        · dsimp [neg]
          omega
        · intro i hi
          change i.val < 0 at hi
          omega
      · have hz : x 0 = 0 := by omega
        rcases ih (tail x) with ht | ht | ht
        · left
          funext i
          refine Fin.cases ?_ (fun j => ?_) i
          · exact hz
          · exact congrFun ht j
        · exact Or.inr (Or.inl (positive_of_head_zero hz ht))
        · apply Or.inr ∘ Or.inr
          exact positive_of_head_zero (by simp [neg, hz]) ht

theorem positive_or_negative_of_ne_zero {d : Nat} {x : Vec d}
    (hx : x ≠ zero) : LexPositive x ∨ LexPositive (neg x) := by
  rcases zero_or_positive_or_negative d x with h | h
  · exact False.elim (hx h)
  · exact h

end Legacy.TorusEndpoint.FiniteCone
