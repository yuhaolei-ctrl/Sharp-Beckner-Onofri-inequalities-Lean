module

public import BecknerOnofri.V2.IntervalKernel.Pack

@[expose] public section

/-!
# A persistent register file (binary trie of depth 11)

`Trie.get t 11 i` / `Trie.set t 11 i v` implement a finite map `{0,…,2047} → Nat`.  The smart
constructors `mkL`/`mkR` and `leafF` force the freshly built subtree/leaf to a constructor/literal,
so that no chain of unevaluated terms accumulates in the kernel.
-/

namespace BecknerOnofri.V2.IntervalKernel

inductive Trie
  | empty
  | leaf (v : Nat)
  | node (l r : Trie)

namespace Trie

/-- Forced leaf. -/
def leafF (v : Nat) : Trie := bif Nat.ble 0 v then leaf v else leaf v

/-- `node a b` with `a` forced. -/
def mkL (a b : Trie) : Trie :=
  match a with
  | empty => node empty b
  | leaf v => node (leaf v) b
  | node l r => node (node l r) b

/-- `node a b` with `b` forced. -/
def mkR (a b : Trie) : Trie :=
  match b with
  | empty => node a empty
  | leaf v => node a (leaf v)
  | node l r => node a (node l r)

def get : Trie → Nat → Nat → Option Nat
  | leaf v, 0, _ => some v
  | node l r, d + 1, n =>
    bif Nat.beq (Nat.mod n 2) 0 then l.get d (Nat.div n 2) else r.get d (Nat.div n 2)
  | _, _, _ => none

def set : Trie → Nat → Nat → Nat → Trie
  | _, 0, _, v => leafF v
  | node l r, d + 1, n, v =>
    bif Nat.beq (Nat.mod n 2) 0 then mkL (l.set d (Nat.div n 2) v) r
    else mkR l (r.set d (Nat.div n 2) v)
  | _, d + 1, n, v =>
    bif Nat.beq (Nat.mod n 2) 0 then mkL (empty.set d (Nat.div n 2) v) empty
    else mkR empty (empty.set d (Nat.div n 2) v)

theorem leafF_eq (v : Nat) : leafF v = leaf v := by
  unfold leafF; cases Nat.ble 0 v <;> rfl

theorem mkL_eq (a b : Trie) : mkL a b = node a b := by
  cases a <;> rfl

theorem mkR_eq (a b : Trie) : mkR a b = node a b := by
  cases b <;> rfl

theorem get_empty (d n : Nat) : empty.get d n = none := by
  cases d <;> rfl

theorem beq_mod_two (n : Nat) : Nat.beq (Nat.mod n 2) 0 = decide (n % 2 = 0) := by
  show Nat.beq (n % 2) 0 = _
  cases h : Nat.beq (n % 2) 0
  · have := Nat.ne_of_beq_eq_false h
    simp [this]
  · have := Nat.eq_of_beq_eq_true h
    simp [this]

theorem div_two (m : Nat) : Nat.div m 2 = m / 2 := rfl

theorem get_set : ∀ (d : Nat) (t : Trie) (n m v : Nat), n < 2 ^ d → m < 2 ^ d →
    (t.set d n v).get d m = if m = n then some v else t.get d m
  | 0, t, n, m, v, hn, hm => by
    have hn0 : n = 0 := by simpa using hn
    have hm0 : m = 0 := by simpa using hm
    subst hn0 hm0
    simp [set, leafF_eq, get]
  | d + 1, t, n, m, v, hn, hm => by
    have hn' : n / 2 < 2 ^ d := by
      rw [pow_succ] at hn; omega
    have hm' : m / 2 < 2 ^ d := by
      rw [pow_succ] at hm; omega
    have ih := fun t => get_set d t (n / 2) (m / 2) v hn' hm'
    have key : ∀ (l r : Trie),
        (bif Nat.beq (Nat.mod n 2) 0 then mkL (l.set d (Nat.div n 2) v) r
          else mkR l (r.set d (Nat.div n 2) v)).get (d + 1) m
        = if m = n then some v else (node l r).get (d + 1) m := by
      intro l r
      rw [beq_mod_two]
      by_cases h1 : n % 2 = 0
      · simp only [h1, decide_true, Bool.cond_true, mkL_eq]
        by_cases h2 : m % 2 = 0
        · simp only [get, beq_mod_two, h2, decide_true, Bool.cond_true]
          show (l.set d (n / 2) v).get d (m / 2) = _
          rw [ih]
          by_cases h3 : m / 2 = n / 2
          · have : m = n := by omega
            simp [this]
          · have : ¬ m = n := by omega
            simp [this, h3, div_two]
        · simp only [get, beq_mod_two, h2, decide_false, Bool.cond_false]
          have : ¬ m = n := by omega
          simp [this]
      · simp only [h1, decide_false, Bool.cond_false, mkR_eq]
        by_cases h2 : m % 2 = 0
        · simp only [get, beq_mod_two, h2, decide_true, Bool.cond_true]
          have : ¬ m = n := by omega
          simp [this]
        · simp only [get, beq_mod_two, h2, decide_false, Bool.cond_false]
          show (r.set d (n / 2) v).get d (m / 2) = _
          rw [ih]
          by_cases h3 : m / 2 = n / 2
          · have : m = n := by omega
            simp [this]
          · have : ¬ m = n := by omega
            simp [this, h3, div_two]
    cases t with
    | node l r => exact key l r
    | empty =>
      have := key empty empty
      simp only [set] at this ⊢
      rw [this]
      simp [get]
    | leaf w =>
      have := key empty empty
      simp only [set] at this ⊢
      rw [this]
      simp [get]

end Trie

end BecknerOnofri.V2.IntervalKernel
