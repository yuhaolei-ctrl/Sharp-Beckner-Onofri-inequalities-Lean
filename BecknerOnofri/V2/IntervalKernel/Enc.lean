module

public import BecknerOnofri.V2.IntervalKernel.Reg

@[expose] public section

/-!
# Encoding of reference registers as packed registers

`encode c` packs a reference centred jet; `encode_spec` says that the packed register decodes back
to `c`.  `encHalf` does the same for one half (a jet) and is used by the operations that compute a
jet with the reference-free code and then tighten it in packed form.
-/

namespace BecknerOnofri.V2.IntervalKernel

open BecknerOnofri.V2.Interval

/-! ### Encoding of reference registers -/

/-- The biased field of an integer, if it is in range. -/
def fieldOf (v : Int) : Option Nat :=
  if 0 ≤ v + (B : Int) ∧ v + (B : Int) ≤ (TWOB : Int) then some (v + (B : Int)).toNat else none

theorem fieldOf_spec {v : Int} {f : Nat} (h : fieldOf v = some f) : f ≤ TWOB ∧ dec f = v := by
  unfold fieldOf at h
  split_ifs at h with hh
  · obtain rfl := Option.some.inj h
    unfold dec
    refine ⟨by omega, by omega⟩

def encIv (iv : Iv) : Option (Nat × Nat) :=
  match fieldOf iv.lo, fieldOf iv.hi with
  | some a, some b => some (a, b)
  | _, _ => none

theorem encIv_spec {iv : Iv} {a b : Nat} (h : encIv iv = some (a, b)) :
    a ≤ TWOB ∧ b ≤ TWOB ∧ (⟨dec a, dec b⟩ : Iv) = iv := by
  unfold encIv at h
  split at h
  · rename_i a' b' ha hb
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    obtain ⟨h1, h2⟩ := fieldOf_spec ha
    obtain ⟨h3, h4⟩ := fieldOf_spec hb
    refine ⟨h1, h3, ?_⟩
    rw [h2, h4]
  · simp at h

def encJetL : Jet → Option (List Nat)
  | [] => some []
  | iv :: rest =>
    match encIv iv, encJetL rest with
    | some (a, b), some l => some (a :: b :: l)
    | _, _ => none

theorem encJetL_spec : ∀ (j : Jet) (l : List Nat), encJetL j = some l →
    l.length = 2 * j.length ∧ (∀ x ∈ l, x ≤ TWOB) ∧
      ∀ k, k < j.length → ivL l (2 * k) = j.getD k Iv.zero
  | [], l, h => by
    simp only [encJetL, Option.some.injEq] at h
    subst h
    simp
  | iv :: rest, l, h => by
    unfold encJetL at h
    split at h
    · rename_i a b l' ha hl
      obtain rfl := Option.some.inj h
      obtain ⟨h1, h2, h3⟩ := encIv_spec ha
      obtain ⟨k1, k2, k3⟩ := encJetL_spec rest l' hl
      refine ⟨by simp [k1]; ring, ?_, ?_⟩
      · intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | rfl | hx
        · exact h1
        · exact h2
        · exact k2 x hx
      · intro k hk
        rcases k with _ | k
        · simp [ivL, h3.symm]
        · have hk' : k < rest.length := by simpa using hk
          have := k3 k hk'
          unfold ivL at this ⊢
          simp only [List.getD_cons_succ]
          rw [show 2 * (k + 1) = 2 * k + 2 by ring]
          simpa using this
    · simp at h

/-- Encode a reference register (fails if a field is out of range or a jet is not of length 7). -/
def encode (c : CJet) : Option Nat :=
  match encJetL c.mid, encJetL c.box with
  | some lm, some lb => bif Nat.beq lm.length 14 && Nat.beq lb.length 14 then some (packList (lm ++ lb)) else none
  | _, _ => none

theorem jetL_of_enc {j : Jet} {l : List Nat} (hj : j.length = 7) (h : encJetL j = some l) :
    jetL l 0 = j := by
  obtain ⟨k1, k2, k3⟩ := encJetL_spec j l h
  unfold jetL
  apply List.ext_getElem
  · simp [hj]
  · intro n h1 h2
    simp only [List.getElem_map, List.getElem_range]
    have hn : n < 7 := by simpa using h1
    have := k3 n (by omega)
    rw [Nat.zero_add, this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show n < j.length by omega)]

theorem encode_spec {c : CJet} {r : Nat} (h : encode c = some r) :
    (∃ l, RegL r l) ∧ decCJet r = c := by
  unfold encode at h
  split at h
  · rename_i lm lb hm hb
    cases hc : (Nat.beq lm.length 14 && Nat.beq lb.length 14)
    · rw [hc] at h; simp at h
    · rw [hc] at h
      simp only [Bool.cond_true, Option.some.injEq] at h
      simp only [Bool.and_eq_true] at hc
      have hl1 : lm.length = 14 := Nat.eq_of_beq_eq_true hc.1
      have hl2 : lb.length = 14 := Nat.eq_of_beq_eq_true hc.2
      obtain ⟨m1, m2, m3⟩ := encJetL_spec _ _ hm
      obtain ⟨b1, b2, b3⟩ := encJetL_spec _ _ hb
      have hreg : RegL r (lm ++ lb) := by
        refine ⟨by simp [hl1, hl2], ?_, h.symm⟩
        intro x hx
        rcases List.mem_append.1 hx with hx | hx
        · exact m2 x hx
        · exact b2 x hx
      refine ⟨⟨_, hreg⟩, ?_⟩
      have hmid : c.mid.length = 7 := by omega
      have hbox : c.box.length = 7 := by omega
      rw [decCJet_pack hreg, jetL_append_left _ _ hl1, jetL_append_right _ _ hl1,
        jetL_of_enc hmid hm, jetL_of_enc hbox hb]
  · simp at h

end BecknerOnofri.V2.IntervalKernel
