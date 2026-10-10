module

public import BecknerOnofri.V2.IntervalKernel.Tight

@[expose] public section

/-!
# Register operations of the kernel interpreter

A register is `packList l` with `l` of length `28` (mid half, then box half).  `finish` assembles
the result of an operation from its two halves and the mean-value tightening.  The five lemmas
`mulOp_spec`, `addOp_spec`, `negOp_spec`, `smulOp_spec`, `addcOp_spec` say that a successful fast
operation computes exactly the corresponding `CJet` operation of the reference interpreter.
-/

namespace BecknerOnofri.V2.IntervalKernel

open BecknerOnofri.V2.Interval

/-- A register with field list `l`. -/
def RegL (r : Nat) (l : List Nat) : Prop := l.length = 28 ∧ (∀ x ∈ l, x ≤ TWOB) ∧ r = packList l

/-- The centred jet stored in a register. -/
def decCJet (r : Nat) : CJet :=
  ⟨(List.range 7).map fun k => ⟨dec (fld r (2 * k)), dec (fld r (2 * k + 1))⟩,
   (List.range 7).map fun k => ⟨dec (fld r (14 + 2 * k)), dec (fld r (14 + 2 * k + 1))⟩⟩

theorem decCJet_pack {r : Nat} {l : List Nat} (h : RegL r l) :
    decCJet r = ⟨jetL l 0, jetL l 14⟩ := by
  obtain ⟨_, hl, rfl⟩ := h
  unfold decCJet jetL
  simp only [CJet.mk.injEq]
  constructor
  · apply List.map_congr_left
    intro k _
    rw [ivL_pack hl]; simp
  · apply List.map_congr_left
    intro k _
    rw [ivL_pack hl]

theorem getD_append_left' (l1 l2 : List Nat) (i : Nat) (h : i < l1.length) :
    (l1 ++ l2).getD i 0 = l1.getD i 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_append_right' (l1 l2 : List Nat) (i : Nat) (h : l1.length ≤ i) :
    (l1 ++ l2).getD i 0 = l2.getD (i - l1.length) 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_right h]

theorem jetL_append_left (l1 l2 : List Nat) (h : l1.length = 14) : jetL (l1 ++ l2) 0 = jetL l1 0 := by
  unfold jetL
  apply List.map_congr_left
  intro k hk
  have hk' : k < 7 := List.mem_range.1 hk
  unfold ivL
  rw [getD_append_left' _ _ _ (by omega), getD_append_left' _ _ _ (by omega)]

theorem jetL_append_right (l1 l2 : List Nat) (h : l1.length = 14) : jetL (l1 ++ l2) 14 = jetL l2 0 := by
  unfold jetL
  apply List.map_congr_left
  intro k hk
  unfold ivL
  rw [getD_append_right' _ _ _ (by omega), getD_append_right' _ _ _ (by omega), h]
  congr 3 <;> omega

/-- Register from a mid half and a box half. -/
def mkReg (m b : Nat) : Nat := Nat.add m (Nat.shiftLeft b 3584)

theorem mkReg_pack {l1 l2 : List Nat} (h : l1.length = 14) :
    mkReg (packList l1) (packList l2) = packList (l1 ++ l2) := by
  rw [packList_append, h]
  have : 2 ^ (256 * 14) = 2 ^ 3584 := by norm_num
  rw [this]
  show packList l1 + (packList l2 <<< 3584) = _
  rw [Nat.shiftLeft_eq, mul_comm]

/-- Finish an operation: tighten the box and assemble the register. -/
def finish (q1 : Nat) (m b : Nat × Bool) : Option Nat :=
  let t := tightF m.1 b.1 q1
  bif m.2 && b.2 && t.2 then some (mkReg m.1 t.1) else none

theorem finish_spec {x : Ctx} {q1 : Nat} (hrad : x.rad = ⟨-(q1 : Int), q1⟩) {m b : Nat × Bool}
    {A B : Jet}
    (hm : m.2 = true → ∃ l, HalfL m.1 l ∧ jetL l 0 = A)
    (hb : b.2 = true → ∃ l, HalfL b.1 l ∧ jetL l 0 = B) {r : Nat}
    (h : finish q1 m b = some r) :
    ∃ l, RegL r l ∧ CJet.build x A B = some (decCJet r) := by
  unfold finish at h
  simp only [] at h
  cases hc : (m.2 && b.2 && (tightF m.1 b.1 q1).2)
  · rw [hc] at h; simp at h
  · rw [hc] at h
    simp only [Bool.cond_true, Option.some.injEq] at h
    simp only [Bool.and_eq_true] at hc
    obtain ⟨⟨hm2, hb2⟩, ht⟩ := hc
    obtain ⟨lm, ⟨hlen, hbd, hpk⟩, hA⟩ := hm hm2
    obtain ⟨lb, ⟨hlen', hbd', hpk'⟩, hB⟩ := hb hb2
    subst hA hB
    rw [hpk, hpk'] at ht h
    have htight := tightF_spec hbd hbd' hrad ht
    obtain ⟨⟨hlt, hbt, hpt⟩, htight⟩ := htight
    refine ⟨lm ++ tightFields (packList lm) (packList lb) q1, ⟨?_, ?_, ?_⟩, ?_⟩
    · simp [hlen, hlt]
    · intro y hy
      rcases List.mem_append.1 hy with hy | hy
      · exact hbd y hy
      · exact hbt y hy
    · rw [← h, tightF_fst, mkReg_pack hlen]
    · have hreg : RegL r (lm ++ tightFields (packList lm) (packList lb) q1) := by
        refine ⟨by simp [hlen, hlt], ?_, ?_⟩
        · intro y hy
          rcases List.mem_append.1 hy with hy | hy
          · exact hbd y hy
          · exact hbt y hy
        · rw [← h, tightF_fst, mkReg_pack hlen]
      rw [decCJet_pack hreg, jetL_append_left _ _ hlen, jetL_append_right _ _ hlen]
      unfold CJet.build
      rw [htight]
      rfl

/-! ### The five register operations -/

def mulOp (q1 ra rb : Nat) : Option Nat := finish q1 (mulHalf ra rb 0) (mulHalf ra rb 14)
def addOp (q1 ra rb : Nat) : Option Nat := finish q1 (addHalf ra rb 0) (addHalf ra rb 14)
def negOp (q1 ra : Nat) : Option Nat := finish q1 (negHalf ra 0) (negHalf ra 14)
def smulOp (q1 ra cl ch : Nat) : Option Nat :=
  finish q1 (smulHalf ra 0 cl ch) (smulHalf ra 14 cl ch)
def addcOp (q1 ra cl ch : Nat) : Option Nat :=
  finish q1 (addcHalf ra 0 cl ch) (addcHalf ra 14 cl ch)

theorem mulOp_spec {x : Ctx} {q1 : Nat} (hrad : x.rad = ⟨-(q1 : Int), q1⟩) {ra rb : Nat}
    {la lb : List Nat} (hra : RegL ra la) (hrb : RegL rb lb) {r : Nat}
    (h : mulOp q1 ra rb = some r) :
    ∃ l, RegL r l ∧ CJet.mul x (decCJet ra) (decCJet rb) = some (decCJet r) := by
  have hra0 := hra
  have hrb0 := hrb
  obtain ⟨_, hla, rfl⟩ := hra
  obtain ⟨_, hlb, rfl⟩ := hrb
  have := finish_spec (x := x) hrad
    (A := Jet.mul (jetL la 0) (jetL lb 0)) (B := Jet.mul (jetL la 14) (jetL lb 14))
    (fun hok => by
      obtain ⟨l, h1, h2⟩ := mulHalf_spec hla hlb 0 hok; exact ⟨l, h1, h2⟩)
    (fun hok => by
      obtain ⟨l, h1, h2⟩ := mulHalf_spec hla hlb 14 hok; exact ⟨l, h1, h2⟩) h
  obtain ⟨l, hl, hb⟩ := this
  refine ⟨l, hl, ?_⟩
  rw [decCJet_pack hra0, decCJet_pack hrb0]
  exact hb

theorem addOp_spec {x : Ctx} {q1 : Nat} (hrad : x.rad = ⟨-(q1 : Int), q1⟩) {ra rb : Nat}
    {la lb : List Nat} (hra : RegL ra la) (hrb : RegL rb lb) {r : Nat}
    (h : addOp q1 ra rb = some r) :
    ∃ l, RegL r l ∧ CJet.add x (decCJet ra) (decCJet rb) = some (decCJet r) := by
  have hra0 := hra
  have hrb0 := hrb
  obtain ⟨_, hla, rfl⟩ := hra
  obtain ⟨_, hlb, rfl⟩ := hrb
  have := finish_spec (x := x) hrad
    (A := Jet.add (jetL la 0) (jetL lb 0)) (B := Jet.add (jetL la 14) (jetL lb 14))
    (fun hok => by
      obtain ⟨l, h1, h2⟩ := addHalf_spec hla hlb 0 hok; exact ⟨l, h1, h2⟩)
    (fun hok => by
      obtain ⟨l, h1, h2⟩ := addHalf_spec hla hlb 14 hok; exact ⟨l, h1, h2⟩) h
  obtain ⟨l, hl, hb⟩ := this
  refine ⟨l, hl, ?_⟩
  rw [decCJet_pack hra0, decCJet_pack hrb0]
  exact hb

theorem negOp_spec {x : Ctx} {q1 : Nat} (hrad : x.rad = ⟨-(q1 : Int), q1⟩) {ra : Nat}
    {la : List Nat} (hra : RegL ra la) {r : Nat} (h : negOp q1 ra = some r) :
    ∃ l, RegL r l ∧ CJet.neg x (decCJet ra) = some (decCJet r) := by
  have hra0 := hra
  obtain ⟨_, hla, rfl⟩ := hra
  have := finish_spec (x := x) hrad
    (A := Jet.neg (jetL la 0)) (B := Jet.neg (jetL la 14))
    (fun hok => by
      obtain ⟨l, h1, h2⟩ := negHalf_spec hla 0 hok; exact ⟨l, h1, h2⟩)
    (fun hok => by
      obtain ⟨l, h1, h2⟩ := negHalf_spec hla 14 hok; exact ⟨l, h1, h2⟩) h
  obtain ⟨l, hl, hb⟩ := this
  refine ⟨l, hl, ?_⟩
  rw [decCJet_pack hra0]
  exact hb

theorem smulOp_spec {x : Ctx} {q1 : Nat} (hrad : x.rad = ⟨-(q1 : Int), q1⟩) {ra cl ch : Nat}
    {la : List Nat} (hra : RegL ra la) (hcl : cl ≤ TWOB) (hch : ch ≤ TWOB) {r : Nat}
    (h : smulOp q1 ra cl ch = some r) :
    ∃ l, RegL r l ∧ CJet.smul x (decCJet ra) ⟨dec cl, dec ch⟩ = some (decCJet r) := by
  have hra0 := hra
  obtain ⟨_, hla, rfl⟩ := hra
  have := finish_spec (x := x) hrad
    (A := Jet.smul (jetL la 0) ⟨dec cl, dec ch⟩) (B := Jet.smul (jetL la 14) ⟨dec cl, dec ch⟩)
    (fun hok => by
      obtain ⟨l, h1, h2⟩ := smulHalf_spec hla 0 hcl hch hok; exact ⟨l, h1, h2⟩)
    (fun hok => by
      obtain ⟨l, h1, h2⟩ := smulHalf_spec hla 14 hcl hch hok; exact ⟨l, h1, h2⟩) h
  obtain ⟨l, hl, hb⟩ := this
  refine ⟨l, hl, ?_⟩
  rw [decCJet_pack hra0]
  exact hb

theorem addcOp_spec {x : Ctx} {q1 : Nat} (hrad : x.rad = ⟨-(q1 : Int), q1⟩) {ra cl ch : Nat}
    {la : List Nat} (hra : RegL ra la) {r : Nat}
    (h : addcOp q1 ra cl ch = some r) :
    ∃ l, RegL r l ∧ CJet.addc x (decCJet ra) ⟨dec cl, dec ch⟩ = some (decCJet r) := by
  have hra0 := hra
  obtain ⟨_, hla, rfl⟩ := hra
  have := finish_spec (x := x) hrad
    (A := Jet.add (jetL la 0) (Jet.const ⟨dec cl, dec ch⟩))
    (B := Jet.add (jetL la 14) (Jet.const ⟨dec cl, dec ch⟩))
    (fun hok => by
      obtain ⟨l, h1, h2⟩ := addcHalf_spec hla 0 hok; exact ⟨l, h1, h2⟩)
    (fun hok => by
      obtain ⟨l, h1, h2⟩ := addcHalf_spec hla 14 hok; exact ⟨l, h1, h2⟩) h
  obtain ⟨l, hl, hb⟩ := this
  refine ⟨l, hl, ?_⟩
  rw [decCJet_pack hra0]
  exact hb

end BecknerOnofri.V2.IntervalKernel
