module

public import BecknerOnofri.V2.IntervalKernel.Machine

@[expose] public section

/-!
# The kernel cell checker and its soundness

`fastCheck r k fp outs` runs the compiled program `fp` on the cell `k` of the row `r` with `runF`
and applies the same margin tests as `Row.checkCell` to the output registers `outs`.
`fastCheck_sound`: if it returns `true` (for the compiled reference program), then
`Row.checkCell r k = true`.
-/

namespace BecknerOnofri.V2.IntervalKernel

open BecknerOnofri.V2.Interval

/-- `Row.okAt` with an abstract register. -/
def okAtO (c : Cell) (o : Option CJet) (m : Int × Nat) : Bool :=
  match o with
  | some cj =>
    Row.okLow m (taylorEnclosure cj.mid cj.box (c.hi - c.lo) (2 * c.den))
      (scale.toNat * (2 * c.den) ^ 6)
  | none => false

def okSmallFO (m : Int × Nat) (o : Option CJet) : Bool :=
  match o with
  | some fj => gtQ (fj.box.get 4).lo scale.toNat (1 * m.2 + 10 * m.1) (10 * m.2)
  | none => false

def okSmallVO (m : Int × Nat) (o : Option CJet) : Bool :=
  match o with
  | some vj => ltQ (vj.box.get 4).hi scale.toNat (1 * m.2 - 50 * m.1) (50 * m.2)
  | none => false

def okSmallEO (m : Int × Nat) (o : Option CJet) : Bool :=
  match o with
  | some ej => gtQ (ej.box.get 0).lo scale.toNat m.1 m.2
  | none => false

theorem okAt_eq (c : Cell) (st : RS) (m : Int × Nat) (i : Nat) :
    Row.okAt c st m i = okAtO c (st.get i) m := by
  unfold Row.okAt okAtO; rfl

theorem okSmallF_eq (m : Int × Nat) (st : RS) (i : Nat) :
    Row.okSmallF m st i = okSmallFO m (st.get i) := by
  unfold Row.okSmallF okSmallFO; rfl

theorem okSmallV_eq (m : Int × Nat) (st : RS) (i : Nat) :
    Row.okSmallV m st i = okSmallVO m (st.get i) := by
  unfold Row.okSmallV okSmallVO; rfl

theorem okSmallE_eq (m : Int × Nat) (st : RS) (i : Nat) :
    Row.okSmallE m st i = okSmallEO m (st.get i) := by
  unfold Row.okSmallE okSmallEO; rfl

/-- The kernel checker of one cell. -/
def fastCheck (r : Row) (k : Nat) (fp : List FOp) (outs : Outs) : Bool :=
  let c := r.cell k
  let x := c.ctx
  decide (x.rad.lo = -x.rad.hi ∧ 0 ≤ x.rad.hi) &&
    match runF x x.rad.hi.toNat fp 0 Trie.empty with
    | none => false
    | some (_, t) =>
      if r.small then
        okSmallFO r.m0 ((tget t outs.f).map decCJet) &&
          okSmallVO r.m1 ((tget t outs.v).map decCJet) &&
          outs.e.all fun i => okSmallEO r.m2 ((tget t i).map decCJet)
      else
        okAtO c ((tget t outs.f).map decCJet) r.m0 &&
          okAtO c ((tget t outs.v).map decCJet) r.m1 &&
          outs.e.all fun i => okAtO c ((tget t i).map decCJet) r.m2

theorem Rel_init : Rel 0 Trie.empty ⟨0, []⟩ := by
  refine ⟨rfl, by norm_num, ?_, ?_⟩
  · intro i
    have : tget Trie.empty i = none := by
      unfold tget
      cases Nat.ble 2048 i
      · simp [Trie.get_empty]
      · rfl
    rw [this]
    simp [RS.get]
  · intro i r h
    have : tget Trie.empty i = none := by
      unfold tget
      cases Nat.ble 2048 i
      · simp [Trie.get_empty]
      · rfl
    rw [this] at h
    simp at h

theorem fastCheck_sound (r : Row) (k : Nat) (fp : List FOp) (outs : Outs)
    (hfp : fp = ((familyProg r.small).1).map compile) (houts : outs = (familyProg r.small).2)
    (h : fastCheck r k fp outs = true) : r.checkCell k = true := by
  unfold fastCheck at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hrad0, h⟩ := h
  set c := r.cell k with hc
  set x := c.ctx with hx
  have hq : ((x.rad.hi.toNat : Nat) : Int) = x.rad.hi := Int.toNat_of_nonneg hrad0.2
  have hrad : x.rad = ⟨-(x.rad.hi.toNat : Int), x.rad.hi.toNat⟩ := by
    rw [hq]
    cases hr : x.rad with
    | mk lo hi =>
      have := hrad0.1
      rw [hr] at this
      simp only [] at this ⊢
      rw [this]
  cases hrun : runF x x.rad.hi.toNat fp 0 Trie.empty with
  | none => rw [hrun] at h; simp at h
  | some nt =>
    obtain ⟨n', t'⟩ := nt
    rw [hrun] at h
    simp only [] at h
    rw [hfp] at hrun
    obtain ⟨rs', hrs, hrel⟩ := runF_sound hrad _ 0 Trie.empty ⟨0, []⟩ Rel_init hrun
    unfold Row.checkCell
    simp only []
    rw [← hc, ← hx]
    have hrr : runRS x (familyProg r.small).1 = some rs' := by
      rw [runRS_eq]; exact hrs
    rw [hrr]
    simp only []
    have hg : ∀ i, (tget t' i).map decCJet = rs'.get i := hrel.2.2.1
    subst houts
    by_cases hs : r.small = true
    · rw [hs] at h ⊢
      simp only [if_true, Bool.and_eq_true, List.all_eq_true] at h ⊢
      obtain ⟨⟨h1, h2⟩, h3⟩ := h
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [okSmallF_eq, ← hg]; exact h1
      · rw [okSmallV_eq, ← hg]; exact h2
      · intro i hi; rw [okSmallE_eq, ← hg]; exact h3 i hi
    · have hs' : r.small = false := by simpa using hs
      rw [hs'] at h ⊢
      simp only [Bool.false_eq_true, if_false, Bool.and_eq_true, List.all_eq_true] at h ⊢
      obtain ⟨⟨h1, h2⟩, h3⟩ := h
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [okAt_eq, ← hg]; exact h1
      · rw [okAt_eq, ← hg]; exact h2
      · intro i hi; rw [okAt_eq, ← hg]; exact h3 i hi

end BecknerOnofri.V2.IntervalKernel
