module

public import BecknerOnofri.V2.IntervalKernel.LogOp
public import BecknerOnofri.V2.IntervalKernel.Trie

@[expose] public section

/-!
# The kernel interpreter and its refinement of the reference interpreter

`runF` executes a compiled program (`FOp`) on packed registers kept in a `Trie`.  The five hot
operations use the packed arithmetic of `Reg.lean`; every other operation (`var`, `const`, `inv`,
`log`, and any operation whose constant does not fit) is delegated to the reference
implementation of `Prog.lean` on the decoded registers (`slowStep`) and re-encoded.

`Rel n t rs` says that the trie `t` holds the registers of the reference state `rs`.
`runF_sound`: if `runF` succeeds then `runRS` succeeds and the final states are related.
-/

namespace BecknerOnofri.V2.IntervalKernel

open BecknerOnofri.V2.Interval

/-! ### The register file -/

/-- Lookup with the capacity check. -/
def tget (t : Trie) (i : Nat) : Option Nat := bif Nat.ble 2048 i then none else t.get 11 i

def tset (t : Trie) (i v : Nat) : Trie := t.set 11 i v

theorem tget_tset (t : Trie) {n v : Nat} (hn : n < 2048) (i : Nat) :
    tget (tset t n v) i = if i = n then some v else tget t i := by
  unfold tget tset
  by_cases hi : 2048 ≤ i
  · have : Nat.ble 2048 i = true := ble_iff.2 hi
    have hne : i ≠ n := by omega
    simp [this, hne]
  · have : Nat.ble 2048 i = false := by
      cases h : Nat.ble 2048 i
      · rfl
      · exact absurd (ble_iff.1 h) hi
    simp only [this, Bool.cond_false]
    rw [Trie.get_set 11 t n i v (by norm_num; omega) (by norm_num; omega)]

/-! ### The interpreter -/

/-- The reference `step` with an abstract register lookup. -/
def stepG (x : Ctx) (get : Nat → Option CJet) : Op → Option CJet
  | .var => CJet.var x
  | .const c => (c.toIv).map CJet.const
  | .add i j => do CJet.add x (← get i) (← get j)
  | .neg i => do CJet.neg x (← get i)
  | .mul i j => do CJet.mul x (← get i) (← get j)
  | .smul i c => do CJet.smul x (← get i) (← c.toIv)
  | .addc i c => do CJet.addc x (← get i) (← c.toIv)
  | .inv i => do CJet.recip x (← get i)
  | .log i => do CJet.log x (← get i)

theorem step_eq (x : Ctx) (st : RS) (op : Op) : step x st op = stepG x st.get op := by
  cases op <;> rfl

/-- Compiled operations. -/
inductive FOp
  | slow (o : Op)
  | add (i j : Nat)
  | neg (i : Nat)
  | mul (i j : Nat)
  | smul (i cl ch : Nat)
  | addc (i cl ch : Nat)
  | lit (r : Nat)
  | log (i : Nat)

def compileConst (c : Const) : Option (Nat × Nat) :=
  match c.toIv with
  | some iv => encIv iv
  | none => none

/-- The packed register of a constant, computed once at compile time. -/
def compileLit (c : Const) : Option Nat :=
  (c.toIv).bind fun iv => encode (CJet.const iv)

def compile : Op → FOp
  | .add i j => .add i j
  | .neg i => .neg i
  | .mul i j => .mul i j
  | .smul i c =>
    match compileConst c with
    | some (cl, ch) => .smul i cl ch
    | none => .slow (.smul i c)
  | .addc i c =>
    match compileConst c with
    | some (cl, ch) => .addc i cl ch
    | none => .slow (.addc i c)
  | .var => .slow .var
  | .const c =>
    match compileLit c with
    | some r => .lit r
    | none => .slow (.const c)
  | .inv i => .slow (.inv i)
  | .log i => .log i

/-- Delegation to the reference implementation. -/
def slowStep (x : Ctx) (t : Trie) (o : Op) : Option Nat :=
  (stepG x (fun i => (tget t i).map decCJet) o).bind encode

def fstep (x : Ctx) (q1 : Nat) (t : Trie) : FOp → Option Nat
  | .slow o => slowStep x t o
  | .add i j => (tget t i).bind fun a => (tget t j).bind fun b => addOp q1 a b
  | .neg i => (tget t i).bind fun a => negOp q1 a
  | .mul i j => (tget t i).bind fun a => (tget t j).bind fun b => mulOp q1 a b
  | .smul i cl ch => (tget t i).bind fun a => smulOp q1 a cl ch
  | .addc i cl ch => (tget t i).bind fun a => addcOp q1 a cl ch
  | .lit r => some r
  | .log i => (tget t i).bind fun a => logOp q1 a

def runF (x : Ctx) (q1 : Nat) : List FOp → Nat → Trie → Option (Nat × Trie)
  | [], n, t => some (n, t)
  | op :: rest, n, t =>
    match fstep x q1 t op with
    | none => none
    | some r => bif Nat.ble 2048 n then none else runF x q1 rest (n + 1) (tset t n r)

/-! ### Refinement -/

def Rel (n : Nat) (t : Trie) (rs : RS) : Prop :=
  rs.n = n ∧ n ≤ 2048 ∧ (∀ i, (tget t i).map decCJet = rs.get i) ∧
    (∀ i r, tget t i = some r → ∃ l, RegL r l)

theorem Rel.get_some {n : Nat} {t : Trie} {rs : RS} (h : Rel n t rs) {i r : Nat}
    (hi : tget t i = some r) : (∃ l, RegL r l) ∧ rs.get i = some (decCJet r) := by
  refine ⟨h.2.2.2 i r hi, ?_⟩
  rw [← h.2.2.1 i, hi]
  rfl

theorem RS.get_push (rs : RS) (c : CJet) (i : Nat) :
    (RS.mk (rs.n + 1) (c :: rs.rev)).get i = if i = rs.n then some c else rs.get i := by
  unfold RS.get
  simp only []
  by_cases h1 : i = rs.n
  · subst h1
    simp
  · by_cases h2 : i < rs.n
    · have h3 : i < rs.n + 1 := by omega
      rw [if_pos h3, if_pos h2, if_neg h1]
      have : rs.n + 1 - 1 - i = (rs.n - 1 - i) + 1 := by omega
      rw [this]
      simp
    · have h3 : ¬ i < rs.n + 1 := by omega
      rw [if_neg h3, if_neg h2, if_neg h1]

theorem fstep_sound {x : Ctx} {q1 : Nat} (hrad : x.rad = ⟨-(q1 : Int), q1⟩) {n : Nat} {t : Trie}
    {rs : RS} (hrel : Rel n t rs) (op : Op) {r : Nat} (h : fstep x q1 t (compile op) = some r) :
    (∃ l, RegL r l) ∧ step x rs op = some (decCJet r) := by
  have slow : ∀ o : Op, slowStep x t o = some r →
      (∃ l, RegL r l) ∧ step x rs o = some (decCJet r) := by
    intro o hs
    unfold slowStep at hs
    obtain ⟨cj, hcj, henc⟩ := Option.bind_eq_some_iff.1 hs
    have hfun : (fun i => (tget t i).map decCJet) = rs.get := funext hrel.2.2.1
    rw [hfun] at hcj
    obtain ⟨h1, h2⟩ := encode_spec henc
    refine ⟨h1, ?_⟩
    rw [step_eq, hcj, h2]
  cases op with
  | var => exact slow _ h
  | const c =>
    simp only [compile] at h
    cases hc : compileLit c with
    | none => rw [hc] at h; exact slow _ h
    | some r0 =>
      rw [hc] at h
      simp only [fstep, Option.some.injEq] at h
      subst h
      unfold compileLit at hc
      obtain ⟨iv, hiv, henc⟩ := Option.bind_eq_some_iff.1 hc
      obtain ⟨h1, h2⟩ := encode_spec henc
      refine ⟨h1, ?_⟩
      rw [step_eq]
      simp only [stepG, hiv, Option.map_some, h2]
  | inv i => exact slow _ h
  | log i =>
    simp only [compile, fstep] at h
    obtain ⟨a, ha, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨⟨la, hla⟩, hga⟩ := hrel.get_some ha
    obtain ⟨hr, hs⟩ := logOp_spec hrad h
    refine ⟨hr, ?_⟩
    rw [step_eq]
    simp only [stepG, hga]
    exact hs
  | add i j =>
    simp only [compile, fstep] at h
    obtain ⟨a, ha, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨b, hb, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨⟨la, hla⟩, hga⟩ := hrel.get_some ha
    obtain ⟨⟨lb, hlb⟩, hgb⟩ := hrel.get_some hb
    obtain ⟨l, hl, hs⟩ := addOp_spec hrad hla hlb h
    refine ⟨⟨l, hl⟩, ?_⟩
    rw [step_eq]
    simp only [stepG, Op.add, hga, hgb]
    exact hs
  | neg i =>
    simp only [compile, fstep] at h
    obtain ⟨a, ha, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨⟨la, hla⟩, hga⟩ := hrel.get_some ha
    obtain ⟨l, hl, hs⟩ := negOp_spec hrad hla h
    refine ⟨⟨l, hl⟩, ?_⟩
    rw [step_eq]
    simp only [stepG, hga]
    exact hs
  | mul i j =>
    simp only [compile, fstep] at h
    obtain ⟨a, ha, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨b, hb, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨⟨la, hla⟩, hga⟩ := hrel.get_some ha
    obtain ⟨⟨lb, hlb⟩, hgb⟩ := hrel.get_some hb
    obtain ⟨l, hl, hs⟩ := mulOp_spec hrad hla hlb h
    refine ⟨⟨l, hl⟩, ?_⟩
    rw [step_eq]
    simp only [stepG, hga, hgb]
    exact hs
  | smul i c =>
    simp only [compile] at h
    cases hc : compileConst c with
    | none => rw [hc] at h; exact slow _ h
    | some p =>
      obtain ⟨cl, ch⟩ := p
      rw [hc] at h
      simp only [fstep] at h
      obtain ⟨a, ha, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨⟨la, hla⟩, hga⟩ := hrel.get_some ha
      unfold compileConst at hc
      cases hiv : c.toIv with
      | none => rw [hiv] at hc; simp at hc
      | some iv =>
        rw [hiv] at hc
        obtain ⟨hcl, hch, hciv⟩ := encIv_spec hc
        obtain ⟨l, hl, hs⟩ := smulOp_spec hrad hla hcl hch h
        refine ⟨⟨l, hl⟩, ?_⟩
        rw [step_eq]
        simp only [stepG, hga, hiv]
        rw [hciv] at hs
        exact hs
  | addc i c =>
    simp only [compile] at h
    cases hc : compileConst c with
    | none => rw [hc] at h; exact slow _ h
    | some p =>
      obtain ⟨cl, ch⟩ := p
      rw [hc] at h
      simp only [fstep] at h
      obtain ⟨a, ha, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨⟨la, hla⟩, hga⟩ := hrel.get_some ha
      unfold compileConst at hc
      cases hiv : c.toIv with
      | none => rw [hiv] at hc; simp at hc
      | some iv =>
        rw [hiv] at hc
        obtain ⟨hcl, hch, hciv⟩ := encIv_spec hc
        obtain ⟨l, hl, hs⟩ := addcOp_spec hrad hla h
        refine ⟨⟨l, hl⟩, ?_⟩
        rw [step_eq]
        simp only [stepG, hga, hiv]
        rw [hciv] at hs
        exact hs

/-- The reference run from an arbitrary state. -/
def runFrom (x : Ctx) (p : Prog) (st : RS) : Option RS :=
  p.foldlM (fun st op => do
    let r ← step x st op
    pure ⟨st.n + 1, r :: st.rev⟩) st

theorem runRS_eq (x : Ctx) (p : Prog) : runRS x p = runFrom x p ⟨0, []⟩ := rfl

theorem runF_sound {x : Ctx} {q1 : Nat} (hrad : x.rad = ⟨-(q1 : Int), q1⟩) :
    ∀ (p : Prog) (n : Nat) (t : Trie) (rs : RS), Rel n t rs →
      ∀ {n' : Nat} {t' : Trie}, runF x q1 (p.map compile) n t = some (n', t') →
        ∃ rs', runFrom x p rs = some rs' ∧ Rel n' t' rs'
  | [], n, t, rs, hrel, n', t', h => by
    simp only [List.map_nil, runF, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rs, rfl, hrel⟩
  | op :: rest, n, t, rs, hrel, n', t', h => by
    simp only [List.map_cons, runF] at h
    cases hf : fstep x q1 t (compile op) with
    | none => rw [hf] at h; simp at h
    | some r =>
      rw [hf] at h
      simp only [] at h
      cases hb : Nat.ble 2048 n
      · rw [hb] at h
        simp only [Bool.cond_false] at h
        have hn : n < 2048 := by
          by_contra hc
          have := ble_iff.2 (by omega : 2048 ≤ n)
          rw [hb] at this; simp at this
        obtain ⟨⟨l, hl⟩, hs⟩ := fstep_sound hrad hrel op hf
        have hrel' : Rel (n + 1) (tset t n r) ⟨rs.n + 1, decCJet r :: rs.rev⟩ := by
          refine ⟨by simp [hrel.1], by omega, ?_, ?_⟩
          · intro i
            rw [tget_tset t hn, RS.get_push, hrel.1]
            by_cases hi : i = n
            · simp [hi]
            · simp [hi, hrel.2.2.1 i]
          · intro i r' hi
            rw [tget_tset t hn] at hi
            by_cases hin : i = n
            · simp only [hin, if_true, Option.some.injEq] at hi
              subst hi
              exact ⟨l, hl⟩
            · simp only [hin, if_false] at hi
              exact hrel.2.2.2 i r' hi
        obtain ⟨rs', hrs', hrel''⟩ := runF_sound hrad rest (n + 1) (tset t n r) _ hrel' h
        refine ⟨rs', ?_, hrel''⟩
        unfold runFrom at hrs' ⊢
        simp only [List.foldlM_cons]
        rw [hs]
        exact hrs'
      · rw [hb] at h
        simp at h

end BecknerOnofri.V2.IntervalKernel
