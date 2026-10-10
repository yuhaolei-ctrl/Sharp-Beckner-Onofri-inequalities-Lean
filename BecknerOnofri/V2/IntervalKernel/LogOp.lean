module

public import BecknerOnofri.V2.IntervalKernel.Enc
public import BecknerOnofri.V2.IntervalKernel.Log

@[expose] public section

/-!
# The packed logarithm operation

`logOp q1 ra` computes the logarithm jets of the two halves of the register `ra` with the
natural-number logarithm of `Log.lean` (`jetLogF`, equal to the reference `Jet.log`), packs them
(`encHalf`), and tightens in packed form (`finish`).  `logOp_spec`: the result is
`CJet.log x (decCJet ra)`.
-/

namespace BecknerOnofri.V2.IntervalKernel

open BecknerOnofri.V2.Interval

def logIvF (a : Iv) : Option Iv :=
  if 0 < a.lo then do
    let l ← logPointF a.lo
    let h ← logPointF a.hi
    Iv.mk? l.lo h.hi
  else none

theorem logIvF_eq (a : Iv) : logIvF a = Iv.log a := by
  unfold logIvF Iv.log
  rw [show logPointF a.lo = logPoint a.lo from logPointF_eq _,
    show logPointF a.hi = logPoint a.hi from logPointF_eq _]

def jetLogF (a : Jet) : Option Jet := do
  let l0 ← logIvF (a.get 0)
  Jet.logFold a l0 6

theorem jetLogF_eq (a : Jet) : jetLogF a = Jet.log a := by
  unfold jetLogF Jet.log
  rw [logIvF_eq]

/-- Pack a jet as a half (failing flag if a field is out of range or the length is wrong). -/
def encHalf (j : Jet) : Nat × Bool :=
  match encJetL j with
  | some l => (packList l, Nat.beq l.length 14)
  | none => (0, false)

theorem encHalf_spec {j : Jet} (h : (encHalf j).2 = true) :
    ∃ l, HalfL (encHalf j).1 l ∧ jetL l 0 = j := by
  unfold encHalf at h ⊢
  generalize he : encJetL j = o at h ⊢
  cases o with
  | none => simp at h
  | some l =>
    have hl : l.length = 14 := Nat.eq_of_beq_eq_true h
    obtain ⟨k1, k2, k3⟩ := encJetL_spec j l he
    have hj : j.length = 7 := by omega
    exact ⟨l, ⟨hl, k2, rfl⟩, jetL_of_enc hj he⟩

def logOp (q1 ra : Nat) : Option Nat :=
  (jetLogF (decCJet ra).mid).bind fun m =>
    (jetLogF (decCJet ra).box).bind fun b => finish q1 (encHalf m) (encHalf b)

theorem logOp_spec {x : Ctx} {q1 : Nat} (hrad : x.rad = ⟨-(q1 : Int), q1⟩) {ra r : Nat}
    (h : logOp q1 ra = some r) :
    (∃ l, RegL r l) ∧ CJet.log x (decCJet ra) = some (decCJet r) := by
  unfold logOp at h
  obtain ⟨m, hm, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨b, hb, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨l, hl, hbuild⟩ := finish_spec hrad (A := m) (B := b)
    (fun hok => encHalf_spec hok) (fun hok => encHalf_spec hok) h
  refine ⟨⟨l, hl⟩, ?_⟩
  unfold CJet.log
  rw [← jetLogF_eq, ← jetLogF_eq, hm, hb]
  exact hbuild

end BecknerOnofri.V2.IntervalKernel
