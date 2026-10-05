module

public import BecknerOnofri.EntropyExpRows

@[expose] public section

namespace BecknerOnofri.HighDim.EntropyTail.ExpCertificate

def Entry.argument (e : Entry) : ℚ := (e.numerator : ℚ)/e.denominator
def Entry.lowerBound (e : Entry) : ℚ := (e.lower : ℚ)/10^60
def Entry.upperBound (e : Entry) : ℚ := (e.upper : ℚ)/10^60

def Entry.Valid (e : Entry) : Prop :=
  (e.lowerBound : ℝ) ≤ Real.exp (-(e.argument : ℝ)) ∧
    Real.exp (-(e.argument : ℝ)) ≤ (e.upperBound : ℝ)

theorem entry_valid_of_check (e : Entry) (h : entryCheck e = true) : e.Valid := by
  simpa only [Entry.Valid, Entry.argument, Entry.lowerBound, Entry.upperBound,
    Rat.cast_div, Rat.cast_intCast, Rat.cast_pow, Rat.cast_ofNat] using entryCheck_sound e h

structure CheckedChunk where
  entries : List Entry
  accepted : rowsCheck entries = true

theorem CheckedChunk.valid (c : CheckedChunk) (i : Fin c.entries.length) :
    (c.entries[i]).Valid := by
  apply entry_valid_of_check
  exact List.all_eq_true.mp c.accepted _ (List.getElem_mem i.isLt)

#print axioms CheckedChunk.valid
end BecknerOnofri.HighDim.EntropyTail.ExpCertificate
