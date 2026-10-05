module

public import BecknerOnofri.ScalarConvexMinorant

@[expose] public section

namespace BecknerOnofri.HighDim.ScalarCertificate
open Set

theorem affinePiece_le_convexMinorant (a e : ℝ) (ps : List AffinePiece)
    (p : AffinePiece) (hp : p∈ps) (x : ℝ) : p.value x≤convexMinorant a e ps x := by
  induction ps with
  | nil => simp at hp
  | cons q qs ih =>
    rcases List.mem_cons.mp hp with rfl|hp
    · exact le_max_left _ _
    · exact (ih hp).trans (le_max_right _ _)

theorem quarticBase_le_convexMinorant (a e : ℝ) (ps : List AffinePiece) (x : ℝ) :
    quarticBase a e x≤convexMinorant a e ps x := by
  induction ps with
  | nil => exact le_rfl
  | cons q qs ih => exact ih.trans (le_max_right _ _)

def minorantSmallCheck (a e : ℚ) (ps : List AffinePiece) : Bool :=
  ps.all (fun p => decide (4*a*e^3≤p.slope ∧ p.slope*e+p.intercept≤a*e^4))

theorem minorantSmallCheck_sound (a e : ℚ) (ha : 0≤a) (ps : List AffinePiece)
    (hc : minorantSmallCheck a e ps=true) {x : ℝ} (hx : x≤(e : ℝ)) :
    convexMinorant a e ps x=(a : ℝ)*x^4 := by
  apply convexMinorant_small a e (by exact_mod_cast ha) ps _ x hx
  intro p hp
  have h := of_decide_eq_true (List.all_eq_true.mp hc p hp)
  constructor
  · exact_mod_cast h.1
  · unfold AffinePiece.value
    exact_mod_cast h.2

#print axioms minorantSmallCheck_sound
#print axioms affinePiece_le_convexMinorant
end BecknerOnofri.HighDim.ScalarCertificate
