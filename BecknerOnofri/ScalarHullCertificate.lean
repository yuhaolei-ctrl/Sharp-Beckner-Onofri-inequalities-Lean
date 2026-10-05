module

public import BecknerOnofri.ScalarHullOrder
public import BecknerOnofri.ScalarMinorantBounds
public import Mathlib.Data.List.GetD

@[expose] public section

namespace BecknerOnofri.HighDim.ScalarCertificate
open Set

def hullLine (ps : List AffinePiece) (k : ℕ) : AffinePiece := ps.getD k ⟨0,0⟩
def hullKnot (ks : List ℚ) (k : ℕ) : ℚ := ks.getD k 0

def orderedHullCheck (ps : List AffinePiece) (ks : List ℚ) : Bool :=
  decide (ks.length=ps.length+1) &&
    (ks.zip ks.tail).all (fun p => decide (p.1≤p.2)) &&
    ((ps.zip ps.tail).zip ks.tail).all (fun p => decide
      (p.1.1.slope≤p.1.2.slope ∧
       p.1.1.slope*p.2+p.1.1.intercept=p.1.2.slope*p.2+p.1.2.intercept))

theorem orderedHullCheck_data (ps : List AffinePiece) (ks : List ℚ)
    (hc : orderedHullCheck ps ks=true) :
    ks.length=ps.length+1 ∧
    (∀ k : Fin ps.length,hullKnot ks k≤hullKnot ks (k+1)) ∧
    ∀ k : Fin (ps.length-1),
      (hullLine ps k).slope≤(hullLine ps (k+1)).slope ∧
      (hullLine ps k).slope*hullKnot ks (k+1)+(hullLine ps k).intercept=
        (hullLine ps (k+1)).slope*hullKnot ks (k+1)+(hullLine ps (k+1)).intercept := by
  have h := Bool.and_eq_true_iff.mp hc
  have h' := Bool.and_eq_true_iff.mp h.1
  have hlen := of_decide_eq_true h'.1
  refine ⟨hlen,?_,?_⟩
  · intro k
    have hk : k.val<(ks.zip ks.tail).length := by simp only [List.length_zip,List.length_tail]; omega
    have hh := of_decide_eq_true (List.all_eq_true.mp h'.2 _ (List.getElem_mem hk))
    simpa only [List.getElem_zip,List.getElem_tail,hullKnot,
      List.getD_eq_getElem _ _ (show k.val<ks.length by omega),
      List.getD_eq_getElem _ _ (show k.val+1<ks.length by omega)] using hh
  · intro k
    have hk : k.val<((ps.zip ps.tail).zip ks.tail).length := by
      simp only [List.length_zip,List.length_tail]; omega
    have hh := of_decide_eq_true (List.all_eq_true.mp h.2 _ (List.getElem_mem hk))
    simpa only [List.getElem_zip,List.getElem_tail,hullKnot,hullLine,
      List.getD_eq_getElem _ _ (show k.val<ps.length by omega),
      List.getD_eq_getElem _ _ (show k.val+1<ps.length by omega),
      List.getD_eq_getElem _ _ (show k.val+1<ks.length by omega)] using hh

def orderedHullOfLists (ps : List AffinePiece) (ks : List ℚ)
    (hc : orderedHullCheck ps ks=true) : OrderedAffineHull ps.length where
  line := hullLine ps
  knot := hullKnot ks
  knot_step := by
    intro k hk
    exact (orderedHullCheck_data ps ks hc).2.1 ⟨k,hk⟩
  slope_step := by
    intro k hk
    exact ((orderedHullCheck_data ps ks hc).2.2 ⟨k,by omega⟩).1
  join := by
    intro k hk
    exact ((orderedHullCheck_data ps ks hc).2.2 ⟨k,by omega⟩).2

theorem quarticBase_le_affine {a e x : ℝ} (p : AffinePiece) (hx : e≤x)
    (hs : 4*a*e^3≤(p.slope : ℝ)) (he : a*e^4≤p.value e) :
    quarticBase a e x≤p.value x := by
  have hm := mul_le_mul_of_nonneg_right hs (sub_nonneg.mpr hx)
  unfold quarticBase
  split_ifs with h
  · have hx' : x=e := le_antisymm h hx
    simpa only [hx'] using he
  · unfold AffinePiece.value at he ⊢
    nlinarith

theorem hull_piece_upper (a e : ℝ) (ps : List AffinePiece) (ks : List ℚ)
    (hc : orderedHullCheck ps ks=true) (i : ℕ) (hi : i<ps.length)
    (hstart : 4*a*e^3≤((hullLine ps 0).slope : ℝ))
    (hstartval : a*e^4≤(hullLine ps 0).value e) (x : ℝ)
    (hxe : e≤x) (hleft : (hullKnot ks i : ℝ)≤x)
    (hright : i+1=ps.length ∨ x≤(hullKnot ks (i+1) : ℝ)) :
    convexMinorant a e ps x≤(hullLine ps i).value x := by
  let H := orderedHullOfLists ps ks hc
  have hdom (j : ℕ) (hj : j<ps.length) : (hullLine ps j).value x≤(hullLine ps i).value x := by
    rcases hright with hend|hx
    · exact H.prefix_le (by omega) hi x hleft
    · exact H.piece_dominates i hi x ⟨hleft,hx⟩ j hj
  apply convexMinorant_le
  · exact (quarticBase_le_affine _ hxe hstart hstartval).trans (hdom 0 (by omega))
  · intro p hp
    obtain ⟨j,hj,he⟩ := List.mem_iff_getElem.mp hp
    have h := hdom j hj
    simpa only [hullLine,List.getD_eq_getElem _ _ hj,he] using h

#print axioms hull_piece_upper
end BecknerOnofri.HighDim.ScalarCertificate
