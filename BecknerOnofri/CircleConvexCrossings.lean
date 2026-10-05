import BecknerOnofri.CircleTwoSignChange
import Mathlib.Topology.Order.Basic

/-! A continuous convex logarithmic density ratio has the exact two-crossing
sign pattern, with endpoints constructed from its negative set. -/
noncomputable section
open Set
namespace BecknerOnofri.HighDim.CircleScalar

theorem negative_pair (F : ℝ → ℝ) (hc : Continuous F)
    (hn : ∃ x ∈ Icc (-1:ℝ) 1,F x<0) :
    ∃ x y : ℝ,x ∈ Icc (-1:ℝ) 1 ∧ y ∈ Icc (-1:ℝ) 1 ∧ x<y ∧ F x<0 ∧ F y<0 := by
  obtain ⟨x,hx,hFx⟩ := hn
  have hopen : IsOpen {y : ℝ | F y<0} := isOpen_lt hc continuous_const
  obtain ⟨l,u,hlu,hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hopen.mem_nhds hFx)
  let L := max (-1:ℝ) l
  let U := min (1:ℝ) u
  have hLU : L<U := by
    apply max_lt_iff.mpr
    constructor <;> apply lt_min_iff.mpr <;> constructor <;> linarith [hx.1,hx.2,hlu.1,hlu.2]
  have hL : -1≤L := le_max_left _ _
  have hU : U≤1 := min_le_left _ _
  have hl : l≤L := le_max_right _ _
  have hu : U≤u := min_le_right _ _
  refine ⟨(2*L+U)/3,(L+2*U)/3,⟨by linarith,by linarith⟩,
    ⟨by linarith,by linarith⟩,by linarith,?_,?_⟩
  · exact hsub ⟨by linarith,by linarith⟩
  · exact hsub ⟨by linarith,by linarith⟩

theorem convex_negative_crossings (F : ℝ → ℝ) (hc : Continuous F)
    (hf : ConvexOn ℝ (Icc (-1:ℝ) 1) F) (hn : ∃ x ∈ Icc (-1:ℝ) 1,F x<0) :
    ∃ a b : ℝ,a ∈ Icc (-1:ℝ) 1 ∧ b ∈ Icc (-1:ℝ) 1 ∧ a<b ∧
      (∀ x,a<x → x<b → F x<0) ∧
      (∀ x ∈ Icc (-1:ℝ) 1,x<a ∨ b<x → 0≤F x) := by
  let S : Set ℝ := {x ∈ Icc (-1:ℝ) 1 | F x<0}
  have hs : S.Nonempty := hn
  have hlo : BddBelow S := ⟨-1,fun x hx => hx.1.1⟩
  have hup : BddAbove S := ⟨1,fun x hx => hx.1.2⟩
  obtain ⟨x,y,hx,hy,hxy,hFx,hFy⟩ := negative_pair F hc hn
  have hxi : x ∈ S := ⟨hx,hFx⟩
  have hyi : y ∈ S := ⟨hy,hFy⟩
  have hax := csInf_le hlo hxi
  have hyb := le_csSup hup hyi
  refine ⟨sInf S,sSup S,⟨le_csInf hs (fun z hz => hz.1.1),hax.trans hx.2⟩,
    ⟨hy.1.trans hyb,csSup_le hs (fun z hz => hz.1.2)⟩,by linarith,?_,?_⟩
  · intro z haz hzb
    obtain ⟨l,hl,hlz⟩ := exists_lt_of_csInf_lt hs haz
    obtain ⟨u,hu,hzu⟩ := exists_lt_of_lt_csSup hs hzb
    exact (((hf.convex_lt 0).ordConnected.out hl hu) ⟨hlz.le,hzu.le⟩).2
  · intro z hz hout
    by_contra hF
    have hzS : z ∈ S := ⟨hz,lt_of_not_ge hF⟩
    rcases hout with hout | hout
    · exact (not_lt_of_ge (csInf_le hlo hzS)) hout
    · exact (not_lt_of_ge (le_csSup hup hzS)) hout

#print axioms convex_negative_crossings
end BecknerOnofri.HighDim.CircleScalar
