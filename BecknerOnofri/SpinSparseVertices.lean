import BecknerOnofri.SpinExtremeSupport
import BecknerOnofri.SpinExactArithmetic

/-! Reduction of the extreme points to the 220 formula-generated vertices. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open Set
namespace BecknerOnofri.HighDim.Spin

theorem extreme_support_three {q : Count → ℝ}
    (hq : q ∈ tangentPolytope.extremePoints ℝ) :
    ∃ i j k : Count,1 ≤ i.val ∧ i<j ∧ j<k ∧
      ∀ r,r ≠ i → r ≠ j → r ≠ k → q r=0 := by
  classical
  let s := Finset.univ.filter (fun j : Count => q j ≠ 0)
  have hsc : s.card ≤ 3 := by
    simpa [s,Fintype.card_subtype] using extreme_support_card_le_three hq
  have hs : s ⊆ Finset.univ.erase 0 := by
    intro j hj
    have hjq : q j ≠ 0 := (Finset.mem_filter.mp hj).2
    simp only [Finset.mem_erase,Finset.mem_univ,and_true]
    intro hj0
    exact hjq (hj0 ▸ hq.1.1)
  obtain ⟨t,hst,ht,hcard⟩ := Finset.exists_subsuperset_card_eq hs hsc
    (by decide : 3 ≤ (Finset.univ.erase (0:Count)).card)
  let e := t.orderEmbOfFin hcard
  have he (r : Fin 3) : e r ∈ t := Finset.orderEmbOfFin_mem t hcard r
  refine ⟨e 0,e 1,e 2,?_,e.strictMono (by decide),e.strictMono (by decide),?_⟩
  · have hn : e 0 ≠ 0 := (Finset.mem_erase.mp (ht (he 0))).1
    have hn' : (e 0).val ≠ 0 := by
      intro hh
      exact hn (Fin.ext hh)
    omega
  · intro r hi hj hk
    by_contra hr
    have hrt : r ∈ t := hst (Finset.mem_filter.mpr ⟨Finset.mem_univ r,hr⟩)
    have hrange : r ∈ Set.range e := by
      simpa only [e,Finset.range_orderEmbOfFin,Finset.mem_coe] using hrt
    obtain ⟨a,ha⟩ := hrange
    fin_cases a <;> simp_all

theorem sum_supported_three (f : Count → ℝ) {i j k : Count}
    (hij : i<j) (hjk : j<k)
    (hf : ∀ r,r ≠ i → r ≠ j → r ≠ k → f r=0) :
    (∑ r : Count,f r)=f i+f j+f k := by
  classical
  have hsum : (∑ r : Count,f r)=∑ r ∈ ({i,j,k}:Finset Count),f r := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro r _ hr
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hr
    exact hf r hr.1 hr.2.1 hr.2.2
  rw [hsum]
  simp [hij.ne,hjk.ne,(hij.trans hjk).ne,add_assoc]

theorem meanCoordinate_eq (j : Count) : meanCoordinate j=(2*(j.val:ℝ)-12)/12 := by
  unfold meanCoordinate meanCoordinateQ
  push_cast
  rfl

theorem sparse_mass_moment {q : Count → ℝ} {i j k : Count}
    (hij : i<j) (hjk : j<k)
    (hs : ∀ r,r ≠ i → r ≠ j → r ≠ k → q r=0)
    (hmass : (∑ r : Count,q r)=0) (hmean : mean q=0) :
    q i+q j+q k=0 ∧ (i.val:ℝ)*q i+(j.val:ℝ)*q j+(k.val:ℝ)*q k=0 := by
  have hm := sum_supported_three q hij hjk hs
  have hx := sum_supported_three (fun r => meanCoordinate r*q r) hij hjk
    (by intro r hi hj hk; rw [hs r hi hj hk,mul_zero])
  change (∑ r : Count,meanCoordinate r*q r)=0 at hmean
  rw [hmean] at hx
  simp_rw [meanCoordinate_eq] at hx
  constructor
  · linarith
  · nlinarith

#print axioms extreme_support_three
end BecknerOnofri.HighDim.Spin
