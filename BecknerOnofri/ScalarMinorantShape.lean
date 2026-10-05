module

public import BecknerOnofri.EntropyScalarCertificate.Minorant
public import Mathlib.Analysis.Convex.Jensen

@[expose] public section

/-! Shape properties of the explicit witness in the manuscript's entropy
proposition: nonnegative, increasing on [0,1], continuous, and convex. -/
namespace BecknerOnofri.HighDim.ScalarCertificate.CertifiedMinorant
open Set

theorem psi_nonneg (x : ℝ) : 0≤psi x := by
  have hbase : 0≤quarticBase (3/40) (1/16) x := by
    unfold quarticBase
    split_ifs with hx
    · positivity
    · have h : 0≤x-1/16 := sub_nonneg.mpr (le_of_not_ge hx)
      positivity
  exact hbase.trans (quarticBase_le_convexMinorant _ _ _ x)

theorem psi_monotoneOn : MonotoneOn psi (Ici (0 : ℝ)) := by
  intro x hx y hy hxy
  have h := psi_convex.le_max_of_mem_Icc (x := 0) (y := y) (z := x)
    (show (0 : ℝ)∈univ from trivial) (show y∈univ from trivial) ⟨hx,hxy⟩
  have hz : psi 0=0 := by simpa using psi_small (x := 0) (by norm_num)
  simpa only [hz,max_eq_right (psi_nonneg y)] using h

#print axioms psi_nonneg
#print axioms psi_monotoneOn
end BecknerOnofri.HighDim.ScalarCertificate.CertifiedMinorant
