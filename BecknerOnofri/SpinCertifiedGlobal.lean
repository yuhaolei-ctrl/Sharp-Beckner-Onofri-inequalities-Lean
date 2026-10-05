import BecknerOnofri.SpinCertifiedMiddle
import BecknerOnofri.SpinCertifiedEndRanges

/-! The complete finite-state inequality for the explicit rational convex
function. The separate claim that this function lies below gamma is proved
in the scalar certificate assembly, not assumed in this spin theorem. -/
namespace BecknerOnofri.HighDim.Spin
open Set ScalarCertificate.CertifiedMinorant

theorem certified_global_spin_bound (q : Count → ℝ) (hq : Feasible q)
    (ht : mean q∈Icc (0 : ℝ) 1) :
    (mean q)^4/250≤functional q+12*psi (mean q) := by
  have hqa : FeasibleAt (mean q) q := ⟨hq,rfl⟩
  by_cases hs : mean q≤1/16
  · exact small_spin_bound q (mean q) hqa ⟨ht.1,hs⟩
  · by_cases hm : mean q≤197/200
    · exact middle_spin_bound q (mean q) hqa ⟨le_of_not_ge hs,hm⟩
    · exact large_spin_bound q (mean q) hqa ⟨le_of_not_ge hm,ht.2⟩

#print axioms certified_global_spin_bound
end BecknerOnofri.HighDim.Spin
