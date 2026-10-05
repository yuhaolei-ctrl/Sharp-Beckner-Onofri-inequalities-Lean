module

public import BecknerOnofri.ScalarCertifiedGlobal
public import BecknerOnofri.ScalarMinorantShape
public import BecknerOnofri.SpinCertifiedGlobal

@[expose] public section

/-! The same explicit convex witness satisfies both sides of the entropy
certificate. This module is accepted only once the complete scalar assembly
has been checked; it has no numerical premise. -/
namespace BecknerOnofri.HighDim
open Set ScalarCertificate.CertifiedMinorant

theorem exists_certified_entropy_minorant :
    ∃ ψ : ℝ → ℝ,
      ContinuousOn ψ (Icc (0 : ℝ) 1) ∧
      ConvexOn ℝ (Icc (0 : ℝ) 1) ψ ∧
      MonotoneOn ψ (Icc (0 : ℝ) 1) ∧
      (∀ t∈Icc (0 : ℝ) 1,0≤ψ t) ∧
      (∀ t∈Icc (0 : ℝ) (1/16),ψ t=(3/40 : ℝ)*t^4) ∧
      (∀ t∈Ico (0 : ℝ) 1,ψ t≤CircleScalar.gamma t) ∧
      (∀ q : Spin.Count → ℝ,Spin.Feasible q → Spin.mean q∈Icc (0 : ℝ) 1 →
        (Spin.mean q)^4/250≤Spin.functional q+12*ψ (Spin.mean q)) := by
  refine ⟨psi,psi_continuous.continuousOn,
    psi_convex.subset (subset_univ _) (convex_Icc _ _),?_,?_,?_,
    psi_le_gamma,Spin.certified_global_spin_bound⟩
  · intro x hx y hy hxy
    exact psi_monotoneOn hx.1 hy.1 hxy
  · intro t _
    exact psi_nonneg t
  · intro t ht
    exact psi_small ht.2

#print axioms exists_certified_entropy_minorant
end BecknerOnofri.HighDim
