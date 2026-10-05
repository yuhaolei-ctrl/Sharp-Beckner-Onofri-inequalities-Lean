import BecknerOnofri.NormalHessianCoercivity
import BecknerOnofri.PhysicalTranslationTangents
import BecknerOnofri.FullBranchHessian

/-! Strict normal coercivity of the actual physical full-mode branch, with
the exact raw H^(d/2) orthogonality and norm in the trusted theorem. -/
noncomputable section
open Filter MeasureTheory
open scoped Topology
namespace BecknerOnofri.HighDim.PhysicalNormalCoercivity
open DiagonalScalarBranch

theorem physical_normalCoercivity {d : ℕ} (hd : 12≤d) :
    ∀ᶠ β in 𝓝[>] (spectralThreshold d), ∃ c : ℝ, 0<c ∧
      ∀ h : Torus d → ℝ, InCriticalSobolev h → InSobolev ((d:ℝ)/2) h → MeanZero h →
        (∀ j : Fin d, (∫ x, h x*coordinateDerivative (physicalPotential hd β) j x ∂torusMeasure d)=0) →
        secondVariation β (physicalPotential hd β) h≤-c*sobolevNorm ((d:ℝ)/2) h^2 := by
  filter_upwards [FullBranchHessian.physical_hessian_nonpos_kernel hd,
    PhysicalTranslationTangents.coordinateDerivative_memLp hd,self_mem_nhdsWithin] with β hH ht hβ
  have hp : 0<β := lt_trans (Legacy.TorusEndpoint.endpointSigma_pos (by omega)) hβ
  exact NormalHessianCoercivity.normal_sobolev_coercivity (by omega) hp (physicalPotential hd β) ht
    (fun h hh hm => (hH h hh hm).1) (fun h hh hm hz => (hH h hh hm).2.mp hz)

#print axioms physical_normalCoercivity
end BecknerOnofri.HighDim.PhysicalNormalCoercivity
