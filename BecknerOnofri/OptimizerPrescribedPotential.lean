import BecknerOnofri.OptimizerDuality
import BecknerOnofri.RawGapIdentities

/-! Identification of an optimizer with the prescribed Green potential,
rather than an existentially chosen Gibbs representative. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
namespace BecknerOnofri.FiniteEntropyGreen
open Legacy.TorusEndpoint Legacy.BecknerOnofri TorusSobolev
open SubcriticalAttainment SubcriticalEuler

theorem optimizer_eq_dualPotential {d : ℕ} (hd : 0 < d) {b Ab A : ℝ}
    (hR : RoughExponentialBound d b Ab) (hA : 0 < A)
    (u : TorusL2 d) (hu : Admissible u)
    (hmax : ∀ v : TorusL2 d, Admissible v → functional A v ≤ functional A u) :
    u = dualPotential hd A (gibbsDensity hR hu) (gibbsDensity_finiteEntropy hR hu) := by
  apply (fourierIsometry d).injective
  ext k
  simp only [dualPotential, map_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
    potentialLp_fourier]
  by_cases hk : k = 0
  · subst k
    simp [hu.2.1]
  · rw [if_neg hk, maximizer_fourier_formula hR hA hu hmax hk]
    simp only [Complex.ofReal_mul, one_div, mul_assoc]
    rfl

theorem optimizer_physical_green {d : ℕ} (hd : 0 < d) {b Ab β : ℝ}
    (hR : RoughExponentialBound d b Ab) (hβ : 0 < β)
    (u : TorusL2 d) (hu : Admissible u)
    (hmax : ∀ v : TorusL2 d, Admissible v →
      functional (HighDim.spectralThreshold d/(2*β)) v ≤
        functional (HighDim.spectralThreshold d/(2*β)) u) :
    HighDim.RawAttainment.realValue u =ᵐ[HighDim.torusMeasure d]
      HighDim.Gap.densityPotential β (gibbsValue u) := by
  have hA : 0 < HighDim.spectralThreshold d/(2*β) :=
    div_pos (endpointSigma_pos hd) (by positivity)
  have he := optimizer_eq_dualPotential hd hR hA u hu hmax
  have hp := HighDim.Gap.potential_ae hd hβ (gibbsDensity hR hu) (gibbsDensity_finiteEntropy hR hu)
  rw [← he] at hp
  exact hp

#print axioms optimizer_eq_dualPotential
#print axioms optimizer_physical_green
end BecknerOnofri.FiniteEntropyGreen
