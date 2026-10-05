module

public import BecknerOnofri.EndpointRigidity.AnalyticEndpoint
public import Legacy.BecknerOnofri.SubcriticalEulerEnergy
public import Legacy.BecknerOnofri.SubcriticalDensityCompactness

@[expose] public section

/-! At the proved endpoint, equality densities and their genuine dual
potentials lie on a fixed entropy / logarithmic partition level. This allows
compact selection without a subcritical coercivity assertion. -/
noncomputable section
namespace BecknerOnofri.EndpointRigidity.MaximizerLevel
open MeasureTheory Legacy.TorusEndpoint Legacy.BecknerOnofri
open TorusSobolev SubcriticalAttainment SubcriticalEuler
open SubcriticalPrimalDual GreenDensityPotentialL2 GibbsL2Continuity

variable {d : ℕ} {C : ℝ} (hd : 0 < d) (hEndpoint : CoefficientEndpoint d C) {b Ab A : ℝ}
  (hR : RoughExponentialBound d b Ab) (hA : 0 < A)
  (hCoeff : 1/(4*A) = C)

include hEndpoint hCoeff
theorem densityFunctional_nonpos (r : ProbabilityDensity d)
    (hr : r.FiniteEntropy) : densityFunctional A r ≤ 0 := by
  unfold densityFunctional
  rw [hCoeff]
  exact sub_nonpos.mpr (hEndpoint r hr).2

include hd hR hA
theorem functional_nonpos {u : TorusL2 d} (hu : Admissible u) : functional A u ≤ 0 :=
  (dual_le_gibbs hd hR hA hu).trans
    (densityFunctional_nonpos hEndpoint hCoeff _ (gibbsDensity_finiteEntropy hR hu))

theorem maximizer_functional_zero {u : TorusL2 d} (hu : Admissible u)
    (hmax : ∀ v : TorusL2 d, Admissible v → functional A v ≤ functional A u) :
    functional A u = 0 := by
  apply le_antisymm (functional_nonpos hd hEndpoint hR hA hCoeff hu)
  simpa only [functional_zero] using hmax 0 (admissible_zero d)

theorem maximizer_entropy_eq_log {u : TorusL2 d} (hu : Admissible u)
    (hmax : ∀ v : TorusL2 d, Admissible v → functional A v ≤ functional A u) :
    densityEntropy (gibbsValue u) = Real.log (partition u) := by
  have he := maximizer_functional_zero hd hEndpoint hR hA hCoeff hu hmax
  rw [functional] at he
  rw [gibbsDensity_entropy hR hu, maximizer_pairing hR hu hmax]
  linarith

omit hd hR hA in
theorem equality_density_maximizer (r : ProbabilityDensity d)
    (he : densityEntropy r.value = C * fourierEnergy r) :
    ∀ q : ProbabilityDensity d, MemLp q.value 2 (torusMeasure d) →
      densityFunctional A q ≤ densityFunctional A r := by
  intro q hq
  have hz : densityFunctional A r = 0 := by simp [densityFunctional, hCoeff, he]
  rw [hz]
  exact densityFunctional_nonpos hEndpoint hCoeff q (PhysicalGreenL2.finiteEntropy_of_memLp q hq)

omit hd hEndpoint hR in
theorem dualPotential_energy_of_equality (r : ProbabilityDensity d)
    (hr : MemLp r.value 2 (torusMeasure d)) (hd : 0 < d)
    (he : densityEntropy r.value = C * fourierEnergy r) :
    criticalEnergy (dualPotential A r hr) = densityEntropy r.value / A := by
  rw [dualPotential, criticalEnergy_smul_real, potentialLp_energy hd, he, ← hCoeff]
  field_simp
  ring

theorem dualPotential_log_of_equality (r : ProbabilityDensity d)
    (hr : MemLp r.value 2 (torusMeasure d))
    (he : densityEntropy r.value = C * fourierEnergy r) :
    Real.log (partition (dualPotential A r hr)) = densityEntropy r.value := by
  have hm := equality_density_maximizer hEndpoint hCoeff r he
  have hz := maximizer_functional_zero hd hEndpoint hR hA hCoeff
    (dualPotential_admissible hd A r hr) (density_maximizer_dual hd hR hA r hr hm).2
  rw [functional, dualPotential_energy_of_equality hA hCoeff r hr hd he] at hz
  have hh : A * (densityEntropy r.value / A) = densityEntropy r.value := by
    field_simp
  rw [hh] at hz
  exact sub_eq_zero.mp hz

omit hd hEndpoint hR hA hCoeff in
theorem densityEntropy_congr_ae {f g : Torus d → ℝ}
    (h : f =ᵐ[torusMeasure d] g) : densityEntropy f = densityEntropy g := by
  apply integral_congr_ae
  filter_upwards [h] with x hx
  rw [hx]

#print axioms functional_nonpos
#print axioms maximizer_entropy_eq_log
#print axioms dualPotential_log_of_equality
end BecknerOnofri.EndpointRigidity.MaximizerLevel
