import Legacy.BecknerOnofri.SubcriticalPrimalDual
import Legacy.BecknerOnofri.EntropyVariationalEquality

/-! Actual coefficient-parametrized entropy endpoint and its proved Sobolev duality. -/

noncomputable section
open MeasureTheory
namespace BecknerOnofri.EndpointRigidity
open Legacy.TorusEndpoint Legacy.BecknerOnofri
open TorusSobolev SubcriticalAttainment SubcriticalEuler SubcriticalPrimalDual

/-- The genuine full finite-entropy density inequality, with its coefficient
explicit instead of tied to the dimension-one-through-ten coefficient. -/
def CoefficientEndpoint (d : ℕ) (C : ℝ) : Prop :=
  ∀ r : ProbabilityDensity d, r.FiniteEntropy →
    Summable (densitySpectralTerm r) ∧ C * fourierEnergy r ≤ densityEntropy r.value

namespace AnalyticEndpoint

def coefficient (C : ℝ) : ℝ := 1 / (4 * C)

theorem coefficient_pos {C : ℝ} (hC : 0 < C) : 0 < coefficient C := by
  unfold coefficient
  positivity

theorem rough_of_endpoint {d : ℕ} (hd : 0 < d) {C : ℝ} (hC : 0 < C)
    (hE : CoefficientEndpoint d C) : RoughExponentialBound d C 1 :=
  roughExponentialBound_of_density_bound hd hC
    (fun r hr => by simpa using (hE r (PhysicalGreenL2.finiteEntropy_of_memLp r hr)).2)

theorem onofri_scaled {d : ℕ} (hd : 0 < d) {C : ℝ} (hC : 0 < C)
    (hE : CoefficientEndpoint d C) {u : TorusL2 d} (hu : Admissible u) {p : ℝ} (hp : 0 < p) :
    Integrable (fun x => Real.exp (p * (u x).re)) (torusMeasure d) ∧
      Real.log (∫ x, Real.exp (p * (u x).re) ∂torusMeasure d) ≤
        p ^ 2 * criticalEnergy u / (4 * C) := by
  simpa using rough_of_endpoint hd hC hE u hu p hp

theorem onofri {d : ℕ} (hd : 0 < d) {C : ℝ} (hC : 0 < C)
    (hE : CoefficientEndpoint d C) {u : TorusL2 d} (hu : Admissible u) :
    Integrable (fun x => Real.exp (u x).re) (torusMeasure d) ∧
      Real.log (partition u) ≤ coefficient C * criticalEnergy u := by
  simpa only [one_mul, one_pow, partition, coefficient, div_eq_mul_inv, mul_comm] using
    onofri_scaled hd hC hE hu zero_lt_one

#print axioms onofri

end AnalyticEndpoint
end BecknerOnofri.EndpointRigidity
