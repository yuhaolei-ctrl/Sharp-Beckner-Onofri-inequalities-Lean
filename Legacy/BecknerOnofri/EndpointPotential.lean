import Legacy.BecknerOnofri.SubcriticalPrimalDual
import Legacy.BecknerOnofri.EntropyVariationalEquality

/-! Conditional duality from the actual finite-entropy Endpoint statement to
the sharp potential inequality. Exponential integrability is proved using
truncated Gibbs densities, rather than included as an additional hypothesis. -/
noncomputable section
open MeasureTheory Legacy.TorusEndpoint
namespace Legacy.BecknerOnofri.EndpointPotential
open TorusSobolev SubcriticalAttainment SubcriticalEuler SubcriticalPrimalDual

def coefficient (d : ℕ) : ℝ := 1/(4*endpointConstant d)

theorem endpointConstant_pos {d : ℕ} (hd : 0 < d) : 0 < endpointConstant d :=
  div_pos (Nat.cast_pos.mpr hd) (endpointSigma_pos hd)

theorem coefficient_pos {d : ℕ} (hd : 0 < d) : 0 < coefficient d := by
  have := endpointConstant_pos hd
  unfold coefficient
  positivity

/-- The zero-defect rough bound is a consequence of Endpoint, for every actual
admissible potential and every positive exponential moment. -/
theorem rough_of_endpoint {d : ℕ} (hd : 0 < d) (hE : Endpoint d) :
    RoughExponentialBound d (endpointConstant d) 1 :=
  roughExponentialBound_of_density_bound hd (endpointConstant_pos hd)
    (fun r hr => by simpa using (hE r (PhysicalGreenL2.finiteEntropy_of_memLp r hr)).2)

theorem onofri_scaled {d : ℕ} (hd : 0 < d) (hE : Endpoint d)
    {u : TorusL2 d} (hu : Admissible u) {p : ℝ} (hp : 0 < p) :
    Integrable (fun x => Real.exp (p*(u x).re)) (torusMeasure d) ∧
      Real.log (∫ x, Real.exp (p*(u x).re) ∂torusMeasure d) ≤
        p^2 * criticalEnergy u/(4*endpointConstant d) := by
  simpa using rough_of_endpoint hd hE u hu p hp

theorem onofri {d : ℕ} (hd : 0 < d) (hE : Endpoint d)
    {u : TorusL2 d} (hu : Admissible u) :
    Integrable (fun x => Real.exp (u x).re) (torusMeasure d) ∧
      Real.log (partition u) ≤ coefficient d * criticalEnergy u := by
  simpa only [one_mul,one_pow,partition,coefficient,div_eq_mul_inv,mul_comm] using
    onofri_scaled hd hE hu zero_lt_one

theorem functional_nonpositive {d : ℕ} (hd : 0 < d) (hE : Endpoint d)
    {u : TorusL2 d} (hu : Admissible u) : functional (coefficient d) u ≤ 0 :=
  sub_nonpos.mpr (onofri hd hE hu).2

theorem densityFunctional_nonpositive {d : ℕ} (_hd : 0 < d) (hE : Endpoint d)
    (r : ProbabilityDensity d) (hr : r.FiniteEntropy) : densityFunctional (coefficient d) r ≤ 0 := by
  have hc : 1/(4*coefficient d) = endpointConstant d := by unfold coefficient; field_simp
  rw [densityFunctional,hc]
  exact sub_nonpos.mpr (hE r hr).2

/-- Potential equality gives an actual global endpoint maximizer. -/
theorem maximizer_of_equality {d : ℕ} (hd : 0 < d) (hE : Endpoint d)
    {u : TorusL2 d} (_hu : Admissible u)
    (he : Real.log (partition u) = coefficient d * criticalEnergy u) :
    ∀ v : TorusL2 d, Admissible v → functional (coefficient d) v ≤ functional (coefficient d) u := by
  intro v hv
  have hz : functional (coefficient d) u = 0 := sub_eq_zero.mpr he
  rw [hz]
  exact functional_nonpositive hd hE hv

/-- Every potential equality case has an actual finite-entropy L2 Gibbs density
which attains equality in the density endpoint. -/
theorem gibbs_equality_of_potential_equality {d : ℕ} (hd : 0 < d) (hE : Endpoint d)
    {u : TorusL2 d} (hu : Admissible u)
    (he : Real.log (partition u) = coefficient d * criticalEnergy u) :
    endpointConstant d * fourierEnergy (gibbsDensity (rough_of_endpoint hd hE) hu) =
      densityEntropy (gibbsValue u) := by
  have hlo := dual_le_gibbs hd (rough_of_endpoint hd hE) (coefficient_pos hd) hu
  have hhi := densityFunctional_nonpositive hd hE (gibbsDensity (rough_of_endpoint hd hE) hu)
    (gibbsDensity_finiteEntropy (rough_of_endpoint hd hE) hu)
  have hz : functional (coefficient d) u = 0 := sub_eq_zero.mpr he
  have hc : 1/(4*coefficient d) = endpointConstant d := by unfold coefficient; field_simp
  rw [hz,densityFunctional,hc] at hlo
  rw [densityFunctional,hc] at hhi
  change _ ≤ endpointConstant d*fourierEnergy _-densityEntropy (gibbsValue u) at hlo
  change endpointConstant d*fourierEnergy _-densityEntropy (gibbsValue u) ≤ _ at hhi
  linarith

/-- The dimension range is only used to select the supplied Endpoint theorem. -/
theorem onofri_through_ten (hE : EndpointThroughTen) {d : ℕ} (hd : 1 ≤ d) (hd10 : d ≤ 10)
    {u : TorusL2 d} (hu : Admissible u) :
    Integrable (fun x => Real.exp (u x).re) (torusMeasure d) ∧
      Real.log (partition u) ≤ coefficient d * criticalEnergy u :=
  onofri (by omega) (hE d hd hd10) hu

#print axioms rough_of_endpoint
#print axioms onofri
#print axioms gibbs_equality_of_potential_equality
end Legacy.BecknerOnofri.EndpointPotential
