import Legacy.BecknerOnofri.SteinerSelection

/-!
Dimension-independent critical exponential integrability and variational selection.

The imported legacy proof has been generalized at its only dimension-specific
analytic step: a finite, dimension-dependent theta majorant replaces the old
ten-dimensional majorant. No endpoint inequality, optimizer, or rough exponential
estimate is assumed in the theorems below. All objects are the actual normalized
Haar torus, its Fourier L² basis, and the real mean-zero critical Sobolev class.
-/

noncomputable section
open MeasureTheory

namespace BecknerOnofri.GenericAttainment

open Legacy.TorusEndpoint Legacy.BecknerOnofri
open Legacy.BecknerOnofri.TorusSobolev
open Legacy.BecknerOnofri.SubcriticalAttainment

/-- Genuine rough exponential bound in every positive dimension. -/
theorem rough_bound {d : ℕ} (hd : 0 < d) {b : ℝ}
    (hb : 0 < b) (hbd : b < endpointConstant d) :
    RoughExponentialBound d b (GreenRoughEnergy.partition d b) :=
  roughExponentialBound hd hb hbd

/-- Every positive exponential moment of a real critical Sobolev potential exists. -/
theorem critical_exp_integrable {d : ℕ} (hd : 0 < d)
    (u : TorusL2 d) (hu : Admissible u) {p : ℝ} (hp : 0 < p) :
    Integrable (fun x => Real.exp (p * (u x).re)) (torusMeasure d) := by
  have hC : 0 < endpointConstant d :=
    div_pos (Nat.cast_pos.mpr hd) (endpointSigma_pos hd)
  exact (rough_bound hd (by positivity : 0 < endpointConstant d / 2)
    (by linarith : endpointConstant d / 2 < endpointConstant d) u hu p hp).1

/-- Quantitative logarithmic bound; the additive constant is an actual finite
Green-kernel exponential integral. -/
theorem critical_log_partition_bound {d : ℕ} (hd : 0 < d) {b : ℝ}
    (hb : 0 < b) (hbd : b < endpointConstant d)
    (u : TorusL2 d) (hu : Admissible u) {p : ℝ} (hp : 0 < p) :
    Real.log (∫ x, Real.exp (p * (u x).re) ∂torusMeasure d) ≤
      p ^ 2 * criticalEnergy u / (4 * b) +
        Real.log (GreenRoughEnergy.partition d b) :=
  (rough_bound hd hb hbd u hu p hp).2

/-- Attainment strictly above the concentration coefficient, in every positive
integer dimension, without an assumed compactness or rough-bound premise. -/
theorem exists_subcritical_optimizer {d : ℕ} (hd : 0 < d) {A : ℝ}
    (hA : 1 / (4 * endpointConstant d) < A) :
    ∃ u : TorusL2 d, Admissible u ∧ 0 ≤ functional A u ∧
      ∀ v : TorusL2 d, Admissible v → functional A v ≤ functional A u :=
  exists_subcritical_maximizer hd hA

/-- A smooth Gibbs density and its continuous potential may both be selected
coordinatewise Steiner, with the true variational maximum preserved. -/
theorem exists_steiner_optimizer {d : ℕ} (hd : 0 < d) {A : ℝ}
    (hA : 1 / (4 * endpointConstant d) < A) :
    ∃ u : TorusL2 d, Admissible u ∧
      (∀ v : TorusL2 d, Admissible v → functional A v ≤ functional A u) ∧
      SteinerSelection.Steiner (SmoothFourier.smoothGibbsValue u) ∧
      SteinerSelection.Steiner (fun x => (WienerFourier.representative u x).re) :=
  SteinerSelection.exists_steiner_maximizer hd hA

#print axioms rough_bound
#print axioms critical_exp_integrable
#print axioms critical_log_partition_bound
#print axioms exists_subcritical_optimizer
#print axioms exists_steiner_optimizer

end BecknerOnofri.GenericAttainment
