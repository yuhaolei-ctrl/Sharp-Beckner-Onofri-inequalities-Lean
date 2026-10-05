import Legacy.BecknerOnofri.GreenDensityPotentialL2
import Legacy.BecknerOnofri.SubcriticalCounterexample
import Legacy.BecknerOnofri.SubcriticalEulerEnergy

/-! Primal-dual comparison and actual density maximizers on the full L2
probability class. These results do not assume a selected or smooth optimizer. -/
noncomputable section
namespace Legacy.BecknerOnofri.SubcriticalPrimalDual
open MeasureTheory Legacy.TorusEndpoint TorusSobolev SubcriticalAttainment SubcriticalEuler
open GreenDensityPotentialL2

def densityFunctional {d : ℕ} (A : ℝ) (r : ProbabilityDensity d) : ℝ :=
  (1/(4*A))*fourierEnergy r - densityEntropy r.value

theorem scaledPotential_pairing {d : ℕ} (hd : 0 < d) (r : ProbabilityDensity d)
    (hr : MemLp r.value 2 (torusMeasure d)) (t : ℝ) :
    (∫ x, r.value x * ((((t : ℂ) • potentialLp r hr) x).re) ∂torusMeasure d) =
      t * fourierEnergy r := by
  calc
    _ = ∫ x, t * (r.value x * GreenRoughEnergy.potential r x) ∂torusMeasure d := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_smul (t : ℂ) (potentialLp r hr), potentialLp_ae r hr] with x hx hg
      rw [hx]
      change r.value x * ((t : ℂ) * potentialLp r hr x).re = _
      rw [hg]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      ring
    _ = _ := by rw [integral_const_mul, GreenRoughEnergy.pairing_eq_fourier hd r hr]

def dualPotential {d : ℕ} (A : ℝ) (r : ProbabilityDensity d)
    (hr : MemLp r.value 2 (torusMeasure d)) : TorusL2 d :=
  ((1/(2*A) : ℝ) : ℂ) • potentialLp r hr

theorem dualPotential_admissible {d : ℕ} (hd : 0 < d) (A : ℝ)
    (r : ProbabilityDensity d) (hr : MemLp r.value 2 (torusMeasure d)) :
    Admissible (dualPotential A r hr) :=
  admissible_smul_real (potentialLp_admissible hd r hr) _

theorem density_le_dual {d : ℕ} (hd : 0 < d) {b Ab A : ℝ}
    (hR : RoughExponentialBound d b Ab) (hA : 0 < A) (r : ProbabilityDensity d)
    (hr : MemLp r.value 2 (torusMeasure d)) :
    densityFunctional A r ≤ functional A (dualPotential A r hr) := by
  let v := dualPotential A r hr
  have hv := dualPotential_admissible hd A r hr
  have h := entropy_variational_of_integrable r.nonneg r.mass r.integrable
    (PhysicalGreenL2.finiteEntropy_of_memLp r hr)
    (hr.integrable_mul (Lp.memLp v).re) (partition_integrable hR hv)
  change (∫ x, r.value x*(v x).re ∂torusMeasure d) - Real.log (partition v) ≤ densityEntropy r.value at h
  have hp := scaledPotential_pairing hd r hr (1/(2*A))
  change (∫ x, r.value x*(v x).re ∂torusMeasure d) = _ at hp
  rw [hp] at h
  have hE : criticalEnergy v = (1/(2*A))^2 * fourierEnergy r := by
    dsimp only [v, dualPotential]
    rw [criticalEnergy_smul_real, potentialLp_energy hd]
  have he : A*((1/(2*A))^2*fourierEnergy r) = (1/(4*A))*fourierEnergy r := by
    field_simp
    ring
  change densityFunctional A r ≤ functional A v
  rw [functional, hE, he, densityFunctional]
  have hpA : 1/(2*A) = 2*(1/(4*A)) := by field_simp; norm_num
  rw [hpA] at h
  linarith

theorem dual_le_gibbs {d : ℕ} (hd : 0 < d) {b Ab A : ℝ}
    (hR : RoughExponentialBound d b Ab) (hA : 0 < A)
    {u : TorusL2 d} (hu : Admissible u) :
    functional A u ≤ densityFunctional A (gibbsDensity hR hu) := by
  have hpair := SobolevDensityPairing.pairing_quadratic_bound hd u hu.2
    (gibbsDensity hR hu) (gibbsValue_memLp_two hR hu) (1/(4*A)) (by positivity) 1 (by norm_num)
  have hcoef : (1:ℝ)^2*criticalEnergy u/(4*(1/(4*A))) = A*criticalEnergy u := by field_simp
  rw [hcoef, one_mul] at hpair
  unfold densityFunctional
  change functional A u ≤ _ - densityEntropy (gibbsValue u)
  rw [gibbsDensity_entropy hR hu, functional]
  change (∫ x, gibbsValue u x * (u x).re ∂torusMeasure d) ≤ _ at hpair
  linarith

theorem gibbs_density_maximizer {d : ℕ} (hd : 0 < d) {b Ab A : ℝ}
    (hR : RoughExponentialBound d b Ab) (hA : 0 < A) {u : TorusL2 d}
    (hu : Admissible u)
    (hmax : ∀ v : TorusL2 d, Admissible v → functional A v ≤ functional A u)
    (r : ProbabilityDensity d) (hr : MemLp r.value 2 (torusMeasure d)) :
    densityFunctional A r ≤ densityFunctional A (gibbsDensity hR hu) := by
  calc
    _ ≤ functional A (dualPotential A r hr) := density_le_dual hd hR hA r hr
    _ ≤ functional A u := hmax _ (dualPotential_admissible hd A r hr)
    _ = _ := maximizer_functional_eq_density hd hR hA hu hmax

/-- Every L2 density maximizer produces an actual global Sobolev maximizer,
and both objective values agree. This is the interface needed after rearrangement. -/
theorem density_maximizer_dual {d : ℕ} (hd : 0 < d) {b Ab A : ℝ}
    (hR : RoughExponentialBound d b Ab) (hA : 0 < A)
    (r : ProbabilityDensity d) (hr : MemLp r.value 2 (torusMeasure d))
    (hmax : ∀ q : ProbabilityDensity d, MemLp q.value 2 (torusMeasure d) →
      densityFunctional A q ≤ densityFunctional A r) :
    functional A (dualPotential A r hr) = densityFunctional A r ∧
      ∀ v : TorusL2 d, Admissible v →
        functional A v ≤ functional A (dualPotential A r hr) := by
  have hv := dualPotential_admissible hd A r hr
  have hupper (v : TorusL2 d) (hvad : Admissible v) : functional A v ≤ densityFunctional A r :=
    (dual_le_gibbs hd hR hA hvad).trans (hmax _ (gibbsValue_memLp_two hR hvad))
  have he := le_antisymm (hupper _ hv) (density_le_dual hd hR hA r hr)
  exact ⟨he, fun v hvad => by rw [he]; exact hupper v hvad⟩

theorem exists_density_maximizer {d : ℕ} (hd : 0 < d) {A : ℝ}
    (hA : 1/(4*endpointConstant d) < A) :
    ∃ r : ProbabilityDensity d, MemLp r.value 2 (torusMeasure d) ∧ r.FiniteEntropy ∧
      0 ≤ densityFunctional A r ∧
      ∀ q : ProbabilityDensity d, MemLp q.value 2 (torusMeasure d) →
        densityFunctional A q ≤ densityFunctional A r := by
  have hC : 0 < endpointConstant d := div_pos (Nat.cast_pos.mpr hd) (endpointSigma_pos hd)
  have hA0 : 0 < A := (by positivity : 0 < 1/(4*endpointConstant d)).trans hA
  have hR := roughExponentialBound hd (by positivity : 0 < endpointConstant d/2)
    (by linarith : endpointConstant d/2 < endpointConstant d)
  obtain ⟨u, hu, hzero, hmax⟩ := exists_subcritical_maximizer hd hA
  refine ⟨gibbsDensity hR hu, gibbsValue_memLp_two hR hu, gibbsDensity_finiteEntropy hR hu, ?_, ?_⟩
  · rwa [maximizer_functional_eq_density hd hR hA0 hu hmax] at hzero
  · exact gibbs_density_maximizer hd hR hA0 hu hmax

#print axioms density_le_dual
#print axioms dual_le_gibbs
#print axioms density_maximizer_dual
#print axioms exists_density_maximizer
end Legacy.BecknerOnofri.SubcriticalPrimalDual
