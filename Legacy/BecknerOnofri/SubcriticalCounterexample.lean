module

public import Legacy.BecknerOnofri.GreenDensityPotential
public import Legacy.BecknerOnofri.SobolevScalar
public import Legacy.BecknerOnofri.SubcriticalRoughBound
public import Legacy.TorusEndpoint.ExtendedEntropy

@[expose] public section

/-! An actual strict density counterexample produces a positive subcritical
global maximizer. The Green potential and all variational bounds are proved.
-/
namespace Legacy.BecknerOnofri.SubcriticalCounterexample
open MeasureTheory Legacy.TorusEndpoint TorusSobolev SubcriticalAttainment GreenDensityPotential

theorem scaledPotential_pairing {d : ℕ} (hd : 0 < d) (r : ProbabilityDensity d)
    (hc : Continuous r.value) (t : ℝ) :
    (∫ x, r.value x * ((((t : ℂ) • potentialLp r hc) x).re) ∂torusMeasure d) =
      t * fourierEnergy r := by
  have hr : MemLp r.value 2 (torusMeasure d) :=
    hc.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have he : potentialLp r hc =ᵐ[torusMeasure d] (fun x => (GreenRoughEnergy.potential r x : ℂ)) :=
    (potential_memLp r hc).ofReal.coeFn_toLp
  calc
    _ = ∫ x, t * (r.value x * GreenRoughEnergy.potential r x) ∂torusMeasure d := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_smul (t : ℂ) (potentialLp r hc), he] with x hx hg
      rw [hx]
      change r.value x * ((t : ℂ) * potentialLp r hc x).re = _
      rw [hg]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      ring
    _ = _ := by rw [integral_const_mul, GreenRoughEnergy.pairing_eq_fourier hd r hr]

theorem scaledPotential_functional_lower {d : ℕ} (hd : 0 < d)
    (r : ProbabilityDensity d) (hc : Continuous r.value) {b : ℝ}
    (hb : 0 < b) (hbd : b < endpointConstant d) :
    b * fourierEnergy r - densityEntropy r.value ≤
      functional (1/(4*b)) (((2*b : ℝ) : ℂ) • potentialLp r hc) := by
  let v : TorusL2 d := (((2*b : ℝ) : ℂ) • potentialLp r hc)
  have hv : Admissible v := admissible_smul_real (potentialLp_admissible hd r hc) (2*b)
  have hr : MemLp r.value 2 (torusMeasure d) :=
    hc.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hR := roughExponentialBound hd hb hbd
  have h := entropy_variational_of_integrable r.nonneg r.mass r.integrable
    (PhysicalGreenL2.finiteEntropy_of_memLp r hr)
    (hr.integrable_mul (Lp.memLp v).re) (partition_integrable hR hv)
  change (∫ x, r.value x*(v x).re ∂torusMeasure d) - Real.log (partition v) ≤ densityEntropy r.value at h
  have hp := scaledPotential_pairing hd r hc (2*b)
  change (∫ x, r.value x*(v x).re ∂torusMeasure d) = _ at hp
  rw [hp] at h
  have hE : criticalEnergy v = (2*b)^2 * fourierEnergy r := by
    dsimp only [v]
    rw [criticalEnergy_smul_real, potentialLp_energy hd]
  have he : (1/(4*b))*((2*b)^2*fourierEnergy r) = b*fourierEnergy r := by
    field_simp
    ring
  change b*fourierEnergy r-densityEntropy r.value ≤ functional (1/(4*b)) v
  rw [functional, hE, he]
  linarith

theorem exists_positive_subcritical_maximizer {d : ℕ} (hd : 0 < d)
    (r : ProbabilityDensity d) (hc : Continuous r.value)
    (hfail : densityEntropy r.value < endpointConstant d * fourierEnergy r) :
    ∃ A : ℝ, 1/(4*endpointConstant d) < A ∧
      ∃ u : TorusL2 d, Admissible u ∧ 0 < functional A u ∧
        ∀ v : TorusL2 d, Admissible v → functional A v ≤ functional A u := by
  have hC : 0 < endpointConstant d := div_pos (Nat.cast_pos.mpr hd) (endpointSigma_pos hd)
  have hr : MemLp r.value 2 (torusMeasure d) :=
    hc.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hEnt := densityEntropy_nonneg_of_finite r (PhysicalGreenL2.finiteEntropy_of_memLp r hr)
  have hQ : 0 < fourierEnergy r := by nlinarith
  have hgap : densityEntropy r.value / fourierEnergy r < endpointConstant d :=
    (div_lt_iff₀ hQ).mpr (by simpa [mul_comm] using hfail)
  obtain ⟨b, hbEnt, hbC⟩ := exists_between hgap
  have hb : 0 < b := (div_nonneg hEnt hQ.le).trans_lt hbEnt
  have hA : 1/(4*endpointConstant d) < 1/(4*b) :=
    one_div_lt_one_div_of_lt (by positivity) (by nlinarith)
  obtain ⟨u, hu, _, hmax⟩ := exists_subcritical_maximizer hd hA
  refine ⟨1/(4*b), hA, u, hu, ?_, hmax⟩
  have hv := admissible_smul_real (potentialLp_admissible hd r hc) (2*b)
  have hm := hmax _ hv
  have hl := scaledPotential_functional_lower hd r hc hb hbC
  have hpos := (div_lt_iff₀ hQ).mp hbEnt
  linarith

#print axioms exists_positive_subcritical_maximizer
end Legacy.BecknerOnofri.SubcriticalCounterexample
