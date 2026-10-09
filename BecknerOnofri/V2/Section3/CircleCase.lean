module

public import BecknerOnofri.V2.Section3.CircleBound
public import BecknerOnofri.PartitionRegularity
public import Legacy.BecknerOnofri.CircleEqualityComplete

@[expose] public section

/-! # The circle `d = 1` of Theorem 1.1: equality cases (G04)

The equality classification (Poisson kernels, resp. the logarithms `-2 log |1 - \bar a e^{2πix}| + c`)
is the repository's circle theorem `CircleEquality.{density,onofri}_equality_iff_paper_family`,
translated to the manuscript normalization (it is *nonconstant*, and nothing from `d ≥ 2` is used).
The entropy and potential bounds are in `CircleBound.lean`.

(Module closure note: `CircleEqualityComplete` imports the legacy module `LowDimensionOnofri` whose
other theorems use the old numerical chain; the declarations used here do not, see `RESOLUTION.md`.) -/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology ComplexConjugate

namespace BecknerOnofri.V2.Section3
open BecknerOnofri.HighDim BecknerOnofri.V2.Vocab

/-- Equality in the circle entropy bound: exactly the Poisson kernels `ρ_a`. -/
theorem circle_entropy_equality_iff (ρ : ProbabilityDensity 1) (hρ : ρ.FiniteEntropy) :
    EntropyEquality 1 ρ ↔
      ∃ a : ℂ, ‖a‖ < 1 ∧ ρ.value =ᵐ[torusMeasure 1]
        fun x => (1 - ‖a‖ ^ 2) / ‖fourier 1 (x 0) - a‖ ^ 2 := by
  have h := Legacy.BecknerOnofri.CircleEquality.density_equality_iff_paper_family
    (Bridge.density ρ) hρ
  obtain ⟨hsum, -⟩ := Legacy.D10.CircleEntropy.entropy_bound (Bridge.density ρ) hρ
  have hterm : Legacy.TorusEndpoint.densitySpectralTerm (Bridge.density ρ) =
      fun k : Legacy.TorusEndpoint.NonzeroFrequency 1 =>
        Legacy.D10.CircleEntropy.weight k.val *
          ‖Legacy.TorusEndpoint.densityFourier (Bridge.density ρ).value k.val‖ ^ 2 :=
    funext (Legacy.BecknerOnofri.circle_energyTerm (Bridge.density ρ))
  have hsum' : Summable (Legacy.TorusEndpoint.densitySpectralTerm (Bridge.density ρ)) := by
    rw [hterm]; exact hsum
  have h1 := energy_real_eq_legacy (d := 1) (by norm_num) ρ (Bridge.density ρ)
    (Filter.EventuallyEq.rfl) hsum'
  have h2 := entropy_real_eq_legacy ρ hρ (Bridge.density ρ) (Filter.EventuallyEq.rfl)
  unfold EntropyEquality
  rw [h1, h2]
  exact h


/-! ### The potential equality family -/

theorem collapseCoefficient_eq_legacy {d : ℕ} (hd : 0 < d) :
    collapseCoefficient d = 1 / (4 * (d : ℝ) * Legacy.TorusEndpoint.endpointSymbolConstant d) := by
  unfold collapseCoefficient
  change Legacy.TorusEndpoint.endpointSigma d / (4 * (d : ℝ) * (2 * Real.pi)^d) = _
  rw [← Legacy.TorusEndpoint.endpointSymbolConstant_mul_sigma hd]
  have hs := Legacy.TorusEndpoint.endpointSigma_pos hd
  have hc := Legacy.TorusEndpoint.endpointSymbolConstant_pos hd
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  field_simp

theorem centeredPartition_potentialLp {d : ℕ} (u : Torus d → ℝ) (hu : MemLp u 2 (torusMeasure d)) :
    Legacy.BecknerOnofri.EndpointPotential.centeredPartition (Bridge.potentialLp u hu) =
      ∫ x, Real.exp (centered u x) ∂torusMeasure d := by
  have hr : (fun x => (Bridge.potentialLp u hu x).re) =ᵐ[torusMeasure d] u := by
    filter_upwards [Bridge.potentialLp_ae u hu] with x hx
    simp [hx]
  have hi := integral_congr_ae hr
  apply integral_congr_ae
  filter_upwards [hr] with x hx
  change Real.exp ((Bridge.potentialLp u hu x).re -
    ∫ y, (Bridge.potentialLp u hu y).re ∂torusMeasure d) = Real.exp (centered u x)
  simp only [centered, hx, hi]

theorem manuscriptEnergy_potentialLp {d : ℕ} (hd : 0 < d) (u : Torus d → ℝ)
    (hu : InCriticalSobolev u) :
    Legacy.BecknerOnofri.EndpointPotential.manuscriptEnergy (Bridge.potentialLp u hu.1) =
      potentialEnergy u := by
  rw [Legacy.BecknerOnofri.EndpointPotential.manuscriptEnergy_eq hd _
    (Bridge.potentialLp_summable hd u hu), Bridge.potentialLp_energy hd u hu]

/-- Equality in the circle potential inequality: exactly the conformal family
`u_a = -2 log |1 - \bar a e^{2πix}| + c`. -/
theorem circle_potential_equality_iff (u : Torus 1 → ℝ) (hu : InCriticalSobolev u) :
    logPartition u = ((collapseCoefficient 1 * potentialEnergy u : ℝ) : EReal) ↔
      ∃ a : ℂ, ‖a‖ < 1 ∧ ∃ c : ℝ,
        u =ᵐ[torusMeasure 1] fun x => -2 * Real.log ‖1 - conj a * fourier 1 (x 0)‖ + c := by
  have h := Legacy.BecknerOnofri.CircleEquality.onofri_equality_iff_paper_family
    (Bridge.potentialLp_real u hu.1) (Bridge.potentialLp_summable (by norm_num) u hu)
  rw [centeredPartition_potentialLp u hu.1, manuscriptEnergy_potentialLp (by norm_num) u hu] at h
  have hc := collapseCoefficient_eq_legacy (by norm_num : 0 < 1)
  norm_num only [Nat.cast_one, mul_one] at hc h
  rw [← hc] at h
  rw [logPartition_eq_log_integral (by norm_num) u hu, EReal.coe_eq_coe_iff, h]
  constructor
  · rintro ⟨a, ha, c, hc⟩
    refine ⟨a, ha, c, ?_⟩
    filter_upwards [hc, Bridge.potentialLp_ae u hu.1] with x hx hu'
    have := congrArg Complex.re (hu'.symm.trans hx)
    simpa using this
  · rintro ⟨a, ha, c, hc⟩
    refine ⟨a, ha, c, ?_⟩
    filter_upwards [hc, Bridge.potentialLp_ae u hu.1] with x hx hu'
    simpa [hx] using hu'

#print axioms circle_entropy_bound
#print axioms circle_pressure_two
#print axioms circle_potential_bound
#print axioms circle_entropy_equality_iff
#print axioms circle_potential_equality_iff

end BecknerOnofri.V2.Section3
