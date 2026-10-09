module

public import BecknerOnofri.V2.Section3.Lemma31
public import BecknerOnofri.V2.Section3.LegacyBridge
public import BecknerOnofri.PartitionRegularity
public import Legacy.D10.CircleEntropy
public import Legacy.BecknerOnofri.CircleEqualityComplete

@[expose] public section

/-! # The circle `d = 1` of Theorem 1.1 (G04)

`d = 1` is *not* obtained from the rigidity argument of Lemma 3.1 (which is false there: the
Lebedev--Milin equality family is nonconstant).  Instead:

* the entropy bound `Ent ρ ≥ c_1 ‖ρ‖²_{Ḣ^{-1/2}}` on the full finite-entropy domain is Lemma 3.2 with
  `d = 1` (`Legacy.D10.CircleEntropy.entropy_bound`), translated to the manuscript normalization;
* `P_1(2) = 0`, `C_1(A_c(1)) = 0` and the potential inequality follow by the same duality as in
  Lemma 3.1 (`..._of_full`);
* the equality classification (Poisson kernels, resp. the logarithms `-2 log |1 - \bar a e^{2πix}| + c`)
  is the repository's circle theorem `CircleEquality.{density,onofri}_equality_iff_paper_family`,
  translated to the manuscript normalization (it is *nonconstant*, and nothing from `d ≥ 2` is used).

(Module closure note: `CircleEqualityComplete` imports the legacy module `LowDimensionOnofri` whose
other theorems use the old numerical chain; the declarations used here do not, see `RESOLUTION.md`.) -/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology ComplexConjugate

namespace BecknerOnofri.V2.Section3
open BecknerOnofri.HighDim BecknerOnofri.V2.Vocab

/-- Lemma 3.2 for the circle, in the manuscript normalization: `Ent ρ ≥ c_1 ‖ρ‖²` for every
finite-entropy density on `𝕋`. -/
theorem circle_entropy_bound (ρ : ProbabilityDensity 1) (hρ : ρ.FiniteEntropy) :
    EntropyBound 1 ρ := by
  obtain ⟨hsum, hbound⟩ := Legacy.D10.CircleEntropy.entropy_bound (Bridge.density ρ) hρ
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
  unfold EntropyBound
  rw [h1, h2]
  have hc : Legacy.BecknerOnofri.endpointConstant 1 = 1 / 2 := Legacy.BecknerOnofri.endpointConstant_one
  rw [hc]
  unfold Legacy.BecknerOnofri.fourierEnergy
  rw [hterm]
  change 1 / 2 * _ ≤ Legacy.TorusEndpoint.densityEntropy (Bridge.density ρ).value
  linarith

/-- `P_1(2) = 0`. -/
theorem circle_pressure_two : pressure 1 (2 * ((1 : ℕ) : ℝ)) = 0 :=
  pressure_two_d_eq_zero_of_full (by norm_num) (fun ρ hρ => circle_entropy_bound ρ hρ)

/-- Lebedev--Milin: the potential inequality on the circle with the coefficient `A_c(1)`. -/
theorem circle_potential_bound (u : Torus 1 → ℝ) (hu : InCriticalSobolev u) :
    Integrable (fun x => Real.exp (centered u x)) (torusMeasure 1) ∧
      logPartition u ≤ ((collapseCoefficient 1 * potentialEnergy u : ℝ) : EReal) :=
  potential_bound_of_full (by norm_num) (fun ρ hρ => circle_entropy_bound ρ hρ) u hu

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
