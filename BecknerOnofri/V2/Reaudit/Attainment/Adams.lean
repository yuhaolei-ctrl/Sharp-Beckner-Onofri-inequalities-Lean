module

public import BecknerOnofri.V2.Reaudit.Attainment.Basic
public import BecknerOnofri.GenericAttainment
public import BecknerOnofri.V2.Onset.Bootstrap

@[expose] public section

/-! # The form of `eq:section2-critical-adams` used in Section 2 (package `Attainment`)

The manuscript's input is `eq:section2-critical-adams`:
`log ∫ e^{u-ū} ≤ A_crit ‖u‖²_{Ḣ^{d/2}} + B_d`, i.e. `BecknerOnofri.V2.Vocab.CriticalAdamsInput`.
The proof of `prop:section2-subcritical-attainment` applies it only at coefficients `A > A_crit`
(coercivity) and to `2u_n`, where `4 A_crit ‖u_n‖²` may be replaced by `4 a ‖u_n‖²` for any
`a > A_crit`.  We therefore isolate the following consequence of the printed inequality:

`CriticalAdamsAboveThreshold d`: for every `a > A_crit(d)` there is `B` with `e^u` integrable and
`log ∫ e^u ≤ a ‖u‖²_{Ḣ^{d/2}} + B` for every mean-zero `u ∈ H^{d/2}`.

This is a *weaker* statement than `CriticalAdamsInput d` (`criticalAdamsAboveThreshold_of_input` in `AdamsInput.lean`).
It is also proved outright, without any hypothesis, from the repository's rough exponential bound
(`criticalAdamsAboveThreshold_unconditional`); that bound is available for every coefficient
`a > A_crit` but, unlike the sharp inequality, not at `a = A_crit`. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped Topology ENNReal

namespace BecknerOnofri.V2.Reaudit.Attainment
open BecknerOnofri.HighDim
open Legacy.BecknerOnofri.SubcriticalAttainment Legacy.BecknerOnofri.TorusSobolev

variable {d : ℕ}

/-- The consequence of `eq:section2-critical-adams` used in `prop:section2-subcritical-attainment`. -/
def CriticalAdamsAboveThreshold (d : ℕ) : Prop :=
  ∀ a : ℝ, collapseCoefficient d < a → ∃ B : ℝ, ∀ u : Torus d → ℝ, InCriticalSobolev u →
    MeanZero u → Integrable (fun x => Real.exp (u x)) (torusMeasure d) ∧
      Real.log (∫ x, Real.exp (u x) ∂torusMeasure d) ≤ a * potentialEnergy u + B

/-- The consequence used in Section 2 holds unconditionally, by the rough exponential bound
`GenericAttainment.rough_bound` (valid for every coefficient strictly above `A_crit`). -/
theorem criticalAdamsAboveThreshold_unconditional (hd : 0 < d) : CriticalAdamsAboveThreshold d := by
  intro a ha
  have hc : 0 < (2 * Real.pi) ^ d := pow_pos (by positivity) d
  have hσ : 0 < spectralThreshold d := Legacy.TorusEndpoint.endpointSigma_pos hd
  have hcrit0 : 0 < collapseCoefficient d := by
    unfold collapseCoefficient
    have : (0 : ℝ) < d := by exact_mod_cast hd
    positivity
  have ha0 : 0 < a := lt_trans hcrit0 ha
  set b : ℝ := 1 / (4 * a * (2 * Real.pi) ^ d) with hb
  have hb0 : 0 < b := by rw [hb]; positivity
  have hthr := RawAttainment.physical_threshold hd (A := a) ha
  have hbd : b < Legacy.BecknerOnofri.endpointConstant d := by
    have hEC : 0 < Legacy.BecknerOnofri.endpointConstant d :=
      div_pos (Nat.cast_pos.mpr hd) hσ
    rw [hb, div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ (by positivity)] at hthr
    nlinarith
  have hR := GenericAttainment.rough_bound hd hb0 hbd
  refine ⟨Real.log (Legacy.BecknerOnofri.GreenRoughEnergy.partition d b), fun u hu hm => ?_⟩
  set P : TorusL2 d := Bridge.potentialLp u hu.1 with hP
  have hcrit : CriticalSobolev P := by
    refine ⟨?_, Bridge.potentialLp_summable hd u hu⟩
    rw [hP, Bridge.potentialLp_fourier]
    exact BecknerOnofri.V2.Onset.fourierCoeff_zero_meanZero hm
  have hadm : Admissible P := ⟨Bridge.potentialLp_real u hu.1, hcrit⟩
  obtain ⟨hint, hlog⟩ := hR P hadm 1 zero_lt_one
  have hre : (fun x => (P x).re) =ᵐ[torusMeasure d] u := by
    filter_upwards [Bridge.potentialLp_ae u hu.1] with x hx
    simp [hP, hx]
  have hexp : (fun x => Real.exp (1 * (P x).re)) =ᵐ[torusMeasure d] fun x => Real.exp (u x) := by
    filter_upwards [hre] with x hx
    rw [one_mul, hx]
  refine ⟨hint.congr hexp, ?_⟩
  have h3 : (∫ x, Real.exp (1 * (P x).re) ∂torusMeasure d) = ∫ x, Real.exp (u x) ∂torusMeasure d :=
    integral_congr_ae hexp
  have hlog' : Real.log (∫ x, Real.exp (1 * (P x).re) ∂torusMeasure d) ≤
      1 ^ 2 * criticalEnergy P / (4 * b) +
        Real.log (Legacy.BecknerOnofri.GreenRoughEnergy.partition d b) := hlog
  rw [h3] at hlog'
  have hen : criticalEnergy P = potentialEnergy u / (2 * Real.pi) ^ d := by
    rw [hP, Bridge.potentialLp_energy hd u hu]
    field_simp
  rw [hen] at hlog'
  refine hlog'.trans (le_of_eq ?_)
  rw [hb]
  field_simp

end BecknerOnofri.V2.Reaudit.Attainment
