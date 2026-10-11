module

public import BecknerOnofri.V2.Reaudit.ExternalInputs.CriticalAdams
public import BecknerOnofri.V2.Reaudit.Attainment.Basic
public import BecknerOnofri.SubcriticalGap
public import BecknerOnofri.ElevenConstants

@[expose] public section

/-! # The rough exponential estimate from the printed critical Adams inequality

The compactness arguments of Section 4 (`prop:section4-first-order-coexistence`, estimate
`eq:section4-uniform-exponential-p-bound`) and of Section 5 (`eq:section5-onset-uniform-bounds`) use the
*sharp* critical Adams inequality `eq:section2-critical-adams`,
`log ∫ e^{u-ū} ≤ A_crit ‖u‖²_{Ḣ^{d/2}} + B`, applied to `p u` (so with the constant `p² A_crit`).
The repository's compactness code is written against the predicate
`Legacy.BecknerOnofri.SubcriticalAttainment.RoughExponentialBound d b Ab`, i.e. for every admissible
(real, mean-zero, `Ḣ^{d/2}`) potential `u` and every `p > 0`, `e^{p u}` is integrable and
`log ∫ e^{p u} ≤ p² E(u)/(4b) + log Ab`, `E` the critical energy `Σ_{k≠0} |k|^d |û(k)|²`.

This file proves that predicate **from `V2.Vocab.CriticalAdamsInput d`** with the *sharp* exponent
`b = endpointConstant d = d/β_s(d)`, i.e. `1/(4b) = A_crit(d)` in the energy normalization of the
`RoughExponentialBound` (`potentialEnergy u = (2π)^d E(u)`, `A_crit = β_s/(4 d (2π)^d)`).  Nothing from the
low-dimensional endpoint chain or from the old rough bound `GenericAttainment.rough_bound` is used here.

Admissible potentials are real-valued and have mean zero, so `centered u = u` and no hypothesis of
mean zero is lost (the predicate is false for potentials that are not mean zero, but it only ever
quantifies over `Admissible` ones).

* `integrable_and_log_le_of_criticalAdams`: the content of the inequality for one mean-zero
  `v ∈ H^{d/2}`: `e^v` is integrable (finiteness of the right-hand side) and the log bound in real form.
* `roughExponentialBound_of_criticalAdams`: the bridge, with `Ab = exp B`.
* `eleven_rough_gap_of_adams`, `exists_rough_gap_of_adams`: the statements of
  `HighDim.Eleven.eleven_rough_gap` and `OnsetCompactness.exists_rough_gap` (suppliers of the rough
  bound for the compactness arguments in `d = 11` and `d ≥ 12`), proved from the bridge with
  `b = endpointConstant d` and the gap `1/(4b) = A_crit(d) < 1/2`. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory

namespace BecknerOnofri.V2.Reaudit.ExternalInputs
open BecknerOnofri.HighDim
open Legacy.BecknerOnofri Legacy.BecknerOnofri.TorusSobolev Legacy.BecknerOnofri.SubcriticalAttainment

/-- `A_crit(d) (2π)^d = 1/(4 b)` with `b = endpointConstant d`: the normalization of the energy in
`RoughExponentialBound` (no `2π`) against `potentialEnergy` (with `(2π|k|)^d`). -/
theorem collapseCoefficient_mul_twoPi_pow {d : ℕ} (hd : 0 < d) :
    collapseCoefficient d * (2 * Real.pi) ^ d = 1 / (4 * endpointConstant d) := by
  have hσ : 0 < Legacy.TorusEndpoint.endpointSigma d := Legacy.TorusEndpoint.endpointSigma_pos hd
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hc : (2 * Real.pi) ^ d ≠ 0 := (pow_pos (by positivity : 0 < 2 * Real.pi) d).ne'
  unfold collapseCoefficient endpointConstant
  change Legacy.TorusEndpoint.endpointSigma d / (4 * (d : ℝ) * (2 * Real.pi) ^ d) * (2 * Real.pi) ^ d =
    1 / (4 * ((d : ℝ) / Legacy.TorusEndpoint.endpointSigma d))
  field_simp

/-- The printed critical Adams inequality, for one mean-zero `v ∈ H^{d/2}`: `e^v` is integrable (the
right-hand side is finite) and `log ∫ e^v ≤ A_crit ‖v‖² + B`. -/
theorem integrable_and_log_le_of_criticalAdams {d : ℕ} {B : ℝ}
    (hB : ∀ u : Torus d → ℝ, InCriticalSobolev u →
      logPartition u ≤ ((collapseCoefficient d * potentialEnergy u + B : ℝ) : EReal))
    {v : Torus d → ℝ} (hv : InCriticalSobolev v) (hm : MeanZero v) :
    Integrable (fun x => Real.exp (v x)) (torusMeasure d) ∧
      Real.log (∫ x, Real.exp (v x) ∂torusMeasure d) ≤ collapseCoefficient d * potentialEnergy v + B := by
  have h := hB v hv
  have hc : centered v = v := Attainment.centered_eq_self hm
  unfold logPartition at h
  rw [hc] at h
  have hItop : (∫⁻ x, ENNReal.ofReal (Real.exp (v x)) ∂torusMeasure d) ≠ ⊤ := by
    intro ht
    rw [ht, ENNReal.log_top] at h
    exact EReal.coe_ne_top _ (top_le_iff.mp h)
  have hmeas : AEStronglyMeasurable (fun x => Real.exp (v x)) (torusMeasure d) :=
    Real.continuous_exp.comp_aestronglyMeasurable hv.1.aestronglyMeasurable
  have hnn : 0 ≤ᵐ[torusMeasure d] fun x => Real.exp (v x) :=
    Filter.Eventually.of_forall fun x => (Real.exp_pos _).le
  have hint : Integrable (fun x => Real.exp (v x)) (torusMeasure d) :=
    ⟨hmeas, (hasFiniteIntegral_iff_ofReal hnn).2 (lt_top_iff_ne_top.2 hItop)⟩
  refine ⟨hint, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn,
    ENNReal.log_ofReal_of_pos (integral_exp_pos hint)] at h
  exact EReal.coe_le_coe_iff.mp h

/-- **The rough exponential bound from the printed critical Adams inequality (sharp exponent).**
With `b = endpointConstant d` (`1/(4b) = A_crit(d)` in the `RoughExponentialBound` normalization) and
`Ab = exp B`, `B` the additive constant of `eq:section2-critical-adams`. -/
theorem roughExponentialBound_of_criticalAdams {d : ℕ} (hd : 0 < d)
    (h : V2.Vocab.CriticalAdamsInput d) :
    ∃ Ab : ℝ, 0 < Ab ∧ RoughExponentialBound d (endpointConstant d) Ab := by
  obtain ⟨B, hB⟩ := (V2.Vocab.criticalAdamsInput_iff hd).1 h
  refine ⟨Real.exp B, Real.exp_pos B, fun U hU p hp => ?_⟩
  have hu := RawAttainment.realValue_sobolev U hU
  have hum := RawAttainment.realValue_meanZero U hU
  have hv := Attainment.inCriticalSobolev_const_mul p hu
  have hvm := Attainment.meanZero_const_mul p hum
  obtain ⟨hint, hlog⟩ := integrable_and_log_le_of_criticalAdams hB hv hvm
  have hE : potentialEnergy (fun x => p * RawAttainment.realValue U x) =
      p ^ 2 * ((2 * Real.pi) ^ d * criticalEnergy U) := by
    rw [Attainment.potentialEnergy_const_mul, RawAttainment.realValue_energy hd U hU]
  refine ⟨hint, ?_⟩
  refine hlog.trans (le_of_eq ?_)
  rw [hE, Real.log_exp]
  have hk := collapseCoefficient_mul_twoPi_pow hd
  calc collapseCoefficient d * (p ^ 2 * ((2 * Real.pi) ^ d * criticalEnergy U)) + B
      = p ^ 2 * criticalEnergy U * (collapseCoefficient d * (2 * Real.pi) ^ d) + B := by ring
    _ = p ^ 2 * criticalEnergy U / (4 * endpointConstant d) + B := by
        rw [hk]; ring

/-- The bridge applied to `ExternalInputs.criticalAdams`. -/
theorem roughExponentialBound_sharp {d : ℕ} (hd : 0 < d) :
    ∃ Ab : ℝ, 0 < Ab ∧ RoughExponentialBound d (endpointConstant d) Ab :=
  roughExponentialBound_of_criticalAdams hd (criticalAdams hd)

/-- `endpointConstant d > 1/2` for `d = 11` (`β_s(11) < 22`). -/
theorem endpointConstant_eleven_gt_half : (1 / 2 : ℝ) < endpointConstant 11 := by
  unfold endpointConstant
  change (1 / 2 : ℝ) < (11 : ℝ) / spectralThreshold 11
  apply (lt_div_iff₀ (spectralThreshold_pos (d := 11) (by norm_num))).mpr
  linarith [Eleven.spectralThreshold_bounds.2]

/-- `endpointConstant d > 1/2` for `d ≥ 12` (the strict subcritical gap `β_s(d) < 2d`). -/
theorem endpointConstant_gt_half {d : ℕ} (hd : 12 ≤ d) : (1 / 2 : ℝ) < endpointConstant d := by
  have hd0 : 0 < d := by omega
  unfold endpointConstant
  apply (lt_div_iff₀ (Legacy.TorusEndpoint.endpointSigma_pos hd0)).mpr
  have := spectral_subcritical_gap hd
  change Legacy.TorusEndpoint.endpointSigma d < 2 * (d : ℝ) at this
  linarith

/-- Statement of `HighDim.Eleven.eleven_rough_gap`, now from the printed critical Adams inequality with the
sharp exponent `b = endpointConstant 11`. -/
theorem eleven_rough_gap_of_adams :
    ∃ b Ab : ℝ, 0 < b ∧ RoughExponentialBound 11 b Ab ∧ 1 / (4 * b) < (1 / 2 : ℝ) := by
  have hC := endpointConstant_eleven_gt_half
  obtain ⟨Ab, -, hR⟩ := roughExponentialBound_sharp (d := 11) (by norm_num)
  refine ⟨endpointConstant 11, Ab, by linarith, hR, ?_⟩
  apply (div_lt_iff₀ (by linarith : 0 < 4 * endpointConstant 11)).mpr
  linarith

/-- Statement of `OnsetCompactness.exists_rough_gap`, now from the printed critical Adams inequality with
the sharp exponent `b = endpointConstant d`. -/
theorem exists_rough_gap_of_adams {d : ℕ} (hd : 12 ≤ d) :
    ∃ b Ab : ℝ, 0 < b ∧ RoughExponentialBound d b Ab ∧ 1 / (4 * b) < (1 / 2 : ℝ) := by
  have hC := endpointConstant_gt_half hd
  obtain ⟨Ab, -, hR⟩ := roughExponentialBound_sharp (d := d) (by omega)
  refine ⟨endpointConstant d, Ab, by linarith, hR, ?_⟩
  apply (div_lt_iff₀ (by linarith : 0 < 4 * endpointConstant d)).mpr
  linarith

end BecknerOnofri.V2.Reaudit.ExternalInputs
