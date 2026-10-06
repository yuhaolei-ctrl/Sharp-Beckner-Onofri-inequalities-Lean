module

public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Tactic

@[expose] public section

/-! # An elementary bound for the exponential integral

Lemma 3.1 (lem:E1-bound): for `x > 0`,
`e^x ∫_1^∞ e^{-x r}/r dr < g(x)` with `g(x) = (x²+5x+2)/(x(x²+6x+6))`.

The proof is derivative-free in the sense of the paper: `g - 1/y - g' = ρ > 0`, so the
function `r ↦ -e^{-x(r-1)} g(xr)` has the positive derivative `e^{-x(r-1)} (1/r + xρ(xr))`
and tends to zero, and the fundamental theorem of calculus on `[1, ∞)` concludes. -/

noncomputable section
open MeasureTheory Set Filter Topology

namespace BecknerOnofri.HighDim.ThetaElementary

/-- The rational majorant `g(x) = (x²+5x+2)/(x(x²+6x+6))` of Lemma 3.1. -/
def e1Majorant (x : ℝ) : ℝ := (x ^ 2 + 5 * x + 2) / (x * (x ^ 2 + 6 * x + 6))

/-- The defect `ρ(y) = 12/(y²(y²+6y+6)²) = g(y) - 1/y - g'(y)`. -/
def e1Defect (y : ℝ) : ℝ := 12 / (y ^ 2 * (y ^ 2 + 6 * y + 6) ^ 2)

theorem e1Majorant_pos {x : ℝ} (hx : 0 < x) : 0 < e1Majorant x := by
  unfold e1Majorant; positivity

theorem e1Defect_pos {y : ℝ} (hy : 0 < y) : 0 < e1Defect y := by
  unfold e1Defect; positivity

theorem e1Majorant_le_inv {x : ℝ} (hx : 0 < x) : e1Majorant x ≤ x⁻¹ := by
  unfold e1Majorant
  rw [div_le_iff₀ (by positivity), ← mul_assoc, inv_mul_cancel₀ hx.ne', one_mul]
  nlinarith

/-- The derivative identity `g' = g - 1/y - ρ`. -/
theorem hasDerivAt_e1Majorant {y : ℝ} (hy : 0 < y) :
    HasDerivAt e1Majorant (e1Majorant y - y⁻¹ - e1Defect y) y := by
  have hD : y * (y ^ 2 + 6 * y + 6) ≠ 0 := by positivity
  have h := ((((hasDerivAt_pow 2 y).add ((hasDerivAt_id' y).const_mul 5)).add_const 2).div
    ((hasDerivAt_id' y).mul (((hasDerivAt_pow 2 y).add
      ((hasDerivAt_id' y).const_mul 6)).add_const 6)) hD)
  convert h using 1
  · funext t
    simp only [e1Majorant, Pi.add_apply, Pi.mul_apply, Pi.div_apply]
  simp only [e1Majorant, e1Defect, Pi.add_apply, Pi.mul_apply, Nat.cast_ofNat,
    Nat.add_one_sub_one, pow_one, mul_one, one_mul]
  field_simp
  ring

/-- The antiderivative `r ↦ -e^{-x(r-1)} g(xr)` used in Lemma 3.1. -/
def e1Primitive (x r : ℝ) : ℝ := -(Real.exp (-x * (r - 1)) * e1Majorant (x * r))

/-- The derivative of `e1Primitive x`, namely `e^{-x(r-1)} (1/r + x ρ(xr))`. -/
def e1Density (x r : ℝ) : ℝ := Real.exp (-x * (r - 1)) * (r⁻¹ + x * e1Defect (x * r))

theorem hasDerivAt_e1Primitive {x r : ℝ} (hx : 0 < x) (hr : 0 < r) :
    HasDerivAt (e1Primitive x) (e1Density x r) r := by
  have hxr : 0 < x * r := mul_pos hx hr
  have he : HasDerivAt (fun s : ℝ => Real.exp (-x * (s - 1)))
      (Real.exp (-x * (r - 1)) * (-x * 1)) r :=
    (((hasDerivAt_id' r).sub_const 1).const_mul (-x)).exp
  have hg : HasDerivAt (fun s : ℝ => e1Majorant (x * s))
      ((e1Majorant (x * r) - (x * r)⁻¹ - e1Defect (x * r)) * (x * 1)) r :=
    (hasDerivAt_e1Majorant hxr).comp r ((hasDerivAt_id' r).const_mul x)
  convert (he.mul hg).neg using 1
  · funext s
    simp only [e1Primitive, Pi.neg_apply, Pi.mul_apply]
  unfold e1Density
  rw [mul_inv]
  field_simp
  ring

theorem e1Density_nonneg {x r : ℝ} (hx : 0 < x) (hr : 0 < r) : 0 ≤ e1Density x r := by
  have := e1Defect_pos (mul_pos hx hr)
  unfold e1Density
  positivity

theorem tendsto_e1Primitive {x : ℝ} (hx : 0 < x) :
    Tendsto (e1Primitive x) atTop (𝓝 0) := by
  have hlin : Tendsto (fun r : ℝ => x * (r - 1)) atTop atTop :=
    Tendsto.const_mul_atTop hx (tendsto_atTop_add_const_right _ (-1) tendsto_id)
  have hexp : Tendsto (fun r : ℝ => Real.exp (-x * (r - 1))) atTop (𝓝 0) := by
    refine (Real.tendsto_exp_neg_atTop_nhds_zero.comp hlin).congr fun r => ?_
    simp only [Function.comp_apply, neg_mul]
  have hup : Tendsto (fun r : ℝ => Real.exp (-x * (r - 1)) * x⁻¹) atTop (𝓝 0) := by
    simpa only [zero_mul] using hexp.mul_const x⁻¹
  have hsq : Tendsto (fun r : ℝ => Real.exp (-x * (r - 1)) * e1Majorant (x * r))
      atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
    · filter_upwards [eventually_ge_atTop 1] with r hr
      have := e1Majorant_pos (mul_pos hx (zero_lt_one.trans_le hr))
      positivity
    · filter_upwards [eventually_ge_atTop 1] with r hr
      have hxr : 0 < x * r := mul_pos hx (zero_lt_one.trans_le hr)
      refine mul_le_mul_of_nonneg_left ((e1Majorant_le_inv hxr).trans ?_) (Real.exp_pos _).le
      exact inv_anti₀ hx (le_mul_of_one_le_right hx.le hr)
  show Tendsto (fun r => -(Real.exp (-x * (r - 1)) * e1Majorant (x * r))) atTop (𝓝 0)
  simpa only [neg_zero] using hsq.neg

theorem e1Density_integrableOn {x : ℝ} (hx : 0 < x) :
    IntegrableOn (e1Density x) (Ioi 1) :=
  integrableOn_Ioi_deriv_of_nonneg'
    (fun _ hr => hasDerivAt_e1Primitive hx (zero_lt_one.trans_le hr))
    (fun _ hr => e1Density_nonneg hx (zero_lt_one.trans hr)) (tendsto_e1Primitive hx)

theorem integral_e1Density {x : ℝ} (hx : 0 < x) :
    ∫ r in Ioi 1, e1Density x r = e1Majorant x := by
  rw [integral_Ioi_of_hasDerivAt_of_nonneg'
    (fun _ hr => hasDerivAt_e1Primitive hx (zero_lt_one.trans_le hr))
    (fun _ hr => e1Density_nonneg hx (zero_lt_one.trans hr)) (tendsto_e1Primitive hx)]
  simp [e1Primitive]

/-- The shifted reciprocal exponential `r⁻¹ e^{-x(r-1)}` is integrable on `[1, ∞)`. -/
theorem inv_mul_exp_integrableOn {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun r : ℝ => r⁻¹ * Real.exp (-x * (r - 1))) (Ici 1) := by
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  refine (e1Density_integrableOn hx).mono' (by fun_prop) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  have hr0 : 0 < r := zero_lt_one.trans hr
  have := e1Defect_pos (mul_pos hx hr0)
  have hp : 0 ≤ Real.exp (-x * (r - 1)) * (x * e1Defect (x * r)) := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  unfold e1Density
  rw [mul_add, mul_comm (Real.exp _) r⁻¹]
  linarith

/-- Lemma 3.1 (lem:E1-bound), shifted form:
`∫_1^∞ r⁻¹ e^{-x(r-1)} dr < g(x)` for `x > 0`. -/
theorem integral_inv_mul_exp_lt {x : ℝ} (hx : 0 < x) :
    ∫ r in Ici (1 : ℝ), r⁻¹ * Real.exp (-x * (r - 1)) < e1Majorant x := by
  set h : ℝ → ℝ := fun r => Real.exp (-x * (r - 1)) * (x * e1Defect (x * r)) with hh
  have hf := (inv_mul_exp_integrableOn hx).mono_set Ioi_subset_Ici_self
  have hsplit : e1Density x = fun r => r⁻¹ * Real.exp (-x * (r - 1)) + h r := by
    funext r
    simp only [e1Density, hh]
    ring
  have hhi : IntegrableOn h (Ioi 1) := by
    have := (e1Density_integrableOn hx).sub hf
    refine this.congr_fun (fun r _ => ?_) measurableSet_Ioi
    simp only [Pi.sub_apply, hsplit]
    ring
  have hpos : 0 < ∫ r in Ioi 1, h r := by
    rw [setIntegral_pos_iff_support_of_nonneg_ae _ hhi]
    · have hsub : Ioi (1 : ℝ) ⊆ Function.support h ∩ Ioi 1 := by
        intro r hr
        refine ⟨?_, hr⟩
        have hr0 : 0 < r := zero_lt_one.trans hr
        have := e1Defect_pos (mul_pos hx hr0)
        exact (show 0 < h r by simp only [hh]; positivity).ne'
      exact lt_of_lt_of_le (by simp) (measure_mono hsub)
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      have := e1Defect_pos (mul_pos hx (zero_lt_one.trans hr))
      simp only [Pi.zero_apply, hh]
      positivity
  have hint := integral_e1Density hx
  rw [hsplit, integral_add hf hhi] at hint
  rw [integral_Ici_eq_integral_Ioi]
  linarith

/-- Lemma 3.1 (lem:E1-bound), non-strict shifted form used in the theta certificate. -/
theorem integral_inv_mul_exp_le {x : ℝ} (hx : 0 < x) :
    ∫ r in Ici (1 : ℝ), r⁻¹ * Real.exp (-x * (r - 1)) ≤ e1Majorant x :=
  (integral_inv_mul_exp_lt hx).le

/-- Lemma 3.1 (lem:E1-bound), as stated in the paper:
`e^x ∫_1^∞ e^{-xr}/r dr < (x²+5x+2)/(x(x²+6x+6))` for `x > 0`. -/
theorem exp_mul_integral_exp_div_lt {x : ℝ} (hx : 0 < x) :
    Real.exp x * ∫ r in Ioi (1 : ℝ), Real.exp (-x * r) / r <
      (x ^ 2 + 5 * x + 2) / (x * (x ^ 2 + 6 * x + 6)) := by
  have he : (fun r : ℝ => Real.exp (-x * r) / r) =
      fun r => Real.exp (-x) * (r⁻¹ * Real.exp (-x * (r - 1))) := by
    funext r
    have hs : Real.exp (-x * r) = Real.exp (-x) * Real.exp (-x * (r - 1)) := by
      rw [← Real.exp_add]; ring_nf
    rw [hs, div_eq_mul_inv]
    ring
  rw [he, integral_const_mul, ← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero,
    one_mul, ← integral_Ici_eq_integral_Ioi]
  exact integral_inv_mul_exp_lt hx

end BecknerOnofri.HighDim.ThetaElementary
