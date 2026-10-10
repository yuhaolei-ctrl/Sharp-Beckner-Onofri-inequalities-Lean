module

public import BecknerOnofri.V2.Reaudit.Attainment.Basic
public import BecknerOnofri.V2.Onset.Bootstrap
public import BecknerOnofri.V2.Onset.FirstStep
public import BecknerOnofri.GraphRegularity
public import BecknerOnofri.GeneralSobolevEmbedding

@[expose] public section

/-! # Membership in every `H^{jd}` implies smoothness (package `Attainment`)

The last sentence of the regularity paragraph of `cor:section2-extremizer-correspondence`:
"Iterating proves `u, ρ ∈ C^∞`."  The Sobolev bootstrap (`V2.Onset.sobolev_bootstrap`) places a
continuous function in `H^{(m+1)d}` for every `m`; this file converts that into
`SmoothOnTorus`, by showing that membership in `H^{s}` with `s ≥ m + d` makes the polynomially
weighted Fourier series `∑ (1+|k|)^m |û(k)|` converge (Cauchy–Schwarz against
`∑ (1+(2π|k|)²)^{-d}`, which converges because `d > d/2`), and then using the repository's
`GraphRegularity.smooth_of_radial`. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped Topology ENNReal

namespace BecknerOnofri.V2.Reaudit.Attainment
open BecknerOnofri.HighDim

variable {d : ℕ}

/-- Pointwise weight comparison: `(1+|k|)^m ≤ (√2)^m (1 + (2π|k|)²)^{m/2}`. -/
theorem radialWeight_le_scale (m : ℕ) (k : Frequency d) :
    Legacy.BecknerOnofri.RadialWiener.radialWeight m k ≤
      Real.sqrt 2 ^ m * sobolevScale (m : ℝ) k := by
  have hr : 0 ≤ frequencyLength k := Real.sqrt_nonneg _
  set B : ℝ := 1 + (2 * Real.pi * frequencyLength k) ^ 2 with hB
  have hpi : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have h1 : (1 + frequencyLength k) ^ 2 ≤ 2 * B := by
    have : frequencyLength k ^ 2 ≤ (2 * Real.pi * frequencyLength k) ^ 2 := by
      rw [mul_pow]
      exact le_mul_of_one_le_left (sq_nonneg _) (by nlinarith)
    nlinarith [sq_nonneg (frequencyLength k - 1)]
  have hs2 : sobolevScale (m : ℝ) k ^ 2 = B ^ m := by
    rw [sobolevScale_sq, Real.rpow_natCast]
  have hnn : 0 ≤ Real.sqrt 2 ^ m * sobolevScale (m : ℝ) k :=
    mul_nonneg (pow_nonneg (Real.sqrt_nonneg _) _) (sobolevScale_pos _ _).le
  unfold Legacy.BecknerOnofri.RadialWiener.radialWeight
  change (1 + frequencyLength k) ^ m ≤ _
  refine le_of_sq_le_sq ?_ hnn
  calc ((1 + frequencyLength k) ^ m) ^ 2 = ((1 + frequencyLength k) ^ 2) ^ m := by
        rw [← pow_mul, ← pow_mul, mul_comm]
    _ ≤ (2 * B) ^ m := pow_le_pow_left₀ (by positivity) h1 m
    _ = (Real.sqrt 2 ^ m * sobolevScale (m : ℝ) k) ^ 2 := by
      rw [mul_pow 2 B m, mul_pow (Real.sqrt 2 ^ m) _ 2, hs2, ← pow_mul, mul_comm m 2, pow_mul,
        Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-- Splitting a Sobolev weight: `scale_{s-d} = scale_s / scale_d`. -/
theorem sobolevScale_sub_mul (s e : ℝ) (k : Frequency d) :
    sobolevScale (s - e) k = sobolevScale s k * (sobolevScale e k)⁻¹ := by
  unfold sobolevScale
  have hB : 0 < 1 + (2 * Real.pi * frequencyLength k) ^ 2 := by positivity
  rw [← Real.rpow_neg hB.le, ← Real.rpow_add hB]
  congr 1
  ring

theorem sobolevScale_mono {s t : ℝ} (hst : s ≤ t) (k : Frequency d) :
    sobolevScale s k ≤ sobolevScale t k := by
  unfold sobolevScale
  exact Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg (2 * Real.pi * frequencyLength k)])
    (by linarith)

/-- Membership in `H^s` with `s ≥ m + d` makes the radial moment of order `m` summable. -/
theorem radial_of_inSobolev (hd : 0 < d) (v : ContinuousGibbs.Space d) (m : ℕ) {s : ℝ}
    (hs : (m : ℝ) + d ≤ s) (hv : InSobolev s (⇑v)) : GraphRegularity.Radial m v := by
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have ha : Summable (fun k : Frequency d => (sobolevScale s k * ‖fourierCoeff (⇑v) k‖) ^ 2) := by
    refine hv.2.congr fun k => ?_
    rw [Onset.sobolevTerm_eq]
  have hb : Summable (fun k : Frequency d => ((sobolevScale (d : ℝ) k)⁻¹) ^ 2) :=
    Onset.summable_inverse_scale_sq hd (by linarith)
  have hab : Summable (fun k : Frequency d =>
      (sobolevScale s k * ‖fourierCoeff (⇑v) k‖) * (sobolevScale (d : ℝ) k)⁻¹) := by
    refine Summable.of_nonneg_of_le (fun k => by
      have := sobolevScale_pos (d := d) s k
      have := sobolevScale_pos (d := d) (d : ℝ) k
      positivity) (fun k => ?_) ((ha.add hb).mul_left (1 / 2))
    nlinarith [sq_nonneg (sobolevScale s k * ‖fourierCoeff (⇑v) k‖ - (sobolevScale (d : ℝ) k)⁻¹)]
  have hfin := hab.mul_left (Real.sqrt 2 ^ m)
  unfold GraphRegularity.Radial Legacy.BecknerOnofri.RadialWiener.RadialSummable
  refine Summable.of_nonneg_of_le (fun k => mul_nonneg (by
    unfold Legacy.BecknerOnofri.RadialWiener.radialWeight
    exact pow_nonneg (by linarith [Legacy.TorusEndpoint.frequencyRadius_nonneg k]) _)
    (norm_nonneg _)) (fun k => ?_) hfin
  beta_reduce
  rw [ContinuousFirstShell.coefficient_eq_fourierCoeff]
  have h1 := radialWeight_le_scale (d := d) m k
  have h2 : sobolevScale (m : ℝ) k ≤ sobolevScale (s - d) k := sobolevScale_mono (by linarith) k
  rw [sobolevScale_sub_mul] at h2
  have hn := norm_nonneg (fourierCoeff (⇑v) k)
  calc Legacy.BecknerOnofri.RadialWiener.radialWeight m k * ‖fourierCoeff (⇑v) k‖
      ≤ (Real.sqrt 2 ^ m * sobolevScale (m : ℝ) k) * ‖fourierCoeff (⇑v) k‖ :=
        mul_le_mul_of_nonneg_right h1 hn
    _ ≤ (Real.sqrt 2 ^ m * (sobolevScale s k * (sobolevScale (d : ℝ) k)⁻¹)) *
          ‖fourierCoeff (⇑v) k‖ := by
        gcongr
    _ = Real.sqrt 2 ^ m * ((sobolevScale s k * ‖fourierCoeff (⇑v) k‖) *
          (sobolevScale (d : ℝ) k)⁻¹) := by ring

/-- A continuous function lying in `H^{(m+1)d}` for every `m` is smooth. -/
theorem smooth_of_inSobolev_multiples (hd : 0 < d) (v : ContinuousGibbs.Space d)
    (h : ∀ m : ℕ, InSobolev (((m : ℝ) + 1) * d) (⇑v)) : SmoothOnTorus (⇑v) := by
  refine GraphRegularity.smooth_of_radial v fun m => radial_of_inSobolev hd v m ?_ (h m)
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  nlinarith

end BecknerOnofri.V2.Reaudit.Attainment
