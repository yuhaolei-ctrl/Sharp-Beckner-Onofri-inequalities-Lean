module

public import Legacy.BecknerOnofri.GaussianScalarTwo
public import BecknerOnofri.LowScalarFull
public import BecknerOnofri.V2.Reaudit.ShellMargins.Theta

@[expose] public section

/-! # Row S020, two-dimensional tail: the elementary boundary case `s = 1` for `n ≥ 4`

Replacement text: `ManuscriptPatch/manuscript_v2_proposed.tex` lines 2186-2198 (marker `% REAUDIT S020`),
`eq:reaudit-S020-two-central` and `eq:dimension-two-large`; original text in the decisions package,
section 3.4 ("For the remaining two-dimensional indices ...").

The Lean route (`Legacy.BecknerOnofri.GaussianScalarTwo.large_indices_lattice_gap`) is the route of the
text, concluding only the margin `3/1100`; here the central estimate is stated as printed and the margin
`63407/1500000` is proved from the same ingredients. -/

noncomputable section
open Legacy.BecknerOnofri

namespace BecknerOnofri.V2.Reaudit.ShellMargins

open BecknerOnofri.HighDim

/-- `4/β_s(2) = 2d/β_s(d) |_{d = 2} = 2/π` ([TeX `manuscript_v2_proposed.tex` line 2187]) (`2d/β_s(d) = dΓ(s)/π^s`, `s = d/2 = 1`). -/
theorem coupling_two : (4 : ℝ) / spectralThreshold 2 = 2 / Real.pi := by
  have he : (4 : ℝ) / spectralThreshold 2 = 2 * endpointConstant 2 := by
    unfold endpointConstant spectralThreshold Legacy.TorusEndpoint.endpointSigma
    push_cast
    ring
  rw [he]
  exact GaussianScalarTwoFinite.lambda_two

/-- **`eq:reaudit-S020-two-central`** [TeX `manuscript_v2_proposed.tex` lines 2188-2191].  For `n ≥ 1` and `a = log(1 + 1/n)`:
`(2/π) G_{2,n} ≤ 2 (log π - log a - 1 + J_2) + 2a/π`. -/
theorem two_central_bound {n : ℕ} (hn : 1 ≤ n) :
    (2 / Real.pi) * LowScalar.energy 2 n ≤
      2 * (Real.log Real.pi - Real.log (Real.log (1 + 1 / (n : ℝ))) - 1 +
        LowScalar.thetaIntegral 2) + 2 * Real.log (1 + 1 / (n : ℝ)) / Real.pi := by
  set a := Real.log (1 + 1 / (n : ℝ)) with ha_def
  have ha : 0 < a := GaussianLattice.log_parameter_pos (by omega)
  have hap : a < Real.pi := GaussianScalarTail.gaussian_parameter_lt_pi n hn
  have hgauss := GaussianHeatTwo.gaussianEnergy_two_le ha hap
  rw [LowScalar.energy_eq_legacy]
  calc
    _ ≤ (2 / Real.pi) * GaussianLattice.gaussianEnergy 2 a :=
        mul_le_mul_of_nonneg_left (GaussianLattice.binomialEnergy_le_gaussianEnergy (by omega))
          (by positivity)
    _ ≤ (2 / Real.pi) * (Real.pi * (Real.log Real.pi - Real.log a - 1 +
          ThetaDomination.thetaIntegral ThetaDomination.realTheta 2) + a) :=
        mul_le_mul_of_nonneg_left hgauss (by positivity)
    _ = _ := by
        change _ = 2 * (Real.log Real.pi - Real.log a - 1 +
          ThetaDomination.thetaIntegral ThetaDomination.realTheta 2) + 2 * a / Real.pi
        field_simp

/-- The constant of `eq:dimension-two-large`:
`2 (5772/10000 + 1 - 1144731/10^6 - 41/125) - 1/6 = 63407/1500000 > 3/1100`. -/
theorem dimension_two_constant :
    2 * (5772 / 10000 + 1 - 1144731 / 10 ^ 6 - 41 / 125 : ℚ) - 1 / 6 = 63407 / 1500000 ∧
      (3 / 1100 : ℚ) < 63407 / 1500000 := by
  constructor <;> norm_num

/-- **`eq:dimension-two-large`** [TeX `manuscript_v2_proposed.tex` lines 2193-2197].  For `n ≥ 4`,
`2 H_n - (4/β_s(2)) G_{2,n} > 2 (5772/10000 + 1 - 1144731/10^6 - 41/125) - 1/6 = 63407/1500000`. -/
theorem dimension_two_large {n : ℕ} (hn : 4 ≤ n) :
    2 * (5772 / 10000 + 1 - 1144731 / 10 ^ 6 - 41 / 125 : ℝ) - 1 / 6 <
      2 * (harmonic n : ℝ) - ((4 : ℝ) / spectralThreshold 2) * LowScalar.energy 2 n := by
  have h1 : 1 ≤ n := by omega
  set a := Real.log (1 + 1 / (n : ℝ)) with ha_def
  have hcen := two_central_bound h1
  rw [← ha_def] at hcen
  have hsmall : 2 * a / Real.pi < (1 / 6 : ℝ) := by
    have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn
    have hrecip : 1 / (n : ℝ) ≤ (1 / 4 : ℝ) :=
      one_div_le_one_div_of_le (by norm_num) hnR
    have hlog := UniformTail.log_one_add_inv_lt n (by omega)
    have ha4 : a < (1 / 4 : ℝ) := hlog.trans_le hrecip
    rw [div_lt_iff₀ Real.pi_pos]
    nlinarith [Real.pi_gt_three]
  have hH := HarmonicGaussian.harmonic_add_log_gaussian_ge_gamma n h1
  rw [← ha_def] at hH
  have hJ : LowScalar.thetaIntegral 2 ≤ (41 / 125 : ℝ) := J2_le_41_125.1.trans J2_le_41_125.2
  have hg := EulerLower.gamma_lower
  have hpi := UniformTail.log_pi_upper
  rw [coupling_two]
  nlinarith only [hcen, hsmall, hH, hJ, hg, hpi]

/-- The printed form: the margin `63407/1500000` itself. -/
theorem dimension_two_large_printed {n : ℕ} (hn : 4 ≤ n) :
    (63407 / 1500000 : ℝ) < 2 * (harmonic n : ℝ) -
      ((4 : ℝ) / spectralThreshold 2) * LowScalar.energy 2 n := by
  have h := dimension_two_large hn
  have e : 2 * (5772 / 10000 + 1 - 1144731 / 10 ^ 6 - 41 / 125 : ℝ) - 1 / 6 = 63407 / 1500000 := by
    norm_num
  rwa [e] at h

/-- The case `d = 2` of `eq:delta-common` (the text's "nine rational inequalities", `2 ≤ d ≤ 10`; the
legacy `UniformTail.delta_gt_common` covers `3 ≤ d ≤ 10`):
`Δ_2 > (3/200) · 2 · max(1, 2)`, with `Δ_2 = 2 (ψ(1) + 2γ + 1 - log π - J_2)`, from the printed constants
and `J_2 ≤ 41/125`.  [TeX `manuscript_v2_proposed.tex` lines 2174-2178.] -/
theorem delta_gt_common_two (gamma logPi logTwo J : ℝ)
    (hgamma : (5772 / 10000 : ℝ) < gamma) (hlogPi : logPi < 1144731 / 1000000)
    (hJ : J ≤ (41 / 125 : ℝ)) :
    (3 / 200 : ℝ) * UniformTail.tailWeight 2 < UniformTail.delta 2 gamma logPi logTwo J := by
  norm_num [UniformTail.delta, UniformTail.psiCombination, UniformTail.tailWeight,
    UniformTail.harmonicQ, Finset.sum_range_succ]
  linarith

theorem scalarDelta_gt_common_two :
    (3 / 200 : ℝ) * UniformTail.tailWeight 2 < scalarDelta 2 :=
  delta_gt_common_two _ _ _ _ EulerLower.gamma_lower UniformTail.log_pi_upper
    (J2_le_41_125.1.trans J2_le_41_125.2)

end BecknerOnofri.V2.Reaudit.ShellMargins

end
