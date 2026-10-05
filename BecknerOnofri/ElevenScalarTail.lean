module

public import BecknerOnofri.ElevenScalarFinite
public import BecknerOnofri.ElevenThetaCertificate
public import BecknerOnofri.ElevenGaussianHeat
public import Legacy.BecknerOnofri.GaussianScalarTail
public import Legacy.BecknerOnofri.EulerLower

@[expose] public section

/-! The large-index part of the eleven-dimensional scalar gap, using the
actual Gaussian lattice sum and the certified improper theta integral. -/
noncomputable section
open scoped BigOperators
namespace BecknerOnofri.HighDim.Eleven.ScalarTail
open Legacy.BecknerOnofri GaussianCentral GaussianLattice ThetaDomination

lemma center_constant : constant (11/2) + 2/11 =
    -2 * Real.log 2 + 1126/315 + 2/11 := by
  have h9 := constant_eq_psiCombination 9 (by norm_num) (by norm_num)
  have h11 := constant_add_one (9/2) (by norm_num)
  norm_num [UniformTail.psiCombination, UniformTail.oddHarmonicQ,
    Finset.sum_range_succ] at h9 h11
  linarith

lemma central_bound {x : ℝ} (hx : 0 < x) (hx1 : x < 1) :
    central (11/2) x ≤ -Real.log x -
      (-2 * Real.log 2 + 1126/315 + 2/11) + (11/2)*x := by
  have h := central_le (11/2) x (by norm_num) hx hx1
  norm_num only [show max (11/2 : ℝ) 2 = 11/2 by norm_num,
    show (1:ℝ)/(11/2) = 2/11 by norm_num] at h
  rwa [center_constant] at h

lemma delta_lower : (-8 : ℝ) < 11 * (Real.eulerMascheroniConstant -
    2 * Real.log 2 + 1126/315 + 2/11 - Real.log Real.pi -
    thetaIntegral realTheta 11) := by
  linarith [EulerLower.gamma_lower, UniformTail.log_two_upper,
    UniformTail.log_pi_upper, ThetaBound.thetaIntegral_lt]

lemma normalized_energy_bound {n : ℕ} (hn : 1 ≤ n) :
    (22 / spectralThreshold 11) * scalarEnergy n <
      11 * (_root_.harmonic n : ℝ) + 8 + 20/(n:ℝ) := by
  let a := Real.log (1+1/(n:ℝ))
  have ha : 0 < a := log_parameter_pos (by omega)
  have hap : a < Real.pi := GaussianScalarTail.gaussian_parameter_lt_pi n hn
  have hHeat := Heat.gaussianEnergy_le_central (by norm_num : 3 ≤ 11) rfl ha hap
  have hc := central_bound (div_pos ha Real.pi_pos) ((div_lt_one Real.pi_pos).mpr hap)
  rw [Real.log_div ha.ne' Real.pi_pos.ne'] at hc
  have hH := HarmonicGaussian.harmonic_add_log_gaussian_ge_gamma n hn
  have hEnergy : (2 * endpointConstant 11) * scalarEnergy n ≤
      11 * (central (11/2) (a/Real.pi) + thetaIntegral realTheta 11) := by
    rw [ScalarFinite.scalarEnergy_eq_legacy]
    calc
      _ ≤ (2 * endpointConstant 11) * gaussianEnergy 11 a :=
        mul_le_mul_of_nonneg_left (binomialEnergy_le_gaussianEnergy (by omega))
          (GaussianScalarTail.coefficient_nonneg (by norm_num))
      _ ≤ (2 * endpointConstant 11) *
          ((Real.pi^((11:ℝ)/2) / Real.Gamma ((11:ℝ)/2)) *
            (central (11/2) (a/Real.pi) + thetaIntegral realTheta 11)) :=
        mul_le_mul_of_nonneg_left hHeat
          (GaussianScalarTail.coefficient_nonneg (by norm_num))
      _ = _ := by
        have h := GaussianScalarTail.coefficient_gamma_normalization (by norm_num : 0 < 11)
        norm_num only [Nat.cast_ofNat] at h
        rw [← mul_assoc, h]
  have heq : 2 * endpointConstant 11 = 22 / spectralThreshold 11 := by
    unfold endpointConstant spectralThreshold Legacy.TorusEndpoint.endpointSigma
    ring
  rw [heq] at hEnergy
  have htail : (121/2 : ℝ) / Real.pi * a < 20/(n:ℝ) := by
    have hcoef : (121/2 : ℝ) / Real.pi < 20 := by
      apply (div_lt_iff₀ Real.pi_pos).2
      linarith [Real.pi_gt_d2]
    have halim := UniformTail.log_one_add_inv_lt n (by omega)
    have hmul := mul_lt_mul_of_pos_right hcoef ha
    dsimp only [a] at hmul ⊢
    simp only [div_eq_mul_inv] at hmul halim ⊢
    nlinarith
  have hd := delta_lower
  dsimp only [a] at hc hEnergy htail
  simp only [div_eq_mul_inv] at hc hEnergy htail hH hd ⊢
  nlinarith only [hc, hEnergy, htail, hd, hH]

/-- The large-index estimate at beta0 = 17.715, with the manuscript's
strict margin. Every occurrence is an actual infinite lattice sum. -/
theorem tail_scalar_gap {n : ℕ} (hn : 22 ≤ n) :
    (1/2000 : ℝ) < 11 * (_root_.harmonic n : ℝ) -
      ((3543 : ℝ)/200) / spectralThreshold 11 * scalarEnergy n := by
  have hE := normalized_energy_bound (show 1 ≤ n by omega)
  have hH : (_root_.harmonic 22 : ℝ) ≤ (_root_.harmonic n : ℝ) := by
    exact_mod_cast (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hn)
      (fun i _ _ => by positivity) : _root_.harmonic 22 ≤ _root_.harmonic n)
  have h22 : (_root_.harmonic 22 : ℝ) = 19093197/5173168 := by
    norm_num [_root_.harmonic, Finset.sum_range_succ]
  rw [h22] at hH
  have hnR : (22 : ℝ) ≤ n := by exact_mod_cast hn
  have hi : (20 : ℝ) / n ≤ 20/22 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hnR
  have hs := mul_lt_mul_of_pos_left hE (by norm_num : (0 : ℝ) < 3543/4400)
  have heq : (3543/4400 : ℝ) * ((22 / spectralThreshold 11) * scalarEnergy n) =
      ((3543 : ℝ)/200) / spectralThreshold 11 * scalarEnergy n := by ring
  rw [heq] at hs
  nlinarith only [hs, hi, hH]

/-- Section 4's scalar inequality, unconditionally at every positive index. -/
theorem all_scalar_gap {n : ℕ} (hn : 1 ≤ n) :
    (1/2000 : ℝ) < 11 * (_root_.harmonic n : ℝ) -
      ((3543 : ℝ)/200) / spectralThreshold 11 * scalarEnergy n := by
  by_cases h : n ≤ 21
  · exact ScalarFinite.finite_scalar_gap hn h
  · exact tail_scalar_gap (by omega)

#print axioms normalized_energy_bound
#print axioms all_scalar_gap

end BecknerOnofri.HighDim.Eleven.ScalarTail
