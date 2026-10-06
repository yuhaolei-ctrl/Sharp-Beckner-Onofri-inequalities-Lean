module

public import BecknerOnofri.EntropyTailExact
public import BecknerOnofri.TwelveGaussianHeat
public import BecknerOnofri.TwelveThetaCertificate
public import Legacy.BecknerOnofri.GaussianScalarTail
public import Legacy.BecknerOnofri.EulerLower
public import Legacy.BecknerOnofri.HarmonicGaussian

@[expose] public section

/-!
# Lemma 5.13: the scalar tail bound `T_n ≤ R_n`

For `n > 50` we follow the manuscript: `G_{12,n} ≤ S_{12}(a)` with `a = log(1+1/n)`,
the dimension-uniform Gaussian bound with `d = 12`,
`S_{12}(a) ≤ K [-log a + log π - H_6 + J_{12} + 6a/π]` with `K = π^6/120`, the bound
`J_{12} < 3.29`, `-log a ≤ H_n - γ`, and Bernoulli's inequality for the cube part `C_n`.
For `3 ≤ n ≤ 50` we use the exact shell sums of `EntropyTailExact`.
-/

noncomputable section

open MeasureTheory Set Finset
open Legacy.BecknerOnofri Legacy.BecknerOnofri.GaussianCentral Legacy.BecknerOnofri.GaussianLattice
open Legacy.BecknerOnofri.ThetaDomination

namespace BecknerOnofri.HighDim.EntropyTail

/-- `G_{12,n} = T_n + C_n`. -/
theorem binomialEnergy_eq {n : ℕ} (hn : 1 ≤ n) :
    binomialEnergy 12 n = scalarTail n + ExactTail.cubeSum n := by
  have hbox : binomialEnergy 12 n =
      ∑ k ∈ RectangleLattice.box (fun _ : Fin 12 => n), ExactTail.term n k := by
    unfold binomialEnergy
    rw [tsum_eq_sum (s := RectangleLattice.box (fun _ : Fin 12 => n))]
    · apply sum_congr rfl
      intro k _
      unfold binomialTerm binomialProduct ExactTail.term spectralWeight binomialZ
      congr 1
      · have hR : frequencyLength k ^ 12 = (Legacy.TorusEndpoint.GreenMultiplierSummability.radiusSq k) ^ 6 := by
          rw [show frequencyLength k ^ 12 = (frequencyLength k ^ 2) ^ 6 by ring, frequencyLength,
            Real.sq_sqrt (by positivity)]
          rfl
        rw [hR]
        split_ifs with hk
        · subst hk
          simp [Legacy.TorusEndpoint.GreenMultiplierSummability.radiusSq]
        · have h0 : 0 ≤ Legacy.TorusEndpoint.GreenMultiplierSummability.radiusSq k := by
            unfold Legacy.TorusEndpoint.GreenMultiplierSummability.radiusSq; positivity
          rw [show Legacy.TorusEndpoint.GreenMultiplierSummability.radiusSq k ^ 12 =
            (Legacy.TorusEndpoint.GreenMultiplierSummability.radiusSq k ^ 6) ^ 2 by ring,
            Real.sqrt_sq (by positivity), one_div]
      · exact prod_congr rfl (fun i _ => (scalarCoefficient_eq n _).symm)
    · intro k hk
      unfold binomialTerm binomialProduct binomialZ
      rw [RandomRectangles.mem_box_natAbs] at hk
      push Not at hk
      obtain ⟨i, hi⟩ := hk
      rw [prod_eq_zero (mem_univ i) (RandomRectangles.coeff_eq_zero hi), mul_zero]
  have h := Finset.sum_sdiff (f := ExactTail.term n) (ExactTail.box_one_subset hn)
  rw [← ExactTail.scalarTail_eq_sdiff, ExactTail.sum_box_one] at h
  rw [hbox, ← h]

/-- `ψ(6) + γ + 1/6 = H_6`, in the form of the central constant. -/
lemma central_constant_six : constant 6 + 1 / 6 = 49 / 20 := by
  have h3 := constant_add_one 2 (by norm_num)
  have h4 := constant_add_one 3 (by norm_num)
  have h5 := constant_add_one 4 (by norm_num)
  have h6 := constant_add_one 5 (by norm_num)
  norm_num at h3 h4 h5 h6
  rw [h6, h5, h4, h3, constant_two]
  norm_num

/-- The bound `gaussian-all-d` for `d = 12`, i.e. (5.24) of the manuscript. -/
theorem binomialEnergy_twelve_le {n : ℕ} (hn : 1 ≤ n) :
    binomialEnergy 12 n ≤ Real.pi ^ 6 / 120 *
      (-Real.log (Real.log (1 + 1 / (n : ℝ))) + Real.log Real.pi - 49 / 20 +
        thetaIntegral realTheta 12 + 6 * Real.log (1 + 1 / (n : ℝ)) / Real.pi) := by
  set a := Real.log (1 + 1 / (n : ℝ))
  have ha : 0 < a := log_parameter_pos (by omega)
  have hap : a < Real.pi := GaussianScalarTail.gaussian_parameter_lt_pi n hn
  have hHeat := Twelve.Heat.gaussianEnergy_le_central (by norm_num : 3 ≤ 12) rfl ha hap
  have hc := central_le 6 (a / Real.pi) (by norm_num) (div_pos ha Real.pi_pos)
    ((div_lt_one Real.pi_pos).mpr hap)
  rw [central_constant_six, Real.log_div ha.ne' Real.pi_pos.ne'] at hc
  have hpi : Real.pi ^ ((12 : ℕ) / 2 : ℝ) = Real.pi ^ 6 := by
    rw [show ((12 : ℕ) : ℝ) / 2 = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hg : Real.Gamma ((12 : ℕ) / 2 : ℝ) = 120 := by
    rw [show ((12 : ℕ) : ℝ) / 2 = (5 : ℕ) + 1 by norm_num, Real.Gamma_nat_eq_factorial]
    norm_num [Nat.factorial]
  rw [hpi, hg, show ((12 : ℕ) : ℝ) / 2 = 6 by norm_num] at hHeat
  norm_num only [show max (6 : ℝ) 2 = 6 by norm_num] at hc
  have hK : 0 ≤ Real.pi ^ 6 / 120 := by positivity
  calc
    _ ≤ gaussianEnergy 12 a := binomialEnergy_le_gaussianEnergy (by omega)
    _ ≤ _ := hHeat
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ hK
      have : 6 * (a / Real.pi) = 6 * a / Real.pi := by ring
      linarith

lemma pi_six_lt : Real.pi ^ 6 / 120 < 8012 / 1000 := by
  have h := Real.pi_lt_d4
  have h0 := Real.pi_pos
  have : Real.pi ^ 6 < (3.1416 : ℝ) ^ 6 := pow_lt_pow_left₀ h h0.le (by norm_num : (6 : ℕ) ≠ 0)
  norm_num at this ⊢
  linarith

lemma harmonic_fifty_one : (4518 / 1000 : ℝ) < (harmonic 51 : ℝ) := by
  have h : (4518 / 1000 : ℚ) < harmonic 51 := by decide +kernel
  have hh := (Rat.cast_lt (K := ℝ)).mpr h
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hh
  linarith

/-- Lemma 5.13 for `n > 50`, from the Gaussian bound and `J_{12} < 3.29`. -/
theorem scalarTail_lt_budget_large {n : ℕ} (hn : 51 ≤ n) : scalarTail n < scalarBudget n := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (51 : ℝ) ≤ n := by exact_mod_cast hn
  have hG := binomialEnergy_twelve_le hn1
  rw [binomialEnergy_eq hn1] at hG
  have hC := ExactTail.cubeSum_lower (n := n)
  norm_num [sum_range_succ, Nat.choose] at hC
  have hR := tailBudget_harmonic_lower n
  rw [← scalarBudget_eq] at hR
  have hH := HarmonicGaussian.harmonic_add_log_gaussian_ge_gamma n hn1
  have hγ := EulerLower.gamma_lower
  have hlogpi := UniformTail.log_pi_upper
  have hJ := Twelve.ThetaBound.thetaIntegral_lt
  have ha := UniformTail.log_one_add_inv_lt n (by omega)
  have ha0 : 0 < Real.log (1 + 1 / (n : ℝ)) := log_parameter_pos (by omega)
  have hK := pi_six_lt
  have hK0 : 0 < Real.pi ^ 6 / 120 := by positivity
  have hpi := Real.pi_gt_d2
  have hH51 : (harmonic 51 : ℝ) ≤ (harmonic n : ℝ) := by
    have h : harmonic 51 ≤ harmonic n :=
      sum_le_sum_of_subset_of_nonneg (range_mono hn) (fun i _ _ => by positivity)
    exact_mod_cast h
  have h51 := harmonic_fifty_one
  set a := Real.log (1 + 1 / (n : ℝ)) with ha_def
  set H : ℝ := (harmonic n : ℝ) with hH_def
  have ha51 : a ≤ 1 / 51 :=
    ha.le.trans (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hnR)
  have hfrac : 6 * a / Real.pi ≤ 6 * (1 / 51) / (314 / 100) := by
    calc
      _ ≤ 6 * a / (314 / 100) :=
        div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith)
      _ ≤ _ := by gcongr
  have hB : -Real.log a + Real.log Real.pi - 49 / 20 + thetaIntegral realTheta 12 +
      6 * a / Real.pi ≤ H - 5772 / 10000 + 1144731 / 1000000 - 49 / 20 + 329 / 100 +
        6 * (1 / 51) / (314 / 100) := by linarith
  have hBu : 0 ≤ H - 5772 / 10000 + 1144731 / 1000000 - 49 / 20 + 329 / 100 +
      6 * (1 / 51) / (314 / 100) := by linarith
  have hKB := (mul_le_mul_of_nonneg_left hB hK0.le).trans
    (mul_le_mul_of_nonneg_right hK.le hBu)
  have hn52 : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 / 52 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  rw [div_eq_mul_one_div _ ((n : ℝ) + 1)] at hC
  nlinarith

#print axioms scalarTail_lt_budget_large

/-- **Lemma 5.13** (lem:section5-global-scalar-tail): `T_n ≤ R_n` for every `n`. -/
theorem scalarTail_le_budget (n : ℕ) : scalarTail n ≤ scalarBudget n := by
  by_cases h2 : n ≤ 2
  · exact scalarTail_le_budget_of_le_two h2
  by_cases h50 : n ≤ 50
  · exact (ExactTail.scalarTail_lt_budget_mid (by omega) h50).le
  · exact (scalarTail_lt_budget_large (by omega)).le

#print axioms scalarTail_le_budget

end BecknerOnofri.HighDim.EntropyTail
