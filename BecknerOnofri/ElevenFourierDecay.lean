module

public import BecknerOnofri.ElevenPeriodizedFourier
public import Legacy.BecknerOnofri.RadialWiener

@[expose] public section

/-! Every polynomial Fourier moment of the competitor is absolutely
summable. Exponential decay is compared with the existing summable lattice
product majorant, with no smoothness assumed in advance. -/
noncomputable section
namespace BecknerOnofri.HighDim.Eleven

lemma scaled_polynomial_bound {c r : ℝ} (hc : 0 ≤ c) (hr : 0 ≤ r) :
    fourierPolynomial (c*r) ≤ fourierPolynomial c*(1+r)^5 := by
  have hp (j : ℕ) (hj : j ≤ 5) : (c*r)^j ≤ c^j*(1+r)^5 := by
    rw [mul_pow]
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg hc j)
    exact (pow_le_pow_left₀ hr (by linarith) j).trans
      (pow_le_pow_right₀ (by linarith : 1 ≤ 1+r) hj)
  have h0 := hp 0 (by omega)
  have h1 := hp 1 (by omega)
  have h2 := hp 2 (by omega)
  have h3 := hp 3 (by omega)
  have h4 := hp 4 (by omega)
  have h5 := hp 5 (by omega)
  unfold fourierPolynomial
  norm_num only [pow_zero, pow_one, one_mul] at h0 h1
  nlinarith

lemma polynomial_exp_bound (N : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    (1+r)^N*Real.exp (-r) ≤ Real.exp 1*(N.factorial:ℝ) := by
  have hf : (0:ℝ)<N.factorial := Nat.cast_pos.mpr (Nat.factorial_pos N)
  have h := (div_le_iff₀ hf).mp (Real.pow_div_factorial_le_exp (1+r) (by linarith : 0 ≤ 1+r) N)
  calc
    _ ≤ (Real.exp (1+r)*(N.factorial:ℝ))*Real.exp (-r) :=
      mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
    _ = Real.exp 1*(N.factorial:ℝ) := by
      rw [mul_right_comm, ← Real.exp_add]
      congr 2
      ring

lemma fourierProfile_weighted_bound (m : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    (1+r)^m*fourierProfile ((2*Real.pi/5)*r) ≤
      (fourierPolynomial (2*Real.pi/5)/945*Real.exp 1*((m+27).factorial:ℝ)) /
        (1+r^2)^11 := by
  let c : ℝ := 2*Real.pi/5
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hc1 : 1 ≤ c := by dsimp [c]; linarith [Real.pi_gt_three]
  have hp : 0 ≤ fourierPolynomial c := by unfold fourierPolynomial; positivity
  have hpr : 0 ≤ fourierPolynomial (c*r) := by unfold fourierPolynomial; positivity
  have hpoly := scaled_polynomial_bound hc hr
  have he : Real.exp (-(c*r)) ≤ Real.exp (-r) := Real.exp_le_exp.mpr (by nlinarith)
  have hbase : fourierProfile (c*r) ≤ (fourierPolynomial c/945)*(1+r)^5*Real.exp (-r) := by
    unfold fourierProfile
    calc
      _ ≤ Real.exp (-r)*(fourierPolynomial c*(1+r)^5)/945 := by gcongr
      _ = _ := by ring
  have hpow : (1+r^2)^11 ≤ (1+r)^22 := by
    calc
      _ ≤ ((1+r)^2)^11 := by gcongr; nlinarith
      _ = _ := by rw [← pow_mul]
  have hd : 0 < (1+r^2)^11 := by positivity
  apply (le_div_iff₀ hd).mpr
  calc
    _ ≤ ((1+r)^m*((fourierPolynomial c/945)*(1+r)^5*Real.exp (-r)))*(1+r)^22 := by
      gcongr
    _ = (fourierPolynomial c/945)*((1+r)^(m+27)*Real.exp (-r)) := by
      rw [pow_add]
      ring
    _ ≤ (fourierPolynomial c/945)*(Real.exp 1*((m+27).factorial:ℝ)) :=
      mul_le_mul_of_nonneg_left (polynomial_exp_bound (m+27) hr) (by positivity)
    _ = _ := by dsimp [c]; ring

lemma periodized_fourier_radial (m : ℕ) :
    Legacy.BecknerOnofri.RadialWiener.RadialSummable (fourierCoeff periodizedProfile) m := by
  let C : ℝ := fourierPolynomial (2*Real.pi/5)/945*Real.exp 1*((m+27).factorial:ℝ)
  have hC : 0 ≤ C := by dsimp [C]; unfold fourierPolynomial; positivity
  apply (Legacy.TorusEndpoint.GreenMultiplierSummability.summable_productMajorant 11).mul_left C |>.of_nonneg_of_le
  · intro k
    exact mul_nonneg ((Legacy.BecknerOnofri.RadialWiener.radialWeight_isWeight m).nonneg k) (norm_nonneg _)
  · intro k
    rw [periodizedProfile_fourier, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by unfold fourierProfile fourierPolynomial frequencyLength; positivity)]
    change (1+frequencyLength k)^m * fourierProfile (2*Real.pi*frequencyLength k/5) ≤ _
    have he : 2*Real.pi*frequencyLength k/5 = (2*Real.pi/5)*frequencyLength k := by ring
    rw [he]
    have h := fourierProfile_weighted_bound m (Real.sqrt_nonneg _ : 0 ≤ frequencyLength k)
    apply h.trans
    have hs : frequencyLength k^2 = Legacy.TorusEndpoint.GreenMultiplierSummability.radiusSq k :=
      Real.sq_sqrt (Legacy.TorusEndpoint.GreenMultiplierSummability.radiusSq_nonneg k)
    change C / (1 + frequencyLength k ^ 2) ^ 11 ≤
      C * Legacy.TorusEndpoint.GreenMultiplierSummability.productMajorant k
    rw [hs, div_eq_mul_inv, ← inv_pow]
    exact mul_le_mul_of_nonneg_left
      (Legacy.TorusEndpoint.GreenMultiplierSummability.shifted_radial_inv_le_product k) hC

#print axioms periodized_fourier_radial
end BecknerOnofri.HighDim.Eleven
