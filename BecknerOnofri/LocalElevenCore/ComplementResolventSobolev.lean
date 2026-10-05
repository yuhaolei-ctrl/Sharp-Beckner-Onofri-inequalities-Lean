module

public import BecknerOnofri.LocalElevenCore.QuadraticCorrectionCoefficients
public import BecknerOnofri.LocalElevenCore.GraphSobolevBounds

@[expose] public section

noncomputable section
open Filter Asymptotics
open scoped Topology
namespace BecknerOnofri.HighDim.LocalEleven.QuadraticModes
open ContinuousGibbs ContinuousFirstShell GraphEnergy GraphSobolevBounds

theorem resolvent_weighted_coefficient {d : ℕ} (hd : 11≤d) (f : complement d)
    (k : Frequency d) : frequencyLength k^d*‖coefficient k (resolvent hd f).val‖≤
      2*‖coefficient k f.val‖ := by
  by_cases hk : ComplementFrequency k
  · have he := complement_eigenvalue_ge_thirtytwo hd hk
    have hp : 0<frequencyLength k^d-1 := by linarith
    have hh : (frequencyLength k^d-1)*‖coefficient k (resolvent hd f).val‖=
        ‖coefficient k f.val‖ := by
      rw [resolvent_coefficient hd f hk,norm_mul,Complex.norm_real,Real.norm_eq_abs,
        abs_of_pos (div_pos zero_lt_one hp)]
      field_simp
    nlinarith [norm_nonneg (coefficient k (resolvent hd f).val)]
  · rw [(mem_complement_fourier_iff _).mp (resolvent hd f).property k hk,norm_zero,mul_zero]
    positivity

theorem resolvent_sobolevTerm_le {d : ℕ} (hd : 11≤d) {s : ℝ} (hs : s≤d)
    (f : complement d) (k : Frequency d) :
    sobolevTerm s (resolvent hd f).val k≤
      (4*ellipticWeightConstant d)*‖coefficient k f.val‖^2 := by
  by_cases hk : ComplementFrequency k
  · have hw := physical_weight_le_eigenvalue_sq hs k hk
    have hb := resolvent_weighted_coefficient hd f k
    have hr : 0≤frequencyLength k := Real.sqrt_nonneg _
    have hsq := pow_le_pow_left₀
      (mul_nonneg (pow_nonneg hr _) (norm_nonneg _)) hb 2
    unfold sobolevTerm
    rw [← coefficient_eq_fourierCoeff]
    have hC := ellipticWeightConstant_pos d
    have hh := mul_le_mul_of_nonneg_right hw (sq_nonneg ‖coefficient k (resolvent hd f).val‖)
    have hh' := mul_le_mul_of_nonneg_left hsq hC.le
    nlinarith
  · unfold sobolevTerm
    rw [← coefficient_eq_fourierCoeff,(mem_complement_fourier_iff _).mp
      (resolvent hd f).property k hk,norm_zero]
    simp only [zero_pow (by norm_num : (2:ℕ)≠0),mul_zero]
    have hC := ellipticWeightConstant_pos d
    positivity

theorem resolvent_inSobolev {d : ℕ} (hd : 11≤d) {s : ℝ} (hs : s≤d)
    (f : complement d) : InSobolev s (resolvent hd f).val := by
  refine ⟨(resolvent hd f).val.continuous.memLp_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _),?_⟩
  exact ((hasSum_square f.val).summable.mul_left (4*ellipticWeightConstant d)).of_nonneg_of_le
    (fun k => by unfold sobolevTerm; positivity) (resolvent_sobolevTerm_le hd hs f)

theorem resolvent_sobolevNorm_bound {d : ℕ} (hd : 11≤d) {s : ℝ} (hs : s≤d)
    (f : complement d) : sobolevNorm s (resolvent hd f).val ≤
      (2*Real.sqrt (ellipticWeightConstant d))*‖f.val‖ := by
  have hC := ellipticWeightConstant_pos d
  have hb := hasSum_le (resolvent_sobolevTerm_le hd hs f)
    (resolvent_inSobolev hd hs f).2.hasSum
    ((hasSum_square f.val).mul_left (4*ellipticWeightConstant d))
  have hm : mean d (f.val^2)≤‖f.val‖^2 := by
    calc
      _ ≤ mean d (ContinuousMap.const (Torus d) (‖f.val‖^2)) := by
        apply MeasureTheory.integral_mono (integrable d _) (integrable d _)
        intro y
        change f.val y^2≤‖f.val‖^2
        exact (sq_le_sq).mpr (by simpa only [Real.norm_eq_abs,abs_norm] using f.val.norm_coe_le_norm y)
      _ = _ := by simp [mean_apply]
  unfold sobolevNorm
  apply (Real.sqrt_le_iff).mpr
  refine ⟨by positivity,?_⟩
  have hsqrt := Real.sq_sqrt hC.le
  have hh := mul_le_mul_of_nonneg_left hm (show 0≤4*ellipticWeightConstant d by positivity)
  nlinarith

#print axioms resolvent_sobolevNorm_bound
end BecknerOnofri.HighDim.LocalEleven.QuadraticModes
