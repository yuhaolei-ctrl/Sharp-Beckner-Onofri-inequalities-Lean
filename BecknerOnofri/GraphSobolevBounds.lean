module

public import BecknerOnofri.UniformComplementBounds
public import BecknerOnofri.GraphEnergy

@[expose] public section

/-! Quantitative physical Sobolev estimates for the actual complementary
graph, from its genuine Fourier equation and Haar Parseval identity. -/
noncomputable section
open MeasureTheory Filter Asymptotics
open scoped Topology BigOperators
namespace BecknerOnofri.HighDim.GraphSobolevBounds
open ContinuousGibbs ContinuousFirstShell ContinuousComplement GreenLocalBranch ReducedEquation
open QuadraticModes GraphEnergy UniformComplementBounds

theorem complement_nonlinear_euler {d : ℕ} (hd : 0 < d) (μ : ℝ)
    (z : Coordinates d) (w : complement d)
    (he : projectedEquation (greenContinuous d) ((μ,z),w) = 0)
    (k : Frequency d) (hk : ComplementFrequency k) :
    ((frequencyLength k^d-μ : ℝ) : ℂ)*coefficient k (w : Space d) =
      (μ:ℂ)*coefficient k (nonlinearRemainder (reconstruction d (z,w))) := by
  have hh := complement_fourier_euler hd μ z w he k hk
  have hv : coefficient k (assembly d z) = 0 := by
    rw [← projection_assembly z]
    exact coefficient_projection_off_shell _ _ hk.2
  have h1 : coefficient k (1 : Space d) = 0 := by
    change coefficient k (ContinuousMap.const (Torus d) 1) = 0
    rw [coefficient_const, if_neg hk.1]
  rw [nonlinearRemainder, map_sub, map_sub, h1, sub_zero, center_reconstruction,
    reconstruction_apply, map_add, hv, zero_add]
  rw [reconstruction_apply] at hh
  push_cast at hh ⊢
  linear_combination hh

/-- A full order of elliptic gain, uniform for 0≤μ≤2. -/
theorem weighted_coefficient_bound {d : ℕ} (hd : 12 ≤ d) {μ : ℝ}
    (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2) (z : Coordinates d) (w : complement d)
    (he : projectedEquation (greenContinuous d) ((μ,z),w) = 0) (k : Frequency d) :
    frequencyLength k^d * ‖coefficient k (w : Space d)‖ ≤
      4*‖coefficient k (nonlinearRemainder (reconstruction d (z,w)))‖ := by
  by_cases hk : ComplementFrequency k
  · have hlambda := complement_eigenvalue_ge_sixtyfour hd hk
    have hg : 0 ≤ frequencyLength k^d-μ := by linarith
    have hh := congrArg norm (complement_nonlinear_euler (by omega) μ z w he k hk)
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hg,
      abs_of_nonneg hμ0] at hh
    have hl : frequencyLength k^d ≤ 2*(frequencyLength k^d-μ) := by linarith
    have hm := mul_le_mul_of_nonneg_right hl (norm_nonneg (coefficient k (w : Space d)))
    have hn := mul_le_mul_of_nonneg_right hμ2
      (norm_nonneg (coefficient k (nonlinearRemainder (reconstruction d (z,w)))))
    nlinarith
  · rw [(mem_complement_fourier_iff (w : Space d)).mp w.property k hk, norm_zero, mul_zero]
    positivity

def ellipticWeightConstant (d : ℕ) : ℝ := (1+(2*Real.pi)^2)^d

theorem ellipticWeightConstant_pos (d : ℕ) : 0 < ellipticWeightConstant d := by
  unfold ellipticWeightConstant
  positivity

theorem physical_weight_le_eigenvalue_sq {d : ℕ} {s : ℝ} (hs : s ≤ d)
    (k : Frequency d) (hk : ComplementFrequency k) :
    (1+(2*Real.pi*frequencyLength k)^2)^s ≤ ellipticWeightConstant d*(frequencyLength k^d)^2 := by
  have hn : (1:ℝ) ≤ latticeSquare k := by
    exact_mod_cast (show 1 ≤ latticeSquare k from (by have := complement_latticeSquare_ge_two hk; omega))
  have he : frequencyLength k^2 = (latticeSquare k:ℝ) := by
    unfold frequencyLength
    rw [Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _)), ← latticeSquare_cast]
  have hb : 1+(2*Real.pi*frequencyLength k)^2 ≤ (1+(2*Real.pi)^2)*frequencyLength k^2 := by
    rw [mul_pow, he]
    nlinarith
  calc
    _ ≤ (1+(2*Real.pi*frequencyLength k)^2)^(d:ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg (2*Real.pi*frequencyLength k)]) hs
    _ = (1+(2*Real.pi*frequencyLength k)^2)^d := Real.rpow_natCast _ _
    _ ≤ ((1+(2*Real.pi)^2)*frequencyLength k^2)^d := pow_le_pow_left₀ (by positivity) hb d
    _ = _ := by simp only [ellipticWeightConstant, mul_pow, ← pow_mul, Nat.mul_comm]

theorem correction_sobolevTerm_le {d : ℕ} (hd : 12 ≤ d) {μ s : ℝ}
    (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2) (hs : s ≤ d) (z : Coordinates d) (w : complement d)
    (he : projectedEquation (greenContinuous d) ((μ,z),w) = 0) (k : Frequency d) :
    sobolevTerm s (w : Space d) k ≤ (16*ellipticWeightConstant d)*
      ‖coefficient k (nonlinearRemainder (reconstruction d (z,w)))‖^2 := by
  have hC := ellipticWeightConstant_pos d
  by_cases hk : ComplementFrequency k
  · have hweight := physical_weight_le_eigenvalue_sq hs k hk
    have hcoeff := weighted_coefficient_bound hd hμ0 hμ2 z w he k
    have hcoeffsq : (frequencyLength k^d)^2 * ‖coefficient k (w : Space d)‖^2 ≤
        16*‖coefficient k (nonlinearRemainder (reconstruction d (z,w)))‖^2 := by
      have hp := pow_le_pow_left₀ (mul_nonneg
        (le_trans (by norm_num : (0:ℝ)≤64) (complement_eigenvalue_ge_sixtyfour hd hk))
        (norm_nonneg (coefficient k (w : Space d)))) hcoeff 2
      nlinarith
    unfold sobolevTerm
    rw [← coefficient_eq_fourierCoeff]
    calc
      _ ≤ (ellipticWeightConstant d*(frequencyLength k^d)^2)*‖coefficient k (w : Space d)‖^2 :=
        mul_le_mul_of_nonneg_right hweight (sq_nonneg _)
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hcoeffsq (ellipticWeightConstant_pos d).le]
  · unfold sobolevTerm
    rw [← coefficient_eq_fourierCoeff, (mem_complement_fourier_iff (w : Space d)).mp w.property k hk]
    simp only [norm_zero, zero_pow (by norm_num : (2:ℕ)≠0), mul_zero]
    positivity

theorem correction_inSobolev {d : ℕ} (hd : 12 ≤ d) {μ s : ℝ}
    (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2) (hs : s ≤ d) (z : Coordinates d) (w : complement d)
    (he : projectedEquation (greenContinuous d) ((μ,z),w) = 0) : InSobolev s (w : Space d) := by
  refine ⟨w.val.continuous.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _), ?_⟩
  apply ((hasSum_square (nonlinearRemainder (reconstruction d (z,w)))).summable.mul_left
    (16*ellipticWeightConstant d)).of_nonneg_of_le
  · intro k
    unfold sobolevTerm
    positivity
  · exact correction_sobolevTerm_le hd hμ0 hμ2 hs z w he

theorem correction_sobolevNorm_bound {d : ℕ} (hd : 12 ≤ d) {μ s : ℝ}
    (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2) (hs : s ≤ d) (z : Coordinates d) (w : complement d)
    (he : projectedEquation (greenContinuous d) ((μ,z),w) = 0) :
    sobolevNorm s (w : Space d) ≤ (4*Real.sqrt (ellipticWeightConstant d))*
      ‖nonlinearRemainder (reconstruction d (z,w))‖ := by
  have hC := ellipticWeightConstant_pos d
  let R := nonlinearRemainder (reconstruction d (z,w))
  have hsum := (hasSum_square R).mul_left (16*ellipticWeightConstant d)
  have hb := hasSum_le (correction_sobolevTerm_le hd hμ0 hμ2 hs z w he)
    (correction_inSobolev hd hμ0 hμ2 hs z w he).2.hasSum hsum
  have hmean : mean d (R^2) ≤ ‖R‖^2 := by
    calc
      _ ≤ mean d (ContinuousMap.const (Torus d) (‖R‖^2)) := by
        apply integral_mono (integrable d (R^2)) (integrable d _)
        intro y
        change R y ^ 2 ≤ ‖R‖^2
        exact (sq_le_sq).mpr (by simpa only [Real.norm_eq_abs, abs_norm] using R.norm_coe_le_norm y)
      _ = _ := by simp [mean_apply]
  have hmul := mul_le_mul_of_nonneg_left hmean (show 0 ≤ 16*ellipticWeightConstant d by positivity)
  unfold sobolevNorm
  apply (Real.sqrt_le_iff).mpr
  refine ⟨by positivity, ?_⟩
  have hsq : (Real.sqrt (ellipticWeightConstant d))^2 = ellipticWeightConstant d :=
    Real.sq_sqrt (ellipticWeightConstant_pos d).le
  nlinarith

/-- Uniform quadratic correction in each physical H^s norm up to one full
elliptic order, with genuine Sobolev membership established alongside it. -/
theorem correction_sobolev_quadratic {d : ℕ} (hd : 12 ≤ d) {s : ℝ} (hs : s ≤ d) :
    (fun x => sobolevNorm s (correction hd x : Space d))
      =O[𝓝 (1,(0 : Coordinates d))] (fun x => ‖x.2‖^2) := by
  have hR : (fun x => nonlinearRemainder (potential hd x))
      =O[𝓝 (1,(0 : Coordinates d))] (fun x => ‖x.2‖^2) :=
    ((nonlinearRemainder_quadratic d).comp_tendsto (UniformComplementBounds.potential_tendsto hd)).trans
      ((potential_uniform_linear hd).norm_left.pow 2)
  have hb : (fun x => sobolevNorm s (correction hd x : Space d))
      =O[𝓝 (1,(0 : Coordinates d))] (fun x => nonlinearRemainder (potential hd x)) := by
    apply IsBigO.of_bound (4*Real.sqrt (ellipticWeightConstant d))
    filter_upwards [correction_solves hd, parameter_interval (d := d)] with x hx hμ
    rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ sobolevNorm s (correction hd x : Space d) from Real.sqrt_nonneg _)]
    exact correction_sobolevNorm_bound hd hμ.1 hμ.2 hs x.2 (correction hd x) hx
  exact hb.trans hR

#print axioms correction_sobolevNorm_bound
#print axioms correction_sobolev_quadratic
end BecknerOnofri.HighDim.GraphSobolevBounds
