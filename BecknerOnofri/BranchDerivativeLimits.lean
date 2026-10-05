import BecknerOnofri.BranchEnergyDerivatives
import BecknerOnofri.DiagonalParameterMonotonicity

/-! Exact limits of the differentiated branch energy in the physical parameter.
These are obtained from analytic Taylor remainders, not formal differentiation
of an arbitrary asymptotic estimate. -/
noncomputable section
open Filter Asymptotics
open scoped Topology
namespace BecknerOnofri

lemma tendsto_div_of_monomial_bigO {f : ℝ → ℝ} (a : ℝ) (n m : ℕ) (hnm : n < m)
    (ho : (fun t => f t-a*t^n) =O[𝓝 0] (fun t : ℝ => ‖t‖^m)) :
    Tendsto (fun t => f t/t^n) (𝓝[>] (0:ℝ)) (𝓝 a) := by
  have hlo := ho.trans_isLittleO (isLittleO_norm_pow_norm_pow (E' := ℝ) hnm)
  have hlo' : (fun t => f t-a*t^n) =o[𝓝 0] (fun t : ℝ => t^n) := by
    apply IsLittleO.of_norm_right
    simpa only [norm_pow] using hlo
  have ht := (hlo'.tendsto_div_nhds_zero.mono_left (show (𝓝[>] (0:ℝ)) ≤ 𝓝 0 from nhdsWithin_le_nhds)).add_const a
  simp only [zero_add] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : t ≠ 0 := (show 0 < t from ht).ne'
  field_simp
  <;> ring

namespace HighDim.DiagonalScalarBranch

lemma parameter_second_derivative_expansion {d : ℕ} (hd : 12 ≤ d) :
    (fun t => deriv (deriv (parameter hd)) t-2*kappa d)
      =O[𝓝 0] (fun t : ℝ => ‖t‖^2) := by
  have h := analytic_monomial_deriv_remainder (parameter_analytic hd).deriv
    (2*kappa d) 1 2 (by simpa only [pow_one] using parameter_derivative_expansion hd)
  simpa using h

lemma parameter_derivative_ratio_limit {d : ℕ} (hd : 12 ≤ d) :
    Tendsto (fun t => deriv (parameter hd) t/t) (𝓝[>] (0:ℝ)) (𝓝 (2*kappa d)) := by
  simpa only [pow_one] using tendsto_div_of_monomial_bigO (2*kappa d) 1 3 (by decide)
    (by simpa only [pow_one] using parameter_derivative_expansion hd)

lemma parameter_second_derivative_limit {d : ℕ} (hd : 12 ≤ d) :
    Tendsto (deriv (deriv (parameter hd))) (𝓝[>] (0:ℝ)) (𝓝 (2*kappa d)) := by
  simpa using tendsto_div_of_monomial_bigO (2*kappa d) 0 2 (by decide)
    (by simpa using parameter_second_derivative_expansion hd)

lemma energy_derivative_ratio_limit {d : ℕ} (hd : 12 ≤ d) :
    Tendsto (fun t => deriv (branchEnergy hd) t/t^3) (𝓝[>] (0:ℝ)) (𝓝 (2*(d:ℝ)*kappa d)) :=
  tendsto_div_of_monomial_bigO _ 3 5 (by decide) (branchEnergy_derivative_expansion hd)

lemma energy_second_derivative_ratio_limit {d : ℕ} (hd : 12 ≤ d) :
    Tendsto (fun t => deriv (deriv (branchEnergy hd)) t/t^2) (𝓝[>] (0:ℝ))
      (𝓝 (6*(d:ℝ)*kappa d)) :=
  tendsto_div_of_monomial_bigO _ 2 4 (by decide) (branchEnergy_second_derivative_expansion hd)

lemma energy_parameter_second_derivative_limit {d : ℕ} (hd : 12 ≤ d) :
    Tendsto (fun t => (deriv (deriv (branchEnergy hd)) t*deriv (parameter hd) t-
      deriv (branchEnergy hd) t*deriv (deriv (parameter hd)) t)/(deriv (parameter hd) t)^3)
      (𝓝[>] (0:ℝ)) (𝓝 ((d:ℝ)/kappa d)) := by
  have hk := (kappa_pos d hd).ne'
  have hp := parameter_derivative_ratio_limit hd
  have hn := ((energy_second_derivative_ratio_limit hd).mul hp).sub
    ((energy_derivative_ratio_limit hd).mul (parameter_second_derivative_limit hd))
  have ht := hn.div (hp.pow 3) (by positivity : (2*kappa d)^3 ≠ 0)
  have hvalue : (6*(d:ℝ)*kappa d*(2*kappa d)-2*(d:ℝ)*kappa d*(2*kappa d))/(2*kappa d)^3 =
      (d:ℝ)/kappa d := by field_simp; ring
  rw [hvalue] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin,(parameter_derivative_pos hd).filter_mono nhdsWithin_le_nhds]
    with t ht hp
  have ht0 : t ≠ 0 := (show 0 < t from ht).ne'
  have hp0 : deriv (parameter hd) t ≠ 0 := (hp ht).ne'
  dsimp only [Pi.div_apply]
  field_simp
  <;> ring

#print axioms energy_parameter_second_derivative_limit
end HighDim.DiagonalScalarBranch
end BecknerOnofri
