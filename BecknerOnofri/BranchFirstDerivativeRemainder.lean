module

public import BecknerOnofri.BranchDerivativeLimits

@[expose] public section

/-! Quantitative first derivative remainder in the parameterized branch. -/
noncomputable section
open Filter Asymptotics
open scoped Topology
namespace BecknerOnofri.HighDim.DiagonalScalarBranch

lemma energy_parameter_derivative_expansion {d : ℕ} (hd : 12 ≤ d) :
    (fun t => deriv (branchEnergy hd) t/deriv (parameter hd) t-(d:ℝ)*t^2)
      =O[𝓝[>] (0:ℝ)] (fun t : ℝ => ‖t‖^4) := by
  obtain ⟨C₁,hC₁,hE⟩ := (branchEnergy_derivative_expansion hd).exists_pos
  obtain ⟨C₂,hC₂,hP⟩ := (parameter_derivative_expansion hd).exists_pos
  have hk := kappa_pos d hd
  have hratio : ∀ᶠ t in 𝓝[>] (0:ℝ), kappa d < deriv (parameter hd) t/t :=
    (parameter_derivative_ratio_limit hd).eventually (lt_mem_nhds (by linarith : kappa d < 2*kappa d))
  let B := C₁+(d:ℝ)*C₂
  have hB : 0 ≤ B := by dsimp [B]; positivity
  apply IsBigO.of_bound (B/kappa d)
  filter_upwards [hE.bound.filter_mono nhdsWithin_le_nhds,
    hP.bound.filter_mono nhdsWithin_le_nhds,hratio,self_mem_nhdsWithin] with t he hp hr ht
  have htpos : 0 < t := ht
  have hplow : kappa d*t ≤ deriv (parameter hd) t := (lt_div_iff₀ htpos).mp hr |>.le
  have hppos : 0 < deriv (parameter hd) t := (mul_pos hk htpos).trans_le hplow
  simp only [norm_pow,Real.norm_eq_abs,abs_of_pos htpos] at he hp ⊢
  have heq : deriv (branchEnergy hd) t-(d:ℝ)*t^2*deriv (parameter hd) t =
      (deriv (branchEnergy hd) t-2*(d:ℝ)*kappa d*t^3)-
        (d:ℝ)*t^2*(deriv (parameter hd) t-2*kappa d*t) := by ring
  have hnum : |deriv (branchEnergy hd) t-(d:ℝ)*t^2*deriv (parameter hd) t| ≤ B*t^5 := by
    rw [heq]
    calc
      _ ≤ |deriv (branchEnergy hd) t-2*(d:ℝ)*kappa d*t^3|+
          |(d:ℝ)*t^2*(deriv (parameter hd) t-2*kappa d*t)| := abs_sub _ _
      _ = |deriv (branchEnergy hd) t-2*(d:ℝ)*kappa d*t^3|+
          (d:ℝ)*t^2*|deriv (parameter hd) t-2*kappa d*t| := by
        rw [abs_mul,abs_of_nonneg (by positivity : 0 ≤ (d:ℝ)*t^2)]
      _ ≤ C₁*t^5+(d:ℝ)*t^2*(C₂*t^3) :=
        add_le_add he (mul_le_mul_of_nonneg_left hp (by positivity))
      _ = _ := by dsimp [B]; ring
  rw [div_sub' hppos.ne',mul_comm (deriv (parameter hd) t) ((d:ℝ)*t^2),abs_div,abs_of_pos hppos]
  apply (div_le_iff₀ hppos).mpr
  refine hnum.trans ?_
  calc
    B*t^5 = (B/kappa d)*t^4*(kappa d*t) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hplow (by positivity)

#print axioms energy_parameter_derivative_expansion
end BecknerOnofri.HighDim.DiagonalScalarBranch
