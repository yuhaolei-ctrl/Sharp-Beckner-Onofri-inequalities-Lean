module

public import BecknerOnofri.BranchDerivativeLimits

@[expose] public section

/-! Quantitative control of the curvature remainder by analytic branch expansions. -/
noncomputable section
open Filter Asymptotics
open scoped Topology
namespace BecknerOnofri

lemma monomial_bigO_div_pow {f : ℝ → ℝ} (a : ℝ) (n m : ℕ)
    (ho : (fun t => f t-a*t^n) =O[𝓝 0] (fun t : ℝ => ‖t‖^(n+m))) :
    (fun t => f t/t^n-a) =O[𝓝[>] (0:ℝ)] (fun t : ℝ => ‖t‖^m) := by
  obtain ⟨C,hC,h⟩ := ho.exists_pos
  apply IsBigO.of_bound C
  filter_upwards [h.bound.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with t hb ht
  have htpos : 0 < t := ht
  have hpow : 0 < t^n := pow_pos htpos _
  simp only [norm_pow,Real.norm_eq_abs,abs_of_pos htpos] at hb ⊢
  rw [div_sub' hpow.ne',abs_div,abs_of_pos hpow]
  apply (div_le_iff₀ hpow).mpr
  calc
    |f t-t^n*a| = |f t-a*t^n| := by rw [mul_comm (t^n) a]
    _ ≤ C*t^(n+m) := hb
    _ = _ := by rw [pow_add]; ring

lemma bigO_mul_constant_remainder {α : Type*} {l : Filter α}
    {f g h : α → ℝ} {a b : ℝ}
    (hf : (fun t => f t-a) =O[l] h) (hg : (fun t => g t-b) =O[l] h)
    (ht : Tendsto g l (𝓝 b)) : (fun t => f t*g t-a*b) =O[l] h := by
  have hp : (fun t => (f t-a)*g t) =O[l] h := by
    simpa using hf.mul (ht.isBigO_one ℝ)
  convert! hp.add (hg.const_mul_left a) using 1
  funext t
  ring

lemma bigO_div_constant_remainder {α : Type*} {l : Filter α}
    {f g h : α → ℝ} {a b : ℝ}
    (hf : (fun t => f t-a) =O[l] h) (hg : (fun t => g t-b) =O[l] h)
    (ht : Tendsto g l (𝓝 b)) (hb : b ≠ 0) :
    (fun t => f t/g t-a/b) =O[l] h := by
  have hn : (fun t => (f t-a)-(a/b)*(g t-b)) =O[l] h :=
    hf.sub (hg.const_mul_left (a/b))
  have hi := (ht.inv₀ hb).isBigO_one ℝ
  have hh : (fun t => ((f t-a)-(a/b)*(g t-b))*(g t)⁻¹) =O[l] h := by
    simpa using hn.mul hi
  apply hh.congr'
  · filter_upwards [ht.eventually (eventually_ne_nhds hb)] with t ht
    field_simp
    <;> ring
  · rfl

namespace HighDim.DiagonalScalarBranch

lemma energy_parameter_second_derivative_expansion {d : ℕ} (hd : 12 ≤ d) :
    (fun t => (deriv (deriv (branchEnergy hd)) t*deriv (parameter hd) t-
      deriv (branchEnergy hd) t*deriv (deriv (parameter hd)) t)/(deriv (parameter hd) t)^3-
        (d:ℝ)/kappa d) =O[𝓝[>] (0:ℝ)] (fun t : ℝ => ‖t‖^2) := by
  have hk := (kappa_pos d hd).ne'
  have hp : (fun t => deriv (parameter hd) t/t-2*kappa d)
      =O[𝓝[>] (0:ℝ)] (fun t : ℝ => ‖t‖^2) := by
    simpa only [pow_one] using monomial_bigO_div_pow (2*kappa d) 1 2
      (by simpa only [pow_one] using parameter_derivative_expansion hd)
  have he₁ := monomial_bigO_div_pow (2*(d:ℝ)*kappa d) 3 2
    (branchEnergy_derivative_expansion hd)
  have he₂ := monomial_bigO_div_pow (6*(d:ℝ)*kappa d) 2 2
    (branchEnergy_second_derivative_expansion hd)
  have hp₂ := (parameter_second_derivative_expansion hd).mono
    (show (𝓝[>] (0:ℝ)) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  have hpt := parameter_derivative_ratio_limit hd
  have hn := (bigO_mul_constant_remainder he₂ hp hpt).sub
    (bigO_mul_constant_remainder he₁ hp₂ (parameter_second_derivative_limit hd))
  have hn' : (fun t =>
      (deriv (deriv (branchEnergy hd)) t/t^2*(deriv (parameter hd) t/t)-
        deriv (branchEnergy hd) t/t^3*deriv (deriv (parameter hd)) t)-
        (6*(d:ℝ)*kappa d*(2*kappa d)-2*(d:ℝ)*kappa d*(2*kappa d)))
        =O[𝓝[>] (0:ℝ)] (fun t : ℝ => ‖t‖^2) := by
    convert! hn using 1
    funext t
    ring
  have hsq := bigO_mul_constant_remainder hp hp hpt
  have hcube := bigO_mul_constant_remainder hsq hp hpt
  have hh := bigO_div_constant_remainder hn' hcube ((hpt.mul hpt).mul hpt)
    (by positivity : (2*kappa d)*(2*kappa d)*(2*kappa d) ≠ 0)
  apply hh.congr'
  · filter_upwards [self_mem_nhdsWithin,
      (parameter_derivative_pos hd).filter_mono nhdsWithin_le_nhds] with t ht hp
    have ht0 : t ≠ 0 := (show 0<t from ht).ne'
    have hp0 : deriv (parameter hd) t ≠ 0 := (hp ht).ne'
    field_simp
    <;> ring
  · rfl

#print axioms energy_parameter_second_derivative_expansion
end HighDim.DiagonalScalarBranch
end BecknerOnofri
