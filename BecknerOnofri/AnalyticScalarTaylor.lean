import Mathlib.Analysis.Calculus.FDeriv.Analytic

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter Asymptotics
open scoped Topology
namespace BecknerOnofri

theorem analytic_linear_remainder {f : ℝ → ℝ} {c : ℝ}
    (hf : AnalyticAt ℝ f 0) (hd : HasDerivAt f c 0) :
    (fun t => f t-f 0-c*t) =O[𝓝 (0:ℝ)] (fun t => ‖t‖^2) := by
  obtain ⟨p,hp⟩ := hf
  have h0 : p.coeff 0=f 0 := hp.coeff_zero _
  have h1 : p.coeff 1=c := hp.deriv.symm.trans hd.deriv
  have he : p.partialSum 2 = fun t => f 0+c*t := by
    funext t
    simp only [FormalMultilinearSeries.partialSum,Finset.sum_range_succ,
      Finset.sum_range_zero,zero_add,FormalMultilinearSeries.apply_eq_pow_smul_coeff,
      h0,h1,pow_zero,pow_one,smul_eq_mul,one_mul]
    ring
  have h := hp.isBigO_sub_partialSum_pow 2
  simp only [zero_add,he] at h
  apply h.congr_left
  intro t
  ring

#print axioms analytic_linear_remainder
end BecknerOnofri
