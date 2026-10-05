import BecknerOnofri.DiagonalEnergyExpansion
import BecknerOnofri.AnalyticDerivativeOrder
import BecknerOnofri.ReducedQuarticAnalytic

/-! Differentiated analytic energy remainders on the actual diagonal branch.
The analytic hypothesis is proved from the Gibbs graph before differentiating. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter Asymptotics
open scoped Topology
namespace BecknerOnofri

lemma analytic_monomial_deriv_remainder {f : ℝ → ℝ} (hf : AnalyticAt ℝ f 0)
    (a : ℝ) (n N : ℕ)
    (ho : (fun t => f t-a*t^n) =O[𝓝 0] (fun t : ℝ => ‖t‖^(N+1))) :
    (fun t => deriv f t-(n:ℝ)*a*t^(n-1)) =O[𝓝 0] (fun t : ℝ => ‖t‖^N) := by
  have ha : AnalyticAt ℝ (fun t => f t-a*t^n) 0 :=
    hf.sub (analyticAt_const.mul (analyticAt_id.pow n))
  have hh := analytic_deriv_order (N := N) ha ho
  apply hh.congr'
  · filter_upwards [hf.eventually_analyticAt] with t ht
    have he : HasDerivAt (fun y => f y-a*y^n) (deriv f t-(n:ℝ)*a*t^(n-1)) t := by
      convert! ht.differentiableAt.hasDerivAt.sub (((hasDerivAt_id t).pow n).const_mul a) using 1
      simp only [id_eq]
      ring
    exact he.deriv
  · rfl

namespace HighDim.DiagonalScalarBranch
open ContinuousGibbs ContinuousFirstShell ContinuousComplement GreenLocalBranch ReducedEquation
open ReducedEnergyGradient ReducedCubicExpansion

lemma branchEnergy_analytic {d : ℕ} (hd : 12 ≤ d) : AnalyticAt ℝ (branchEnergy hd) 0 := by
  let p : ℝ → ℝ × Coordinates d := fun t => (parameter hd t,realDiagonal d t)
  have hp : AnalyticAt ℝ p 0 := (parameter_analytic hd).prod ((realDiagonal d).analyticAt 0)
  have hbase : p 0 = (1,0) := by simp [p]
  have hw : AnalyticAt ℝ (fun t => (correction hd (p t) : Space d)) 0 := by
    have hh : AnalyticAt ℝ (fun t => correction hd (p t)) 0 := by
      have h := correction_analytic hd
      rw [← hbase] at h
      exact h.comp hp
    exact ((complement d).subtypeL.analyticAt _).comp hh
  have hu := branchPotential_analytic hd
  have hZ := (partition_analytic (branchPotential hd 0)).comp hu
  have hlog : AnalyticAt ℝ (fun t => Real.log (partition (branchPotential hd t))) 0 :=
    (analyticAt_log (partition_pos (branchPotential hd 0))).comp (f := fun t => partition (branchPotential hd t)) hZ
  have has : AnalyticAt ℝ (fun t => assembly d (realDiagonal d t)) 0 :=
    ((assembly d).analyticAt _).comp ((realDiagonal d).analyticAt 0)
  have hsq := ((mean d).analyticAt _).comp (has.pow 2)
  have hn := (normalized_analytic (branchPotential hd 0)).comp hu
  have hpair := ((mean d).analyticAt _).comp (hw.mul hn)
  have hden : (2:ℝ)*parameter hd 0 ≠ 0 := by simp
  have hg : AnalyticAt ℝ (fun t : ℝ => Real.log (partition (branchPotential hd t))-
      mean d ((assembly d (realDiagonal d t))^2)/(2*parameter hd t)-
      (1/2:ℝ)*mean d ((correction hd (p t):Space d)*normalized (branchPotential hd t))) 0 := (hlog.sub (hsq.div (analyticAt_const.mul (parameter_analytic hd)) hden)).sub
    (analyticAt_const.mul hpair)
  apply hg.congr
  filter_upwards [(branch_coordinates_tendsto hd).eventually (correction_solves hd),
    (parameter_analytic hd).continuousAt.eventually (Ioi_mem_nhds (by simp : (0:ℝ)<parameter hd 0))]
    with t hs ht
  symm
  change branchEnergy hd t = _
  change physicalReducedEnergy hd (parameter hd t,realDiagonal d t) = _
  rw [physicalReducedEnergy_eq_graphValue hd ht _ hs]
  rfl

lemma branchEnergy_derivative_expansion {d : ℕ} (hd : 12 ≤ d) :
    (fun t => deriv (branchEnergy hd) t-2*(d:ℝ)*kappa d*t^3)
      =O[𝓝 0] (fun t : ℝ => ‖t‖^5) := by
  have h := analytic_monomial_deriv_remainder (branchEnergy_analytic hd)
    ((d:ℝ)*kappa d/2) 4 5 (branchEnergy_amplitude_expansion hd)
  apply h.congr_left
  intro t
  norm_num only [Nat.cast_ofNat,Nat.reduceSub]
  ring

lemma branchEnergy_second_derivative_expansion {d : ℕ} (hd : 12 ≤ d) :
    (fun t => deriv (deriv (branchEnergy hd)) t-6*(d:ℝ)*kappa d*t^2)
      =O[𝓝 0] (fun t : ℝ => ‖t‖^4) := by
  have h := analytic_monomial_deriv_remainder (branchEnergy_analytic hd).deriv
    (2*(d:ℝ)*kappa d) 3 4 (branchEnergy_derivative_expansion hd)
  apply h.congr_left
  intro t
  norm_num only [Nat.cast_ofNat,Nat.reduceSub]
  ring

#print axioms branchEnergy_analytic
#print axioms branchEnergy_derivative_expansion
#print axioms branchEnergy_second_derivative_expansion
end HighDim.DiagonalScalarBranch
end BecknerOnofri
