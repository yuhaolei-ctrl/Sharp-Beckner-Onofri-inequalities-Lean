import BecknerOnofri.ReducedCubicExpansion
import BecknerOnofri.AnalyticEvenOrder
import BecknerOnofri.FirstShellOrbits

/-! Genuine translation parity improves the actual reduced cubic remainder to order five. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Filter Asymptotics
open scoped Topology
namespace BecknerOnofri.HighDim.ReducedCubicExpansion
open ContinuousGibbs ContinuousFirstShell QuadraticModes QuadraticSlaving SlavedMoments ReducedEquation

theorem quadraticCorrection_analytic {d : ℕ} (hd : 12 ≤ d) :
    AnalyticAt ℝ (quadraticCorrection hd) (0 : Coordinates d) := by
  have hv := (assembly d).analyticAt (0 : Coordinates d)
  have hc := ((center d).analyticAt _).comp (hv.pow 2)
  have hq : AnalyticAt ℝ (fun z : Coordinates d => (1/2:ℝ) • center d ((assembly d z)^2)) 0 :=
    by convert! (show AnalyticAt ℝ (fun _ : Coordinates d => (1/2:ℝ)) 0 from analyticAt_const).smul hc using 1
  have hh := ((inverseGreen hd).analyticAt _).comp hq
  convert! hh using 1
  funext z
  unfold quadraticCorrection
  rw [quadraticTerm_of_mean_zero (mean_assembly z)]
  rfl

theorem cubicTerm_assembly_analytic (d : ℕ) :
    AnalyticAt ℝ (fun z : Coordinates d => cubicTerm (assembly d z)) 0 := by
  have hv := (assembly d).analyticAt (0 : Coordinates d)
  have hc := ((center d).analyticAt _).comp (hv.pow 3)
  have hm := ((mean d).analyticAt _).comp (hv.pow 2)
  have h1 : AnalyticAt ℝ (fun z : Coordinates d => (1/6:ℝ) • center d ((assembly d z)^3)) 0 :=
    by convert! (show AnalyticAt ℝ (fun _ : Coordinates d => (1/6:ℝ)) 0 from analyticAt_const).smul hc using 1
  have h2 : AnalyticAt ℝ (fun z : Coordinates d => ((1/2:ℝ)*mean d ((assembly d z)^2)) • assembly d z) 0 :=
    (analyticAt_const.mul hm).smul hv
  convert! h1.sub h2 using 1
  funext z
  exact cubicTerm_of_mean_zero (mean_assembly z)

theorem cubicModel_analytic {d : ℕ} (hd : 12 ≤ d) :
    AnalyticAt ℝ (cubicModel hd) (0 : Coordinates d) := by
  have hv := (assembly d).analyticAt (0 : Coordinates d)
  have hw := ((complement d).subtypeL.analyticAt _).comp (quadraticCorrection_analytic hd)
  exact (((coordinates d).analyticAt _).comp ((hv.mul hw).add (cubicTerm_assembly_analytic d))).neg

theorem cubicModel_neg {d : ℕ} (hd : 12 ≤ d) (z : Coordinates d) : cubicModel hd (-z) = -cubicModel hd z := by
  funext i
  rw [Pi.neg_apply, cubicModel_apply, cubicModel_apply]
  simp only [Pi.neg_apply, norm_neg]
  ring

/-- The actual vector reduced equation has the sharp parity-consistent O5 cubic remainder. -/
theorem reduced_cubic_expansion_fifth {d : ℕ} (hd : 12 ≤ d) :
    (fun z => reduced hd (1,z) - cubicModel hd z)
      =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖^5) := by
  have ha : AnalyticAt ℝ (fun z : Coordinates d => reduced hd (1,z)) 0 :=
    (reduced_analytic hd).comp (analyticAt_const.prod analyticAt_id)
  apply analytic_odd_fourth_order (ha.sub (cubicModel_analytic hd)) (reduced_cubic_expansion hd)
  have ht : Tendsto (fun z : Coordinates d => ((1:ℝ),z)) (𝓝 0) (𝓝 (1,0)) :=
    (continuous_const.prodMk continuous_id).continuousAt
  filter_upwards [ht.eventually (ContinuousSymmetry.reduced_neg hd)] with z hz
  change reduced hd (1,-z) - cubicModel hd (-z) = -(reduced hd (1,z) - cubicModel hd z)
  change reduced hd (1,-z) = -reduced hd (1,z) at hz
  rw [hz, cubicModel_neg]
  abel

/-- Actual diagonal scalar equation R(1,t)=κd t³+O(t⁵). -/
theorem reduced_diagonal_cubic_expansion_fifth {d : ℕ} (hd : 12 ≤ d) (i : Fin d) :
    (fun t : ℝ => (reduced hd (1, realDiagonal d t) i).re - kappa d*t^3)
      =O[𝓝 0] (fun t : ℝ => ‖t‖^5) := by
  have ht : Tendsto (realDiagonal d) (𝓝 0) (𝓝 0) := by
    simpa only [map_zero] using (realDiagonal d).continuous.continuousAt.tendsto (x := (0:ℝ))
  have h := (reduced_cubic_expansion_fifth hd).comp_tendsto ht
  have hnorm := ((realDiagonal d).isBigO_id (𝓝 0)).norm_left.norm_right.pow 5
  have h' := h.trans hnorm
  let ev : Coordinates d →L[ℝ] ℝ := Complex.reCLM.comp (ContinuousLinearMap.proj i)
  apply (((ev).isBigO_comp _ _).trans h').congr_left
  intro t
  change (reduced hd (1, realDiagonal d t) i - cubicModel hd (realDiagonal d t) i).re = _
  rw [cubicModel_diagonal, Complex.sub_re, Complex.ofReal_re]

#print axioms reduced_cubic_expansion_fifth
#print axioms reduced_diagonal_cubic_expansion_fifth
end BecknerOnofri.HighDim.ReducedCubicExpansion
