module

public import BecknerOnofri.AnalyticPitchforkInvertible
public import BecknerOnofri.AnalyticDerivativeOrder
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

@[expose] public section

noncomputable section
open Filter Asymptotics
open scoped Topology
namespace BecknerOnofri.AnalyticPitchfork

theorem parameter_derivative_pos (D : Data) (hD : 0<D.coefficient) :
    ∀ᶠ t in 𝓝 (0:ℝ),0<t → 0<deriv (parameter D) t :=
  analytic_quadratic_deriv_pos (parameter_analytic D) 1 hD (parameter_expansion D)

theorem parameter_gt_one (D : Data) (hD : 0<D.coefficient) :
    ∀ᶠ t in 𝓝 (0:ℝ),0<t → 1<parameter D t := by
  obtain ⟨ε,hε,he⟩ := Metric.eventually_nhds_iff.mp
    ((parameter_analytic D).eventually_analyticAt.and (parameter_derivative_pos D hD))
  have hn {t : ℝ} (ht : t∈Set.Icc 0 (ε/2)) : dist t 0<ε := by
    rw [Real.dist_eq,sub_zero,abs_of_nonneg ht.1]
    linarith [ht.2]
  have hc : ContinuousOn (parameter D) (Set.Icc 0 (ε/2)) :=
    fun t ht => (he (hn ht)).1.continuousAt.continuousWithinAt
  have hm : StrictMonoOn (parameter D) (Set.Icc 0 (ε/2)) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 (ε/2)) hc
    intro t ht
    rw [interior_Icc] at ht
    exact (he (hn ⟨ht.1.le,ht.2.le⟩)).2 ht.1
  filter_upwards [gt_mem_nhds (show (0:ℝ)<ε/2 by positivity)] with t ht
  intro hp
  simpa only [parameter_base] using hm ⟨le_rfl,by positivity⟩ ⟨hp.le,ht.le⟩ hp

#print axioms parameter_gt_one
end BecknerOnofri.AnalyticPitchfork
