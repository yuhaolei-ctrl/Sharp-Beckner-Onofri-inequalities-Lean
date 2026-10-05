module

public import BecknerOnofri.DiagonalScalarBranch
public import BecknerOnofri.AnalyticDerivativeOrder
public import BecknerOnofri.Kappa
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

@[expose] public section

/-! Strict monotonicity of the actual analytic parameter branch on positive
amplitudes, from its proved expansion and exact positivity of κd. -/
noncomputable section
open Filter Asymptotics
open scoped Topology
namespace BecknerOnofri.HighDim.DiagonalScalarBranch

theorem parameter_derivative_expansion {d : ℕ} (hd : 12 ≤ d) :
    (fun t => deriv (parameter hd) t - 2*kappa d*t)
      =O[𝓝 0] (fun t : ℝ => ‖t‖^3) :=
  analytic_quadratic_deriv_remainder (parameter_analytic hd) 1 (kappa d) (parameter_expansion hd)

theorem parameter_derivative_pos {d : ℕ} (hd : 12 ≤ d) :
    ∀ᶠ t in 𝓝 (0:ℝ), 0 < t → 0 < deriv (parameter hd) t :=
  analytic_quadratic_deriv_pos (parameter_analytic hd) 1 (kappa_pos d hd) (parameter_expansion hd)

/-- One closed positive amplitude interval has strictly increasing parameter,
including the uniform branch endpoint. -/
theorem parameter_strictMonoOn {d : ℕ} (hd : 12 ≤ d) :
    ∃ r : ℝ, 0 < r ∧ StrictMonoOn (parameter hd) (Set.Icc 0 r) ∧
      ContinuousOn (parameter hd) (Set.Icc 0 r) := by
  obtain ⟨ε,hε,he⟩ := Metric.eventually_nhds_iff.mp
    ((parameter_analytic hd).eventually_analyticAt.and (parameter_derivative_pos hd))
  have hn {t : ℝ} (ht : t ∈ Set.Icc 0 (ε/2)) : dist t 0 < ε := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg ht.1]
    linarith [ht.2]
  have hc : ContinuousOn (parameter hd) (Set.Icc 0 (ε/2)) := by
    intro t ht
    exact (he (hn ht)).1.continuousAt.continuousWithinAt
  refine ⟨ε/2,by positivity,?_,hc⟩
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 (ε/2)) hc
  intro t ht
  rw [interior_Icc] at ht
  exact (he (hn ⟨ht.1.le,ht.2.le⟩)).2 ht.1

/-- Positive amplitudes are strictly supercritical and cannot represent the
same parameter twice in this actual local branch. -/
theorem parameter_positive_unique {d : ℕ} (hd : 12 ≤ d) :
    ∃ r : ℝ, 0 < r ∧
      (∀ t, 0 < t → t ≤ r → 1 < parameter hd t) ∧
      (∀ s t, 0 ≤ s → s ≤ r → 0 ≤ t → t ≤ r →
        parameter hd s = parameter hd t → s=t) := by
  obtain ⟨r,hr,hm,hc⟩ := parameter_strictMonoOn hd
  refine ⟨r,hr,?_,?_⟩
  · intro t ht htr
    simpa only [parameter_base] using hm ⟨le_rfl,hr.le⟩ ⟨ht.le,htr⟩ ht
  · intro s t hs hsr ht htr he
    exact hm.injOn ⟨hs,hsr⟩ ⟨ht,htr⟩ he

#print axioms parameter_derivative_expansion
#print axioms parameter_strictMonoOn
#print axioms parameter_positive_unique
end BecknerOnofri.HighDim.DiagonalScalarBranch
