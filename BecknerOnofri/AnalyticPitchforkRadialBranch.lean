module

public import BecknerOnofri.AnalyticPitchforkRadial

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter Asymptotics
open scoped Topology
namespace BecknerOnofri.AnalyticPitchfork

/-- Analytic radial squared-amplitude eigenvalue germ with its precise
leading coefficient and a proved quadratic amplitude error. -/
theorem exists_radial_branch_coefficient (D : Data) :
    ∃ R : ℝ → ℝ,AnalyticAt ℝ R 0 ∧ R 0= -D.coefficient ∧
      ((fun t => R t-(-D.coefficient)) =O[𝓝 (0:ℝ)] (fun t => ‖t‖^2)) ∧
      (∀ᶠ t in 𝓝 (0:ℝ),amplitudePartial D (parameter D t,t)=
        -(2*parameter D t*t)*R t) := by
  obtain ⟨K,hK,hK0,he,hn⟩ := exists_radial_factor D
  let R : ℝ → ℝ := fun t => -K (parameter D t,t)/(2*parameter D t)
  have hcomp : AnalyticAt ℝ (fun t => K (parameter D t,t)) 0 := by
    have ho : AnalyticAt ℝ K (parameter D 0,0) := by simpa only [parameter_base] using hK
    exact ho.comp (f := fun t => (parameter D t,t))
      ((parameter_analytic D).prod analyticAt_id)
  have hR : AnalyticAt ℝ R 0 := hcomp.neg.div (analyticAt_const.mul (parameter_analytic D))
    (by simp only [parameter_base,mul_one]; norm_num)
  have hR0 : R 0= -D.coefficient := by simp [R,parameter_base,hK0]; ring
  have heven : ∀ᶠ t in 𝓝 (0:ℝ),R (-t)=R t := by
    filter_upwards [parameter_even D,(parameter_pair_tendsto D).eventually hn] with t ht hn
    dsimp only [R]
    rw [ht]
    change K (parameter D t,-t)=K (parameter D t,t) at hn
    rw [hn]
  refine ⟨R,hR,hR0,?_,?_⟩
  · simpa only [hR0] using analytic_even_quadratic_remainder hR heven
  · have hμ : ∀ᶠ t in 𝓝 (0:ℝ),parameter D t≠0 := by
      have hp := (parameter_analytic D).continuousAt.tendsto
      rw [parameter_base] at hp
      exact hp.eventually (eventually_ne_nhds (by norm_num : (1:ℝ)≠0))
    filter_upwards [(parameter_pair_tendsto D).eventually he,hμ] with t ht hμ
    rw [ht]
    dsimp only [R]
    field_simp
    <;> ring

#print axioms exists_radial_branch_coefficient
end BecknerOnofri.AnalyticPitchfork
