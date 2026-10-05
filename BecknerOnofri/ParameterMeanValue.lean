import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Asymptotics.Defs

/-! Integrating a uniform parameter derivative bound without losing amplitude powers. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Filter Asymptotics Set
open scoped Topology
namespace BecknerOnofri

variable {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem parameter_difference_isBigO {F D : ℝ × E → W} {a : ℝ} (n : ℕ)
    (hder : ∀ᶠ x in 𝓝 (a,(0:E)), HasDerivAt (fun t => F (t,x.2)) (D x) x.1)
    (hD : D =O[𝓝 (a,(0:E))] (fun x => ‖x.2‖^n)) :
    (fun x => F x - F (a,x.2)) =O[𝓝 (a,(0:E))] (fun x => |x.1-a| * ‖x.2‖^n) := by
  obtain ⟨C,hC,hbound⟩ := hD.exists_pos
  obtain ⟨ε,hε,hball⟩ := Metric.eventually_nhds_iff.mp (hder.and hbound.bound)
  apply IsBigO.of_bound C
  filter_upwards [Metric.ball_mem_nhds (a,(0:E)) hε] with x hx
  have hseg (t : ℝ) (ht : t ∈ uIcc a x.1) :
      HasDerivAt (fun t => F (t,x.2)) (D (t,x.2)) t ∧ ‖D (t,x.2)‖ ≤ C*‖x.2‖^n := by
    have hdist : dist (t,x.2) (a,(0:E)) < ε := by
      have ht' : dist t a ≤ dist x.1 a := by
        simpa only [dist_comm] using Real.dist_left_le_of_mem_uIcc ht
      change max (dist t a) (dist x.2 0) < ε
      exact lt_of_le_of_lt (max_le_max ht' le_rfl) hx
    have hh := hball hdist
    simpa only [norm_pow, norm_norm] using hh
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t ht => (hseg t ht).1.hasDerivWithinAt)
    (fun t ht => (hseg t ht).2) (convex_uIcc a x.1) (left_mem_uIcc) (right_mem_uIcc)
  simp only [norm_mul, norm_pow, norm_norm, Real.norm_eq_abs, abs_abs, abs_norm]
  simpa only [Real.norm_eq_abs, mul_assoc, mul_left_comm, mul_comm] using hh

#print axioms parameter_difference_isBigO
end BecknerOnofri
