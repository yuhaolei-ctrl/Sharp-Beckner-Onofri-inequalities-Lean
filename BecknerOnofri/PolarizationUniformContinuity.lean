import Legacy.BecknerOnofri.CoordinatePolarization
import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-! Uniform continuity of genuine max/min polarization, needed for invariance
of the uniform closure of the finite orbit. -/
noncomputable section
open Filter Legacy.TorusEndpoint
namespace BecknerOnofri.PolarizationL1
open Legacy.BecknerOnofri.CoordinatePolarization
attribute [local instance] Classical.propDecidable

theorem polarize_distance_le_max {d : ℕ} (i : Fin d) (a : ℝ)
    (f g : Torus d → ℝ) (x : Torus d) :
    dist (polarize i a f x) (polarize i a g x)≤
      max (dist (f x) (g x)) (dist (f (reflection i a x)) (g (reflection i a x))) := by
  simp only [Real.dist_eq,polarize]
  split_ifs
  · exact abs_max_sub_max_le_max _ _ _ _
  · exact abs_min_sub_min_le_max _ _ _ _

theorem polarize_uniform_error {d : ℕ} (i : Fin d) (a : ℝ)
    {f g : Torus d → ℝ} {C : ℝ} (h : ∀ x,dist (f x) (g x)≤C) :
    ∀ x,dist (polarize i a f x) (polarize i a g x)≤C := by
  intro x
  exact (polarize_distance_le_max i a f g x).trans (max_le (h x) (h _))

theorem polarize_tendstoUniformly {d : ℕ} {ι : Type*} (i : Fin d) (a : ℝ)
    {F : ι → Torus d → ℝ} {f : Torus d → ℝ} {l : Filter ι}
    (h : TendstoUniformly F f l) :
    TendstoUniformly (fun n => polarize i a (F n)) (polarize i a f) l := by
  rw [Metric.tendstoUniformly_iff] at h ⊢
  intro ε hε
  filter_upwards [h ε hε] with n hn
  intro x
  exact (polarize_distance_le_max i a f (F n) x).trans_lt (max_lt (hn x) (hn _))

#print axioms polarize_tendstoUniformly
end BecknerOnofri.PolarizationL1
