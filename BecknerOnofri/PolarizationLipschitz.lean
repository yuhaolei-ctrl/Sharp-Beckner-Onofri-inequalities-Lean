module

public import BecknerOnofri.PolarizationMetricGeometry
public import Legacy.BecknerOnofri.CoordinatePolarization
public import Mathlib.Topology.MetricSpace.Lipschitz

@[expose] public section

/-! Polarization preserves the Lipschitz modulus on the actual Haar torus. -/
noncomputable section
open scoped NNReal
open Set Legacy.TorusEndpoint
namespace BecknerOnofri.PolarizationL1
open Legacy.BecknerOnofri.CoordinatePolarization

lemma reflection_dist_le {d : ℕ} (i : Fin d) (a : ℝ) (x y : Torus d) :
    dist (reflection i a x) (reflection i a y)≤dist x y := by
  apply (dist_pi_le_iff dist_nonneg).mpr
  intro j
  by_cases hj : j=i
  · subst j
    simpa only [reflection,ite_true,circleReflection_dist] using dist_le_pi_dist x y i
  · simpa only [reflection,if_neg hj] using dist_le_pi_dist x y j

lemma reflection_dist {d : ℕ} (i : Fin d) (a : ℝ) (x y : Torus d) :
    dist (reflection i a x) (reflection i a y)=dist x y := by
  apply le_antisymm (reflection_dist_le i a x y)
  have h := reflection_dist_le i a (reflection i a x) (reflection i a y)
  rw [reflection_involutive i a x,reflection_involutive i a y] at h
  exact h

lemma reflection_isometry {d : ℕ} (i : Fin d) (a : ℝ) : Isometry (reflection i a) :=
  isometry_iff_dist_eq.mpr (reflection_dist i a)

lemma reflection_dist_opposite {d : ℕ} (i : Fin d) (a : ℝ) {x y : Torus d}
    (hx : x∈halfTorus i a) (hy : y∉halfTorus i a) :
    dist x (reflection i a y)≤dist x y := by
  apply (dist_pi_le_iff dist_nonneg).mpr
  intro j
  by_cases hj : j=i
  · subst j
    simpa only [reflection,ite_true] using (circle_dist_opposite a hx hy).trans (dist_le_pi_dist x y i)
  · simpa only [reflection,if_neg hj] using dist_le_pi_dist x y j

lemma polarize_dist_opposite {d : ℕ} (i : Fin d) (a : ℝ) {f : Torus d → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) {x y : Torus d} (hx : x∈halfTorus i a) (hy : y∉halfTorus i a) :
    dist (polarize i a f x) (polarize i a f y)≤K*dist x y := by
  have hxy := reflection_dist_opposite i a hx hy
  have hyx : dist (reflection i a x) y≤dist x y := by
    have he := reflection_dist i a x (reflection i a y)
    rw [reflection_involutive i a y] at he
    exact he.le.trans hxy
  rcases polarize_value_or_reflected i a f x with he | he <;>
    rcases polarize_value_or_reflected i a f y with he' | he' <;> rw [he,he']
  · exact hf.dist_le_mul x y
  · exact (hf.dist_le_mul x (reflection i a y)).trans (mul_le_mul_of_nonneg_left hxy K.2)
  · exact (hf.dist_le_mul (reflection i a x) y).trans (mul_le_mul_of_nonneg_left hyx K.2)
  · simpa only [reflection_dist] using hf.dist_le_mul (reflection i a x) (reflection i a y)

theorem polarize_lipschitz {d : ℕ} (i : Fin d) (a : ℝ) {f : Torus d → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) : LipschitzWith K (polarize i a f) := by
  have hr : LipschitzWith K (fun x => f (reflection i a x)) := by
    simpa only [Function.comp_def,mul_one] using hf.comp (reflection_isometry i a).lipschitz
  apply LipschitzWith.of_dist_le_mul
  intro x y
  by_cases hx : x∈halfTorus i a <;> by_cases hy : y∈halfTorus i a
  · simpa only [polarize,if_pos hx,if_pos hy,max_self] using (hf.max hr).dist_le_mul x y
  · exact polarize_dist_opposite i a hf hx hy
  · simpa only [dist_comm] using polarize_dist_opposite i a hf hy hx
  · simpa only [polarize,if_neg hx,if_neg hy,max_self] using (hf.min hr).dist_le_mul x y

#print axioms polarize_lipschitz
end BecknerOnofri.PolarizationL1
