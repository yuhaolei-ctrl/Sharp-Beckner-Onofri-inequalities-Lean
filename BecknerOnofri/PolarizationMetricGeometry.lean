import Legacy.BecknerOnofri.CoordinateReflection
import Mathlib.Analysis.Normed.Group.AddCircle

/-! Metric geometry of the actual half-circle reflections. -/
noncomputable section
open Set Legacy.TorusEndpoint
namespace BecknerOnofri.PolarizationL1
open Legacy.BecknerOnofri.CoordinatePolarization

lemma circleReflection_dist (a : ℝ) (x y : UnitAddCircle) :
    dist (circleReflection a x) (circleReflection a y)=dist x y := by
  simp only [circleReflection,dist_eq_norm]
  rw [show ((2*a : ℝ) : UnitAddCircle)-x-(((2*a : ℝ) : UnitAddCircle)-y)=-(x-y) by abel,norm_neg]

lemma circle_norm_small {u : ℝ} (hu : |u|≤1/2) : ‖(u : UnitAddCircle)‖=|u| := by
  apply (AddCircle.norm_coe_eq_abs_iff 1 (by norm_num : (1 : ℝ)≠0)).mpr
  simpa using hu

lemma circle_sum_norm_ge_sub {u v : ℝ} (hu : u∈Icc (0 : ℝ) (1/2))
    (hv : v∈Icc (0 : ℝ) (1/2)) :
    ‖((u-v : ℝ) : UnitAddCircle)‖≤‖((u+v : ℝ) : UnitAddCircle)‖ := by
  rw [circle_norm_small (abs_le.mpr ⟨by linarith [hu.1,hv.2],by linarith [hu.2,hv.1]⟩)]
  by_cases hs : u+v≤1/2
  · rw [circle_norm_small (abs_le.mpr ⟨by linarith [hu.1,hv.1],hs⟩),
      abs_of_nonneg (by linarith [hu.1,hv.1] : 0≤u+v)]
    exact abs_le.mpr ⟨by linarith [hu.1],by linarith [hv.1]⟩
  · have he : ((u+v : ℝ) : UnitAddCircle)=(-((1-(u+v) : ℝ) : UnitAddCircle)) := by
      rw [← AddCircle.coe_neg]
      have h := AddCircle.coe_add_period 1 (u+v-1)
      convert h using 1 <;> congr 1 <;> ring
    rw [he,norm_neg,circle_norm_small (abs_le.mpr ⟨by linarith [hu.2,hv.2],by linarith⟩),
      abs_of_nonneg (by linarith [hu.2,hv.2] : 0≤1-(u+v))]
    exact abs_le.mpr ⟨by linarith [hv.2],by linarith [hu.2]⟩

lemma circle_dist_half (a : ℝ) {x y : UnitAddCircle}
    (hx : x∈circleHalf a) (hy : y∈circleHalf a) :
    dist x y≤dist x (circleReflection a y) := by
  rw [circleHalf_eq_image] at hx hy
  obtain ⟨r,hr,rfl⟩ := hx
  obtain ⟨s,hs,rfl⟩ := hy
  have h := circle_sum_norm_ge_sub
    (u := r-a) (v := s-a) ⟨by linarith [hr.1],by linarith [hr.2]⟩
    ⟨by linarith [hs.1],by linarith [hs.2]⟩
  have he1 : (r : UnitAddCircle)-circleReflection a (s : UnitAddCircle)=
      (((r-a)+(s-a) : ℝ) : UnitAddCircle) := by
    simp only [circleReflection,AddCircle.coe_add,AddCircle.coe_sub]
    rw [show 2*a=a+a by ring,AddCircle.coe_add]
    abel
  have he2 : (r : UnitAddCircle)-(s : UnitAddCircle)=
      (((r-a)-(s-a) : ℝ) : UnitAddCircle) := by
    rw [show (r-a)-(s-a)=r-s by ring,AddCircle.coe_sub]
  simpa only [dist_eq_norm,he1,he2] using h

lemma circle_dist_opposite (a : ℝ) {x y : UnitAddCircle}
    (hx : x∈circleHalf a) (hy : y∉circleHalf a) :
    dist x (circleReflection a y)≤dist x y := by
  rcases circleReflection_half_or_fixed a y with he | he
  · rw [he]
  · have h := circle_dist_half a hx (he.mpr hy)
    rwa [circleReflection_involutive a y] at h

#print axioms circle_dist_half
#print axioms circle_dist_opposite
end BecknerOnofri.PolarizationL1
