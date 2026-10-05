module

public import Legacy.BecknerOnofri.CircleHeatPoisson

@[expose] public section

/-! The actual circular half-arc comparison for the unit-circle heat kernel. -/
noncomputable section
open Set MeasureTheory Legacy.TorusEndpoint TorusHeatPositivity
open scoped BigOperators
namespace Legacy.BecknerOnofri.CircleHeat
open CoordinatePolarization

theorem realHeat_even {t : ℝ} (ht : 0 < t) (x : ℝ) : realHeat t (-x) = realHeat t x := by
  rw [realHeat_eq_cosine_series ht, realHeat_eq_cosine_series ht]
  congr 2
  apply tsum_congr
  intro n
  dsimp [cosineTerm]
  rw [show 2*Real.pi*(n+1:ℝ)*(-x) = -(2*Real.pi*(n+1:ℝ)*x) by ring, Real.cos_neg]

theorem realHeat_add_one (t x : ℝ) : realHeat t (x+1) = realHeat t x := by
  unfold realHeat
  rw [AddCircle.coe_add_period]

theorem realHeat_one_sub {t : ℝ} (ht : 0 < t) (x : ℝ) : realHeat t (1-x) = realHeat t x := by
  rw [show 1-x = -x+1 by ring, realHeat_add_one, realHeat_even ht]

theorem realHeat_abs {t : ℝ} (ht : 0 < t) (x : ℝ) : realHeat t |x| = realHeat t x := by
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx]
  · rw [abs_of_neg (lt_of_not_ge hx), realHeat_even ht]

theorem realHeat_sum_le_sub {t u v : ℝ} (ht : 0 < t)
    (hu : u ∈ Icc (0:ℝ) (1/2)) (hv : v ∈ Icc (0:ℝ) (1/2)) :
    realHeat t (u+v) ≤ realHeat t (u-v) := by
  have ha : |u-v| ≤ 1/2 := abs_le.mpr ⟨by linarith [hu.1,hv.2], by linarith [hu.2,hv.1]⟩
  have ha0 : |u-v| ∈ Icc (0:ℝ) (1/2) := ⟨abs_nonneg _,ha⟩
  by_cases hsum : u+v ≤ 1/2
  · have hs : u+v ∈ Icc (0:ℝ) (1/2) := ⟨by linarith [hu.1,hv.1],hsum⟩
    have hle : |u-v| ≤ u+v := abs_le.mpr ⟨by linarith [hu.1],by linarith [hv.1]⟩
    simpa only [realHeat_abs ht] using realHeat_antitone ht ha0 hs hle
  · have hs : 1-(u+v) ∈ Icc (0:ℝ) (1/2) := ⟨by linarith [hu.2,hv.2],by linarith⟩
    have hle : |u-v| ≤ 1-(u+v) := abs_le.mpr ⟨by linarith [hv.2],by linarith [hu.2]⟩
    simpa only [realHeat_one_sub ht,realHeat_abs ht] using realHeat_antitone ht ha0 hs hle

theorem theta_re_even {t : ℝ} (ht : 0 < t) (x : UnitAddCircle) :
    (theta t (-x)).re = (theta t x).re := by
  induction x using QuotientAddGroup.induction_on
  rename_i x
  change (theta t (-(x : UnitAddCircle))).re = (theta t (x : UnitAddCircle)).re
  rw [← AddCircle.coe_neg]
  exact realHeat_even ht x

theorem theta_re_half_comparison {t : ℝ} (ht : 0 < t) (a : ℝ)
    {x y : UnitAddCircle} (hx : x ∈ circleHalf a) (hy : y ∈ circleHalf a) :
    (theta t (x-circleReflection a y)).re ≤ (theta t (x-y)).re := by
  rw [circleHalf_eq_image] at hx hy
  rcases hx with ⟨r,hr,rfl⟩
  rcases hy with ⟨s,hs,rfl⟩
  have hh := realHeat_sum_le_sub ht
    (u := r-a) (v := s-a) ⟨by linarith [hr.1],by linarith [hr.2]⟩
      ⟨by linarith [hs.1],by linarith [hs.2]⟩
  have he1 : (r:UnitAddCircle)-circleReflection a (s:UnitAddCircle) =
      (((r-a)+(s-a):ℝ):UnitAddCircle) := by
    simp only [circleReflection, AddCircle.coe_add, AddCircle.coe_sub]
    rw [show 2*a=a+a by ring, AddCircle.coe_add]
    abel
  have he2 : (r:UnitAddCircle)-(s:UnitAddCircle) = (((r-a)-(s-a):ℝ):UnitAddCircle) := by
    rw [show (r-a)-(s-a)=r-s by ring, AddCircle.coe_sub]
  rw [he1,he2]
  exact hh

#print axioms theta_re_half_comparison
end Legacy.BecknerOnofri.CircleHeat
