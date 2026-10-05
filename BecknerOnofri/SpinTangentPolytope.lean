import BecknerOnofri.SpinGeometry
import Mathlib.Analysis.Convex.KreinMilman

/-! The actual compact convex tangent polytope in Lemma 5.18. The reduction
to its extreme points is an analytic theorem, separate from finite arithmetic. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Topology
open Set
namespace BecknerOnofri.HighDim.Spin

def l1 (q : Count → ℝ) : ℝ := ∑ j : Count,|q j|
def tangentPolytope : Set (Count → ℝ) :=
  {q | q 0=0 ∧ (∑ j : Count,q j)=0 ∧ mean q=0 ∧ l1 q≤1}

theorem l1_nonneg (q : Count → ℝ) : 0≤l1 q := Finset.sum_nonneg (fun j _ => abs_nonneg _)
theorem coordinate_le_l1 (q : Count → ℝ) (j : Count) : |q j|≤l1 q :=
  Finset.single_le_sum (fun i _ => abs_nonneg (q i)) (Finset.mem_univ j)
theorem l1_continuous : Continuous l1 := by unfold l1; fun_prop
theorem mean_continuous : Continuous mean := by unfold mean; fun_prop
theorem quadratic_continuous : Continuous quadratic := by unfold quadratic; fun_prop

theorem l1_convex_combination (q r : Count → ℝ) {a b : ℝ} (ha : 0≤a) (hb : 0≤b) :
    l1 (a•q+b•r)≤a*l1 q+b*l1 r := by
  unfold l1
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro j _
  calc
    _ ≤ |a*q j|+|b*r j| := abs_add_le _ _
    _ = _ := by rw [abs_mul,abs_mul,abs_of_nonneg ha,abs_of_nonneg hb]

theorem mean_linear_combination (q r : Count → ℝ) (a b : ℝ) :
    mean (a•q+b•r)=a*mean q+b*mean r := by
  simp only [mean,Pi.add_apply,Pi.smul_apply,smul_eq_mul,mul_add,Finset.sum_add_distrib,
    Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro j _ <;> ring

theorem tangentPolytope_convex : Convex ℝ tangentPolytope := by
  intro q hq r hr a b ha hb hab
  refine ⟨?_,?_,?_,?_⟩
  · simp [hq.1,hr.1]
  · simp [Finset.sum_add_distrib,← Finset.mul_sum,hq.2.1,hr.2.1]
  · rw [mean_linear_combination,hq.2.2.1,hr.2.2.1]
    ring
  · have hh := l1_convex_combination q r ha hb
    have hqa := mul_le_mul_of_nonneg_left hq.2.2.2 ha
    have hrb := mul_le_mul_of_nonneg_left hr.2.2.2 hb
    linarith

theorem tangentPolytope_closed : IsClosed tangentPolytope := by
  apply (isClosed_eq (continuous_apply (0:Count)) continuous_const).inter
  apply (isClosed_eq (by fun_prop : Continuous (fun q : Count → ℝ => ∑ j : Count,q j))
    continuous_const).inter
  exact (isClosed_eq mean_continuous continuous_const).inter
    (isClosed_le l1_continuous continuous_const)

theorem tangentPolytope_compact : IsCompact tangentPolytope := by
  apply (isCompact_closedBall (0 : Count → ℝ) 1).of_isClosed_subset tangentPolytope_closed
  intro q hq
  rw [Metric.mem_closedBall,dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ)≤1)).mpr
  intro j
  simpa only [Real.norm_eq_abs] using (coordinate_le_l1 q j).trans hq.2.2.2

/-- No finite-state evaluation is used in passing from extreme points to the
whole polytope. The extreme-point classification is a separate obligation. -/
theorem quadratic_bound_of_extreme {B : ℝ}
    (hB : ∀ q ∈ tangentPolytope.extremePoints ℝ,quadratic q≤B) :
    ∀ q ∈ tangentPolytope,quadratic q≤B := by
  have hc : Convex ℝ {q : Count → ℝ | quadratic q≤B} := by
    intro q hq r hr a b ha hb hab
    have h := quadratic_convex.2 (Set.mem_univ q) (Set.mem_univ r) ha hb hab
    change quadratic (a•q+b•r)≤B
    have hqa := mul_le_mul_of_nonneg_left hq ha
    have hrb := mul_le_mul_of_nonneg_left hr hb
    simp only [smul_eq_mul] at h
    have he : a*B+b*B=B := by rw [← add_mul,hab,one_mul]
    linarith
  have hs : tangentPolytope.extremePoints ℝ ⊆ {q : Count → ℝ | quadratic q≤B} := hB
  have hh := closure_minimal (convexHull_min hs hc)
    (isClosed_le quadratic_continuous continuous_const)
  rw [closure_convexHull_extremePoints tangentPolytope_compact tangentPolytope_convex] at hh
  exact hh

#print axioms tangentPolytope_compact
#print axioms quadratic_bound_of_extreme
end BecknerOnofri.HighDim.Spin
