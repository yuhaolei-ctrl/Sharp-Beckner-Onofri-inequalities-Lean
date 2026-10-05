import BecknerOnofri.SpinAlgebra
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Function

/-! The manuscript matrix induces an actual seminorm, and its quadratic form
is convex. These facts justify the geometric steps in the curvature proof. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
namespace BecknerOnofri.HighDim.Spin

def featureMap : (Count → ℝ) →ₗ[ℝ] EuclideanSpace ℝ Order where
  toFun q := WithLp.toLp 2 (fun s => Real.sqrt (weight s)*(∑ j : Count,moment s j*q j))
  map_add' q r := by
    ext s
    simp [Finset.mul_sum,Finset.sum_add_distrib,mul_add]
  map_smul' a q := by
    ext s
    change Real.sqrt (weight s)*(∑ j : Count,moment s j*(a*q j)) =
      a*(Real.sqrt (weight s)*(∑ j : Count,moment s j*q j))
    simp_rw [← mul_assoc, mul_comm (moment _ _) a, mul_assoc,← Finset.mul_sum]
    ring

theorem featureMap_norm_sq (q : Count → ℝ) : ‖featureMap q‖^2=quadratic q := by
  rw [EuclideanSpace.real_norm_sq_eq,quadratic_eq_sum]
  apply Finset.sum_congr rfl
  intro s _
  change (Real.sqrt (weight s)*(∑ j : Count,moment s j*q j))^2=_
  rw [mul_pow,Real.sq_sqrt (weight_nonneg s)]

theorem featureMap_norm (q : Count → ℝ) : ‖featureMap q‖=Real.sqrt (quadratic q) := by
  rw [← featureMap_norm_sq,Real.sqrt_sq (norm_nonneg _)]

theorem quadratic_sqrt_triangle (q r : Count → ℝ) :
    Real.sqrt (quadratic (q+r))≤Real.sqrt (quadratic q)+Real.sqrt (quadratic r) := by
  simp only [← featureMap_norm,map_add]
  exact norm_add_le _ _

theorem quadratic_convex : ConvexOn ℝ Set.univ quadratic := by
  refine ⟨convex_univ,?_⟩
  intro q _ r _ a b ha hb hab
  simp only [smul_eq_mul,quadratic_eq_sum,Pi.add_apply,Pi.smul_apply]
  rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro s _
  have he : (∑ j : Count,moment s j*(a*q j+b*r j))=
      a*(∑ j : Count,moment s j*q j)+b*(∑ j : Count,moment s j*r j) := by
    simp only [mul_add,Finset.sum_add_distrib,Finset.mul_sum]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro j _ <;> ring
  rw [he]
  have hs (x y : ℝ) : (a*x+b*y)^2≤a*x^2+b*y^2 := by
    have hb' : b=1-a := by linarith
    have h := mul_nonneg (mul_nonneg ha hb) (sq_nonneg (x-y))
    rw [hb'] at *
    nlinarith
  convert mul_le_mul_of_nonneg_left (hs (∑ j,moment s j*q j) (∑ j,moment s j*r j))
    (weight_nonneg s) using 1 <;> ring

/-- The probability denominator controls the L1 norm; the distinguished
all-minus probability gives the extra 4096 factor required in the paper. -/
theorem curvature_denominator_lower {p q : Count → ℝ}
    (hp : Feasible p) (hpos : ∀ j,0<p j) :
    (∑ j ∈ Finset.univ.erase 0,|q j|)^2+4096*|q 0|^2 ≤
      ∑ j : Count,q j^2/p j := by
  have hsum : (∑ j ∈ Finset.univ.erase 0,p j)≤1 := by
    have h := Finset.sum_erase_add Finset.univ (f:=p) (Finset.mem_univ (0:Count))
    rw [hp.2.1] at h
    linarith [hpos 0]
  have hnon : 0≤∑ j ∈ Finset.univ.erase 0,q j^2/p j :=
    Finset.sum_nonneg (fun j _ => div_nonneg (sq_nonneg _) (hpos j).le)
  have hc := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (Finset.univ.erase (0:Count))
    (r:=fun j => |q j|) (f:=fun j => q j^2/p j) (g:=p)
    (fun j _ => div_nonneg (sq_nonneg _) (hpos j).le) (fun j _ => (hpos j).le)
    (fun j _ => by rw [sq_abs,div_mul_cancel₀ _ (hpos j).ne'])
  have hy : (∑ j ∈ Finset.univ.erase 0,|q j|)^2≤∑ j ∈ Finset.univ.erase 0,q j^2/p j := by
    nlinarith
  have ha : 4096*|q 0|^2≤q 0^2/p 0 := by
    rw [sq_abs,le_div_iff₀ (hpos 0)]
    nlinarith [mul_le_mul_of_nonneg_right hp.2.2 (sq_nonneg (q 0))]
  rw [← Finset.sum_erase_add Finset.univ (f:=fun j => q j^2/p j) (Finset.mem_univ (0:Count))]
  linarith

#print axioms quadratic_convex
#print axioms curvature_denominator_lower
end BecknerOnofri.HighDim.Spin
