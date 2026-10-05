import Legacy.BecknerOnofri.JacobiHeatComparison
import Legacy.BecknerOnofri.JacobiCircleHeat

/-! Strict actual heat-kernel domination follows from the quantified potential gap. -/
noncomputable section
open Set MeasureTheory
open scoped Topology
namespace Legacy.BecknerOnofri.JacobiHeatPositivity
open JacobiHeatBounds

theorem potentialBottom_pos {m : ℕ} (hm : 2≤m) : 0<potentialBottom m := by
  have hh : (2:ℝ)≤m := by exact_mod_cast hm
  unfold potentialBottom
  exact mul_pos (by linarith) (by linarith)

/-- The actual m≥2 Jacobi heat kernel is strictly below the actual Dirichlet heat kernel. -/
theorem heatKernel_lt_dirichlet {m : ℕ} (hm : 2≤m) {t x y : ℝ}
    (ht : 0<t) (hx : x∈Ioo 0 Real.pi) (hy : y∈Ioo 0 Real.pi) :
    heatKernel m t x y<heatKernel 1 t x y := by
  have hm0 : 0<m := by omega
  have hle := heatKernel_le_decayed_dirichlet hm0 ht ⟨hx.1.le,hx.2.le⟩ hy
  have hdec : Real.exp (-potentialBottom m*t)<1 := by
    apply Real.exp_lt_one_iff.mpr
    exact mul_neg_of_neg_of_pos (neg_neg_of_pos (potentialBottom_pos hm)) ht
  exact hle.trans_lt (mul_lt_of_lt_one_left (heatKernel_one_pos ht hx hy) hdec)

/-- All active actual heat kernels are dominated by the m=1 kernel. -/
theorem heatKernel_le_dirichlet {m : ℕ} (hm : 0<m) {t x y : ℝ}
    (ht : 0<t) (hx : x∈Ioo 0 Real.pi) (hy : y∈Ioo 0 Real.pi) :
    heatKernel m t x y≤heatKernel 1 t x y := by
  have hdec : Real.exp (-potentialBottom m*t)≤1 := by
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (potentialBottom_nonnegative hm)) ht.le
  exact (heatKernel_le_decayed_dirichlet hm ht ⟨hx.1.le,hx.2.le⟩ hy).trans
    (mul_le_of_le_one_left (heatKernel_one_pos ht hx hy).le hdec)

/-- The actual active kernel is strictly below the actual inactive Neumann kernel. -/
theorem heatKernel_lt_neumann {m : ℕ} (hm : 0<m) {t x y : ℝ}
    (ht : 0<t) (hx : x∈Ioo 0 Real.pi) (hy : y∈Ioo 0 Real.pi) :
    heatKernel m t x y<heatKernel 0 t x y :=
  (heatKernel_le_dirichlet hm ht hx hy).trans_lt (heatKernel_one_lt_zero ht x y)

/-- The inactive m=0 case and all active cases have nonnegative actual kernels. -/
theorem heatKernel_nonnegative_all (m : ℕ) {t x y : ℝ}
    (ht : 0<t) (hx : x∈Ioo 0 Real.pi) (hy : y∈Ioo 0 Real.pi) :
    0≤heatKernel m t x y := by
  by_cases hm : m=0
  · subst m
    exact (heatKernel_zero_pos ht x y).le
  · exact heatKernel_nonnegative (Nat.pos_of_ne_zero hm) ht ⟨hx.1.le,hx.2.le⟩ ⟨hy.1.le,hy.2.le⟩

#print axioms heatKernel_lt_dirichlet
#print axioms heatKernel_lt_neumann
#print axioms heatKernel_nonnegative_all
end Legacy.BecknerOnofri.JacobiHeatPositivity
