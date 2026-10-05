module

public import BecknerOnofri.GinibreNormMonotonicity
public import BecknerOnofri.GibbsPerturbation
public import BecknerOnofri.GridGibbsComparison

@[expose] public section

/-! Exact L² norm control under a bounded omitted potential. The denominator
monotonicity is kept explicit here and discharged by nonnegative cosine
coefficients in the iteration theorem. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped Topology BigOperators
namespace BecknerOnofri.HighDim.GibbsPerturbation
open ContinuousGibbs GinibreCovariance GridGibbsComparison

theorem gibbsL2Norm_ratio {d : ℕ} (u : Space d) :
    gibbsL2Norm u=Real.sqrt (partition ((2:ℝ) • u))/partition u := by
  rw [gibbsL2Norm_partition,Real.sqrt_div (partition_pos _).le,
    Real.sqrt_sq (partition_pos u).le]

theorem gibbsL2Norm_perturbation {d : ℕ} (u w : Space d) (δ : ℝ)
    (hw : ∀ x, w x≤δ) (hZ : partition u≤partition (u+w)) :
    gibbsL2Norm (u+w)≤Real.exp δ*Real.sqrt (partition ((2:ℝ) • u))/partition u := by
  have hh := partition_perturbation_upper ((2:ℝ) • u) ((2:ℝ) • w) (2*δ)
    (fun x => by change 2*w x≤2*δ; linarith [hw x])
  rw [← smul_add] at hh
  have he : Real.exp (2*δ)=(Real.exp δ)^2 := by
    rw [show 2*δ=δ+δ by ring,Real.exp_add,pow_two]
  have hn := Real.sqrt_le_sqrt hh
  rw [he,Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (Real.exp_pos δ).le] at hn
  rw [gibbsL2Norm_ratio]
  exact (div_le_div_of_nonneg_right hn (partition_pos (u+w)).le).trans
    (div_le_div_of_nonneg_left (mul_nonneg (Real.exp_pos δ).le (Real.sqrt_nonneg _))
      (partition_pos u) hZ)

/-- The numerical denominator lower bound and exact positive grid upper bound
produce the norm update used in the finite certificate. -/
theorem gibbsL2Norm_grid_perturbation {d N : ℕ} [NeZero N] {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (k : ι → Frequency d) (ha : ∀ i,0≤a i)
    (w : Space d) (δ L : ℝ) (hw : ∀ x,w x≤δ)
    (hZ : partition (cosinePotential a k)≤partition (cosinePotential a k+w))
    (hL : 0<L) (hLZ : L≤partition (cosinePotential a k)) :
    gibbsL2Norm (cosinePotential a k+w)≤
      Real.exp δ*Real.sqrt (gridMean (N := N) (exponential ((2:ℝ) • cosinePotential a k)))/L := by
  let q := cosinePotential a k
  have hh := gibbsL2Norm_perturbation q w δ hw hZ
  have hg : partition ((2:ℝ) • q)≤gridMean (N := N) (exponential ((2:ℝ) • q)) := by
    change partition ((2:ℝ) • cosinePotential a k)≤_
    rw [cosinePotential_smul]
    exact partition_le_grid (N := N) (fun i => 2*a i) k (fun i => mul_nonneg (by norm_num) (ha i))
  have hn := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hg) (Real.exp_pos δ).le
  exact hh.trans ((div_le_div_of_nonneg_right hn (partition_pos q).le).trans
    (div_le_div_of_nonneg_left (mul_nonneg (Real.exp_pos δ).le (Real.sqrt_nonneg _)) hL hLZ))

#print axioms gibbsL2Norm_perturbation
#print axioms gibbsL2Norm_grid_perturbation
end BecknerOnofri.HighDim.GibbsPerturbation
