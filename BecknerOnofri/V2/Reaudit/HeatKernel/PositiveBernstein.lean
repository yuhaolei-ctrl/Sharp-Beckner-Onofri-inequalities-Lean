module

public import BecknerOnofri.V2.Reaudit.HeatKernel.RadialTaylor
public import BecknerOnofri.ClosedCubeTaylorDefinitions
public import Mathlib.Analysis.Normed.Group.FunctionSeries

@[expose] public section

/-! # S014 (`lem:positive-bernstein`) by the printed route

Printed route: radial substitution `g_y(t) = f(t y)` for `y ∈ [0,1)^d`; the one-variable
theorem on absolutely monotone functions (proved in `AbsMonotone.lean`; Mathlib has only the
definition `AbsolutelyMonotoneOn`) at `t = 1`; nonnegative coefficients, the closed-boundary limit
`∑_α c_α = lim_{r↑1} f(r,…,r) = f(1,…,1)`, the Weierstrass M-test, and continuity to extend to the
boundary of the cube.

The conclusion `positive_bernstein` has the same type as the (older) wrapper
`BecknerOnofri.HighDim.ClosedCubeTaylor.closed_cube_expansion`, whose proof goes through tensor
Bernstein polynomials; here none of that is used.  The hypothesis can be given either as the
manuscript's `∂^α f ≥ 0` for every multi-index (`NonnegMultiIndexPartials`) or as the older
`nonnegativePartials` (all direction lists); on the cube they are equivalent
(`nonnegativePartials_iff`).
-/

noncomputable section
open Set Finset Filter Topology
open scoped ContDiff unitInterval
namespace BecknerOnofri.V2.Reaudit.HeatKernel
open Legacy.BecknerOnofri.FiniteDifferences
open BecknerOnofri.HighDim.ClosedCubeTaylor (Cube coefficient monomial nonnegativePartials)

variable {d : ℕ}

theorem nonnegativePartials_iff {f : Space d → ℝ} (hf : ContDiffOn ℝ ∞ f (closedCube d)) :
    nonnegativePartials f ↔ NonnegMultiIndexPartials f := by
  constructor
  · intro h a x hx; exact h _ x hx
  · intro h L x hx
    rw [mixedPartial_eq_directions L hf hx]
    exact h _ x hx

theorem coefficient_eq_taylorCoeff (f : Space d → ℝ) (a : Index d) :
    coefficient f a = taylorCoeff f a := rfl

theorem monomial_eq_prod (a : Index d) (y : Cube d) :
    monomial a y = ∏ i, ((y i : ℝ)) ^ a i := rfl

theorem cubeToSpace_mem (y : Cube d) : (fun i => (y i : ℝ)) ∈ closedCube d :=
  ⟨fun i => (y i).2.1, fun i => (y i).2.2⟩

/-- Along the ray `r ↦ r y` (`r ↑ 1`), a function continuous on the cube tends to its value. -/
theorem tendsto_ray {G : Space d → ℝ} (hG : ContinuousOn G (closedCube d)) {y : Space d}
    (hy : y ∈ closedCube d) :
    Tendsto (fun r : ℝ => G (r • y)) (𝓝[<] (1 : ℝ)) (𝓝 (G y)) := by
  have hmem : ∀ᶠ r in 𝓝[<] (1 : ℝ), r • y ∈ closedCube d := by
    filter_upwards [Ioo_mem_nhdsLT (zero_lt_one' ℝ)] with r hr
    refine ⟨fun i => ?_, fun i => ?_⟩
    · exact mul_nonneg hr.1.le (hy.1 i)
    · simp only [Pi.smul_apply, smul_eq_mul, Pi.one_apply]
      have h2 : y i ≤ 1 := hy.2 i
      nlinarith [hy.1 i, hr.1, hr.2]
  have h1 : Tendsto (fun r : ℝ => r • y) (𝓝[<] (1 : ℝ)) (𝓝 y) := by
    have : Tendsto (fun r : ℝ => r • y) (𝓝 (1 : ℝ)) (𝓝 ((1 : ℝ) • y)) :=
      (continuous_id.smul continuous_const).tendsto 1
    simpa using this.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto (fun r : ℝ => r • y) (𝓝[<] (1 : ℝ)) (𝓝[closedCube d] y) :=
    tendsto_nhdsWithin_iff.mpr ⟨h1, hmem⟩
  exact (hG y hy).tendsto.comp h2

/-- **S014** (`lem:positive-bernstein`), proved by radial absolute monotonicity.

Hypotheses: `f ∈ C^∞([0,1]^d)` and `∂^α f ≥ 0` on the cube for every multi-index `α`.
Conclusion: the coefficients `c_α = ∂^α f(0)/α!` are nonnegative, `∑ c_α = f(1,…,1)`, the series
`∑ c_α y^α` converges to `f(y)` at every `y ∈ [0,1]^d`, and the convergence is uniform. -/
theorem positive_bernstein_multiindex {f : Space d → ℝ} (hf : ContDiffOn ℝ ∞ f (closedCube d))
    (hpos : NonnegMultiIndexPartials f) :
    (∀ a, 0 ≤ coefficient f a) ∧ HasSum (coefficient f) (f 1) ∧
    (∀ y : Cube d, HasSum (fun a => coefficient f a * monomial a y)
      (f (fun i => (y i : ℝ)))) ∧
    TendstoUniformly (fun s : Finset (Index d) => fun y : Cube d =>
      ∑ a ∈ s, coefficient f a * monomial a y)
      (fun y => f (fun i => (y i : ℝ))) atTop := by
  classical
  have hcnn : ∀ a, 0 ≤ taylorCoeff f a := fun a => taylorCoeff_nonneg hpos a
  have hfc : ContinuousOn f (closedCube d) := hf.continuousOn
  have h1mem : (1 : Space d) ∈ closedCube d := ⟨fun i => zero_le_one, fun i => le_rfl⟩
  -- Step 1: finite partial sums of the coefficients are bounded by `f 1`.
  have hbound : ∀ F : Finset (Index d), ∑ a ∈ F, taylorCoeff f a ≤ f 1 := by
    intro F
    have hlim1 : Tendsto (fun r : ℝ => ∑ a ∈ F, taylorCoeff f a * ∏ i : Fin d, r ^ a i)
        (𝓝[<] (1 : ℝ)) (𝓝 (∑ a ∈ F, taylorCoeff f a)) := by
      have : Tendsto (fun r : ℝ => ∑ a ∈ F, taylorCoeff f a * ∏ i : Fin d, r ^ a i) (𝓝 (1 : ℝ))
          (𝓝 (∑ a ∈ F, taylorCoeff f a * ∏ i : Fin d, (1 : ℝ) ^ a i)) := by
        apply Continuous.tendsto
        fun_prop
      simpa using this.mono_left nhdsWithin_le_nhds
    have hlim2 : Tendsto (fun r : ℝ => f (r • (1 : Space d))) (𝓝[<] (1 : ℝ)) (𝓝 (f 1)) :=
      tendsto_ray hfc h1mem
    refine le_of_tendsto_of_tendsto hlim1 hlim2 ?_
    filter_upwards [Ioo_mem_nhdsLT (zero_lt_one' ℝ)] with r hr
    have hy0 : ∀ i : Fin d, 0 ≤ (r • (1 : Space d)) i := fun i => by simpa using hr.1.le
    have hy1 : ∀ i : Fin d, (r • (1 : Space d)) i < 1 := fun i => by simpa using hr.2
    have hs := interior_hasSum hf hpos hy0 hy1
    have := sum_le_hasSum F (fun a _ => taylorTerm_nonneg hpos hy0 a) hs
    simpa [taylorTerm] using this
  have hsumm : Summable (taylorCoeff f) :=
    summable_of_sum_le (fun a => hcnn a) (fun F => hbound F)
  -- Step 2: the series is continuous on the cube and agrees with `f` on its interior.
  set S : Space d → ℝ := fun y => ∑' a, taylorCoeff f a * ∏ i, y i ^ a i with hS
  have hnorm : ∀ (a : Index d) (y : Space d), y ∈ closedCube d →
      ‖taylorCoeff f a * ∏ i, y i ^ a i‖ ≤ taylorCoeff f a := by
    intro a y hy
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hcnn a)]
    have : |∏ i, y i ^ a i| ≤ 1 := by
      rw [Finset.abs_prod]
      apply Finset.prod_le_one₀ (fun i _ => abs_nonneg _)
      intro i _
      rw [abs_pow]
      exact pow_le_one₀ (abs_nonneg _) (by rw [abs_of_nonneg (hy.1 i)]; exact hy.2 i)
    nlinarith [hcnn a]
  have hSc : ContinuousOn S (closedCube d) := by
    apply continuousOn_tsum (u := taylorCoeff f) _ hsumm hnorm
    intro a
    fun_prop
  have hSeq : ∀ y ∈ closedCube d, S y = f y := by
    intro y hy
    have h1 : Tendsto (fun r : ℝ => S (r • y)) (𝓝[<] (1 : ℝ)) (𝓝 (S y)) := tendsto_ray hSc hy
    have h2 : Tendsto (fun r : ℝ => f (r • y)) (𝓝[<] (1 : ℝ)) (𝓝 (f y)) := tendsto_ray hfc hy
    refine tendsto_nhds_unique_of_eventuallyEq h1 h2 ?_
    filter_upwards [Ioo_mem_nhdsLT (zero_lt_one' ℝ)] with r hr
    have hy0 : ∀ i : Fin d, 0 ≤ (r • y) i := fun i => mul_nonneg hr.1.le (hy.1 i)
    have hy1 : ∀ i : Fin d, (r • y) i < 1 := fun i => by
      simp only [Pi.smul_apply, smul_eq_mul]
      have h2 : y i ≤ 1 := hy.2 i
      nlinarith [hy.1 i, hr.1, hr.2]
    exact (interior_hasSum hf hpos hy0 hy1).tsum_eq
  -- Step 3: assemble.
  have hS1 : f 1 = ∑' a, taylorCoeff f a := by
    have := hSeq 1 h1mem
    simp only [hS] at this
    simpa using this.symm
  refine ⟨hcnn, ?_, ?_, ?_⟩
  · rw [hS1]
    exact hsumm.hasSum
  · intro y
    have hy := cubeToSpace_mem y
    have hsy : Summable (fun a => taylorCoeff f a * ∏ i, ((y i : ℝ)) ^ a i) :=
      Summable.of_norm_bounded hsumm (fun a => hnorm a _ hy)
    have := hsy.hasSum
    have hv : (∑' a, taylorCoeff f a * ∏ i, ((y i : ℝ)) ^ a i) = f (fun i => (y i : ℝ)) :=
      hSeq _ hy
    rw [hv] at this
    exact this
  · have hu := tendstoUniformly_tsum (f := fun (a : Index d) (y : Cube d) =>
        taylorCoeff f a * ∏ i, ((y i : ℝ)) ^ a i) hsumm
        (fun a y => hnorm a _ (cubeToSpace_mem y))
    have hfun : (fun y : Cube d => ∑' a, taylorCoeff f a * ∏ i, ((y i : ℝ)) ^ a i) =
        fun y : Cube d => f (fun i => (y i : ℝ)) := by
      funext y
      exact hSeq _ (cubeToSpace_mem y)
    rw [hfun] at hu
    exact hu

/-- **S014** with the hypothesis in the form of the older wrapper (`nonnegativePartials`: all
direction lists).  The conclusion is the same as that of
`BecknerOnofri.HighDim.ClosedCubeTaylor.closed_cube_expansion`. -/
theorem positive_bernstein {f : Space d → ℝ} (hf : ContDiffOn ℝ ∞ f (closedCube d))
    (hpos : nonnegativePartials f) :
    (∀ a, 0 ≤ coefficient f a) ∧ HasSum (coefficient f) (f 1) ∧
    (∀ y : Cube d, HasSum (fun a => coefficient f a * monomial a y)
      (f (fun i => (y i : ℝ)))) ∧
    TendstoUniformly (fun s : Finset (Index d) => fun y : Cube d =>
      ∑ a ∈ s, coefficient f a * monomial a y)
      (fun y => f (fun i => (y i : ℝ))) atTop :=
  positive_bernstein_multiindex hf ((nonnegativePartials_iff hf).mp hpos)

end BecknerOnofri.V2.Reaudit.HeatKernel
