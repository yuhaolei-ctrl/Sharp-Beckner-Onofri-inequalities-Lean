module

public import BecknerOnofri.V2.Reaudit.HeatKernel.RadialExpansion
public import BecknerOnofri.V2.Reaudit.HeatKernel.AbsMonotone
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt

@[expose] public section

/-! # S014: the interior expansion by radial substitution

Printed proof of `lem:positive-bernstein`, first half: for `y ∈ [0,1)^d` choose `R > 1` with
`R y ∈ [0,1)^d`, put `g_y(t) = f(t y)`; `g_y` is absolutely monotone on `[0,R)`
(eq. `radial-absolute-monotonicity`), the one-variable theorem (`absMonotone_hasSum_taylor`)
at `t = 1` gives `f(y) = ∑_n g_y^{(n)}(0)/n!`, and the multinomial expansion
(`hasSum_radial_jet_degree`) regroups this as `∑_α ∂^α f(0)/α! y^α`.
-/

noncomputable section
open Set Finset Filter Topology
open scoped ContDiff
namespace BecknerOnofri.V2.Reaudit.HeatKernel
open Legacy.BecknerOnofri.FiniteDifferences

variable {d : ℕ}

/-- The hypothesis of the manuscript: `∂^α f ≥ 0` on the closed cube for every multi-index `α`
(with the repository's fixed ordering `directions α` of the directions of `α`). -/
def NonnegMultiIndexPartials (f : Space d → ℝ) : Prop :=
  ∀ (a : Index d) (x : Space d), x ∈ closedCube d → 0 ≤ mixedPartial (directions a) f x

theorem nonnegJet_of_multiindex {f : Space d → ℝ} (hf : ContDiffOn ℝ ∞ f (closedCube d))
    (hpos : NonnegMultiIndexPartials f) : NonnegJet f := by
  refine ⟨hf, fun L x hx => ?_⟩
  rw [mixedPartial_eq_directions L hf hx]
  exact hpos _ x hx

theorem taylorCoeff_nonneg {f : Space d → ℝ} (hpos : NonnegMultiIndexPartials f) (a : Index d) :
    0 ≤ taylorCoeff f a :=
  div_nonneg (hpos a 0 (zero_mem_closedCube d))
    (Finset.prod_nonneg (fun _ _ => Nat.cast_nonneg _))

theorem taylorTerm_nonneg {f : Space d → ℝ} (hpos : NonnegMultiIndexPartials f) {y : Space d}
    (hy : ∀ i, 0 ≤ y i) (a : Index d) : 0 ≤ taylorTerm y f a :=
  mul_nonneg (taylorCoeff_nonneg hpos a) (Finset.prod_nonneg (fun i _ => pow_nonneg (hy i) _))

/-- There is `R > 1` with `R y` still strictly inside the cube. -/
theorem exists_scale_gt_one {y : Space d} (hy1 : ∀ i, y i < 1) :
    ∃ R : ℝ, 1 < R ∧ ∀ i, R * y i < 1 := by
  have h : ∀ᶠ R in 𝓝 (1 : ℝ), ∀ i, R * y i < 1 := by
    rw [Filter.eventually_all]
    intro i
    have hc : ContinuousAt (fun R : ℝ => R * y i) 1 := (continuous_id.mul continuous_const).continuousAt
    exact hc.eventually_lt continuousAt_const (by simpa using hy1 i)
  have h2 : ∀ᶠ R in 𝓝[>] (1 : ℝ), ∀ i, R * y i < 1 := nhdsWithin_le_nhds h
  exact (h2.and self_mem_nhdsWithin).exists.imp (fun R hR => ⟨hR.2, hR.1⟩)

/-- Interior expansion: the Taylor series at `0` represents `f` at every `y ∈ [0,1)^d`. -/
theorem interior_hasSum {f : Space d → ℝ} (hf : ContDiffOn ℝ ∞ f (closedCube d))
    (hpos : NonnegMultiIndexPartials f) {y : Space d} (hy0 : ∀ i, 0 ≤ y i)
    (hy1 : ∀ i, y i < 1) : HasSum (fun a : Index d => taylorTerm y f a) (f y) := by
  classical
  obtain ⟨R, hR1, hRy⟩ := exists_scale_gt_one hy1
  have hR0 : 0 < R := zero_lt_one.trans hR1
  have hmaps : ∀ t ∈ Ico (0 : ℝ) R, t • y ∈ closedCube d := by
    intro t ht
    refine ⟨fun i => ?_, fun i => ?_⟩
    · exact mul_nonneg ht.1 (hy0 i)
    · simp only [Pi.smul_apply, smul_eq_mul, Pi.one_apply]
      have : t * y i ≤ R * y i := mul_le_mul_of_nonneg_right ht.2.le (hy0 i)
      linarith [hRy i]
  have hJ := nonnegJet_of_multiindex hf hpos
  -- the radial function is absolutely monotone on [0,R)
  have hgcd : ContDiffOn ℝ ∞ (fun s : ℝ => f (s • y)) (Ico 0 R) := by
    refine hf.comp (by fun_prop : ContDiff ℝ ∞ (fun s : ℝ => s • y)).contDiffOn hmaps
  have habs : AbsolutelyMonotoneOn (fun s : ℝ => f (s • y)) (Ico 0 R) := by
    refine (AbsolutelyMonotoneOn.iff_iteratedDerivWithin_nonneg (uniqueDiffOn_Ico 0 R)).mpr
      ⟨hgcd, fun n t ht => ?_⟩
    rw [iteratedDerivWithin_ray hf y hmaps n t ht]
    exact (hJ.radialD_iterate hy0 n).2 [] _ (hmaps t ht)
  have h1 : (1 : ℝ) ∈ Ico (0 : ℝ) R := ⟨zero_le_one, hR1⟩
  have hsum := absMonotone_hasSum_taylor habs h1
  have hjet : ∀ n : ℕ, iteratedDerivWithin n (fun s : ℝ => f (s • y)) (Ico 0 R) 0 =
      ((radialD y)^[n] f) 0 := by
    intro n
    rw [iteratedDerivWithin_ray hf y hmaps n 0 ⟨le_rfl, hR0⟩]
    simp
  simp only [hjet, one_pow, mul_one, one_smul] at hsum
  -- fibrewise sums
  set T : Index d → ℝ := fun a => taylorTerm y f a with hT
  have hTnn : ∀ a, 0 ≤ T a := fun a => taylorTerm_nonneg hpos hy0 a
  set e : (Σ n : ℕ, {a : Index d // deg a = n}) ≃ Index d := Equiv.sigmaFiberEquiv deg with he
  have hfib : ∀ n : ℕ, HasSum (fun c : {a : Index d // deg a = n} => T c.1)
      (((radialD y)^[n] f) 0 / (n.factorial : ℝ)) := by
    intro n
    have h := hasSum_radial_jet_degree hf y n
    refine (hasSum_subtype_iff_indicator (f := T) (s := {a : Index d | deg a = n})).mpr ?_
    convert h using 1
    ext a
    simp [Set.indicator, T]
  set F : (Σ n : ℕ, {a : Index d // deg a = n}) → ℝ := fun p => T p.2.1 with hF
  have hFnn : ∀ p, 0 ≤ F p := fun p => hTnn _
  have hFsum : Summable F := by
    rw [summable_sigma_of_nonneg hFnn]
    refine ⟨fun n => (hfib n).summable, ?_⟩
    have : (fun n : ℕ => ∑' c : {a : Index d // deg a = n}, F ⟨n, c⟩) =
        fun n : ℕ => ((radialD y)^[n] f) 0 / (n.factorial : ℝ) := by
      funext n
      exact (hfib n).tsum_eq
    rw [this]
    exact hsum.summable
  have hTsum : Summable T := by
    have : F = T ∘ e := by
      funext p
      rfl
    rw [this] at hFsum
    exact (e.summable_iff).mp hFsum
  have hTHas : HasSum T (∑' a, T a) := hTsum.hasSum
  have hFHas : HasSum F (∑' a, T a) := by
    have : F = T ∘ e := by
      funext p
      rfl
    rw [this]
    exact (e.hasSum_iff).mpr hTHas
  have hseq : HasSum (fun n : ℕ => ((radialD y)^[n] f) 0 / (n.factorial : ℝ)) (∑' a, T a) :=
    hFHas.sigma (fun n => hfib n)
  have := hseq.unique hsum
  rw [this] at hTHas
  exact hTHas

end BecknerOnofri.V2.Reaudit.HeatKernel
