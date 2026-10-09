module

public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Normed.Group.FunctionSeries

@[expose] public section

/-! # Smoothness of a series with locally uniform summable derivative bounds

Weierstrass M-test for all derivatives, localized by a smooth cut-off: this is the mechanism
behind the first paragraph of Lemma 4.3 (`lem:section4-periodization-entropy-identity`):
"the series ... together with all of its derivatives converges locally uniformly; in particular
`ρ_*` is smooth".

`tsum_contDiff_of_local_bounds` : if each term `f i` is `C^∞` and, for every radius `R` and every
derivative order `k`, `‖D^k (f i) y‖ ≤ v i` on `‖y‖ ≤ R` with `v` summable, then the sum is `C^∞` and
its `k`-th derivative is the sum of the `k`-th derivatives (`HasSum`, locally uniformly). -/

noncomputable section
open scoped ContDiff Topology
open Filter Metric

namespace BecknerOnofri.V2.Eleven

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem tsum_contDiff_of_local_bounds {α : Type*} {f : α → E → F}
    (hf : ∀ i, ContDiff ℝ ∞ (f i))
    (hloc : ∀ R : ℝ, 0 ≤ R → ∀ k : ℕ, ∃ v : α → ℝ, Summable v ∧
      ∀ i (y : E), ‖y‖ ≤ R → ‖iteratedFDeriv ℝ k (f i) y‖ ≤ v i) :
    ContDiff ℝ ∞ (fun y => ∑' i, f i y) ∧
    ∀ (k : ℕ) (y : E), iteratedFDeriv ℝ k (fun z => ∑' i, f i z) y =
      ∑' i, iteratedFDeriv ℝ k (f i) y := by
  have key : ∀ y₀ : E, ContDiffAt ℝ ∞ (fun y => ∑' i, f i y) y₀ ∧
      ∀ k : ℕ, iteratedFDeriv ℝ k (fun z => ∑' i, f i z) y₀ =
        ∑' i, iteratedFDeriv ℝ k (f i) y₀ := by
    intro y₀
    set R : ℝ := ‖y₀‖ + 1 with hR
    have hR0 : 0 < R := by positivity
    let χ : ContDiffBump (0 : E) := ⟨R, R + 1, hR0, by linarith⟩
    have hχc : HasCompactSupport χ := χ.hasCompactSupport
    have hχs : ContDiff ℝ ∞ χ := χ.contDiff
    set Fi : α → E → F := fun i y => χ y • f i y with hFi
    have hFi0 : ∀ i, ContDiff ℝ ∞ (Fi i) := fun i => hχs.smul (hf i)
    -- derivative bounds for the cut-off terms
    have hbound : ∀ k : ℕ, ∃ w : α → ℝ, Summable w ∧
        ∀ i (y : E), ‖iteratedFDeriv ℝ k (Fi i) y‖ ≤ w i := by
      intro k
      obtain ⟨B, hB0, hB⟩ := hχc.exists_bound_iteratedFDeriv hχs k
      have hV : ∀ k' : ℕ, ∃ v : α → ℝ, Summable v ∧
          ∀ i (y : E), ‖y‖ ≤ R + 1 → ‖iteratedFDeriv ℝ k' (f i) y‖ ≤ v i :=
        fun k' => hloc (R + 1) (by positivity) k'
      choose V hVs hVb using hV
      have hV0 : ∀ k' i, 0 ≤ V k' i := fun k' i =>
        (norm_nonneg _).trans (hVb k' i 0 (by simp; positivity))
      refine ⟨fun i => ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * B * V (k - j) i,
        summable_sum fun j _ => ((hVs (k - j)).mul_left _), fun i y => ?_⟩
      refine (norm_iteratedFDeriv_smul_le hχs (hf i) y (n := k) (by exact_mod_cast le_top)).trans ?_
      refine Finset.sum_le_sum fun j hj => ?_
      have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      have hch : (0 : ℝ) ≤ (k.choose j : ℝ) := Nat.cast_nonneg _
      by_cases hy : ‖y‖ ≤ R + 1
      · have h1 := hB j hjk y
        have h2 := hVb (k - j) i y hy
        exact mul_le_mul (mul_le_mul_of_nonneg_left h1 hch) h2 (norm_nonneg _)
          (mul_nonneg hch hB0)
      · have hz : iteratedFDeriv ℝ j (⇑χ) y = 0 := by
          by_contra hne
          have hmem : y ∈ tsupport χ := by
            have : y ∈ Function.support (iteratedFDeriv ℝ j (⇑χ)) := hne
            exact (support_iteratedFDeriv_subset (𝕜 := ℝ) (n := j)) this
          rw [χ.tsupport_eq, mem_closedBall, dist_zero_right] at hmem
          exact hy hmem
        rw [hz]
        simp only [norm_zero, mul_zero, zero_mul]
        exact mul_nonneg (mul_nonneg hch hB0) (hV0 _ _)
    choose w hws hwb using hbound
    have hdiff := contDiff_tsum hFi0 (fun k _ => hws k) (fun k i x _ => hwb k i x)
    have hiter := fun k : ℕ => iteratedFDeriv_tsum hFi0 (fun k _ => hws k)
      (fun k i x _ => hwb k i x) (k := k) (by exact_mod_cast le_top)
    -- the cut-off is `1` near `y₀`
    have hev1 : ∀ᶠ y in 𝓝 y₀, χ y = 1 := by
      have := χ.eventuallyEq_one_of_mem_ball (x := y₀) (by simp [χ, hR])
      exact this.mono fun y hy => by simpa using hy
    have hevi : ∀ i, Fi i =ᶠ[𝓝 y₀] f i := fun i =>
      hev1.mono fun y hy => by simp [hFi, hy]
    have hevs : (fun y => ∑' i, Fi i y) =ᶠ[𝓝 y₀] fun y => ∑' i, f i y := by
      filter_upwards [hev1] with y hy
      exact tsum_congr fun i => by simp [hFi, hy]
    refine ⟨?_, fun k => ?_⟩
    · exact (hdiff.contDiffAt (x := y₀)).congr_of_eventuallyEq hevs.symm
    · have h1 : iteratedFDeriv ℝ k (fun z => ∑' i, f i z) y₀ =
          iteratedFDeriv ℝ k (fun z => ∑' i, Fi i z) y₀ :=
        ((hevs.iteratedFDeriv ℝ k).self_of_nhds).symm
      rw [h1, hiter k]
      exact tsum_congr fun i => ((hevi i).iteratedFDeriv ℝ k).self_of_nhds
  exact ⟨contDiff_iff_contDiffAt.2 fun y => (key y).1, fun k y => (key y).2 k⟩

/-- Locally uniform convergence of every differentiated series, and the termwise `HasSum`. -/
theorem tsum_iteratedFDeriv_hasSum {α : Type*} {f : α → E → F}
    (hf : ∀ i, ContDiff ℝ ∞ (f i))
    (hloc : ∀ R : ℝ, 0 ≤ R → ∀ k : ℕ, ∃ v : α → ℝ, Summable v ∧
      ∀ i (y : E), ‖y‖ ≤ R → ‖iteratedFDeriv ℝ k (f i) y‖ ≤ v i)
    (k : ℕ) (y : E) :
    HasSum (fun i => iteratedFDeriv ℝ k (f i) y)
      (iteratedFDeriv ℝ k (fun z => ∑' i, f i z) y) := by
  obtain ⟨-, h⟩ := tsum_contDiff_of_local_bounds hf hloc
  rw [h k y]
  obtain ⟨v, hv, hb⟩ := hloc (‖y‖) (norm_nonneg _) k
  exact (Summable.of_norm_bounded hv fun i => hb i y le_rfl).hasSum

theorem tsum_iteratedFDeriv_tendstoUniformlyOn {α : Type*} {f : α → E → F}
    (hf : ∀ i, ContDiff ℝ ∞ (f i))
    (hloc : ∀ R : ℝ, 0 ≤ R → ∀ k : ℕ, ∃ v : α → ℝ, Summable v ∧
      ∀ i (y : E), ‖y‖ ≤ R → ‖iteratedFDeriv ℝ k (f i) y‖ ≤ v i)
    (k : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    TendstoUniformlyOn
      (fun s : Finset α => fun y => ∑ i ∈ s, iteratedFDeriv ℝ k (f i) y)
      (iteratedFDeriv ℝ k (fun z => ∑' i, f i z)) atTop (closedBall (0 : E) R) := by
  obtain ⟨-, h⟩ := tsum_contDiff_of_local_bounds hf hloc
  obtain ⟨v, hv, hb⟩ := hloc R hR k
  have := tendstoUniformlyOn_tsum (f := fun i y => iteratedFDeriv ℝ k (f i) y) (s := closedBall (0 : E) R) hv
    (fun i y hy => hb i y (by simpa using hy))
  have e : iteratedFDeriv ℝ k (fun z => ∑' i, f i z) = fun y => ∑' i, iteratedFDeriv ℝ k (f i) y :=
    funext fun y => h k y
  rw [e]
  exact this

end BecknerOnofri.V2.Eleven
