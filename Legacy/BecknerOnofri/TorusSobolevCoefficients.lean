import Legacy.BecknerOnofri.SobolevLatticeBoxes
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Topology.Sequences
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Finite Fourier projections and compactness from a uniform square-summable tail. -/

noncomputable section
open Set Filter MeasureTheory Legacy.TorusEndpoint
open scoped BigOperators Topology ENNReal

namespace Legacy.BecknerOnofri.TorusSobolev

abbrev Coefficients (ι : Type*) := lp (fun _ : ι => ℂ) 2

def finiteProjection {ι : Type*} (s : Finset ι) (u : Coefficients ι) : Coefficients ι := by
  classical
  exact ∑ k ∈ s, lp.single 2 k (u k)

theorem norm_sq_eq_tsum {ι : Type*} (u : Coefficients ι) :
    ‖u‖ ^ 2 = ∑' k, ‖u k‖ ^ 2 := by
  simpa using lp.norm_rpow_eq_tsum (p := 2) (by norm_num) u

theorem summable_sq {ι : Type*} (u : Coefficients ι) : Summable (fun k => ‖u k‖ ^ 2) := by
  simpa using (lp.hasSum_norm (p := 2) (by norm_num) u).summable

theorem finiteProjection_apply {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (u : Coefficients ι) (k : ι) :
    finiteProjection s u k = if k ∈ s then u k else 0 := by
  classical
  simp only [finiteProjection, lp.coeFn_sum, lp.coeFn_single]
  convert! (Finset.sum_apply k s (fun j => Pi.single j (u j))).trans
    (Finset.sum_pi_single k (fun j => u j) s) using 1
  apply congrArg (fun f : ι → ℂ => f k)
  apply Finset.sum_congr rfl
  intro j hj
  funext i
  by_cases h : i = j
  · subst i
    simp
  · simp [Pi.single, Function.update, h]

theorem finiteProjection_compact_image {ι : Type*} (s : Finset ι) (C : ℝ) :
    ∃ K : Set (Coefficients ι), IsCompact K ∧
      ∀ u : Coefficients ι, ‖u‖ ≤ C → finiteProjection s u ∈ K := by
  classical
  let F : (s → ℂ) → Coefficients ι := fun z => ∑ k : s, lp.single 2 k.val (z k)
  have hF : Continuous F := by
    apply continuous_finsetSum
    intro k hk
    exact (lp.isometry_single (p := 2) k.val).continuous.comp (continuous_apply k)
  refine ⟨F '' Metric.closedBall 0 C, (isCompact_closedBall _ _).image hF, ?_⟩
  intro u hu
  refine ⟨(fun k : s => u k.val), ?_, ?_⟩
  · rw [Metric.mem_closedBall, dist_zero_right]
    apply (pi_norm_le_iff_of_nonneg ((norm_nonneg u).trans hu)).mpr
    intro k
    exact (lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) u k.val).trans hu
  · simp [F, finiteProjection]

/-- A proved compactness criterion: uniform finite coefficient tails and a
uniform norm bound give total boundedness in the genuine ell² norm. -/
theorem totallyBounded_of_uniform_finite_tail {ι : Type*} (S : Set (Coefficients ι))
    (C : ℝ) (hC : ∀ u ∈ S, ‖u‖ ≤ C)
    (htail : ∀ ε : ℝ, 0 < ε → ∃ s : Finset ι,
      ∀ u ∈ S, ‖u - finiteProjection s u‖ < ε) : TotallyBounded S := by
  classical
  apply Metric.totallyBounded_iff.mpr
  intro ε hε
  obtain ⟨s, hs⟩ := htail (ε/2) (by positivity)
  obtain ⟨K, hK, hPK⟩ := finiteProjection_compact_image s C
  obtain ⟨T, hT, hcover⟩ := Metric.totallyBounded_iff.mp hK.totallyBounded (ε/2) (by positivity)
  refine ⟨T, hT, ?_⟩
  intro u hu
  obtain ⟨v, hv, hvu⟩ := mem_iUnion₂.mp (hcover (hPK u (hC u hu)))
  apply mem_iUnion₂.mpr
  refine ⟨v, hv, ?_⟩
  change dist u v < ε
  calc
    dist u v ≤ dist u (finiteProjection s u) + dist (finiteProjection s u) v := dist_triangle _ _ _
    _ < ε/2 + ε/2 := add_lt_add (by simpa [dist_eq_norm] using hs u hu) hvu
    _ = ε := by ring

end Legacy.BecknerOnofri.TorusSobolev
