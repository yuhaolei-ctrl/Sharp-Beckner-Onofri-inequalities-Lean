module

public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Tactic

@[expose] public section

/-!
# Finite Taylor-coefficient lemma (Appendix A.3, "Vanishing required at the origin")

If `φ` is `C³` near `0` and `φ(t) = O(t⁴)` as `t → 0`, then `φ^{(k)}(0) = 0` for `0 ≤ k ≤ 3`.
The proof uses Taylor's theorem in little-o form on a small open interval and then peels the
coefficients of the cubic Taylor polynomial one by one; no derivative is inferred from a
pointwise big-O assertion without regularity.

STATEMENT DIFFERENCE.  The manuscript says "analyticity then proves all the required derivative
vanishings".  Here only `ContDiffAt ℝ 3 φ 0` is assumed (weaker than analyticity), so the lemma
is applicable to `C^∞` functions that are not known to be analytic.
-/

noncomputable section
open Filter Topology Asymptotics
open scoped BigOperators
namespace BecknerOnofri.V2.FiniteState

/-- A cubic polynomial that is `o(t³)` at `0` has all four coefficients zero. -/
theorem cubic_isLittleO_coeffs_zero {c0 c1 c2 c3 : ℝ}
    (h : (fun t : ℝ => c0 + c1 * t + c2 * t ^ 2 + c3 * t ^ 3) =o[𝓝 0] fun t : ℝ => t ^ 3) :
    c0 = 0 ∧ c1 = 0 ∧ c2 = 0 ∧ c3 = 0 := by
  set P : ℝ → ℝ := fun t => c0 + c1 * t + c2 * t ^ 2 + c3 * t ^ 3 with hP
  have hu : Tendsto (fun t : ℝ => P t / t ^ 3) (𝓝[≠] 0) (𝓝 0) :=
    (h.mono nhdsWithin_le_nhds).tendsto_div_nhds_zero
  have hne : ∀ᶠ t : ℝ in 𝓝[≠] 0, t ≠ 0 := self_mem_nhdsWithin
  have hcont : ∀ f : ℝ → ℝ, Continuous f → Tendsto f (𝓝[≠] 0) (𝓝 (f 0)) :=
    fun f hf => (hf.tendsto 0).mono_left nhdsWithin_le_nhds
  -- step A: t^3 * u → 0 and = P → c0
  have hA : c0 = 0 := by
    have h1 : Tendsto (fun t : ℝ => t ^ 3 * (P t / t ^ 3)) (𝓝[≠] 0) (𝓝 (0 ^ 3 * 0)) :=
      ((continuous_pow 3).tendsto 0 |>.mono_left nhdsWithin_le_nhds).mul hu
    have h2 : Tendsto (fun t : ℝ => t ^ 3 * (P t / t ^ 3)) (𝓝[≠] 0) (𝓝 c0) := by
      have := hcont P (by rw [hP]; fun_prop)
      refine (this.congr' ?_).trans_eq ?_ <;> [skip; simp [hP]]
      filter_upwards [hne] with t ht
      field_simp
    simpa using tendsto_nhds_unique h2 h1
  have hB : c1 = 0 := by
    have h1 : Tendsto (fun t : ℝ => t ^ 2 * (P t / t ^ 3)) (𝓝[≠] 0) (𝓝 (0 ^ 2 * 0)) :=
      ((continuous_pow 2).tendsto 0 |>.mono_left nhdsWithin_le_nhds).mul hu
    have h2 : Tendsto (fun t : ℝ => t ^ 2 * (P t / t ^ 3)) (𝓝[≠] 0) (𝓝 c1) := by
      have := hcont (fun t : ℝ => c1 + c2 * t + c3 * t ^ 2) (by fun_prop)
      refine (this.congr' ?_).trans_eq ?_ <;> [skip; simp]
      filter_upwards [hne] with t ht
      simp only [hP, hA, zero_add]
      field_simp
    simpa using tendsto_nhds_unique h2 h1
  have hC : c2 = 0 := by
    have h1 : Tendsto (fun t : ℝ => t * (P t / t ^ 3)) (𝓝[≠] 0) (𝓝 (0 * 0)) :=
      (continuous_id.tendsto 0 |>.mono_left nhdsWithin_le_nhds).mul hu
    have h2 : Tendsto (fun t : ℝ => t * (P t / t ^ 3)) (𝓝[≠] 0) (𝓝 c2) := by
      have := hcont (fun t : ℝ => c2 + c3 * t) (by fun_prop)
      refine (this.congr' ?_).trans_eq ?_ <;> [skip; simp]
      filter_upwards [hne] with t ht
      simp only [hP, hA, hB, zero_add, zero_mul]
      field_simp
    simpa using tendsto_nhds_unique h2 h1
  have hD : c3 = 0 := by
    have h2 : Tendsto (fun t : ℝ => P t / t ^ 3) (𝓝[≠] 0) (𝓝 c3) := by
      have := hcont (fun _ : ℝ => c3) continuous_const
      refine (this.congr' ?_)
      filter_upwards [hne] with t ht
      simp only [hP, hA, hB, hC, zero_add, zero_mul]
      field_simp
    exact tendsto_nhds_unique h2 hu
  exact ⟨hA, hB, hC, hD⟩

/-- **Finite Taylor-coefficient lemma.**  `C³` at `0` plus `φ = O(t⁴)` forces
`φ(0) = φ'(0) = φ''(0) = φ'''(0) = 0`. -/
theorem iteratedDeriv_zero_eq_zero_of_isBigO {φ : ℝ → ℝ} (hφ : ContDiffAt ℝ 3 φ 0)
    (h : φ =O[𝓝 0] fun t : ℝ => t ^ 4) :
    iteratedDeriv 0 φ 0 = 0 ∧ iteratedDeriv 1 φ 0 = 0 ∧ iteratedDeriv 2 φ 0 = 0 ∧
      iteratedDeriv 3 φ 0 = 0 := by
  obtain ⟨u, hu, hcd⟩ := hφ.contDiffOn (m := 3) le_rfl (by simp)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hu
  have hconv : Convex ℝ (Metric.ball (0 : ℝ) δ) := convex_ball _ _
  have hcd' : ContDiffOn ℝ 3 φ (Metric.ball (0 : ℝ) δ) := hcd.mono hball
  have htaylor := taylor_isLittleO hconv (Metric.mem_ball_self hδ) hcd'
  have hnhds : Metric.ball (0 : ℝ) δ ∈ 𝓝 (0 : ℝ) := Metric.ball_mem_nhds _ hδ
  rw [nhdsWithin_eq_nhds.mpr hnhds] at htaylor
  -- φ = o(t^3)
  have hid : (fun t : ℝ => t) =o[𝓝 0] fun _ : ℝ => (1 : ℝ) := by
    rw [Asymptotics.isLittleO_one_iff]
    exact continuous_id.tendsto 0
  have h43 : (fun t : ℝ => t ^ 4) =o[𝓝 0] fun t : ℝ => t ^ 3 := by
    have := hid.mul_isBigO (Asymptotics.isBigO_refl (fun t : ℝ => t ^ 3) (𝓝 0))
    simpa [pow_succ, mul_comm] using this
  have hφo : φ =o[𝓝 0] fun t : ℝ => t ^ 3 := h.trans_isLittleO h43
  -- the Taylor polynomial is o(t^3)
  have hT : (fun t : ℝ => taylorWithinEval φ 3 (Metric.ball (0 : ℝ) δ) 0 t) =o[𝓝 0]
      fun t : ℝ => t ^ 3 := by
    have h1 : (fun t : ℝ => φ t - (φ t - taylorWithinEval φ 3 (Metric.ball (0 : ℝ) δ) 0 t)) =o[𝓝 0]
        fun t : ℝ => t ^ 3 := by
      refine hφo.sub ?_
      simpa using htaylor
    simpa using h1
  have hopen : IsOpen (Metric.ball (0 : ℝ) δ) := Metric.isOpen_ball
  have hk : ∀ k, iteratedDerivWithin k φ (Metric.ball (0 : ℝ) δ) 0 = iteratedDeriv k φ 0 :=
    fun k => iteratedDerivWithin_of_isOpen hopen (Metric.mem_ball_self hδ)
  have hpoly : (fun t : ℝ => iteratedDeriv 0 φ 0 + (iteratedDeriv 1 φ 0) * t +
      (iteratedDeriv 2 φ 0 / 2) * t ^ 2 + (iteratedDeriv 3 φ 0 / 6) * t ^ 3) =o[𝓝 0]
      fun t : ℝ => t ^ 3 := by
    refine hT.congr_left ?_
    intro t
    simp only [taylor_within_apply, Finset.sum_range_succ, Finset.sum_range_zero, hk]
    norm_num [Nat.factorial]
    ring
  obtain ⟨c0, c1, c2, c3⟩ := cubic_isLittleO_coeffs_zero hpoly
  refine ⟨c0, c1, ?_, ?_⟩
  · linarith
  · linarith

end BecknerOnofri.V2.FiniteState
