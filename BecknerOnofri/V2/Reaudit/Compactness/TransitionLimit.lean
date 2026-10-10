module

public import BecknerOnofri.V2.Reaudit.Compactness.GibbsL2
public import BecknerOnofri.V2.Reaudit.Compactness.EulerSobolev
public import BecknerOnofri.V2.Reaudit.Sobolev.LocalUniqueness
public import BecknerOnofri.ElevenTransitionSequence
public import BecknerOnofri.ContinuousOptimizerFromL2
public import BecknerOnofri.VariationalCurveConvexity
public import Mathlib.Analysis.Convex.Continuous

@[expose] public section

/-! # Proposition 4.9 (`prop:section4-first-order-coexistence`): the nonuniform limit at `β_gm(11)`

This module follows the printed proof, in the printed order, up to the existence of the nonzero
limit `u_0` and its strong convergence:

* a sequence `β_n ↓ β_gm` with `β_gm < β_n < β_s` (`eq:section4-beta-sequence`),
  `P_11(β_n) > 0`, and potentials `u_n`, the mean-zero dual potentials of nonuniform minimizers,
  maximizing the dual functional at `A_n ∝ 1/β_n` (`cor:section2-extremizer-correspondence`; here
  `Eleven.exists_nonzero_optimizer`, which is `prop:section2-subcritical-attainment` plus positivity of
  the pressure);
* the pressure is finite and convex on `(0, 22)`, hence continuous there, so
  `C_11(A_n) = P_11(β_n) → P_11(β_gm) = 0` (`eq:section4-pressure-limit-zero`);
* `Compactness.compactness_limit`: bounded in `H^{11/2}`, Rellich, Vitali, the limit `u_0` maximizes
  at `A_gm`, norm convergence, **strong** convergence in `H^{11/2}`
  (`eq:section4-uniform-compactness`--`eq:section4-strong-critical-Sobolev`);
* `u_0 ≠ 0`: if `u_0 = 0`, the uniform fourth exponential moment and a.e. convergence give
  `ρ_n → 1` in `L²` (`GibbsL2`), the Euler multiplier gives `u_n → 0` in `H^{11}` (`EulerSobolev`), and the
  Sobolev local uniqueness `Sobolev.local_uniqueness_raw` (Lemma 4.8 on the Banach algebra `H^{11}`)
  forces `u_n = 0`, contradicting `P_11(β_n) > 0`.

Nothing from the old endpoint chain (`coexistence`, `exists_nonzero_limit_optimizer`,
`SubspectralLocalUniqueness.local_unique`, the Wiener bounds) is used. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped Topology

namespace BecknerOnofri.V2.Reaudit.Compactness
open BecknerOnofri.HighDim ContinuousGibbs ContinuousFirstShell ContinuousOptimizers OnsetContinuous
open Legacy.BecknerOnofri.TorusSobolev
open Legacy.BecknerOnofri.SubcriticalAttainment (Admissible functional)

/-- The pressure is convex on `(0, 22)` (finite there). -/
theorem pressureReal_convex : ConvexOn ℝ (Set.Ioo 0 22) Eleven.pressureReal :=
  pressure_toReal_convexOn (by norm_num) (convex_Ioo _ _)
    (fun β hβ => Eleven.pressure_eq_real hβ.1.le hβ.2)

theorem pressureReal_at_transition : Eleven.pressureReal Eleven.globalTransition = 0 := by
  simp only [Eleven.pressureReal, Eleven.pressure_at_transition, EReal.toReal_zero]

/-- The transition lies in `(0, 22)`: non-strict lower bound, then the competitor upper bound. -/
theorem transition_mem_Ioo : Eleven.globalTransition ∈ Set.Ioo (0 : ℝ) 22 :=
  ⟨Eleven.transition_pos, Eleven.transition_upper.trans (by norm_num)⟩

/-- `eq:section4-pressure-limit-zero`: `P_11(β_n) → P_11(β_gm) = 0` along any `β_n → β_gm`
(finite and convex on `(0,22)`, hence continuous). -/
theorem pressureReal_tendsto_zero {β : ℕ → ℝ} (hβ : Tendsto β atTop (𝓝 Eleven.globalTransition)) :
    Tendsto (fun n => Eleven.pressureReal (β n)) atTop (𝓝 0) := by
  have hcont : ContinuousAt Eleven.pressureReal Eleven.globalTransition :=
    (ConvexOn.continuousOn isOpen_Ioo pressureReal_convex).continuousAt
      (isOpen_Ioo.mem_nhds transition_mem_Ioo)
  have := hcont.tendsto.comp hβ
  rwa [pressureReal_at_transition] at this

/-- The Euler equation `u = (β/β_s) G (ρ - 1)` for a continuous potential, in the almost-everywhere
convolution form of Lemma 4.8. -/
theorem eulerEq_of_full {d : ℕ} (hd : 0 < d) (β : ℝ) (v : Space d)
    (h : ReducedEquation.full d (β / spectralThreshold d) v = 0) :
    Sobolev.EulerEq d β ⇑v := by
  have h1 : v = (β / spectralThreshold d) • greenContinuous d (normalized v - 1) := sub_eq_zero.mp h
  refine Filter.Eventually.of_forall fun x => ?_
  show v x = β * ∫ y, Legacy.TorusEndpoint.GreenKernelReal.realGreen d y *
    (normalizedGibbs (fun z => v z) (x - y) - 1) ∂torusMeasure d
  rw [← RawSubspectralLocalUniqueness.continuous_physical_green hd β v x]
  exact congrArg (fun f : Space d => f x) h1

/-- A continuous function vanishing almost everywhere vanishes. -/
theorem eq_zero_of_ae_zero {d : ℕ} (v : Space d) (h : (v : Torus d → ℝ) =ᵐ[torusMeasure d] 0) :
    v = 0 := by
  have : (torusMeasure d).IsOpenPosMeasure := by unfold torusMeasure; infer_instance
  exact ContinuousMap.coe_injective
    (Measure.eq_of_ae_eq h v.continuous continuous_const)

/-- The real part of `toL2 u` is `u` almost everywhere. -/
theorem re_toL2_ae {d : ℕ} (u : Space d) :
    (fun x => ((toL2 d u) x).re) =ᵐ[torusMeasure d] fun x => u x := by
  filter_upwards [toL2_ae u] with x hx
  rw [hx]; simp

/-- **The nonzero limit at the transition, with strong critical-Sobolev convergence.**

There are couplings `β_n ↓ β_gm(11)` strictly between `β_gm` and `β_s` with `P_11(β_n) > 0`, nonzero
continuous mean-zero dual potentials `u_n` of the minimizers at `β_n`, a subsequence `ψ`, and a
**nonzero** admissible limit `U₀`, a global maximizer of the dual functional at the transition
coefficient `A_gm = β_s/(2β_gm)`, such that `u_{ψ n} → U₀` in `L²` and **strongly in the critical
Sobolev space**: `‖u_{ψ n} - U₀‖²_{Ḣ^{11/2}} → 0`. -/
theorem transition_limit :
    ∃ (β : ℕ → ℝ) (u : ℕ → Space 11) (U₀ : TorusL2 11) (ψ : ℕ → ℕ),
      StrictMono ψ ∧
      (∀ n, Eleven.globalTransition < β n ∧ β n < spectralThreshold 11) ∧
      Tendsto β atTop (𝓝 Eleven.globalTransition) ∧
      (∀ n, 0 < pressure 11 (β n)) ∧
      (∀ n, InCriticalSobolev (u n) ∧ MeanZero (u n) ∧ u n ≠ 0 ∧
        ReducedEquation.full 11 (β n / spectralThreshold 11) (u n) = 0 ∧
        ∀ v : Torus 11 → ℝ, InCriticalSobolev v → dualFunctional (β n) v ≤ dualFunctional (β n) (u n)) ∧
      Admissible U₀ ∧ U₀ ≠ 0 ∧
      (∀ V : TorusL2 11, Admissible V →
        functional (spectralThreshold 11 / (2 * Eleven.globalTransition)) V ≤
          functional (spectralThreshold 11 / (2 * Eleven.globalTransition)) U₀) ∧
      Tendsto (fun n => toL2 11 (u (ψ n))) atTop (𝓝 U₀) ∧
      Tendsto (fun n => criticalEnergy (toL2 11 (u (ψ n)) - U₀)) atTop (𝓝 0) := by
  have hσ : 0 < spectralThreshold 11 := spectralThreshold_pos (d := 11) (by norm_num)
  have hβs : Eleven.globalTransition < spectralThreshold 11 :=
    Eleven.transition_upper.trans Eleven.spectralThreshold_bounds.1
  choose u hu hm hmax hfull hnz using Eleven.exists_nonzero_optimizer
  set β : ℕ → ℝ := Eleven.transitionCoupling with hβdef
  let A : ℕ → ℝ := fun n => spectralThreshold 11 / (2 * β n)
  let A₀ : ℝ := spectralThreshold 11 / (2 * Eleven.globalTransition)
  have hA : Tendsto A atTop (𝓝 A₀) :=
    tendsto_const_nhds.div (tendsto_const_nhds.mul Eleven.transitionCoupling_limit)
      (mul_ne_zero (by norm_num) Eleven.transition_pos.ne')
  have hA₀ : (1 / 2 : ℝ) < A₀ :=
    Eleven.normalized_coefficient_gt_half Eleven.transition_pos hβs
  have hU : ∀ n, Admissible (toL2 11 (u n)) := fun n => toL2_admissible (by norm_num) _ (hu n) (hm n)
  have hM : ∀ n (V : TorusL2 11), Admissible V →
      functional (A n) V ≤ functional (A n) (toL2 11 (u n)) := fun n V hV =>
    toL2_optimizer (by norm_num) _ _ (hu n) (hm n) (hmax n) V hV
  obtain ⟨b, Ab, hb, hR, hgapb⟩ := Eleven.eleven_rough_gap
  -- the value of the maximizer is the pressure
  have hvalue : ∀ n, functional (A n) (toL2 11 (u n)) = Eleven.pressureReal (β n) := by
    intro n
    have h1 := OptimizerDuality.pressure_eq_dual (by norm_num) (Eleven.transitionCoupling_pos n) (u n)
      (hu n) (hmax n)
    rw [dualFunctional_eq_toL2 (by norm_num) _ (u n) (hu n) (hm n)] at h1
    unfold Eleven.pressureReal
    rw [h1, EReal.toReal_coe]
  have hval : Tendsto (fun n => functional (A n) (toL2 11 (u n))) atTop (𝓝 0) := by
    simp only [hvalue]
    exact pressureReal_tendsto_zero Eleven.transitionCoupling_limit
  -- the compactness argument
  obtain ⟨B, U₀, ψ, hB, hψ, hU₀, hmem, hlim, hae, hmom, hZ, hV0, hmaxlim, hE, hstrong⟩ :=
    compactness_limit (by norm_num) hb hR (hgapb.trans hA₀) hA (fun n => toL2 11 (u n)) hU hM hval
  have hU₀adm : Admissible U₀ := ⟨hU₀.2, hU₀.1.1⟩
  -- exclusion of the zero limit
  have hne : U₀ ≠ 0 := by
    intro hz
    subst hz
    have hae0 : ∀ᵐ x ∂torusMeasure 11,
        Tendsto (fun n => ((toL2 11 (u (ψ n))) x).re) atTop (𝓝 0) := by
      filter_upwards [hae, Lp.coeFn_zero ℂ 2 (torusMeasure 11)] with x hx hx0
      simpa [hx0] using hx
    have hZ1 : Tendsto (fun n => Legacy.BecknerOnofri.SubcriticalAttainment.partition
        (toL2 11 (u (ψ n)))) atTop (𝓝 1) := by
      have := hZ
      rwa [Legacy.BecknerOnofri.SubcriticalAttainment.partition_zero] at this
    -- `eq:section4-uniform-fourth-exponential-moment` and `eq:section4-rho-n-to-one-L2`
    have hD := gibbs_sq_tendsto_zero (U := fun n => toL2 11 (u (ψ n))) hR
      (fun n => hU (ψ n)) (M := Real.exp (4 ^ 2 * B / (4 * b) + Real.log Ab))
      (fun n => hmom 4 (by norm_num) n) hae0 hZ1
    -- the same quantity in terms of the continuous Gibbs density `ρ_n = normalized u_n`
    have hD' : Tendsto (fun n => ∫ x, (normalized (u (ψ n)) x - 1) ^ 2 ∂torusMeasure 11)
        atTop (𝓝 0) := by
      refine hD.congr fun n => ?_
      apply integral_congr_ae
      filter_upwards [re_toL2_ae (u (ψ n))] with x hx
      rw [hx, ContinuousOptimizers.partition_toL2, normalized_apply]
      simp only [normalizedGibbs, ContinuousGibbs.partition, mean_apply, exponential_apply]
    -- `eq:section4-un-Euler` and `eq:section4-un-H11-convergence`
    have hbound : ∀ n, InSobolev (11 : ℝ) (u (ψ n)) ∧
        sobolevNorm (11 : ℝ) (u (ψ n)) ≤ Real.sqrt ((1 + (2 * Real.pi) ^ 2) ^ 11) *
          |β (ψ n) / spectralThreshold 11| *
          Real.sqrt (∫ x, (normalized (u (ψ n)) x - 1) ^ 2 ∂torusMeasure 11) := by
      intro n
      have h := sobolev_green_bound (d := 11) (by norm_num) (β (ψ n) / spectralThreshold 11)
        (normalized (u (ψ n)) - 1) (u (ψ n)) (sub_eq_zero.mp (hfull (ψ n)))
      simpa using h
    have hnorm0 : Tendsto (fun n => sobolevNorm (11 : ℝ) (u (ψ n))) atTop (𝓝 0) := by
      have hc : Tendsto (fun n => Real.sqrt ((1 + (2 * Real.pi) ^ 2) ^ 11) *
          |β (ψ n) / spectralThreshold 11| *
          Real.sqrt (∫ x, (normalized (u (ψ n)) x - 1) ^ 2 ∂torusMeasure 11)) atTop (𝓝 0) := by
        have hb1 : Tendsto (fun n => β (ψ n)) atTop (𝓝 Eleven.globalTransition) :=
          Eleven.transitionCoupling_limit.comp hψ.tendsto_atTop
        have h1 : Tendsto (fun n => Real.sqrt ((1 + (2 * Real.pi) ^ 2) ^ 11) *
            |β (ψ n) / spectralThreshold 11|) atTop
            (𝓝 (Real.sqrt ((1 + (2 * Real.pi) ^ 2) ^ 11) *
              |Eleven.globalTransition / spectralThreshold 11|)) :=
          tendsto_const_nhds.mul ((hb1.div_const _).abs)
        have h2 := h1.mul (hD'.sqrt)
        simpa using h2
      refine squeeze_zero (fun n => Real.sqrt_nonneg _) (fun n => (hbound n).2) hc
    -- Lemma 4.8 (local uniqueness in `H^{11}`) forces `u_n = 0`
    obtain ⟨ε, hε, hloc⟩ := Sobolev.local_uniqueness_raw Eleven.transition_pos
      (Eleven.transition_upper.trans Eleven.spectralThreshold_bounds.1)
    have hbclose : ∀ᶠ n in atTop, |β (ψ n) - Eleven.globalTransition| < ε := by
      have := (Eleven.transitionCoupling_limit.comp hψ.tendsto_atTop)
      rw [Metric.tendsto_nhds] at this
      filter_upwards [this ε hε] with n hn
      simpa [Real.dist_eq] using hn
    have hsmall : ∀ᶠ n in atTop, sobolevNorm (11 : ℝ) (u (ψ n)) < ε :=
      (tendsto_order.1 hnorm0).2 ε hε
    obtain ⟨n, hn1, hn2⟩ := (hbclose.and hsmall).exists
    have hzero := hloc (β (ψ n)) (u (ψ n)) hn1 (hbound n).1 (hm (ψ n)) hn2
      (eulerEq_of_full (by norm_num) _ _ (hfull (ψ n)))
    exact hnz (ψ n) (eq_zero_of_ae_zero _ hzero)
  refine ⟨β, u, U₀, ψ, hψ, fun n => Eleven.transitionCoupling_bounds n,
    Eleven.transitionCoupling_limit, fun n => Eleven.transitionCoupling_pressure_pos n,
    fun n => ⟨hu n, hm n, hnz n, hfull n, hmax n⟩, hU₀adm, hne, hmaxlim, hlim, hstrong⟩

end BecknerOnofri.V2.Reaudit.Compactness
