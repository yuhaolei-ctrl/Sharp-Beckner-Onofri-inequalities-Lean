module

public import BecknerOnofri.V2.Reaudit.MorseBott.BranchInterface
public import BecknerOnofri.BranchEnergyDerivatives

@[expose] public section

/-! # Differentiating the analytic pressure remainder

`cor:section5-defect-onset`: if `P(β) = a δ² + δ³ R(δ)` for `β ↓ σ`, `δ = 1 - σ/β`, with `R` analytic
at `0`, then
`P'(β) = (2a/σ) δ + O(δ²)` and `P''(β) = 2a/σ² + O(δ)`.
(With `a = d/(2κ_d)`: `d/(κ_d σ) δ` and `d/(κ_d σ²)`, display `(5.pressure-differentiation)`.)
The point of the argument is that `R` is analytic: the right side `g(β) := a δ² + δ³ R(δ)` is an
analytic function of `β` near `σ` (two-sided), so its derivatives are controlled by Taylor expansion
of an analytic function, which an unspecified `O(δ³)` would not allow. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter Set Asymptotics
open scoped Topology BigOperators

namespace BecknerOnofri.V2.Reaudit.MorseBott
open BecknerOnofri.HighDim

/-- `s ↦ s/(σ+s)` is analytic at `0` and `(σ+s)⁻¹` too. -/
theorem analyticAt_inv_add {σ : ℝ} (hσ : σ ≠ 0) : AnalyticAt ℝ (fun s : ℝ => (σ + s)⁻¹) 0 := by
  have : AnalyticAt ℝ (fun s : ℝ => σ + s) 0 := analyticAt_const.add analyticAt_id
  exact this.inv (by simpa using hσ)

theorem analytic_taylor_expansion {σ a : ℝ} (hσ : 0 < σ) {R : ℝ → ℝ} (hR : AnalyticAt ℝ R 0) :
    let g : ℝ → ℝ := fun β => a * (1 - σ / β) ^ 2 + (1 - σ / β) ^ 3 * R (1 - σ / β)
    AnalyticAt ℝ (fun s => g (σ + s)) 0 ∧
    (fun s => deriv (fun s => g (σ + s)) s - 2 * (a / σ ^ 2) * s) =O[𝓝 0] (fun s : ℝ => ‖s‖ ^ 2) ∧
    (fun s => deriv (deriv (fun s => g (σ + s))) s - 2 * (a / σ ^ 2)) =O[𝓝 0]
      (fun s : ℝ => ‖s‖ ^ 1) := by
  intro g
  have hσ0 : σ ≠ 0 := hσ.ne'
  -- w(s) = (σ+s)⁻¹ and δ̃(s) = s * w(s)
  set w : ℝ → ℝ := fun s => (σ + s)⁻¹ with hw
  have hwa : AnalyticAt ℝ w 0 := analyticAt_inv_add hσ0
  have hδ : ∀ s : ℝ, σ + s ≠ 0 → 1 - σ / (σ + s) = s * w s := by
    intro s hs
    simp only [hw]
    field_simp
    ring
  have hδa : AnalyticAt ℝ (fun s : ℝ => s * w s) 0 := analyticAt_id.mul hwa
  have hgeq : ∀ᶠ s in 𝓝 (0 : ℝ), g (σ + s) =
      a * (s * w s) ^ 2 + (s * w s) ^ 3 * R (s * w s) := by
    have : ∀ᶠ s in 𝓝 (0 : ℝ), σ + s ≠ 0 := by
      have hc : ContinuousAt (fun s : ℝ => σ + s) 0 := continuousAt_const.add continuousAt_id
      exact hc.eventually_ne (by simpa using hσ0)
    filter_upwards [this] with s hs
    simp only [g]
    rw [hδ s hs]
  have hRa : AnalyticAt ℝ (fun s => R (s * w s)) 0 := by
    have hg : AnalyticAt ℝ R (0 * w 0) := by simpa using hR
    exact AnalyticAt.comp (f := fun s : ℝ => s * w s) hg hδa
  have hga : AnalyticAt ℝ (fun s => g (σ + s)) 0 := by
    refine (AnalyticAt.congr ?_ (hgeq.mono fun s h => h.symm))
    exact (analyticAt_const.mul (hδa.pow 2)).add ((hδa.pow 3).mul hRa)
  -- the explicit factorisation  g(σ+s) = (a/σ²) s² + s³ M(s)
  have hk : AnalyticAt ℝ (fun s => w s ^ 2 - 1 / σ ^ 2) 0 := (hwa.pow 2).sub analyticAt_const
  have hk0 : (fun s => w s ^ 2 - 1 / σ ^ 2) 0 = 0 := by simp [hw]
  obtain ⟨k, hka, hkeq⟩ := exists_mul_factor hk hk0
  set M : ℝ → ℝ := fun s => a * k s + w s ^ 3 * R (s * w s) with hM
  have hMa : AnalyticAt ℝ M 0 :=
    (analyticAt_const.mul hka).add ((hwa.pow 3).mul hRa)
  have hfac : ∀ᶠ s in 𝓝 (0 : ℝ), g (σ + s) - a / σ ^ 2 * s ^ 2 = s ^ 3 * M s := by
    filter_upwards [hgeq] with s hs
    rw [hs]
    have := hkeq s
    simp only [hM]
    have e : w s ^ 2 = 1 / σ ^ 2 + s * k s := by linarith
    calc a * (s * w s) ^ 2 + (s * w s) ^ 3 * R (s * w s) - a / σ ^ 2 * s ^ 2
        = a * s ^ 2 * (w s ^ 2 - 1 / σ ^ 2) + s ^ 3 * (w s ^ 3 * R (s * w s)) := by ring
      _ = _ := by rw [hkeq s]; ring
  have hbig : (fun s => g (σ + s) - a / σ ^ 2 * s ^ 2) =O[𝓝 0] fun s : ℝ => ‖s‖ ^ 3 := by
    have hMb : M =O[𝓝 0] (fun _ => (1 : ℝ)) := hMa.continuousAt.isBigO
    obtain ⟨C, hC⟩ := hMb.bound
    refine IsBigO.of_bound C ?_
    filter_upwards [hfac, hC] with s h1 h2
    rw [h1, norm_mul, norm_pow]
    simp only [norm_one, mul_one] at h2
    have e : ‖(‖s‖ ^ 3 : ℝ)‖ = ‖s‖ ^ 3 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [e]
    have : ‖s‖ ^ 3 * ‖M s‖ ≤ ‖s‖ ^ 3 * C := mul_le_mul_of_nonneg_left h2 (by positivity)
    linarith
  have h1 := BecknerOnofri.analytic_monomial_deriv_remainder hga (a / σ ^ 2) 2 2 hbig
  have h1' : (fun s => deriv (fun s => g (σ + s)) s - 2 * (a / σ ^ 2) * s) =O[𝓝 0]
      (fun s : ℝ => ‖s‖ ^ 2) := by
    refine h1.congr_left (fun s => ?_)
    norm_num
  have hga' : AnalyticAt ℝ (deriv fun s => g (σ + s)) 0 := hga.deriv
  have h2 := BecknerOnofri.analytic_monomial_deriv_remainder hga' (2 * (a / σ ^ 2)) 1 1
    (by simpa using h1')
  refine ⟨hga, h1', ?_⟩
  refine h2.congr_left (fun s => ?_)
  norm_num

/-- **Differentiating the analytic remainder** (`(5.pressure-differentiation)`). -/
theorem deriv_expansions_of_remainder {σ a : ℝ} (hσ : 0 < σ) {R : ℝ → ℝ} (hR : AnalyticAt ℝ R 0)
    {P : ℝ → ℝ}
    (hP : ∀ᶠ β in 𝓝[>] σ, P β = a * (1 - σ / β) ^ 2 + (1 - σ / β) ^ 3 * R (1 - σ / β)) :
    (fun β => deriv P β - 2 * a / σ * (1 - σ / β)) =O[𝓝[>] σ] (fun β => (1 - σ / β) ^ 2) ∧
    (fun β => deriv (deriv P) β - 2 * a / σ ^ 2) =O[𝓝[>] σ] (fun β => 1 - σ / β) := by
  set g : ℝ → ℝ := fun β => a * (1 - σ / β) ^ 2 + (1 - σ / β) ^ 3 * R (1 - σ / β) with hg
  obtain ⟨-, h1, h2⟩ := analytic_taylor_expansion (a := a) hσ hR
  have hd1 : deriv (fun s => g (σ + s)) = fun s => deriv g (σ + s) := by
    funext s; exact deriv_comp_const_add g σ s
  have hd2 : deriv (deriv (fun s => g (σ + s))) = fun s => deriv (deriv g) (σ + s) := by
    rw [hd1]; funext s; exact deriv_comp_const_add (deriv g) σ s
  rw [hd1] at h1
  rw [hd2] at h2
  -- transfer to the variable `β`
  have hsub : Tendsto (fun β : ℝ => β - σ) (𝓝[>] σ) (𝓝 0) := by
    have : Tendsto (fun β : ℝ => β - σ) (𝓝 σ) (𝓝 0) := by
      simpa using (continuous_sub_right σ).tendsto σ
    exact this.mono_left nhdsWithin_le_nhds
  have A1 := h1.comp_tendsto hsub
  have A2 := h2.comp_tendsto hsub
  simp only [Function.comp_def, add_sub_cancel] at A1 A2
  -- `P = g` near `σ` from the right
  have hPg : ∀ᶠ β in 𝓝[>] σ, ∀ᶠ y in 𝓝 β, P y = g y :=
    DiagonalScalarBranch.eventually_local_right hP
  have hdP : ∀ᶠ β in 𝓝[>] σ, deriv P β = deriv g β := by
    filter_upwards [hPg] with β h
    exact (show P =ᶠ[𝓝 β] g from h).deriv_eq
  have hdP' : ∀ᶠ β in 𝓝[>] σ, deriv (deriv P) β = deriv (deriv g) β := by
    filter_upwards [DiagonalScalarBranch.eventually_local_right hdP] with β h
    exact (show deriv P =ᶠ[𝓝 β] deriv g from h).deriv_eq
  -- comparison of `β - σ` with `δ = 1 - σ/β`
  have hδ : ∀ β : ℝ, 0 < β → 1 - σ / β = (β - σ) / β := by
    intro β hβ; field_simp
  have hbnd : ∀ᶠ β in 𝓝[>] σ, σ < β ∧ β < 2 * σ := by
    filter_upwards [self_mem_nhdsWithin,
      (gt_mem_nhds (by linarith : σ < 2 * σ)).filter_mono nhdsWithin_le_nhds] with β h1 h2
    exact ⟨h1, h2⟩
  have hn1 : ∀ β : ℝ, σ < β → ‖β - σ‖ = β - σ := fun β hb => by
    rw [Real.norm_eq_abs, abs_of_pos (by linarith)]
  have hn2 : ∀ β : ℝ, σ < β → ‖1 - σ / β‖ = (β - σ) / β := fun β hb => by
    have hβ : 0 < β := hσ.trans hb
    rw [hδ β hβ, Real.norm_eq_abs, abs_of_pos (div_pos (by linarith) hβ)]
  have hlin : (fun β : ℝ => ‖β - σ‖ ^ 1) =O[𝓝[>] σ] (fun β : ℝ => 1 - σ / β) := by
    refine IsBigO.of_bound (2 * σ) ?_
    filter_upwards [hbnd] with β ⟨hb1, hb2⟩
    have hβ : 0 < β := hσ.trans hb1
    simp only [hn1 β hb1, hn2 β hb1, pow_one]
    rw [mul_div_assoc', le_div_iff₀ hβ]
    nlinarith
  have hquad : (fun β : ℝ => ‖β - σ‖ ^ 2) =O[𝓝[>] σ] (fun β : ℝ => (1 - σ / β) ^ 2) := by
    refine IsBigO.of_bound ((2 * σ) ^ 2) ?_
    filter_upwards [hbnd] with β ⟨hb1, hb2⟩
    have hβ : 0 < β := hσ.trans hb1
    simp only [norm_pow, hn1 β hb1, hn2 β hb1]
    rw [div_pow, ← mul_div_assoc, le_div_iff₀ (by positivity)]
    have : (β - σ) ^ 2 * β ^ 2 ≤ (β - σ) ^ 2 * (2 * σ) ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith
    nlinarith
  have hB : (fun β : ℝ => 2 * (a / σ ^ 2) * (β - σ) - 2 * a / σ * (1 - σ / β)) =O[𝓝[>] σ]
      (fun β : ℝ => (1 - σ / β) ^ 2) := by
    refine IsBigO.of_bound (4 * |a| / σ) ?_
    filter_upwards [hbnd] with β ⟨hb1, hb2⟩
    have hβ : 0 < β := hσ.trans hb1
    have e : 2 * (a / σ ^ 2) * (β - σ) - 2 * a / σ * (1 - σ / β) =
        (2 * a * β / σ ^ 2) * (1 - σ / β) ^ 2 := by
      rw [hδ β hβ]; field_simp
    rw [e, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs (( 1 - σ / β) ^ 2)]
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    rw [abs_div, abs_mul, abs_mul, abs_of_pos hβ, abs_of_pos (by positivity : (0:ℝ) < σ ^ 2),
      abs_two, div_le_div_iff₀ (by positivity) hσ]
    nlinarith [mul_nonneg (mul_nonneg (abs_nonneg a) hσ.le) (by linarith : (0 : ℝ) ≤ 2 * σ - β)]
  constructor
  · have hA : (fun β : ℝ => deriv g β - 2 * (a / σ ^ 2) * (β - σ)) =O[𝓝[>] σ]
        (fun β : ℝ => (1 - σ / β) ^ 2) := A1.trans hquad
    have := hA.add hB
    refine (this.congr' ?_ EventuallyEq.rfl)
    filter_upwards [hdP] with β h
    rw [h]; ring
  · have hA : (fun β : ℝ => deriv (deriv g) β - 2 * (a / σ ^ 2)) =O[𝓝[>] σ]
        (fun β : ℝ => 1 - σ / β) := by
      simpa using A2.trans hlin
    refine hA.congr' ?_ EventuallyEq.rfl
    filter_upwards [hdP'] with β h
    rw [h]
    ring

/-- **`cor:section5-defect-onset`, pressure level, from the analytic remainder.**  Under the endpoint
inputs `OnsetEndpointInputs d` (Corollary 5.8), the pressure has the form
`(d/(2κ_d)) δ² + δ³ R(δ)` with `R` analytic and, differentiating that identity,
`P' = (d/(κ_d β_s)) δ + O(δ²)`, `P'' = d/(κ_d β_s²) + O(δ)` as `β ↓ β_s`, `δ = 1 - β_s/β`
(display `(5.pressure-differentiation)`); in particular the right limits in
`(5.pressure-derivatives)`. -/
theorem pressure_differentiation_from_remainder {d : ℕ} (hd : 12 ≤ d)
    (E : V2.Onset.OnsetEndpointInputs d) :
    ∃ R : ℝ → ℝ, AnalyticAt ℝ R 0 ∧
      (∀ᶠ β in 𝓝[>] (spectralThreshold d), (pressure d β).toReal =
        (d : ℝ) / (2 * kappa d) * onsetDelta d β ^ 2 + onsetDelta d β ^ 3 * R (onsetDelta d β)) ∧
      (fun β => deriv (fun γ => (pressure d γ).toReal) β -
          (d : ℝ) / (kappa d * spectralThreshold d) * onsetDelta d β)
        =O[𝓝[>] (spectralThreshold d)] (fun β => onsetDelta d β ^ 2) ∧
      (fun β => deriv (deriv (fun γ => (pressure d γ).toReal)) β -
          (d : ℝ) / (kappa d * spectralThreshold d ^ 2))
        =O[𝓝[>] (spectralThreshold d)] (onsetDelta d) ∧
      Tendsto (deriv (fun γ => (pressure d γ).toReal)) (𝓝[>] (spectralThreshold d)) (𝓝 0) ∧
      Tendsto (deriv (deriv (fun γ => (pressure d γ).toReal))) (𝓝[>] (spectralThreshold d))
        (𝓝 ((d : ℝ) / (kappa d * spectralThreshold d ^ 2))) := by
  obtain ⟨R, hR, hform⟩ := pressure_common_branch_form hd E
  unfold onsetDelta at hform ⊢
  have hσ : 0 < spectralThreshold d := spectralThreshold_pos (by omega : 0 < d)
  have hk : kappa d ≠ 0 := (kappa_pos d hd).ne'
  have hreal : ∀ᶠ β in 𝓝[>] (spectralThreshold d), (pressure d β).toReal =
      (d : ℝ) / (2 * kappa d) * (1 - spectralThreshold d / β) ^ 2 +
        (1 - spectralThreshold d / β) ^ 3 * R (1 - spectralThreshold d / β) := by
    filter_upwards [hform] with β h
    rw [h, EReal.toReal_coe]
  obtain ⟨h1, h2⟩ := deriv_expansions_of_remainder (a := (d : ℝ) / (2 * kappa d)) hσ hR hreal
  have e1 : 2 * ((d : ℝ) / (2 * kappa d)) / spectralThreshold d =
      (d : ℝ) / (kappa d * spectralThreshold d) := by field_simp
  have e2 : 2 * ((d : ℝ) / (2 * kappa d)) / spectralThreshold d ^ 2 =
      (d : ℝ) / (kappa d * spectralThreshold d ^ 2) := by field_simp
  rw [e1] at h1
  rw [e2] at h2
  have hδ0 : Tendsto (fun β => 1 - spectralThreshold d / β) (𝓝[>] (spectralThreshold d)) (𝓝 0) := by
    have hc : ContinuousAt (fun β : ℝ => 1 - spectralThreshold d / β) (spectralThreshold d) :=
      continuousAt_const.sub (continuousAt_const.div continuousAt_id hσ.ne')
    have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (spectralThreshold d)))
    simpa [hσ.ne'] using this
  refine ⟨R, hR, hreal, h1, h2, ?_, ?_⟩
  · have hq : Tendsto (fun β => (1 - spectralThreshold d / β) ^ 2) (𝓝[>] (spectralThreshold d))
        (𝓝 0) := by
      simpa using hδ0.pow 2
    have h := h1.trans_tendsto hq
    have h' := h.add (hδ0.const_mul ((d : ℝ) / (kappa d * spectralThreshold d)))
    simpa using h'
  · have h := h2.trans_tendsto hδ0
    have h' := h.add_const ((d : ℝ) / (kappa d * spectralThreshold d ^ 2))
    simpa using h'

#print axioms pressure_differentiation_from_remainder
#print axioms deriv_expansions_of_remainder

end BecknerOnofri.V2.Reaudit.MorseBott
