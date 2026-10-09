module

public import BecknerOnofri.V2.ThetaTail.RouteM.Duplication
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.NumberTheory.ModularForms.JacobiTheta.Manifold
public import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty

@[expose] public section

/-! # Route M, part M1/M2 inputs: behaviour of the theta constants at `i∞` and holomorphy

Limits as `Im τ → ∞` (along the filter `comap Im atTop` on `ℂ`, then transported to `atImInfty`):
`ϑ₃ → 1`, `ϑ₄ → 1`, `jt2 → 2` (the two terms `n = 0, -1`), `e^{πiτ} → 0`, hence
`F₃, F₄ → 1`, `F₂ → 0` and `(jt2·ϑ₃·ϑ₄)⁸ → 256`.  Holomorphy on the upper half plane. -/
noncomputable section
open Complex Filter Topology
open scoped Real
namespace BecknerOnofri.V2.ThetaTail.RouteM

/-- the filter "`Im τ → +∞`" on `ℂ` -/
abbrev imInfty : Filter ℂ := comap Complex.im atTop

lemma norm_tC (τ : ℂ) (n : ℤ) : ‖tC τ n‖ = Real.exp (-π * ((n : ℝ) ^ 2 + n) * τ.im) := by
  unfold tC
  rw [Complex.norm_exp]
  congr 1
  have : (π * I * ((n : ℂ) ^ 2 + n) * τ) = (((π * ((n : ℝ) ^ 2 + n) : ℝ) : ℂ) * τ) * I := by
    push_cast; ring
  rw [this, mul_I_re, im_ofReal_mul]; ring

lemma tendsto_cexp_pi_I : Tendsto (fun τ : ℂ => cexp (π * I * τ)) imInfty (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have : ∀ τ : ℂ, ‖cexp (π * I * τ)‖ = Real.exp (-π * τ.im) := by
    intro τ
    rw [Complex.norm_exp]
    congr 1
    have : (π * I * τ) = ((π : ℝ) : ℂ) * τ * I := by ring
    rw [this, mul_I_re, im_ofReal_mul]; ring
  simp_rw [this]
  exact Real.tendsto_exp_atBot.comp
    (Filter.Tendsto.const_mul_atTop_of_neg (by linarith [Real.pi_pos]) tendsto_comap)

lemma tendsto_jt3 : Tendsto jt3 imInfty (𝓝 1) := by
  have h := isBigO_at_im_infty_jacobiTheta_sub_one
  have h0 : Tendsto (fun τ : ℂ => Real.exp (-π * τ.im)) imInfty (𝓝 0) :=
    Real.tendsto_exp_atBot.comp
      (Filter.Tendsto.const_mul_atTop_of_neg (by linarith [Real.pi_pos]) tendsto_comap)
  have := h.trans_tendsto h0
  have h2 : Tendsto (fun τ => jacobiTheta τ - 1 + 1) imInfty (𝓝 (0 + 1)) := this.add tendsto_const_nhds
  have e : jt3 = jacobiTheta := funext jt3_eq_jacobiTheta
  rw [e]; simpa using h2

lemma tendsto_jt4 : Tendsto jt4 imInfty (𝓝 1) := by
  have hshift : Tendsto (fun τ : ℂ => τ + 1) imInfty imInfty := by
    rw [tendsto_comap_iff]
    simpa [Function.comp_def] using (tendsto_comap : Tendsto Complex.im imInfty atTop)
  have := tendsto_jt3.comp hshift
  refine this.congr fun τ => ?_
  simp [jt3_add_one]

lemma tendsto_jt2 : Tendsto jt2 imInfty (𝓝 2) := by
  have hsum : Summable (fun n : ℤ => Real.exp (-π * ((n : ℝ) ^ 2 + n))) := by
    have := summable_norm_tC (τ := I) (by simp)
    refine this.congr fun n => ?_
    rw [norm_tC]; simp
  have hpos : ∀ n : ℤ, ¬ (n = 0 ∨ n = -1) → (0 : ℝ) < (n : ℝ) ^ 2 + n := by
    intro n hn
    push Not at hn
    have : 0 < n * (n + 1) := by
      rcases lt_or_gt_of_ne hn.1 with h | h
      · have : n + 1 < 0 := by omega
        nlinarith
      · nlinarith
    have h' : (0 : ℝ) < (n : ℝ) * (n + 1) := by exact_mod_cast this
    nlinarith
  have key := tendsto_tsum_of_dominated_convergence (𝓕 := imInfty) (f := fun τ n => tC τ n)
    (g := fun n : ℤ => if n = 0 ∨ n = -1 then (1 : ℂ) else 0)
    (bound := fun n : ℤ => Real.exp (-π * ((n : ℝ) ^ 2 + n))) hsum ?_ ?_
  · have hg : ∑' n : ℤ, (if n = 0 ∨ n = -1 then (1 : ℂ) else 0) = 2 := by
      rw [tsum_eq_sum (s := ({0, -1} : Finset ℤ))]
      · rw [Finset.sum_pair (by norm_num)]; norm_num
      · intro b hb
        simp only [Finset.mem_insert, Finset.mem_singleton] at hb
        simp [hb]
    rw [hg] at key
    refine key.congr fun τ => ?_
    rw [jt2_eq_tsum]
  · intro n
    by_cases hn : n = 0 ∨ n = -1
    · have : ∀ τ : ℂ, tC τ n = 1 := by
        intro τ; rcases hn with rfl | rfl <;> simp [tC]
      simp only [hn, ite_true, this]
      exact tendsto_const_nhds
    · simp only [hn, ite_false]
      rw [tendsto_zero_iff_norm_tendsto_zero]
      simp_rw [norm_tC]
      exact Real.tendsto_exp_atBot.comp
        (Filter.Tendsto.const_mul_atTop_of_neg
          (by have := hpos n hn; nlinarith [Real.pi_pos]) tendsto_comap)
  · filter_upwards [tendsto_comap.eventually (eventually_ge_atTop (1 : ℝ))] with τ hτ n
    rw [norm_tC]
    apply Real.exp_le_exp.2
    have h0 : (0 : ℝ) ≤ (n : ℝ) ^ 2 + n := by
      have : 0 ≤ n * (n + 1) := by
        rcases le_or_gt 0 n with h | h
        · nlinarith
        · have : n + 1 ≤ 0 := by omega
          nlinarith
      have h' : (0 : ℝ) ≤ (n : ℝ) * (n + 1) := by exact_mod_cast this
      nlinarith
    nlinarith [Real.pi_pos, mul_nonneg h0 (sub_nonneg.2 hτ), mul_nonneg Real.pi_pos.le
      (mul_nonneg h0 (sub_nonneg.2 hτ))]

lemma tendsto_F3 : Tendsto F3 imInfty (𝓝 1) := by
  have := tendsto_jt3.pow 4
  rw [one_pow] at this
  exact this

lemma tendsto_F4 : Tendsto F4 imInfty (𝓝 1) := by
  have := tendsto_jt4.pow 4
  rw [one_pow] at this
  exact this

lemma tendsto_F2 : Tendsto F2 imInfty (𝓝 0) := by
  have := tendsto_cexp_pi_I.mul (tendsto_jt2.pow 4)
  rw [zero_mul] at this
  exact this

/-- `H = (jt2·ϑ₃·ϑ₄)^8`, so that `(F₂F₃F₄)² = e^{2πiτ} H` -/
def Hfun (τ : ℂ) : ℂ := (jt2 τ * jt3 τ * jt4 τ) ^ 8

lemma tendsto_Hfun : Tendsto Hfun imInfty (𝓝 256) := by
  have := ((tendsto_jt2.mul tendsto_jt3).mul tendsto_jt4).pow 8
  have e : ((2 : ℂ) * 1 * 1) ^ 8 = 256 := by norm_num
  rw [e] at this
  exact this

lemma F2F3F4_sq (τ : ℂ) : (F2 τ * F3 τ * F4 τ) ^ 2 = cexp (2 * π * I * τ) * Hfun τ := by
  unfold F2 F3 F4 Hfun
  have : cexp (2 * π * I * τ) = cexp (π * I * τ) ^ 2 := by
    rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
  rw [this]; ring

/-! ### Holomorphy -/

lemma differentiableAt_jt3 {τ : ℂ} (hτ : 0 < τ.im) : DifferentiableAt ℂ jt3 τ :=
  differentiableAt_jacobiTheta₂_snd 0 hτ

lemma differentiableAt_jt4 {τ : ℂ} (hτ : 0 < τ.im) : DifferentiableAt ℂ jt4 τ :=
  differentiableAt_jacobiTheta₂_snd (1 / 2) hτ

lemma differentiableAt_jt2 {τ : ℂ} (hτ : 0 < τ.im) : DifferentiableAt ℂ jt2 τ := by
  have h : DifferentiableAt ℂ (fun p : ℂ × ℂ => jacobiTheta₂ p.1 p.2)
      ((fun w : ℂ => (w / 2, w)) τ) := (hasFDerivAt_jacobiTheta₂ (τ / 2) hτ).differentiableAt
  have h2 : DifferentiableAt ℂ (fun w : ℂ => (w / 2, w)) τ :=
    (differentiableAt_id.div_const 2).prodMk differentiableAt_id
  exact DifferentiableAt.comp (g := fun p : ℂ × ℂ => jacobiTheta₂ p.1 p.2)
    (f := fun w : ℂ => (w / 2, w)) τ h h2

lemma differentiableAt_F3 {τ : ℂ} (hτ : 0 < τ.im) : DifferentiableAt ℂ F3 τ :=
  (differentiableAt_jt3 hτ).pow 4

lemma differentiableAt_F4 {τ : ℂ} (hτ : 0 < τ.im) : DifferentiableAt ℂ F4 τ :=
  (differentiableAt_jt4 hτ).pow 4

lemma differentiableAt_F2 {τ : ℂ} (hτ : 0 < τ.im) : DifferentiableAt ℂ F2 τ := by
  have h1 : DifferentiableAt ℂ (fun w : ℂ => cexp (π * I * w)) τ := by fun_prop
  exact h1.mul ((differentiableAt_jt2 hτ).pow 4)

end BecknerOnofri.V2.ThetaTail.RouteM
