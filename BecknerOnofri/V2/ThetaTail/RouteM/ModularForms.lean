module

public import BecknerOnofri.V2.ThetaTail.RouteM.Limits
public import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
public import Mathlib.NumberTheory.ModularForms.Discriminant
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion

@[expose] public section

/-! # Route M, parts M1 and M2: modular-form uniqueness

**Route note (differs from the written proof of Appendix A.1).**  The manuscript derives
`(d12-tail-eq:E6theta)` from the Weierstrass `℘`-function (DLMF 23.8.1, 23.9.2, 23.9.4, 23.6.2-4,
23.3.7, 20.7.5) and the product identity `ϑ₂ϑ₃ϑ₄ = 2η³` from DLMF 20.4.2, 20.4.6.  Here, instead:

* M1 (`E6_theta`): `f₆ = ½(F₂+F₃)(F₃+F₄)(F₄−F₂)`, `F_j = ϑ_j⁴`, is a level-one modular form of
  weight 6 (invariance under the generators `S`,`T` of `SL₂(ℤ)` from the theta transformation
  laws of `RouteM.Basic`, holomorphy, boundedness at `i∞`), so by Mathlib's
  `levelOne_weight_six_rank_one` it is a multiple of `E₆`; both tend to `1` at `i∞`, so `f₆ = E₆`.
* M2 (`theta_product_eq_discriminant`): `(F₂F₃F₄)² = e^{2πiτ} H(τ)` is a weight-12 cusp form, hence
  a multiple of Mathlib's discriminant `Δ = e^{2πiτ} ∏(1-e^{2πinτ})²⁴`
  (`CuspForm.exists_smul_discriminant_of_weight_eq_twelve`); comparing leading terms gives
  `H = 256 ∏(1-q^n)²⁴`.  The sign of the 4th root is fixed on the imaginary axis in `Assembly`.

Nothing here uses `℘`, `g₂`, `g₃`, `e₁,e₂,e₃` or DLMF 20.4/23. -/
noncomputable section
open Complex Filter Topology SlashInvariantForm ModularForm EisensteinSeries
open UpperHalfPlane hiding I
open scoped Real MatrixGroups ModularForm Manifold
namespace BecknerOnofri.V2.ThetaTail.RouteM

set_option backward.isDefEq.respectTransparency.types false in
lemma slash_T_of {F : ℂ → ℂ} {k : ℤ} (h : ∀ τ : ℂ, F (τ + 1) = F τ) :
    (fun z : ℍ => F (z : ℂ)) ∣[k] ModularGroup.T = fun z : ℍ => F (z : ℂ) := by
  ext z
  suffices hz : F ((z : ℂ) + 1) = F z by
    rw [SL_slash_apply, denom, UpperHalfPlane.modular_T_smul, ModularGroup.T]
    simpa [add_comm] using hz
  exact h _

set_option backward.isDefEq.respectTransparency.types false in
lemma slash_S_of {F : ℂ → ℂ} {k : ℤ} (h : ∀ τ : ℍ, F (-(τ : ℂ)⁻¹) = (τ : ℂ) ^ k * F τ) :
    (fun z : ℍ => F (z : ℂ)) ∣[k] ModularGroup.S = fun z : ℍ => F (z : ℂ) := by
  ext z
  suffices hz : F (-(z : ℂ)⁻¹) * ((z : ℂ) ^ k)⁻¹ = F z by
    rw [SL_slash_apply, UpperHalfPlane.modular_S_smul]
    simpa [denom, ModularGroup.S] using hz
  rw [h z]
  have := z.ne_zero
  field_simp

lemma mdiff_of_differentiableAt (F : ℂ → ℂ) (h : ∀ z : ℂ, 0 < z.im → DifferentiableAt ℂ F z) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun z : ℍ => F (z : ℂ)) := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  refine DifferentiableOn.congr (f := F) (fun z hz => (h z hz).differentiableWithinAt) ?_
  intro z hz
  simp [Function.comp, ofComplex_apply_of_im_pos hz]

lemma neg_inv_eq (τ : ℂ) : -τ⁻¹ = -1 / τ := by rw [neg_div, one_div]

lemma tendsto_coe_comp {f : ℂ → ℂ} {c : ℂ} (h : Tendsto f imInfty (𝓝 c)) :
    Tendsto (fun z : ℍ => f (z : ℂ)) atImInfty (𝓝 c) :=
  h.comp UpperHalfPlane.tendsto_coe_atImInfty

/-! ### M1 -/

/-- `f₆(τ) = ½ (F₂+F₃)(F₃+F₄)(F₄−F₂)`, the right side of `(d12-tail-eq:E6theta)` -/
def f6 (τ : ℂ) : ℂ := e6Poly (F2 τ) (F3 τ) (F4 τ)

lemma f6_add_one (τ : ℂ) : f6 (τ + 1) = f6 τ := by
  unfold f6 e6Poly
  rw [F2_add_one, F3_add_one, F4_add_one]; ring

lemma f6_neg_inv (τ : ℍ) : f6 (-(τ : ℂ)⁻¹) = (τ : ℂ) ^ (6 : ℤ) * f6 τ := by
  have hτ : (τ : ℂ) ≠ 0 := τ.ne_zero
  unfold f6 e6Poly
  rw [neg_inv_eq, F2_neg_inv hτ, F3_neg_inv hτ, F4_neg_inv hτ]
  simp only [zpow_ofNat]; ring

lemma tendsto_f6 : Tendsto f6 imInfty (𝓝 1) := by
  have h := (((tendsto_F2.add tendsto_F3).mul (tendsto_F3.add tendsto_F4)).mul
    (tendsto_F4.sub tendsto_F2)).div_const 2
  have e : (((0 : ℂ) + 1) * (1 + 1) * (1 - 0)) / 2 = 1 := by norm_num
  rw [e] at h
  exact h

lemma differentiableAt_f6 {τ : ℂ} (hτ : 0 < τ.im) : DifferentiableAt ℂ f6 τ := by
  unfold f6 e6Poly
  have a := differentiableAt_F2 hτ
  have b := differentiableAt_F3 hτ
  have c := differentiableAt_F4 hτ
  exact (((a.add b).mul (b.add c)).mul (c.sub a)).div_const 2

/-- the weight-6 level-one modular form `f₆` -/
def f6Form : ModularForm 𝒮ℒ 6 where
  toFun := fun z : ℍ => f6 z
  slash_action_eq' A hA := by
    obtain ⟨A, rfl⟩ := hA
    exact slash_action_generators_SL2Z (slash_S_of f6_neg_inv) (slash_T_of f6_add_one) A
  holo' := mdiff_of_differentiableAt f6 fun z hz => differentiableAt_f6 hz
  bdd_at_cusps' hc := by
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
    intro γ _
    rw [slash_action_generators_SL2Z (slash_S_of f6_neg_inv) (slash_T_of f6_add_one)]
    exact (tendsto_coe_comp tendsto_f6).isBigO_one ℝ

@[simp] lemma f6Form_apply (z : ℍ) : f6Form z = f6 z := rfl

/-- **M1, `(d12-tail-eq:E6theta)`**: `E₆(τ) = ½(ϑ₂⁴+ϑ₃⁴)(ϑ₃⁴+ϑ₄⁴)(ϑ₄⁴−ϑ₂⁴)` on the upper half
plane, via modular-form uniqueness (NOT the Weierstrass-function proof of the manuscript). -/
theorem E6_theta (z : ℍ) : (E₆ : ℍ → ℂ) z = e6Poly (F2 z) (F3 z) (F4 z) := by
  obtain ⟨c, hc⟩ : ∃ c : ℂ, c • E₆ = f6Form :=
    (finrank_eq_one_iff_of_nonzero' _ (E_ne_zero _ ⟨3, rfl⟩)).mp
      (Module.rank_eq_one_iff_finrank_eq_one.mp levelOne_weight_six_rank_one) f6Form
  have hpt : ∀ w : ℍ, c * E₆ w = f6 w := fun w => by
    have := congrArg (fun F : ModularForm 𝒮ℒ 6 => F w) hc
    simpa using this
  have h1 : Tendsto (fun w : ℍ => c * E₆ w) atImInfty (𝓝 (c * 1)) :=
    (tendsto_E_atImInfty (k := 6)).const_mul c
  have h2 : Tendsto (fun w : ℍ => f6 (w : ℂ)) atImInfty (𝓝 1) := tendsto_coe_comp tendsto_f6
  have hc1 : c * 1 = 1 := tendsto_nhds_unique (h1.congr hpt) h2
  have : c = 1 := by simpa using hc1
  have := hpt z
  rw [‹c = 1›, one_mul] at this
  exact this

/-! ### M2 -/

/-- `g₁₂(τ) = (F₂F₃F₄)²`, i.e. `(ϑ₂ϑ₃ϑ₄)⁸` -/
def g12 (τ : ℂ) : ℂ := (F2 τ * F3 τ * F4 τ) ^ 2

lemma g12_add_one (τ : ℂ) : g12 (τ + 1) = g12 τ := by
  unfold g12
  rw [F2_add_one, F3_add_one, F4_add_one]; ring

lemma g12_neg_inv (τ : ℍ) : g12 (-(τ : ℂ)⁻¹) = (τ : ℂ) ^ (12 : ℤ) * g12 τ := by
  have hτ : (τ : ℂ) ≠ 0 := τ.ne_zero
  unfold g12
  rw [neg_inv_eq, F2_neg_inv hτ, F3_neg_inv hτ, F4_neg_inv hτ]
  simp only [zpow_ofNat]; ring

lemma tendsto_g12 : Tendsto g12 imInfty (𝓝 0) := by
  have h := (tendsto_F2.mul tendsto_F3).mul tendsto_F4
  have h2 := h.pow 2
  have e : ((0 : ℂ) * 1 * 1) ^ 2 = 0 := by norm_num
  rw [e] at h2
  exact h2

lemma differentiableAt_g12 {τ : ℂ} (hτ : 0 < τ.im) : DifferentiableAt ℂ g12 τ := by
  unfold g12
  exact (((differentiableAt_F2 hτ).mul (differentiableAt_F3 hτ)).mul (differentiableAt_F4 hτ)).pow 2

/-- the weight-12 level-one cusp form `(ϑ₂ϑ₃ϑ₄)⁸` -/
def g12Form : CuspForm 𝒮ℒ 12 where
  toFun := fun z : ℍ => g12 z
  slash_action_eq' A hA := by
    obtain ⟨A, rfl⟩ := hA
    exact slash_action_generators_SL2Z (slash_S_of g12_neg_inv) (slash_T_of g12_add_one) A
  holo' := mdiff_of_differentiableAt g12 fun z hz => differentiableAt_g12 hz
  zero_at_cusps' hc := by
    rw [OnePoint.isZeroAt_iff_forall_SL2Z hc]
    intro γ _
    rw [slash_action_generators_SL2Z (slash_S_of g12_neg_inv) (slash_T_of g12_add_one)]
    exact tendsto_coe_comp tendsto_g12

@[simp] lemma g12Form_apply (z : ℍ) : g12Form z = g12 z := rfl

/-- **M2**: `(ϑ₂ϑ₃ϑ₄)⁸(τ) = 256 · e^{2πiτ}∏(1-e^{2πinτ})²⁴`, i.e. `Hfun τ = 256 ∏(1-q^n)^24`
for `Im τ > 0`.  This is the 8th-power form of `ϑ₂ϑ₃ϑ₄ = 2η³` (DLMF 20.4.2/20.4.6 in the
manuscript); the 4th-root sign is fixed on the imaginary axis in `Assembly`. -/
theorem Hfun_eq_prod (z : ℍ) :
    Hfun z = 256 * ∏' n : ℕ, (1 - cexp (2 * π * I * ((n : ℂ) + 1) * z)) ^ 24 := by
  obtain ⟨c, hc⟩ := CuspForm.exists_smul_discriminant_of_weight_eq_twelve g12Form
  have hpt : ∀ w : ℍ, c * ModularForm.discriminant w = g12 w := fun w => by
    have := congrArg (fun F : CuspForm 𝒮ℒ 12 => F w) hc
    simpa using this
  have hq : ∀ w : ℍ, ModularForm.discriminant w =
      cexp (2 * π * I * w) * ∏' n : ℕ, (1 - cexp (2 * π * I * ((n : ℂ) + 1) * w)) ^ 24 := by
    intro w
    rw [ModularForm.discriminant_eq_q_prod]
    simp [Function.Periodic.qParam, ModularForm.eta_q_eq_cexp]
  have hpt' : ∀ w : ℍ, c * ∏' n : ℕ, (1 - cexp (2 * π * I * ((n : ℂ) + 1) * w)) ^ 24 =
      Hfun w := by
    intro w
    have h1 := hpt w
    rw [hq w, g12, F2F3F4_sq] at h1
    have hne : cexp (2 * π * I * (w : ℂ)) ≠ 0 := Complex.exp_ne_zero _
    apply mul_left_cancel₀ hne
    linear_combination h1
  have hP : Tendsto (fun w : ℍ => ∏' n : ℕ, (1 - cexp (2 * π * I * ((n : ℂ) + 1) * w)) ^ 24)
      atImInfty (𝓝 1) := by
    refine ModularForm.tendsto_atImInfty_tprod_one_sub_eta_q_pow.congr fun w => ?_
    simp [ModularForm.eta_q_eq_cexp]
  have h1 := hP.const_mul c
  have h2 : Tendsto (fun w : ℍ => Hfun (w : ℂ)) atImInfty (𝓝 256) := tendsto_coe_comp tendsto_Hfun
  have : c * 1 = 256 := tendsto_nhds_unique (h1.congr hpt') h2
  rw [← hpt' z]
  rw [mul_one] at this
  rw [this]

end BecknerOnofri.V2.ThetaTail.RouteM
