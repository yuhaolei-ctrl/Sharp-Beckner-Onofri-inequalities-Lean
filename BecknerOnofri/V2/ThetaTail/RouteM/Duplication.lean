module

public import BecknerOnofri.V2.ThetaTail.RouteM.Basic
public import Mathlib.Analysis.Normed.Ring.InfiniteSum

@[expose] public section

/-! # Route M, part M3: theta duplication (DLMF 20.7 type identities), from lattice sums

For `0 < Im τ`, with `ϑ₃(τ)² = a+b`-type relations (this is the content that the written proof
cites as "theta reduction identities [DLMF 20.7.12, 20.7.14]"; here they are proved directly by
splitting the lattice sum `ℤ×ℤ` according to the parity of `m+n`):

* `jt3_sq_duplication`: `ϑ₃(τ)² = ϑ₃(2τ)² + e^{πiτ} jt2(2τ)²`  (i.e. `ϑ₃(τ)² = ϑ₃(2τ)²+ϑ₂(2τ)²`),
* `jt4_sq_duplication`: `ϑ₄(τ)² = ϑ₃(2τ)² − e^{πiτ} jt2(2τ)²`,
* `jt2_sq_duplication`: `jt2(τ)² = 2 jt2(2τ) ϑ₃(2τ)` (i.e. `ϑ₂(τ)² = 2ϑ₂(2τ)ϑ₃(2τ)`),
* `F3_sub_F4_eq_F2`: Jacobi's quartic identity `ϑ₃⁴ = ϑ₂⁴ + ϑ₄⁴` as a consequence. -/
noncomputable section
open Complex Filter Topology
open scoped Real
namespace BecknerOnofri.V2.ThetaTail.RouteM

/-- inverse of the parity bijection, written as a separate function to keep `if` clean -/
def zzInv (m n : ℤ) : (ℤ × ℤ) ⊕ (ℤ × ℤ) :=
  if (m + n) % 2 = 0 then Sum.inl ((m + n) / 2, (m - n) / 2)
  else Sum.inr ((m + n - 1) / 2, (m - n - 1) / 2)

lemma zzInv_even {m n : ℤ} (h : (m + n) % 2 = 0) :
    zzInv m n = Sum.inl ((m + n) / 2, (m - n) / 2) := by
  unfold zzInv; simp [h]

lemma zzInv_odd {m n : ℤ} (h : ¬ (m + n) % 2 = 0) :
    zzInv m n = Sum.inr ((m + n - 1) / 2, (m - n - 1) / 2) := by
  unfold zzInv; simp [h]

/-- the parity bijection `ℤ² ⊕ ℤ² ≃ ℤ²`, `(u,v) ↦ (u+v, u-v)` or `(u+v+1, u-v)` -/
def zzEquiv : (ℤ × ℤ) ⊕ (ℤ × ℤ) ≃ ℤ × ℤ where
  toFun := Sum.elim (fun u => (u.1 + u.2, u.1 - u.2)) (fun u => (u.1 + u.2 + 1, u.1 - u.2))
  invFun p := zzInv p.1 p.2
  left_inv := by
    rintro (⟨a, b⟩ | ⟨a, b⟩)
    · show zzInv (a + b) (a - b) = _
      rw [zzInv_even (by omega)]
      simp only [Sum.inl.injEq, Prod.mk.injEq]; omega
    · show zzInv (a + b + 1) (a - b) = _
      rw [zzInv_odd (by omega)]
      simp only [Sum.inr.injEq, Prod.mk.injEq]; omega
  right_inv := by
    rintro ⟨m, n⟩
    by_cases h : (m + n) % 2 = 0
    · show Sum.elim _ _ (zzInv m n) = _
      rw [zzInv_even h]
      simp only [Sum.elim_inl, Prod.mk.injEq]; omega
    · show Sum.elim _ _ (zzInv m n) = _
      rw [zzInv_odd h]
      simp only [Sum.elim_inr, Prod.mk.injEq]; omega

lemma split_prod (f g : ℤ → ℂ) (hf : Summable fun n => ‖f n‖) (hg : Summable fun n => ‖g n‖) :
    (∑' n, f n) * (∑' n, g n) =
      ∑' u : ℤ × ℤ, f (u.1 + u.2) * g (u.1 - u.2) +
        ∑' u : ℤ × ℤ, f (u.1 + u.2 + 1) * g (u.1 - u.2) := by
  rw [tsum_mul_tsum_of_summable_norm hf hg]
  have hs := summable_mul_of_summable_norm hf hg
  have h1 : Summable ((fun x : ℤ × ℤ => f x.1 * g x.2) ∘ zzEquiv) := (zzEquiv.summable_iff).2 hs
  have e := zzEquiv.tsum_eq (fun x : ℤ × ℤ => f x.1 * g x.2)
  rw [← e]
  change ∑' c, ((fun x : ℤ × ℤ => f x.1 * g x.2) ∘ zzEquiv) c = _
  rw [Summable.tsum_sum (h1.comp_injective Sum.inl_injective) (h1.comp_injective Sum.inr_injective)]
  rfl

/-- the terms `e^{πi n² τ}` -/
def tA (τ : ℂ) (n : ℤ) : ℂ := cexp (π * I * (n : ℂ) ^ 2 * τ)
/-- the terms `e^{πi (n²+n) τ}` -/
def tC (τ : ℂ) (n : ℤ) : ℂ := cexp (π * I * ((n : ℂ) ^ 2 + n) * τ)

lemma jt3_eq_tsum (τ : ℂ) : jt3 τ = ∑' n : ℤ, tA τ n := by
  rw [jt3_eq_jacobiTheta]; rfl

lemma jt2_eq_tsum (τ : ℂ) : jt2 τ = ∑' n : ℤ, tC τ n := by
  unfold jt2 jacobiTheta₂ jacobiTheta₂_term tC
  refine tsum_congr fun n => ?_
  congr 1; ring

lemma summable_norm_tA {τ : ℂ} (hτ : 0 < τ.im) : Summable fun n => ‖tA τ n‖ := by
  have := (summable_jacobiTheta₂_term_iff 0 τ).2 hτ
  have h2 := (summable_norm_iff.2 this)
  refine h2.congr fun n => ?_
  unfold jacobiTheta₂_term tA
  congr 2; ring

lemma summable_norm_tC {τ : ℂ} (hτ : 0 < τ.im) : Summable fun n => ‖tC τ n‖ := by
  have := (summable_jacobiTheta₂_term_iff (τ / 2) τ).2 hτ
  have h2 := (summable_norm_iff.2 this)
  refine h2.congr fun n => ?_
  unfold jacobiTheta₂_term tC
  congr 2; ring

lemma tA_add_mul (τ : ℂ) (a b : ℤ) : tA τ a * tA τ b = cexp (π * I * ((a : ℂ) ^ 2 + b ^ 2) * τ) := by
  unfold tA; rw [← Complex.exp_add]; congr 1; ring

/-- `ϑ₃(τ)² = ϑ₃(2τ)² + e^{πiτ} jt2(2τ)²` -/
theorem jt3_sq_duplication {τ : ℂ} (hτ : 0 < τ.im) :
    jt3 τ ^ 2 = jt3 (2 * τ) ^ 2 + cexp (π * I * τ) * jt2 (2 * τ) ^ 2 := by
  have h2 : 0 < (2 * τ).im := by simp; linarith
  rw [pow_two, jt3_eq_tsum, split_prod _ _ (summable_norm_tA hτ) (summable_norm_tA hτ)]
  rw [pow_two, pow_two, jt3_eq_tsum, jt2_eq_tsum,
    tsum_mul_tsum_of_summable_norm (summable_norm_tA h2) (summable_norm_tA h2),
    tsum_mul_tsum_of_summable_norm (summable_norm_tC h2) (summable_norm_tC h2),
    ← tsum_mul_left]
  congr 1
  · refine tsum_congr fun u => ?_
    rw [tA_add_mul]; unfold tA; rw [← Complex.exp_add]; congr 1; push_cast; ring
  · refine tsum_congr fun u => ?_
    rw [tA_add_mul]; unfold tC; rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; push_cast; ring

lemma jt3_add_two (τ : ℂ) : jt3 (τ + 2) = jt3 τ := by
  rw [show τ + 2 = (τ + 1) + 1 by ring, jt3_add_one, jt4_add_one]

lemma jt2_add_two (τ : ℂ) : jt2 (τ + 2) = jt2 τ := by
  rw [show τ + 2 = (τ + 1) + 1 by ring, jt2_add_one, jt2_add_one]

/-- `ϑ₄(τ)² = ϑ₃(2τ)² − e^{πiτ} jt2(2τ)²` -/
theorem jt4_sq_duplication {τ : ℂ} (hτ : 0 < τ.im) :
    jt4 τ ^ 2 = jt3 (2 * τ) ^ 2 - cexp (π * I * τ) * jt2 (2 * τ) ^ 2 := by
  have h := jt3_sq_duplication (τ := τ + 1) (by simpa using hτ)
  rw [jt3_add_one, show 2 * (τ + 1) = 2 * τ + 2 by ring, jt3_add_two, jt2_add_two,
    mul_add, mul_one, Complex.exp_add, Complex.exp_pi_mul_I] at h
  rw [h]; ring

/-- `jt2(τ)² = 2 jt2(2τ) ϑ₃(2τ)` -/
theorem jt2_sq_duplication {τ : ℂ} (hτ : 0 < τ.im) :
    jt2 τ ^ 2 = 2 * jt2 (2 * τ) * jt3 (2 * τ) := by
  have h2 : 0 < (2 * τ).im := by simp; linarith
  rw [pow_two, jt2_eq_tsum, split_prod _ _ (summable_norm_tC hτ) (summable_norm_tC hτ)]
  have e1 : ∑' u : ℤ × ℤ, tC τ (u.1 + u.2) * tC τ (u.1 - u.2) = jt2 (2 * τ) * jt3 (2 * τ) := by
    rw [jt2_eq_tsum, jt3_eq_tsum,
      tsum_mul_tsum_of_summable_norm (summable_norm_tC h2) (summable_norm_tA h2)]
    refine tsum_congr fun u => ?_
    unfold tC tA; rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; push_cast; ring
  have e2 : ∑' u : ℤ × ℤ, tC τ (u.1 + u.2 + 1) * tC τ (u.1 - u.2) = jt2 (2 * τ) * jt3 (2 * τ) := by
    have hs : Summable fun n => ‖tA (2 * τ) (n + 1)‖ :=
      (summable_norm_tA h2).comp_injective (add_left_injective 1)
    have hsh : ∑' n : ℤ, tA (2 * τ) (n + 1) = ∑' n : ℤ, tA (2 * τ) n :=
      (Equiv.addRight (1 : ℤ)).tsum_eq (tA (2 * τ))
    rw [jt2_eq_tsum, jt3_eq_tsum, ← hsh, mul_comm,
      tsum_mul_tsum_of_summable_norm hs (summable_norm_tC h2)]
    refine tsum_congr fun u => ?_
    unfold tC tA; rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; push_cast; ring
  rw [e1, e2]; ring

/-- the two quantities `α = ϑ₃(2τ)²`, `β = ϑ₂(2τ)²` appearing in the duplication formulas -/
def alphaT (τ : ℂ) : ℂ := jt3 (2 * τ) ^ 2
def betaT (τ : ℂ) : ℂ := cexp (π * I * τ) * jt2 (2 * τ) ^ 2

theorem F3_eq {τ : ℂ} (hτ : 0 < τ.im) : F3 τ = (alphaT τ + betaT τ) ^ 2 := by
  unfold F3 alphaT betaT
  rw [← jt3_sq_duplication hτ]; ring

theorem F4_eq {τ : ℂ} (hτ : 0 < τ.im) : F4 τ = (alphaT τ - betaT τ) ^ 2 := by
  unfold F4 alphaT betaT
  rw [← jt4_sq_duplication hτ]; ring

theorem F2_eq {τ : ℂ} (hτ : 0 < τ.im) : F2 τ = 4 * alphaT τ * betaT τ := by
  unfold F2 alphaT betaT
  have : jt2 τ ^ 4 = (jt2 τ ^ 2) ^ 2 := by ring
  rw [this, jt2_sq_duplication hτ]; ring

/-- Jacobi's identity `ϑ₃⁴ = ϑ₂⁴ + ϑ₄⁴` (a consequence of the three duplication formulas). -/
theorem F3_sub_F4_eq_F2 {τ : ℂ} (hτ : 0 < τ.im) : F3 τ - F4 τ = F2 τ := by
  rw [F3_eq hτ, F4_eq hτ, F2_eq hτ]; ring

end BecknerOnofri.V2.ThetaTail.RouteM
