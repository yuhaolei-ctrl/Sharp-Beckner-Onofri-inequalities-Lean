module

public import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable
public import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
public import BecknerOnofri.V2.ThetaTail.FiniteAlgebra

@[expose] public section

/-! # Route M, part 1: the three theta constants and their `T`/`S` transformation laws

HONEST ROUTE NOTE.  This file belongs to *Route M* (modular-form uniqueness), which is NOT the
route written in Appendix A.1 (that route cites DLMF 23.8.1, 23.6.2-4, 23.3.7, 20.7.5, 20.4.2,
20.4.6 and Weierstrass `℘`; none of that is formalized here).

Conventions (DLMF nome `e^{πiτ}`): `ϑ₃(τ) = ∑ e^{πi n²τ} = jacobiTheta τ`,
`ϑ₄(τ) = ∑ (-1)^n e^{πi n²τ} = jacobiTheta₂ (1/2) τ`,
`ϑ₂(τ) = e^{πiτ/4} ∑ e^{πi(n²+n)τ} = e^{πiτ/4} · jacobiTheta₂ (τ/2) τ`.
We only ever use the fourth powers `F_j = ϑ_j⁴` and, to avoid fractional powers of `e^{πiτ}`,
`F₂ τ = e^{πiτ} · (jacobiTheta₂ (τ/2) τ)⁴`.
All laws are proved from Mathlib's `jacobiTheta₂_functional_equation`, `jacobiTheta₂_add_left`,
`jacobiTheta₂_neg_left`. -/
noncomputable section
open Complex Filter Topology
open scoped Real
namespace BecknerOnofri.V2.ThetaTail.RouteM

/-- `ϑ₃(τ)` -/
def jt3 (τ : ℂ) : ℂ := jacobiTheta₂ 0 τ
/-- `ϑ₄(τ)` -/
def jt4 (τ : ℂ) : ℂ := jacobiTheta₂ (1 / 2) τ
/-- `ϑ₂(τ) / e^{πiτ/4}` -/
def jt2 (τ : ℂ) : ℂ := jacobiTheta₂ (τ / 2) τ

/-- `ϑ₃⁴` -/
def F3 (τ : ℂ) : ℂ := jt3 τ ^ 4
/-- `ϑ₄⁴` -/
def F4 (τ : ℂ) : ℂ := jt4 τ ^ 4
/-- `ϑ₂⁴ = e^{πiτ} (ϑ₂ / e^{πiτ/4})⁴` -/
def F2 (τ : ℂ) : ℂ := cexp (π * I * τ) * jt2 τ ^ 4

lemma jt3_eq_jacobiTheta (τ : ℂ) : jt3 τ = jacobiTheta τ := (jacobiTheta_eq_jacobiTheta₂ τ).symm

/-- `θ(τ+1)`-type shift: `jacobiTheta₂ z (τ+1) = jacobiTheta₂ (z + 1/2) τ`. -/
lemma jacobiTheta₂_add_one_right (z τ : ℂ) :
    jacobiTheta₂ z (τ + 1) = jacobiTheta₂ (z + 1 / 2) τ := by
  unfold jacobiTheta₂ jacobiTheta₂_term
  refine tsum_congr fun n => ?_
  obtain ⟨m, hm⟩ := Int.even_mul_pred_self n
  have hm' : (n : ℂ) * (n - 1) = m + m := by exact_mod_cast hm
  rw [Complex.exp_eq_exp_iff_exists_int]
  refine ⟨m, ?_⟩
  linear_combination (π * I) * hm'

lemma jt3_add_one (τ : ℂ) : jt3 (τ + 1) = jt4 τ := by
  unfold jt3 jt4
  rw [jacobiTheta₂_add_one_right, zero_add]

lemma jt4_add_one (τ : ℂ) : jt4 (τ + 1) = jt3 τ := by
  unfold jt3 jt4
  rw [jacobiTheta₂_add_one_right, show (1 / 2 : ℂ) + 1 / 2 = 0 + 1 by norm_num,
    jacobiTheta₂_add_left]

lemma jt2_add_one (τ : ℂ) : jt2 (τ + 1) = jt2 τ := by
  unfold jt2
  rw [jacobiTheta₂_add_one_right, show (τ + 1) / 2 + 1 / 2 = τ / 2 + 1 by ring,
    jacobiTheta₂_add_left]

lemma F3_add_one (τ : ℂ) : F3 (τ + 1) = F4 τ := by
  unfold F3 F4; rw [jt3_add_one]

lemma F4_add_one (τ : ℂ) : F4 (τ + 1) = F3 τ := by
  unfold F3 F4; rw [jt4_add_one]

lemma F2_add_one (τ : ℂ) : F2 (τ + 1) = -F2 τ := by
  unfold F2
  rw [jt2_add_one, mul_add, mul_one, Complex.exp_add]
  have : cexp (π * I) = -1 := Complex.exp_pi_mul_I
  rw [this]; ring

/-! ### The `S` transformation -/

/-- the square root `(-iτ)^{1/2}` appearing in the functional equation -/
def sq (τ : ℂ) : ℂ := (-I * τ) ^ (1 / 2 : ℂ)

lemma sq_ne_zero {τ : ℂ} (hτ : τ ≠ 0) : sq τ ≠ 0 := by
  unfold sq
  rw [Ne, cpow_eq_zero_iff, not_and_or]
  exact Or.inl (mul_ne_zero (neg_ne_zero.mpr I_ne_zero) hτ)

lemma sq_pow_four (τ : ℂ) : sq τ ^ 4 = -τ ^ 2 := by
  unfold sq
  have h : ((-I * τ) ^ (1 / 2 : ℂ)) ^ 2 = -I * τ := by
    rw [← Complex.cpow_nat_mul]
    norm_num
  calc ((-I * τ) ^ (1 / 2 : ℂ)) ^ 4 = (((-I * τ) ^ (1 / 2 : ℂ)) ^ 2) ^ 2 := by ring
    _ = -τ ^ 2 := by rw [h]; ring_nf; rw [I_sq]; ring

/-- the functional equation in the form needed for `S : τ ↦ -1/τ`. -/
lemma jacobiTheta₂_neg_inv (z : ℂ) {τ : ℂ} (hτ : τ ≠ 0) :
    jacobiTheta₂ z (-1 / τ) = sq τ * cexp (π * I * z ^ 2 * τ) * jacobiTheta₂ (z * τ) τ := by
  have h := jacobiTheta₂_functional_equation (z * τ) τ
  rw [mul_div_cancel_right₀ _ hτ] at h
  have hr := sq_ne_zero hτ
  have hE : cexp (-π * I * (z * τ) ^ 2 / τ) * cexp (π * I * z ^ 2 * τ) = 1 := by
    rw [← Complex.exp_add]
    convert Complex.exp_zero using 2
    field_simp
    ring
  change jacobiTheta₂ (z * τ) τ = 1 / sq τ * cexp (-π * I * (z * τ) ^ 2 / τ) * _ at h
  rw [h]
  calc jacobiTheta₂ z (-1 / τ)
      = (cexp (-π * I * (z * τ) ^ 2 / τ) * cexp (π * I * z ^ 2 * τ)) * jacobiTheta₂ z (-1 / τ) := by
        rw [hE, one_mul]
    _ = _ := by field_simp

lemma jt3_neg_inv {τ : ℂ} (hτ : τ ≠ 0) : jt3 (-1 / τ) = sq τ * jt3 τ := by
  unfold jt3
  rw [jacobiTheta₂_neg_inv 0 hτ]
  simp

lemma jt4_neg_inv {τ : ℂ} (hτ : τ ≠ 0) :
    jt4 (-1 / τ) = sq τ * cexp (π * I * τ / 4) * jt2 τ := by
  unfold jt4 jt2
  rw [jacobiTheta₂_neg_inv _ hτ]
  have e1 : (1 / 2 : ℂ) * τ = τ / 2 := by ring
  have e2 : cexp (π * I * (1 / 2 : ℂ) ^ 2 * τ) = cexp (π * I * τ / 4) := by congr 1; ring
  rw [e1, e2]

lemma jt2_neg_inv {τ : ℂ} (hτ : τ ≠ 0) :
    jt2 (-1 / τ) = sq τ * cexp (π * I / (4 * τ)) * jt4 τ := by
  unfold jt2 jt4
  rw [jacobiTheta₂_neg_inv _ hτ]
  have h1 : (-1 / τ / 2) * τ = -(1 / 2) := by field_simp
  rw [h1, jacobiTheta₂_neg_left]
  have e : cexp (π * I * (-1 / τ / 2) ^ 2 * τ) = cexp (π * I / (4 * τ)) := by
    congr 1; field_simp; ring
  rw [e]

lemma F3_neg_inv {τ : ℂ} (hτ : τ ≠ 0) : F3 (-1 / τ) = -τ ^ 2 * F3 τ := by
  unfold F3
  rw [jt3_neg_inv hτ, mul_pow, sq_pow_four]

lemma cexp_pow_four (a : ℂ) : cexp a ^ 4 = cexp (4 * a) := by
  rw [← Complex.exp_nat_mul]; norm_num

lemma F4_neg_inv {τ : ℂ} (hτ : τ ≠ 0) : F4 (-1 / τ) = -τ ^ 2 * F2 τ := by
  unfold F4 F2
  rw [jt4_neg_inv hτ, mul_pow, mul_pow, sq_pow_four, cexp_pow_four]
  have : cexp (4 * (π * I * τ / 4)) = cexp (π * I * τ) := by congr 1; ring
  rw [this]; ring

lemma F2_neg_inv {τ : ℂ} (hτ : τ ≠ 0) : F2 (-1 / τ) = -τ ^ 2 * F4 τ := by
  unfold F4 F2
  rw [jt2_neg_inv hτ, mul_pow, mul_pow, sq_pow_four, cexp_pow_four]
  have : cexp (π * I * (-1 / τ)) * cexp (4 * (π * I / (4 * τ))) = 1 := by
    rw [← Complex.exp_add]
    convert Complex.exp_zero using 2
    field_simp
    ring
  linear_combination (-τ ^ 2 * jt4 τ ^ 4) * this

end BecknerOnofri.V2.ThetaTail.RouteM
