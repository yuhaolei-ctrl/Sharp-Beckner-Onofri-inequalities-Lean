module

public import BecknerOnofri.V2.ThetaTail.RouteM.ModularForms

@[expose] public section

/-! # Route M, part M4 (A): the displayed equations of Appendix A.1, as separate lemmas

For `s : ℍ` write `a = ϑ₃(2s)²` (`alphaT s`) and `b = ϑ₂(2s)²` (`betaT s`) (so `E₆(s)` is the
manuscript's `E₆(τ)` with `s = τ`, and `2s` plays the role of the manuscript's `2τ`).

* `thetaalg1`  : `(d12-tail-eq:thetaalg1)`  `E₆(τ) = a⁶+b⁶−33a⁴b²−33a²b⁴`
* `thetaalg2`  : `(d12-tail-eq:thetaalg2)`  `64E₆(4τ) = 64a⁶−96a⁴b²+30a²b⁴+b⁶`
* `theta_product_sq` : `16η(2τ)¹² = a²b²(a²−b²)` in the form `ϑ₂⁴ϑ₃⁴ϑ₄⁴(2τ) = a²b²(a²−b²)`
  (the identification with `16 q∏(1−q^{2m})¹²` is `Assembly2`).

Their *proofs* differ from the written proof: `E6_theta` and the theta–eta product identity come
from modular-form uniqueness (`ModularForms.lean`), not from DLMF 23.x / 20.4.x. -/
noncomputable section
open Complex Filter Topology SlashInvariantForm ModularForm EisensteinSeries
open UpperHalfPlane hiding I
open scoped Real MatrixGroups ModularForm
namespace BecknerOnofri.V2.ThetaTail.RouteM

/-- `s ↦ 2s` on the upper half plane -/
def dbl (s : ℍ) : ℍ := ⟨2 * (s : ℂ), by
  have := s.2
  simpa using mul_pos two_pos (show (0 : ℝ) < (s : ℂ).im from this)⟩

@[simp] lemma coe_dbl (s : ℍ) : ((dbl s : ℍ) : ℂ) = 2 * (s : ℂ) := rfl

lemma im_pos' (s : ℍ) : 0 < (s : ℂ).im := s.2

/-- `(d12-tail-eq:thetaalg1)` -/
theorem thetaalg1 (s : ℍ) :
    (E₆ : ℍ → ℂ) s = alphaT s ^ 6 + betaT s ^ 6 - 33 * alphaT s ^ 4 * betaT s ^ 2
      - 33 * alphaT s ^ 2 * betaT s ^ 4 := by
  rw [E6_theta, F2_eq (im_pos' s), F3_eq (im_pos' s), F4_eq (im_pos' s)]
  exact thetaAlg1 (alphaT s) (betaT s)

lemma cexp_pi_I_two_mul (s : ℂ) : cexp (π * I * (2 * s)) = cexp (π * I * s) ^ 2 := by
  rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring

/-- the relations `a = c + d` and `b² = 4cd` between the data at `s` and at `2s`
(`c = ϑ₃(4τ)²`, `d = ϑ₂(4τ)²`) -/
theorem alpha_eq_add (s : ℍ) : alphaT s = alphaT (dbl s) + betaT (dbl s) := by
  unfold alphaT betaT
  simpa using jt3_sq_duplication (τ := 2 * (s : ℂ)) (im_pos' (dbl s))

theorem beta_sq_eq (s : ℍ) : betaT s ^ 2 = 4 * alphaT (dbl s) * betaT (dbl s) := by
  unfold alphaT betaT
  have h := jt2_sq_duplication (τ := 2 * (s : ℂ)) (im_pos' (dbl s))
  simp only [coe_dbl]
  have e : jt2 (2 * s) ^ 4 = (jt2 (2 * s) ^ 2) ^ 2 := by ring
  calc (cexp (π * I * s) * jt2 (2 * s) ^ 2) ^ 2
      = cexp (π * I * s) ^ 2 * jt2 (2 * s) ^ 4 := by ring
    _ = cexp (π * I * (2 * s)) * (2 * jt2 (2 * (2 * s)) * jt3 (2 * (2 * s))) ^ 2 := by
        rw [e, h, cexp_pi_I_two_mul]
    _ = _ := by ring

/-- `(d12-tail-eq:thetaalg2)`: `64 E₆(4τ) = 64a⁶ − 96a⁴b² + 30a²b⁴ + b⁶`. -/
theorem thetaalg2 (s : ℍ) :
    64 * (E₆ : ℍ → ℂ) (dbl (dbl s)) =
      64 * alphaT s ^ 6 - 96 * alphaT s ^ 4 * betaT s ^ 2 + 30 * alphaT s ^ 2 * betaT s ^ 4
        + betaT s ^ 6 := by
  set c := alphaT (dbl s) with hc
  set d := betaT (dbl s) with hd
  have hu : 0 < ((dbl (dbl s) : ℍ) : ℂ).im := im_pos' _
  have hF3 : F3 (dbl (dbl s) : ℍ) = c ^ 2 := by
    rw [hc]; unfold F3 alphaT; simp only [coe_dbl]; ring
  have hF2 : F2 (dbl (dbl s) : ℍ) = d ^ 2 := by
    rw [hd]; unfold F2 betaT; simp only [coe_dbl]
    rw [cexp_pi_I_two_mul (2 * (s : ℂ))]
    ring
  have hF4 : F4 (dbl (dbl s) : ℍ) = c ^ 2 - d ^ 2 := by
    have := F3_sub_F4_eq_F2 hu
    rw [hF3, hF2] at this
    linear_combination -this
  have hE : (E₆ : ℍ → ℂ) (dbl (dbl s)) = e6Poly (d ^ 2) (c ^ 2) (c ^ 2 - d ^ 2) := by
    rw [E6_theta, hF2, hF3, hF4]
  have h1 := thetaAlg2 c d
  have ha : alphaT s = c + d := alpha_eq_add s
  have hb : betaT s ^ 2 = 4 * c * d := beta_sq_eq s
  rw [hE, h1]
  have hb4 : betaT s ^ 4 = (4 * c * d) ^ 2 := by rw [show betaT s ^ 4 = (betaT s ^ 2) ^ 2 by ring, hb]
  have hb6 : betaT s ^ 6 = (4 * c * d) ^ 3 := by rw [show betaT s ^ 6 = (betaT s ^ 2) ^ 3 by ring, hb]
  rw [hb4, hb6, hb, ha]

/-- the product `ϑ₂⁴ϑ₃⁴ϑ₄⁴ (2τ) = a²b²(a²−b²)` (the algebraic half of
`16η(2τ)¹² = a²b²(a²−b²)`; its equality with `16 q ∏(1−q^{2m})^12` is in `Assembly2`) -/
theorem theta_product_sq (s : ℍ) :
    F2 (dbl s : ℍ) * F3 (dbl s : ℍ) * F4 (dbl s : ℍ) =
      alphaT s ^ 2 * betaT s ^ 2 * (alphaT s ^ 2 - betaT s ^ 2) := by
  have hu := im_pos' (dbl s)
  have e3 : F3 (dbl s : ℍ) = alphaT s ^ 2 := by unfold F3 alphaT; simp only [coe_dbl]; ring
  have e2 : F2 (dbl s : ℍ) = betaT s ^ 2 := by
    unfold F2 betaT; simp only [coe_dbl]
    rw [cexp_pi_I_two_mul]; ring
  have e4 : F4 (dbl s : ℍ) = alphaT s ^ 2 - betaT s ^ 2 := by
    have := F3_sub_F4_eq_F2 hu
    rw [e3, e2] at this; linear_combination -this
  rw [e2, e3, e4]; ring

end BecknerOnofri.V2.ThetaTail.RouteM
