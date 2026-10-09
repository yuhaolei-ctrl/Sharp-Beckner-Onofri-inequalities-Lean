module

public import BecknerOnofri.V2.ThetaTail.RouteM.Assembly2

@[expose] public section

/-! # Route M, final assembly: `TwelveSquareIdentity` (unconditional)

`twelve_square_routeM : TwelveSquareIdentity` proves the manuscript identity
`(d12-tail-eq:theta12)` by the chain (each step its own lemma):

1. `E6_theta`        `(d12-tail-eq:E6theta)`        [M1, modular-form uniqueness]
2. `thetaalg1`       `(d12-tail-eq:thetaalg1)`      [theta duplication, M3]
3. `thetaalg2`       `(d12-tail-eq:thetaalg2)`      [theta duplication, M3]
4. `theta_product_sq` + `theta_eta_product`  `16η(2τ)¹² = a²b²(a²−b²)`   [M2]
5. `theta12_elimination` (`FiniteAlgebra`)       the final polynomial elimination
6. `E6_qexp`         `E₆ = 1 − 504∑σ₅(m)qᵐ`          [Lambert conversion, Mathlib]

This is **Route M**, not the written route (see `Assembly2` docstring). -/
noncomputable section
open Complex Filter Topology SlashInvariantForm ModularForm EisensteinSeries
open UpperHalfPlane hiding I
open scoped Real MatrixGroups ModularForm ArithmeticFunction.sigma
namespace BecknerOnofri.V2.ThetaTail.RouteM

/-- **The twelve-square identity `(d12-tail-eq:theta12)`**, unconditionally, via Route M. -/
theorem twelve_square_routeM : TwelveSquareIdentity := by
  intro q hq0 hq1
  have hzim := zq_im hq0 hq1
  set z := zq q with hz
  let sH : ℍ := ⟨z / 2, by
    have : (z / 2).im = z.im / 2 := by simp
    rw [this]; linarith⟩
  have hs : (sH : ℂ) = z / 2 := rfl
  have hd1 : 2 * (sH : ℂ) = z := by rw [hs]; ring
  have hd1' : ((dbl sH : ℍ) : ℂ) = z := by rw [coe_dbl, hd1]
  have hd2 : (((dbl (dbl sH)) : ℍ) : ℂ) = 2 * z := by rw [coe_dbl, hd1']
  have hq1c : cexp (2 * π * Complex.I * (sH : ℂ)) = (q : ℂ) := by
    rw [← cexp_pi_I_zq hq0, ← hz, hs]; congr 1; ring
  have hq4c : cexp (2 * π * Complex.I * ((dbl (dbl sH) : ℍ) : ℂ)) = (q : ℂ) ^ 4 := by
    have := cexp_nat_zq hq0 4
    rw [← hz] at this
    push_cast at this
    rw [hd2, ← this]; congr 1; ring
  have ha : alphaT sH = jt3 z ^ 2 := by unfold alphaT; rw [hd1]
  -- the displayed equations
  have E1 := thetaalg1 sH
  have E2 := thetaalg2 sH
  have T1 := theta_product_sq sH
  rw [hd1'] at T1
  have T2 := theta_eta_product hq0 hq1
  rw [← hz] at T2
  have q1 := E6_qexp sH
  rw [hq1c] at q1
  have q4 := E6_qexp (dbl (dbl sH))
  rw [hq4c] at q4
  have el := theta12_elimination (alphaT sH) (betaT sH ^ 2)
  have hmain : alphaT sH ^ 6 = -(E₆ : ℍ → ℂ) sH / 63 + 64 * (E₆ : ℍ → ℂ) (dbl (dbl sH)) / 63
      + alphaT sH ^ 2 * betaT sH ^ 2 * (alphaT sH ^ 2 - betaT sH ^ 2) := by
    linear_combination (-1) * el + (1 / 63) * E1 - (1 / 63) * E2
  -- casts
  have hth : jt3 z = ((theta q : ℝ) : ℂ) := jt3_zq hq0
  have S1c : ∑' n : ℕ+, ((ArithmeticFunction.sigma 5 n : ℕ) : ℂ) * (q : ℂ) ^ (n : ℕ) =
      ((∑' m : ℕ+, sigma5 m * q ^ (m : ℕ) : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]
    refine tsum_congr fun m => ?_
    simp [sigma5]
  have S4c : ∑' n : ℕ+, ((ArithmeticFunction.sigma 5 n : ℕ) : ℂ) * ((q : ℂ) ^ 4) ^ (n : ℕ) =
      ((∑' m : ℕ+, sigma5 m * q ^ (4 * (m : ℕ)) : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]
    refine tsum_congr fun m => ?_
    simp [sigma5, pow_mul]
  have hPm : (∏' m : ℕ+, (1 - q ^ (2 * (m : ℕ))) ^ 12 : ℝ) =
      (∏' n : ℕ, (1 - q ^ (2 * (n + 1)))) ^ 12 := by
    rw [tprod_pnat_eq_tprod_succ (f := fun m : ℕ => (1 - q ^ (2 * m)) ^ 12)]
    exact (multipliable_g hq0.le hq1).tprod_pow 12
  rw [S1c] at q1
  rw [S4c] at q4
  apply Complex.ofReal_injective
  rw [hPm]
  push_cast
  have h12 : (jt3 z) ^ 12 = alphaT sH ^ 6 := by rw [ha]; ring
  rw [hth] at h12
  push_cast at h12 T2 q1 q4 ⊢
  rw [h12, hmain, q1, q4, ← T1, T2]
  ring

end BecknerOnofri.V2.ThetaTail.RouteM
