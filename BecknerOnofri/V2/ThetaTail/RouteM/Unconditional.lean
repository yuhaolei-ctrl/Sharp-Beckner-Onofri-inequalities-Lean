module

public import BecknerOnofri.V2.ThetaTail.RouteM.Final
public import BecknerOnofri.V2.ThetaTail.ScalarTail
public import BecknerOnofri.V2.ThetaTail.SmallG
public import Mathlib.NumberTheory.TsumDivisorsAntidiagonal

@[expose] public section

/-! # Unconditional versions of the G07 theorems (Route M)

`TwelveSquareIdentity` is now a theorem (`RouteM.twelve_square_routeM`, Route M = modular-form
uniqueness, NOT the written Weierstrass route), so the conditional theorems of the package
specialize to unconditional ones.  The `_of_twelveSquare` originals are kept untouched. -/
noncomputable section
namespace BecknerOnofri.V2.ThetaTail.RouteM

/-- The Lambert conversion of Appendix A.1: `∑ n⁵qⁿ/(1−qⁿ) = ∑ σ₅(m)q^m` (`0 ≤ q < 1`);
Mathlib's `tsum_pow_div_one_sub_eq_tsum_sigma`, specialized. -/
theorem lambert_conversion {q : ℝ} (h0 : 0 ≤ q) (h1 : q < 1) :
    ∑' n : ℕ+, ((n : ℕ) : ℝ) ^ 5 * q ^ (n : ℕ) / (1 - q ^ (n : ℕ)) =
      ∑' m : ℕ+, sigma5 m * q ^ (m : ℕ) := by
  have h := tsum_pow_div_one_sub_eq_tsum_sigma (𝕜 := ℝ) (r := q)
    (by simpa [abs_of_nonneg h0] using h1) 5
  simpa [sigma5] using h

theorem G_two_fifths_lt : G (2 / 5) < 23 / 200 := G_two_fifths_lt_of_twelveSquare twelve_square_routeM

theorem G_two_sevenths_lt : G (2 / 7) < 33 / 100 :=
  G_two_sevenths_lt_of_twelveSquare twelve_square_routeM

theorem G_lt_U {η : ℝ} (hη : 0 < η) (hη1 : η < 1) : G η < Ufun η :=
  G_lt_U_of_twelveSquare twelve_square_routeM hη hη1

/-- **Proposition 5.11 / Lemma 5.13 scalar tail bound, unconditional:** `T_n ≤ R_n` for all `n`
(cases `n = 0,1`; `n = 2`; `n = 3`; `n ≥ 4` as in `Tn_le_Rn_of_twelveSquare`). -/
theorem Tn_le_Rn (n : ℕ) : Tn n ≤ Rn n := Tn_le_Rn_of_twelveSquare twelve_square_routeM n

end BecknerOnofri.V2.ThetaTail.RouteM
