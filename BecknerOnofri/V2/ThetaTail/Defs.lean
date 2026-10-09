module

public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-! # Definitions for the scalar Fourier tail (Proposition 5.11, Lemma 5.13, Appendix A.1)

* `theta q = ∑_{k∈ℤ} q^{k²}`, exactly as in the manuscript;
* `TwelveSquareIdentity`: the identity `(d12-tail-eq:theta12)` as a `Prop`.  It is a SEPARATE
  analytic obligation (Appendix A.1, "A twelve-square identity"); it is **not** assumed or
  proved in the declarations that merely define it;
* the Gaussian tail `G(η)` of Appendix A.1, `a_n(j)`, `H_n`, `T_n`, `R_n` of Subsection
  `subsec:section5-global-tail` (`eq:scalar-def`, `eq:section5-global-tail-definitions`). -/
noncomputable section
open Finset
namespace BecknerOnofri.V2.ThetaTail

/-- `θ(q) = ∑_{k∈ℤ} q^{k²}`. -/
def theta (q : ℝ) : ℝ := ∑' k : ℤ, q ^ (k ^ 2)

/-- `σ₅(m) = ∑_{d∣m} d⁵` as a real number. -/
def sigma5 (m : ℕ) : ℝ := ((ArithmeticFunction.sigma 5 m : ℕ) : ℝ)

/-- The twelve-square identity `(d12-tail-eq:theta12)`:
`θ(q)^12 = 1 + 8∑σ₅(m)q^m − 512∑σ₅(m)q^{4m} + 16 q ∏(1−q^{2m})^12`, for `0 < q < 1`.
This is only a statement; it is the hypothesis of the honestly conditional theorems
`*_of_twelveSquare` of this package.  Its proof is the separate Appendix A.1 derivation. -/
def TwelveSquareIdentity : Prop :=
  ∀ q : ℝ, 0 < q → q < 1 →
    theta q ^ 12 =
      1 + 8 * ∑' m : ℕ+, sigma5 m * q ^ (m : ℕ)
        - 512 * ∑' m : ℕ+, sigma5 m * q ^ (4 * (m : ℕ))
        + 16 * q * ∏' m : ℕ+, (1 - q ^ (2 * (m : ℕ))) ^ 12

/-- the cube `{-1,0,1}^12` -/
def cube12 : Set (Fin 12 → ℤ) := Set.pi Set.univ fun _ => ({-1, 0, 1} : Set ℤ)

/-- `|k|²` -/
def latticeNormSq (k : Fin 12 → ℤ) : ℝ := ∑ i, ((k i : ℤ) : ℝ) ^ 2

/-- `|k|` (Euclidean length) -/
def latticeNorm (k : Fin 12 → ℤ) : ℝ := Real.sqrt (latticeNormSq k)

/-- The summand of `G(η)`: `e^{-η|k|²}/|k|^{12}` off the cube, `0` on it. -/
def gaussSummand (η : ℝ) (k : Fin 12 → ℤ) : ℝ :=
  (cube12ᶜ).indicator (fun k => Real.exp (-η * latticeNormSq k) / latticeNorm k ^ 12) k

/-- `G(η) = ∑_{k ∈ ℤ^{12} \ {-1,0,1}^{12}} e^{-η|k|²}/|k|^{12}`. -/
def G (η : ℝ) : ℝ := ∑' k : Fin 12 → ℤ, gaussSummand η k

/-- `a_n(j) = C(2n, n+j)/C(2n, n)` (`eq:scalar-def`), written with `|j|` (the binomial
coefficient is symmetric); `Nat.choose (2n) m = 0` for `m > 2n` gives the convention that
binomial coefficients vanish outside their support. -/
def aCoef (n : ℕ) (j : ℤ) : ℝ :=
  ((2 * n).choose (n + j.natAbs) : ℝ) / ((2 * n).choose n : ℝ)

/-- `H_n = ∑_{j=1}^n 1/j` -/
def Hn (n : ℕ) : ℝ := ∑ j ∈ Icc 1 n, 1 / (j : ℝ)

/-- `T_n = ∑_{k ∉ {-1,0,1}^{12}} |k|^{-12} ∏ a_n(k_i)` (`eq:section5-global-tail-definitions`). -/
def Tn (n : ℕ) : ℝ :=
  ∑' k : Fin 12 → ℤ, (cube12ᶜ).indicator (fun k => (latticeNorm k ^ 12)⁻¹ * ∏ i, aCoef n (k i)) k

/-- `R_n = 81/10 H_n − 81/5 a_n(1) − 15/2 a_n(2) − 11/5 a_n(3)`. -/
def Rn (n : ℕ) : ℝ :=
  81 / 10 * Hn n - 81 / 5 * aCoef n 1 - 15 / 2 * aCoef n 2 - 11 / 5 * aCoef n 3

end BecknerOnofri.V2.ThetaTail
