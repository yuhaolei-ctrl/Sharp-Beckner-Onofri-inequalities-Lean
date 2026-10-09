module

public import Mathlib.Tactic.Ring
public import Mathlib.Algebra.Order.Field.Basic

@[expose] public section

/-! # Finite algebraic steps of Appendix A.1 (scalar Fourier tail)

Pure commutative-ring/ordered-field identities used in the proof of Lemma 5.13.
Nothing analytic is assumed here: `thetaAlg1`/`thetaAlg2`/`theta12_elimination` are the
polynomial identities `(d12-tail-eq:thetaalg1)`, `(d12-tail-eq:thetaalg2)` and the final
elimination `-E6(τ)/63 + 64E6(4τ)/63 + 16η(2τ)^12 = a^6`, stated for abstract
elements `a,b,c,d` of a field (they do NOT use theta functions).
The nome convention is irrelevant for this file. -/
noncomputable section
namespace BecknerOnofri.V2.ThetaTail

variable {K : Type*} [Field K]

/-- `E6 = ½ (x₂+x₃)(x₃+x₄)(x₄−x₂)` with `x_j = ϑ_j^4` (display `(d12-tail-eq:E6theta)`). -/
def e6Poly (x2 x3 x4 : K) : K := (x2 + x3) * (x3 + x4) * (x4 - x2) / 2

/-- `(d12-tail-eq:thetaalg1)`: with `ϑ₃²=a+b, ϑ₄²=a−b, ϑ₂⁴=4ab`. -/
theorem thetaAlg1 [CharZero K] (a b : K) :
    e6Poly (4 * a * b) ((a + b) ^ 2) ((a - b) ^ 2) =
      a ^ 6 + b ^ 6 - 33 * a ^ 4 * b ^ 2 - 33 * a ^ 2 * b ^ 4 := by
  unfold e6Poly
  ring

/-- `(d12-tail-eq:thetaalg2)` at `4τ`: `c=ϑ₃(4τ)²`, `d=ϑ₂(4τ)²`, `a=c+d`, `b²=4cd`
(ϑ₂⁴=d², ϑ₃⁴=c², ϑ₄⁴=c²−d² by Jacobi). -/
theorem thetaAlg2 [CharZero K] (c d : K) :
    64 * e6Poly (d ^ 2) (c ^ 2) (c ^ 2 - d ^ 2) =
      64 * (c + d) ^ 6 - 96 * (c + d) ^ 4 * (4 * c * d)
        + 30 * (c + d) ^ 2 * (4 * c * d) ^ 2 + (4 * c * d) ^ 3 := by
  unfold e6Poly
  ring

/-- The final polynomial elimination:
`-E6(τ)/63 + 64E6(4τ)/63 + a²b²(a²-b²) = a⁶` with `B = b²`. -/
theorem theta12_elimination [CharZero K] (a B : K) :
    -(a ^ 6 + B ^ 3 - 33 * a ^ 4 * B - 33 * a ^ 2 * B ^ 2) / 63
      + (64 * a ^ 6 - 96 * a ^ 4 * B + 30 * a ^ 2 * B ^ 2 + B ^ 3) / 63
      + a ^ 2 * B * (a ^ 2 - B) = a ^ 6 := by
  ring

/-- Coefficient arithmetic `504/63 = 8`, `64*504/63 = 512`. -/
theorem lambert_coefficients [CharZero K] : (504 : K) / 63 = 8 ∧ (64 * 504 : K) / 63 = 512 := by
  constructor <;> norm_num

end BecknerOnofri.V2.ThetaTail
