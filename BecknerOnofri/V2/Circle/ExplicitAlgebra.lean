module

public import Mathlib.Tactic
public import BecknerOnofri.SpinProductDefinitions
public import BecknerOnofri.V2.Circle.SquareCompletion
public import BecknerOnofri.V2.Circle.ScalarCircle
public import BecknerOnofri.V2.Circle.ScalarPositivity
public import BecknerOnofri.V2.Circle.BaseExpansion
public import BecknerOnofri.V2.Circle.Psi

@[expose] public section

/-! # The algebraic core of Lemma 5.16 (`lem:section5-circle-explicit-bound`)

For arbitrary real `a = r_2`, `b = r_3` (no moment-feasibility constraint), with
`B = c L_1(u)`, `C = c L_2(u)`, `A = 5/16 + 11 C u/(120 C + 11)`, `c = 27/40`, `u = t^2`:
`scalar_circle_ineq` is `d12-circle-eq:scalarcircle` (with `psi(t) = u^2/(14-10u)`), and
`explicit_algebra` assembles `d12-circle-eq:complete-start`, the two completions of squares and
`scalar_circle_ineq` into the conclusion of the lemma, from the three analytic inputs
`Ent >= I_-`, `w_j >= L_j` and the two-term remainder bound. -/
noncomputable section
open BecknerOnofri.HighDim
namespace BecknerOnofri.V2.Circle

/-- The scalar comparison `d12-circle-eq:scalarcircle`, multiplied out and including the
`A, B` completion: for `0 ≤ t < 1`, `u = t²`,
`(1-c) I_-(t) + c u - 2 I_B(t) + AB/(A+B) u² ≥ u²/(14-10u)` (here `u²/(14-10u) = ψ(t)`). -/
theorem scalar_circle_ineq {t : ℝ} (h0 : 0 ≤ t) (h1 : t < 1) :
    psi t ≤ baseLHS t + Ac (t ^ 2) * Bc (t ^ 2) / (Ac (t ^ 2) + Bc (t ^ 2)) * (t ^ 2) ^ 2 := by
  have hu0 : 0 ≤ t ^ 2 := sq_nonneg t
  have hu1 : t ^ 2 ≤ 1 := by nlinarith
  have hab : |t| < 1 := by rw [abs_of_nonneg h0]; exact h1
  have hJ := base_ge_J hab
  have hS := scalar_positivity hu0 hu1
  have hpsi : psi t = (t ^ 2) ^ 2 * (1 / (14 - 10 * t ^ 2)) := by
    unfold psi; ring
  rw [hpsi]
  have hu2 : 0 ≤ (t ^ 2) ^ 2 := sq_nonneg _
  nlinarith [mul_nonneg hu2 hS.le]


/-- The algebraic core of Lemma 5.16 (`d12-circle-eq:complete-start`, `d12-circle-eq:ABC`):
for ARBITRARY real second and third moments `a, b` (no feasibility constraint),
`w₁ ≥ L₁(t²)`, `w₂ ≥ L₂(t²)`, `Ent ≥ I_-(t)` and the first-two-terms remainder bound
give `Ent ≥ 2 I_B(t) + ψ(t) + a²/40 + 2b²/15 + (27/40) T`. -/
theorem explicit_algebra {t a b Ent T w1 w2 : ℝ} (h0 : 0 ≤ t) (h1 : t < 1)
    (hw1 : L1 (t ^ 2) ≤ w1) (hw2 : L2 (t ^ 2) ≤ w2)
    (hI : Iminus t ≤ Ent)
    (hrem : t ^ 2 + a ^ 2 / 2 + b ^ 2 / 3 + T + w1 * (a - t ^ 2) ^ 2 + w2 * (b - t * a) ^ 2 ≤ Ent) :
    2 * Spin.binaryCost t + psi t + a ^ 2 / 40 + 2 * b ^ 2 / 15 + 27 / 40 * T ≤ Ent := by
  have hu0 : 0 ≤ t ^ 2 := sq_nonneg t
  have hu1 : t ^ 2 ≤ 1 := by nlinarith
  set u := t ^ 2 with hu
  have hB := Bc_pos hu1
  have hC := Cc_pos hu1
  have hCnn := hC.le
  -- the weights
  have hBw : Bc u * (a - u) ^ 2 ≤ 27 / 40 * w1 * (a - u) ^ 2 := by
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    unfold Bc
    nlinarith
  have hCw : Cc u * (b - t * a) ^ 2 ≤ 27 / 40 * w2 * (b - t * a) ^ 2 := by
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    unfold Cc
    nlinarith
  -- first completion: δ C/(C+δ) t² a² ≤ C (b - t a)² + δ b²
  have hb := complete_b_lower (Cc u) (11 / 120 : ℝ) t a b hCnn (by norm_num)
  rw [delta_coeff (Cc u) hCnn] at hb
  -- second completion
  have hApos := Ac_pos hu0 hu1
  have ha := complete_a_lower (Ac u) (Bc u) u a hApos hB
  have hAdef : Ac u = 5 / 16 + 11 * Cc u * u / (120 * Cc u + 11) := rfl
  have hA2 : Ac u * a ^ 2 = 5 / 16 * a ^ 2 + 11 * Cc u / (120 * Cc u + 11) * (t ^ 2 * a ^ 2) := by
    rw [hAdef, hu]; ring
  have hscal := scalar_circle_ineq h0 h1
  unfold baseLHS at hscal
  rw [← hu] at hscal hb hA2
  have s1 : 27 / 40 * (u + a ^ 2 / 2 + b ^ 2 / 3 + T + w1 * (a - u) ^ 2 + w2 * (b - t * a) ^ 2) +
      (1 - 27 / 40) * Iminus t ≤ Ent := by linarith
  have s2 : Ac u * Bc u * u ^ 2 / (Ac u + Bc u) ≤ Ac u * a ^ 2 + Bc u * (a - u) ^ 2 := ha
  have s3 : Ac u * a ^ 2 + Bc u * (a - u) ^ 2 ≤ 5 / 16 * a ^ 2 + (Cc u * (b - t * a) ^ 2 + 11 / 120 * b ^ 2)
      + Bc u * (a - u) ^ 2 := by
    rw [hA2]; linarith
  have s4 : Ac u * Bc u / (Ac u + Bc u) * u ^ 2 = Ac u * Bc u * u ^ 2 / (Ac u + Bc u) := by ring
  linarith [hscal, hBw, hCw]

end BecknerOnofri.V2.Circle
