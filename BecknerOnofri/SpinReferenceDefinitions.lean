module

public import BecknerOnofri.SpinDefinitions
public import BecknerOnofri.SpinProductDefinitions

@[expose] public section

/-!
# Definitions for the finite-state inequality (Proposition 5.12(ii))

The functions `ψ`, `η`, the penalized count functional `G_t`, the
explicit reference law `q(t)` and the scalar `𝓑(t)` of Subsection 5.2.5, for the
manuscript dated 2026-10-06. The binary relative entropy `I_B` is `Spin.binaryCost`.
-/

noncomputable section

open scoped BigOperators

namespace BecknerOnofri.HighDim.Spin

/-- `ψ(t) = 3t⁴/40 + 33t¹⁰/200`, (eq:section5-psi-eta). -/
def psi (t : ℝ) : ℝ := 3 / 40 * t ^ 4 + 33 / 200 * t ^ 10

/-- `η(t) = (1-t²)(9t²/20 + 297t⁸/100)/(1-t²/2)`, (eq:section5-psi-eta). -/
def eta (t : ℝ) : ℝ := (1 - t ^ 2) * (9 / 20 * t ^ 2 + 297 / 100 * t ^ 8) / (1 - t ^ 2 / 2)

/-- `G_t(p) = F(p) + 12ψ(t) + η(t)[H(p|b) - 12 I_B(t)]`, (eq:section5-spin-G). -/
def penalized (t : ℝ) (p : Count → ℝ) : ℝ :=
  functional p + 12 * psi t + eta t * (relativeEntropy p reference - 12 * binaryCost t)

/-- The product-law mean `z = t - t⁵/4` of the reference law (eq:section5-spin-reference). -/
def refShift (t : ℝ) : ℝ := t - t ^ 5 / 4

/-- The atom weight `a = t⁵/(4-4t+t⁵)` of the reference law (eq:section5-spin-reference). -/
def refAtom (t : ℝ) : ℝ := t ^ 5 / (4 - 4 * t + t ^ 5)

/-- The reference law `q_j = (1-a) b_j (1+z)^j (1-z)^{12-j} + a 1_{j=12}`, (eq:section5-spin-reference). -/
def refLaw (t : ℝ) (j : Count) : ℝ :=
  (1 - refAtom t) * productProbability (refShift t) j + if j = 12 then refAtom t else 0

/-- `μ = 5t³/(2-t²)`, (eq:section5-spin-reference). -/
def refMu (t : ℝ) : ℝ := 5 * t ^ 3 / (2 - t ^ 2)

/-- `τ = 7/25 + η(t)`. -/
def refTau (t : ℝ) : ℝ := 7 / 25 + eta t

/-- `(Wq)_j`. -/
def interactionApply (p : Count → ℝ) (j : Count) : ℝ := ∑ k : Count, interaction j k * p k

/-- `g_j = (2+η) log(q_j/b_j) - 2 (Wq)_j`. -/
def refGradient (t : ℝ) (j : Count) : ℝ :=
  (2 + eta t) * Real.log (refLaw t j / reference j) - 2 * interactionApply (refLaw t) j

/-- The explicit scalar `𝓑(t)` (eq:12-explicit-scalar). -/
def pressureScalar (t : ℝ) : ℝ :=
  quadratic (refLaw t) + 12 * psi t - 12 * eta t * binaryCost t -
    refTau t * Real.log (∑ j : Count, refLaw t j *
      Real.exp ((-refGradient t j + refMu t * (meanCoordinate j - t)) / refTau t))

end BecknerOnofri.HighDim.Spin
