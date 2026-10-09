module

public import BecknerOnofri.V2.FiniteState.FamilyBounds
public import BecknerOnofri.V2.FiniteState.VarianceComparison
public import BecknerOnofri.SpinDefinitions
public import BecknerOnofri.SpinDifferentialDefinitions

@[expose] public section

/-!
# The explicit reference family: definitions (Lemma 5.19)

Compiled (sorry-free).  Adapted from the handoff's draft ExplicitFamily.lean with these changes:
* all names carry the `fam` prefix (the handoff draft's `psi` and `gradient` would be *ambiguous*
  with `Spin.psi` / `Spin.gradient` once `open BecknerOnofri.HighDim.Spin` is in force);
* `Spin.gradient`, `Spin.functional`, `Spin.meanCoordinate`, `Spin.reference` are reused;
* the rising-factorial (source) form is a separate definition, equated with the stable rational
  form on (0,1);
* the stable form is the one that is *used*; `famLaw 0 = reference` is proved, not defined.
-/
noncomputable section
open scoped BigOperators
namespace BecknerOnofri.V2.FiniteState
open BecknerOnofri.HighDim.Spin

/-- Source correction `ψ(t) = t^4/(14 - 10 t^2)` (new; NOT `Spin.psi`, which is the old model's). -/
def psiV2 (t : ℝ) : ℝ := t ^ 4 / (14 - 10 * t ^ 2)

/-- Rational product form `d12-spin-eq:rationalfamily` (regular at `t = 0`).
Empty products are `1`; the `-` factors number `12 - j`, the `+` factors number `j`. -/
def famNu (t : ℝ) (j : Count) : ℝ :=
  ((12 : ℕ).choose j.val : ℝ) *
    (∏ k ∈ Finset.range j.val, ((1 + famBias t) / 2 + (k : ℝ) * famOmega t)) *
    (∏ k ∈ Finset.range (12 - j.val), ((1 - famBias t) / 2 + (k : ℝ) * famOmega t)) /
    (∏ k ∈ Finset.range 12, (1 + (k : ℝ) * famOmega t))

/-- Source rising-factorial form `d12-spin-eq:beta` (only meaningful for `0 < t < 1`). -/
def famNuRising (t : ℝ) (j : Count) : ℝ :=
  ((12 : ℕ).choose j.val : ℝ) *
    (∏ k ∈ Finset.range j.val, (famChi t * (1 + famBias t) / 2 + k)) *
    (∏ k ∈ Finset.range (12 - j.val), (famChi t * (1 - famBias t) / 2 + k)) /
    (∏ k ∈ Finset.range 12, (famChi t + k))

/-- The mixed law `p(t)`: with the all-plus state (`j = 12`). -/
def famLaw (t : ℝ) (j : Count) : ℝ :=
  (1 - famLam t) * famNu t j + famLam t * (if j.val = 12 then 1 else 0)

def famSpinVar (t : ℝ) : ℝ := regVar (famLaw t) meanCoordinate t

/-- `e_j(t)`, `𝒱(t)`, `f(t)` of `d12-spin-eq:residual`. -/
def famResid (t : ℝ) (j : Count) : ℝ := gradResid t (famLaw t) j
def famResidVar (t : ℝ) : ℝ := ∑ j : Count, famLaw t j * famResid t j ^ 2
def famF (t : ℝ) : ℝ := functional (famLaw t) + 12 * psiV2 t

/-- Variance formula `d12-spin-eq:variance-x`, to be proved equal to `famSpinVar` on `[0,1)`. -/
def famVarFormula (t : ℝ) : ℝ :=
  (1 - famLam t) * (1 - famBias t ^ 2) / 12 * (1 + 12 * famOmega t) / (1 + famOmega t) +
    famLam t * (1 - famLam t) * (1 - famBias t) ^ 2

end BecknerOnofri.V2.FiniteState
