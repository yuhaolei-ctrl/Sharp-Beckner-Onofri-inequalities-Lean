module

public import BecknerOnofri.V2.FiniteState.FamilyBeta

@[expose] public section

/-!
# Lemma 5.20 for the explicit family (`d12-spin-lem:perturb`, `d12-spin-eq:variancecomparison`)

The generic count-vector theorem `variance_comparison_psi` applied to `p = p(t)`, `0 ≤ t < 1`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
namespace BecknerOnofri.V2.FiniteState
open BecknerOnofri.HighDim.Spin

/-- **Lemma 5.20.**  Fix `0 ≤ t < 1`.  If `e_j(t) ≥ -1/4` for every `j`, then every
`q ∈ 𝒫_t` (zero coordinates allowed) satisfies `F(q) + 12 ψ(t) ≥ f(t) - (30/7) 𝒱(t)`. -/
theorem family_variance_comparison {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) {q : Count → ℝ}
    (hq : FeasibleAt t q) (he : ∀ j : Count, -(1 / 4 : ℝ) ≤ famResid t j) :
    famF t - (30 / 7 : ℝ) * famResidVar t ≤ functional q + 12 * psiV2 t :=
  variance_comparison_psi (ψ := psiV2 t) (famLaw_feasibleAt_of_nonneg_beta ht0 ht1)
    (famLaw_pos_of_nonneg ht0 ht1) hq he

end BecknerOnofri.V2.FiniteState
