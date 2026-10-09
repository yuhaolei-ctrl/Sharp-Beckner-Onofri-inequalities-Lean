module

public import BecknerOnofri.V2.FiniteState.EntropyConvexity
public import BecknerOnofri.V2.FiniteState.ExpBound
public import BecknerOnofri.V2.FiniteState.Regression
public import BecknerOnofri.SpinDifferentialDefinitions

@[expose] public section

/-!
# Lemma 5.20 (variance comparison), count-vector form

Compiled (sorry-free).  For a positive feasible reference `p` of mean `t` with positive spin
variance, `q ∈ 𝒫_t` arbitrary (boundary allowed), and only the one-sided hypothesis `e_j ≥ -1/4`:
`F(q) ≥ F(p) - (30/7) 𝒱`.  (No variance positivity is needed for this step: the first centered
relation holds for the totalized slope.)  Adding `12 ψ(t)` to both sides gives `d12-spin-eq:variancecomparison`.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
namespace BecknerOnofri.V2.FiniteState
open BecknerOnofri.HighDim.Spin

/-- Residual of the Count-gradient, with the manuscript's `x_j = meanCoordinate j`. -/
def gradResid (t : ℝ) (p : Count → ℝ) (j : Count) : ℝ :=
  regResid p meanCoordinate (gradient p) t j

theorem variance_comparison {t : ℝ} {p q : Count → ℝ}
    (hp : FeasibleAt t p) (hpos : ∀ j, 0 < p j) (hq : FeasibleAt t q)
    (he : ∀ j, -(1 / 4 : ℝ) ≤ gradResid t p j) :
    functional p - (30 / 7 : ℝ) * (∑ j : Count, p j * gradResid t p j ^ 2) ≤ functional q := by
  have hcor := fixed_mean_entropy_convexity_affine hp.1 hpos hq.1 (by rw [hp.2, hq.2])
  have hpm := hp.1.2.1
  have hqx : ∑ j : Count, q j * meanCoordinate j = t := by
    have := hq.2
    simpa [mean, mul_comm] using this
  have hpx' : ∑ j : Count, p j * meanCoordinate j = t := by
    have := hp.2
    simpa [mean, mul_comm] using this
  have hlin := gradient_pairing_eq (g := gradient p) (x := meanCoordinate) hpm hpx' hq.1.2.1 hqx
  have hcen := regResid_center (g := gradient p) (x := meanCoordinate) hpm hpx'
  have hgibbs := gibbs_variational p q (fun j => -5 * gradResid t p j) hpos hq.1.1 hq.1.2.1
  have hmgf := scaled_log_mgf_le p (gradResid t p) hpos hpm hcen he
  have hsc : (∑ j : Count, q j * (-5 * gradResid t p j)) = -5 * ∑ j : Count, q j * gradResid t p j := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
  have hre : relativeEntropy q p = ∑ j : Count, q j * Real.log (q j / p j) := rfl
  change _ ≤ functional q at hcor
  rw [hlin] at hcor
  rw [hsc] at hgibbs
  -- hgibbs : -5 Σ q e - Hr ≤ log Z ;  hmgf : (1/5) log Z ≤ (30/7) V
  rw [← hre] at hgibbs
  have hexp : (∑ j : Count, p j * Real.exp (-5 * gradResid t p j)) =
      ∑ j : Count, p j * Real.exp ((fun j => -5 * gradResid t p j) j) := rfl
  rw [← hexp] at hgibbs
  have hqe : (∑ j : Count, q j * gradResid t p j) = (∑ j : Count, q j * regResid p meanCoordinate (gradient p) t j) := rfl
  linarith

/-- With the explicit correction `12 ψ(t)` added to both sides (`d12-spin-eq:variancecomparison`). -/
theorem variance_comparison_psi {t : ℝ} {ψ : ℝ} {p q : Count → ℝ}
    (hp : FeasibleAt t p) (hpos : ∀ j, 0 < p j) (hq : FeasibleAt t q)
    (he : ∀ j, -(1 / 4 : ℝ) ≤ gradResid t p j) :
    (functional p + 12 * ψ) - (30 / 7 : ℝ) * (∑ j : Count, p j * gradResid t p j ^ 2) ≤
      functional q + 12 * ψ := by
  have := variance_comparison hp hpos hq he
  linarith

end BecknerOnofri.V2.FiniteState
