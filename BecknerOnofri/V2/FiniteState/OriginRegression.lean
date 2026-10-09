module

public import BecknerOnofri.V2.FiniteState.OriginMoments

@[expose] public section

/-!
# Origin vanishing orders of the regression residuals: `e_j(t) = O(t³)`, `𝒱(t) = O(t⁶)`

(`d12-spin-eq:eorigin`, Appendix A.3.)  The exact mass and mean identities of `FamilyLocal` remove
the common term `2 - 12 t²` from the weighted regression, and `σ_x²(t) → 1/12` makes the slope
`O(t³)`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter Topology Asymptotics
open scoped BigOperators
namespace BecknerOnofri.V2.FiniteState
open BecknerOnofri.HighDim.Spin

theorem bigO_mul_one {f g : ℝ → ℝ} {h : ℝ → ℝ} (hf : f =O[𝓝 0] fun _ : ℝ => (1 : ℝ))
    (hg : g =O[𝓝 0] h) : (fun t => f t * g t) =O[𝓝 0] h := by
  simpa using hf.mul hg

theorem famLaw_tendsto (j : Count) : Tendsto (fun t => famLaw t j) (𝓝 0) (𝓝 (reference j)) := by
  have h := (famLaw_ratio_jet j).tendsto
  have h2 := h.const_mul (reference j)
  have e : ∀ t, reference j * (famLaw t j / reference j) = famLaw t j := by
    intro t; have := (reference_pos j).ne'; field_simp
  simpa [e] using h2

theorem famLaw_isBigO_one (j : Count) : (fun t => famLaw t j) =O[𝓝 0] fun _ : ℝ => (1 : ℝ) :=
  (famLaw_tendsto j).isBigO_one ℝ

theorem famSpinVar_tendsto : Tendsto famSpinVar (𝓝 0) (𝓝 (1 / 12)) := by
  have h : Tendsto (fun t => ∑ j : Count, famLaw t j * (meanCoordinate j - t) ^ 2) (𝓝 0)
      (𝓝 (∑ j : Count, reference j * (meanCoordinate j - 0) ^ 2)) := by
    refine tendsto_finsetSum _ (fun j _ => ?_)
    exact (famLaw_tendsto j).mul ((by fun_prop : Continuous fun t : ℝ => (meanCoordinate j - t) ^ 2).tendsto 0)
  have e : (∑ j : Count, reference j * (meanCoordinate j - 0) ^ 2) = 1 / 12 := by
    have := famSpinVar_zero
    unfold famSpinVar regVar at this
    rw [famLaw_zero] at this
    exact this
  rw [e] at h
  exact h

theorem famSpinVar_inv_isBigO_one :
    (fun t => (famSpinVar t)⁻¹) =O[𝓝 0] fun _ : ℝ => (1 : ℝ) := by
  have := famSpinVar_tendsto.inv₀ (by norm_num : (1 / 12 : ℝ) ≠ 0)
  exact this.isBigO_one ℝ

/-- `r_j(t) = g_j(p(t)) - (2 - 12 t²)`. -/
def famGradDefect (t : ℝ) (j : Count) : ℝ := gradient (famLaw t) j - (2 - 12 * t ^ 2)

theorem famGradDefect_isBigO (j : Count) :
    (fun t => famGradDefect t j) =O[𝓝 0] fun t : ℝ => t ^ 3 := famGradResidual_isBigO j

/-- Exact algebra of the residual near zero: `e_j = r_j - ∑ p r - η (x_j - t)`. -/
theorem famResid_eq_eventually (j : Count) :
    ∀ᶠ t in 𝓝 (0 : ℝ), famResid t j =
      famGradDefect t j - (∑ k : Count, famLaw t k * famGradDefect t k) -
        ((∑ k : Count, famLaw t k * (meanCoordinate k - t) * famGradDefect t k) / famSpinVar t) *
          (meanCoordinate j - t) := by
  filter_upwards [famLaw_sum_eventually, famLaw_mean_eventually] with t hm hx
  have hcen : ∑ k : Count, famLaw t k * (meanCoordinate k - t) = 0 := by
    have : ∑ k : Count, famLaw t k * (meanCoordinate k - t) =
        ∑ k : Count, meanCoordinate k * famLaw t k - t * ∑ k : Count, famLaw t k := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun k _ => by ring)
    rw [this, hx, hm]; ring
  have hg : ∀ k, gradient (famLaw t) k = (2 - 12 * t ^ 2) + famGradDefect t k := by
    intro k; unfold famGradDefect; ring
  have hmean : regMean (famLaw t) (gradient (famLaw t)) =
      (2 - 12 * t ^ 2) + ∑ k : Count, famLaw t k * famGradDefect t k := by
    unfold regMean
    simp_rw [hg, mul_add]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, hm]; ring
  have hnum : ∑ k : Count, famLaw t k * (meanCoordinate k - t) * gradient (famLaw t) k =
      ∑ k : Count, famLaw t k * (meanCoordinate k - t) * famGradDefect t k := by
    simp_rw [hg, mul_add]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, hcen]; ring
  unfold famResid gradResid regResid regSlope
  rw [hmean, show regVar (famLaw t) meanCoordinate t = famSpinVar t from rfl, hnum, hg j]
  ring

theorem famResid_isBigO (j : Count) :
    (fun t => famResid t j) =O[𝓝 0] fun t : ℝ => t ^ 3 := by
  have hr := fun k => famGradDefect_isBigO k
  have hS1 : (fun t => ∑ k : Count, famLaw t k * famGradDefect t k) =O[𝓝 0] fun t : ℝ => t ^ 3 :=
    Asymptotics.IsBigO.fun_sum (fun k _ => bigO_mul_one (famLaw_isBigO_one k) (hr k))
  have hx : ∀ k : Count, (fun t : ℝ => meanCoordinate k - t) =O[𝓝 0] fun _ : ℝ => (1 : ℝ) := by
    intro k
    exact Filter.Tendsto.isBigO_one ℝ (c := meanCoordinate k - 0)
      ((by fun_prop : Continuous fun t : ℝ => meanCoordinate k - t).tendsto 0)
  have hS2 : (fun t => ∑ k : Count, famLaw t k * (meanCoordinate k - t) * famGradDefect t k)
      =O[𝓝 0] fun t : ℝ => t ^ 3 := by
    refine Asymptotics.IsBigO.fun_sum (fun k _ => ?_)
    have h1 : (fun t => famLaw t k * (meanCoordinate k - t)) =O[𝓝 0] fun _ : ℝ => (1 : ℝ) := by
      simpa using (famLaw_isBigO_one k).mul (hx k)
    exact bigO_mul_one h1 (hr k)
  have hη : (fun t => (∑ k : Count, famLaw t k * (meanCoordinate k - t) * famGradDefect t k) /
      famSpinVar t) =O[𝓝 0] fun t : ℝ => t ^ 3 := by
    have := hS2.mul famSpinVar_inv_isBigO_one
    simpa [div_eq_mul_inv] using this
  have hηx := hη.mul (hx j)
  have h3 := ((hr j).sub hS1).sub (by simpa using hηx)
  refine h3.congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [famResid_eq_eventually j] with t ht
  rw [ht]

theorem famResidVar_isBigO : famResidVar =O[𝓝 0] fun t : ℝ => t ^ 6 := by
  unfold famResidVar
  refine Asymptotics.IsBigO.fun_sum (fun j _ => ?_)
  have h2 := (famResid_isBigO j).pow 2
  have := (famLaw_isBigO_one j).mul h2
  simpa [← pow_mul] using this

end BecknerOnofri.V2.FiniteState
