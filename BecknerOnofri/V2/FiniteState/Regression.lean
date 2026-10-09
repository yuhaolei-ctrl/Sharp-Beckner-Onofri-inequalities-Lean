module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic

@[expose] public section

/-!
# Weighted-regression interface (`d12-spin-eq:residual`, `d12-spin-eq:center`; obligation U18)

Compiled (sorry-free).  Generic over a finite index type; the Count-specific instance takes
`x := Spin.meanCoordinate`, `g := Spin.gradient p`.  The centered relations are *proved*, not
assumed.  The slope divides by the weighted variance; the lemmas below need it only to be nonzero.
-/

noncomputable section
open scoped BigOperators
namespace BecknerOnofri.V2.FiniteState

variable {ι : Type*} [Fintype ι]

/-- `σ_x^2(t) = ∑ p_j (x_j - t)^2`. -/
def regVar (p x : ι → ℝ) (t : ℝ) : ℝ := ∑ j, p j * (x j - t) ^ 2
/-- `ḡ = ∑ p_j g_j`. -/
def regMean (p g : ι → ℝ) : ℝ := ∑ j, p j * g j
/-- `η = ∑ p_j (x_j - t) g_j / σ_x^2`. -/
def regSlope (p x g : ι → ℝ) (t : ℝ) : ℝ := (∑ j, p j * (x j - t) * g j) / regVar p x t
/-- `e_j = g_j - ḡ - η (x_j - t)`. -/
def regResid (p x g : ι → ℝ) (t : ℝ) (j : ι) : ℝ :=
  g j - regMean p g - regSlope p x g t * (x j - t)
/-- `𝒱 = ∑ p_j e_j^2`. -/
def regResidVar (p x g : ι → ℝ) (t : ℝ) : ℝ := ∑ j, p j * regResid p x g t j ^ 2

theorem sum_p_centered {p x : ι → ℝ} {t : ℝ} (hmass : ∑ j, p j = 1) (hmean : ∑ j, p j * x j = t) :
    ∑ j, p j * (x j - t) = 0 := by
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hmass, hmean]
  ring

/-- First centered relation `∑ p_j e_j = 0`; needs only unit mass and the mean constraint. -/
theorem regResid_center {p x g : ι → ℝ} {t : ℝ} (hmass : ∑ j, p j = 1)
    (hmean : ∑ j, p j * x j = t) :
    ∑ j, p j * regResid p x g t j = 0 := by
  have h0 := sum_p_centered hmass hmean
  have : ∀ j, p j * regResid p x g t j =
      p j * g j - regMean p g * p j - regSlope p x g t * (p j * (x j - t)) := by
    intro j; unfold regResid; ring
  simp only [this, Finset.sum_sub_distrib, ← Finset.mul_sum, hmass, h0, regMean]
  ring

/-- Second centered relation `∑ p_j (x_j - t) e_j = 0` (asserted in the manuscript; needs `σ_x^2 ≠ 0`). -/
theorem regResid_center_x {p x g : ι → ℝ} {t : ℝ} (hmass : ∑ j, p j = 1)
    (hmean : ∑ j, p j * x j = t) (hvar : regVar p x t ≠ 0) :
    ∑ j, p j * (x j - t) * regResid p x g t j = 0 := by
  have h0 := sum_p_centered hmass hmean
  have : ∀ j, p j * (x j - t) * regResid p x g t j =
      p j * (x j - t) * g j - regMean p g * (p j * (x j - t)) -
        regSlope p x g t * (p j * (x j - t) ^ 2) := by
    intro j; unfold regResid; ring
  simp only [this, Finset.sum_sub_distrib, ← Finset.mul_sum, h0]
  have hη : regSlope p x g t * regVar p x t = ∑ j, p j * (x j - t) * g j := by
    unfold regSlope; field_simp
  unfold regVar at hη
  rw [hη]
  ring

/-- Linear gradient term: for `q` with the same mass and mean as `p`,
`∑ g_j (q_j - p_j) = ∑ q_j e_j`.  Needs only the first centered relation. -/
theorem gradient_pairing_eq {p q x g : ι → ℝ} {t : ℝ}
    (hpm : ∑ j, p j = 1) (hpx : ∑ j, p j * x j = t)
    (hqm : ∑ j, q j = 1) (hqx : ∑ j, q j * x j = t) :
    ∑ j, g j * (q j - p j) = ∑ j, q j * regResid p x g t j := by
  have hc := regResid_center (g := g) hpm hpx
  have hq0 := sum_p_centered hqm hqx
  have hp0 := sum_p_centered hpm hpx
  have : ∀ j, g j * (q j - p j) =
      q j * regResid p x g t j - p j * regResid p x g t j +
        regMean p g * (q j - p j) + regSlope p x g t * (q j * (x j - t) - p j * (x j - t)) := by
    intro j; unfold regResid; ring
  simp only [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hc, hq0, hp0,
    hpm, hqm]
  ring

end BecknerOnofri.V2.FiniteState
