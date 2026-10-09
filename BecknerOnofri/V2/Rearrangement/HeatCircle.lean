module

public import Legacy.BecknerOnofri.CircleHeatGeometry

@[expose] public section

/-! # The unit-circle heat kernel: positivity, evenness, radial monotonicity (Lemma 2.9 input)

Manuscript (`lem:coordinate-rearranged-minimizer`): the circle heat kernel
`p_t(x) = ∑_{n∈ℤ} e^{-4π² n² t} e^{2π i n x}` is nonnegative, even, and nonincreasing on `[0,1/2]`.

The repository's kernel `Legacy.TorusEndpoint.TorusHeatPositivity.theta τ` uses the multiplier
`exp(-π τ n²)`; with `τ = 4π t` this is the manuscript's `exp(-4π² n² t)`
(`heatMultiplier_rescale`).  Below `circleHeat τ z := (theta τ z).re`.  Everything is stated on
`UnitAddCircle`, with the circle norm `‖z‖ ∈ [0,1/2]` (geodesic distance to `0`). -/

noncomputable section
open Set
open Legacy.TorusEndpoint TorusHeatPositivity Legacy.BecknerOnofri.CircleHeat

namespace BecknerOnofri.V2.Rearrangement

/-- The real circle heat kernel `p_τ`, `τ` in the repository's time scale. -/
def circleHeat (τ : ℝ) (z : UnitAddCircle) : ℝ := (theta τ z).re

/-- Fourier-multiplier form: `p_τ = ∑ₙ exp(-π τ n²) e_n`. -/
theorem circleHeat_eq_tsum {τ : ℝ} (hτ : 0 < τ) (z : UnitAddCircle) :
    (circleHeat τ z : ℂ) = ∑' n : ℤ, (Real.exp (-Real.pi * τ * (n : ℝ) ^ 2) : ℂ) * fourier n z :=
  (theta_eq_ofReal_re hτ z).symm

/-- The manuscript's multiplier `e^{-4π² n² t}` is the repository's with `τ = 4π t`. -/
theorem heatMultiplier_rescale (t : ℝ) (n : ℤ) :
    Real.exp (-Real.pi * (4 * Real.pi * t) * (n : ℝ) ^ 2) = Real.exp (-(4 * Real.pi ^ 2) * (n : ℝ) ^ 2 * t) := by
  congr 1
  ring

theorem circleHeat_pos {τ : ℝ} (hτ : 0 < τ) (z : UnitAddCircle) : 0 < circleHeat τ z :=
  theta_re_pos hτ z

theorem circleHeat_nonneg {τ : ℝ} (hτ : 0 < τ) (z : UnitAddCircle) : 0 ≤ circleHeat τ z :=
  (circleHeat_pos hτ z).le

theorem circleHeat_even {τ : ℝ} (hτ : 0 < τ) (z : UnitAddCircle) : circleHeat τ (-z) = circleHeat τ z :=
  theta_re_even hτ z

theorem circleHeat_continuous {τ : ℝ} (hτ : 0 < τ) : Continuous (circleHeat τ) :=
  Complex.continuous_re.comp (theta_continuous hτ)

/-- `p_τ` is bounded (continuous on the compact circle). -/
theorem circleHeat_bounded {τ : ℝ} (hτ : 0 < τ) : ∃ C : ℝ, ∀ z, circleHeat τ z ≤ C := by
  obtain ⟨z₀, -, hz₀⟩ := isCompact_univ.exists_isMaxOn (f := circleHeat τ) univ_nonempty
    (circleHeat_continuous hτ).continuousOn
  exact ⟨circleHeat τ z₀, fun z => hz₀ (mem_univ z)⟩

/-- Every point of the unit circle has a representative `u ∈ [-1/2,1/2]`, `‖z‖ = |u|`. -/
theorem exists_rep (z : UnitAddCircle) : ∃ u : ℝ, |u| ≤ 1 / 2 ∧ z = (u : UnitAddCircle) ∧ ‖z‖ = |u| := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
  have hnorm := AddCircle.norm_eq (p := (1 : ℝ)) (x := x)
  refine ⟨x - round x, ?_, ?_, ?_⟩
  · have := abs_sub_round x
    simpa using this
  · have h0 : ((round x : ℝ) : UnitAddCircle) = 0 := by
      rw [AddCircle.coe_eq_zero_iff]
      exact ⟨round x, by simp⟩
    rw [AddCircle.coe_sub, h0, sub_zero]
  · simpa using hnorm

theorem circleHeat_coe_abs {τ : ℝ} (hτ : 0 < τ) (u : ℝ) :
    circleHeat τ (u : UnitAddCircle) = circleHeat τ ((|u| : ℝ) : UnitAddCircle) := by
  have h := realHeat_abs hτ u
  exact h.symm

/-- Radial monotonicity: `‖z‖ ≤ ‖w‖ ⟹ p_τ(w) ≤ p_τ(z)`. -/
theorem circleHeat_radial_antitone {τ : ℝ} (hτ : 0 < τ) {z w : UnitAddCircle} (h : ‖z‖ ≤ ‖w‖) :
    circleHeat τ w ≤ circleHeat τ z := by
  obtain ⟨u, hu, rfl, hzu⟩ := exists_rep z
  obtain ⟨v, hv, rfl, hwv⟩ := exists_rep w
  rw [hzu, hwv] at h
  have e1 : circleHeat τ (u : UnitAddCircle) = realHeat τ |u| := (realHeat_abs hτ u).symm
  have e2 : circleHeat τ (v : UnitAddCircle) = realHeat τ |v| := (realHeat_abs hτ v).symm
  rw [e1, e2]
  exact realHeat_antitone hτ ⟨abs_nonneg _, hu⟩ ⟨abs_nonneg _, hv⟩ h

end BecknerOnofri.V2.Rearrangement
