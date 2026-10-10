module

public import BecknerOnofri.V2.Reaudit.Attainment.Basic
public import BecknerOnofri.V2.Onset.Bootstrap

@[expose] public section

/-! # Fourier uniqueness for raw critical Sobolev potentials (package `Attainment`)

Used for the step "the Sobolev remainder vanishes if and only if `u = u_{ρ_u}`, since both potentials
have mean zero" in the proof of `cor:section2-extremizer-correspondence`: a function of mean zero in
`H^{d/2}` whose seminorm `‖·‖_{Ḣ^{d/2}}` vanishes is zero almost everywhere (all Fourier
coefficients vanish, and the `L²` Fourier transform is injective). -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped Topology ENNReal

namespace BecknerOnofri.V2.Reaudit.Attainment
open BecknerOnofri.HighDim

variable {d : ℕ}

/-- An `L²` function all of whose Fourier coefficients vanish is zero almost everywhere. -/
theorem ae_eq_zero_of_fourierCoeff_eq_zero {w : Torus d → ℝ} (hw : MemLp w 2 (torusMeasure d))
    (h : ∀ k : Frequency d, fourierCoeff w k = 0) : w =ᵐ[torusMeasure d] 0 := by
  have hW : Legacy.BecknerOnofri.TorusSobolev.fourierIsometry d (Bridge.potentialLp w hw) = 0 := by
    ext k
    rw [Bridge.potentialLp_fourier]
    simp [h k]
  have h0 : Bridge.potentialLp w hw = 0 := by
    have := (Legacy.BecknerOnofri.TorusSobolev.fourierIsometry d).map_eq_zero_iff.mp
      (by simpa using hW)
    exact this
  have h2 : (Bridge.potentialLp w hw : Torus d → ℂ) =ᵐ[torusMeasure d] 0 := by
    rw [h0]; exact Lp.coeFn_zero _ _ _
  filter_upwards [Bridge.potentialLp_ae w hw, h2] with x hx1 hx2
  have : ((w x : ℝ) : ℂ) = 0 := hx1.symm.trans hx2
  simpa using this

/-- The seminorm of a critical Sobolev function vanishes if and only if all its nonzero Fourier
coefficients vanish. -/
theorem potentialEnergy_eq_zero_iff {u : Torus d → ℝ} (hu : InCriticalSobolev u) :
    potentialEnergy u = 0 ↔ ∀ k : Frequency d, k ≠ 0 → fourierCoeff u k = 0 := by
  have hnn : ∀ k : NonzeroFrequency d, 0 ≤ potentialTerm u k := fun k => by
    unfold potentialTerm frequencyLength; positivity
  unfold potentialEnergy
  rw [← hu.2.hasSum_iff, hasSum_zero_iff_of_nonneg hnn]
  constructor
  · intro h k hk
    have h1 := congrFun h ⟨k, hk⟩
    unfold potentialTerm at h1
    have hpos : 0 < (2 * Real.pi * frequencyLength k) ^ d := by
      have : 1 ≤ frequencyLength k := BecknerOnofri.V2.Onset.one_le_frequencyLength hk
      have := Real.pi_pos
      positivity
    have h2 : ‖fourierCoeff u k‖ ^ 2 = 0 := by
      rcases mul_eq_zero.mp h1 with h | h
      · exact absurd h hpos.ne'
      · exact h
    exact norm_eq_zero.mp (pow_eq_zero_iff (two_ne_zero) |>.mp h2)
  · intro h
    funext k
    unfold potentialTerm
    rw [h k.val k.2]
    simp

/-- A mean-zero critical Sobolev function of vanishing seminorm is zero almost everywhere. -/
theorem ae_eq_zero_of_potentialEnergy_eq_zero {u : Torus d → ℝ} (hu : InCriticalSobolev u)
    (hm : MeanZero u) (h : potentialEnergy u = 0) : u =ᵐ[torusMeasure d] 0 := by
  refine ae_eq_zero_of_fourierCoeff_eq_zero hu.1 fun k => ?_
  by_cases hk : k = 0
  · subst hk
    exact BecknerOnofri.V2.Onset.fourierCoeff_zero_meanZero hm
  · exact (potentialEnergy_eq_zero_iff hu).mp h k hk

end BecknerOnofri.V2.Reaudit.Attainment
