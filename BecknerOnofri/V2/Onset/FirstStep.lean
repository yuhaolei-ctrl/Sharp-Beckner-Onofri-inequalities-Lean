module

public import BecknerOnofri.V2.Onset.Bootstrap
public import BecknerOnofri.V2.Onset.Tail

@[expose] public section

/-! # First bootstrap step from an `L²` bound on the density

Manuscript (proof of Proposition 5.24): "`(ρ_n)` is bounded in `L²`; the Fourier multiplier first
bounds `(u_n)` in `H^d`."  This is `sobolev_euler_step` at `s = 0` combined with the Parseval
identity `‖ρ‖²_{H⁰} = ∫ρ²` (`sobolevNorm_zero_sq`); it supplies the hypothesis `hu1`, `hB` of
`sobolev_bootstrap`. -/

noncomputable section
open MeasureTheory

namespace BecknerOnofri.V2.Onset
open BecknerOnofri.HighDim

theorem sobolev_first_step {d : ℕ} (c M : ℝ) (u ρ : Torus d → ℝ) (hu : MemLp u 2 (torusMeasure d))
    (hm : MeanZero u) (hρ : MemLp ρ 2 (torusMeasure d)) (hM : ∫ x, ρ x ^ 2 ∂torusMeasure d ≤ M)
    (heuler : ∀ k : Frequency d, k ≠ 0 →
      ((frequencyLength k : ℂ) ^ d) * fourierCoeff u k = (c : ℂ) * fourierCoeff ρ k) :
    InSobolev (d : ℝ) u ∧ sobolevNorm (d : ℝ) u ≤ eulerConst d * |c| * Real.sqrt M := by
  have h0 : InSobolev 0 ρ := (inSobolev_zero_iff ρ).2 hρ
  obtain ⟨h1, h2⟩ := sobolev_euler_step 0 c u ρ hu hm h0 heuler
  rw [zero_add] at h1 h2
  refine ⟨h1, h2.trans ?_⟩
  have hn : sobolevNorm 0 ρ ≤ Real.sqrt M := by
    apply Real.le_sqrt_of_sq_le
    rw [sobolevNorm_zero_sq ρ hρ]; exact hM
  exact mul_le_mul_of_nonneg_left hn (mul_nonneg (eulerConst_nonneg d) (abs_nonneg c))

end BecknerOnofri.V2.Onset
