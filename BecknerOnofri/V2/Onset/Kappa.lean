module

public import BecknerOnofri.QuarticBranches
public import BecknerOnofri.LocalElevenCore.QuarticTrustedBridge

@[expose] public section

/-! # `q_{d,d} = -κ_d/(2d)` (equation `eq:section5-qdd-kappa`)

The full-support quartic coefficient `q_{d,n} = (a_d + (n-1) b_d/2)/n` at `n = d` equals
`-κ_d/(2d)` where `κ_d = -(2a_d + (d-1)b_d)`.  Consequently the branch pressure coefficient
`-1/(4 q_{d,d})` is `d/(2κ_d)`. -/

noncomputable section

namespace BecknerOnofri.V2.Onset
open BecknerOnofri.HighDim

theorem branchQuarticCoefficient_self {d : ℕ} (hd : 0 < d) :
    branchQuarticCoefficient d d = -kappa d / (2 * (d : ℝ)) := by
  have hd' : (d : ℝ) ≠ 0 := (Nat.cast_pos.mpr hd).ne'
  unfold branchQuarticCoefficient kappa
  field_simp

theorem neg_one_div_four_branchQuartic_self {d : ℕ} (hd : 11 ≤ d) :
    -1 / (4 * branchQuarticCoefficient d d) = (d : ℝ) / (2 * kappa d) := by
  have hk : 0 < kappa d := LocalQuartic.kappa_positive hd
  have hd' : (d : ℝ) ≠ 0 := (Nat.cast_pos.mpr (by omega : 0 < d)).ne'
  rw [branchQuarticCoefficient_self (by omega : 0 < d)]
  field_simp
  norm_num

end BecknerOnofri.V2.Onset
