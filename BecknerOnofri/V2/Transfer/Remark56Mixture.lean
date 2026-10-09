module

public import BecknerOnofri.V2.Transfer.Remark56
public import BecknerOnofri.V2.Transfer.DimensionTransfer

@[expose] public section

/-! # Remark 5.6, last sentence: the cosine-power mixture structure is what permits the energy comparison

For `d ≥ 12` and `0 < |ε| < 1` the counterexample density `ρ_ε` of Remark 5.6 is not a countable
cosine-power mixture: otherwise Proposition 5.5 would give the deletion inequality, whose right side
vanishes for `ρ_ε` while the left side is strictly positive. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

namespace BecknerOnofri.V2.Transfer
open BecknerOnofri.HighDim

theorem remark56_not_mixture {d : ℕ} (hd : 12 ≤ d) {ε : ℝ} (hε0 : ε ≠ 0) (hε : |ε| < 1) :
    ¬ IsCountableCosineMixture (remarkDensity d (by omega) ε hε) := by
  intro hmix
  have hd0 : 0 < d := by omega
  have h := spectral_marginal_energy_deletion hd _ hmix
  have hrhs : ∑ i : Fin d, inversePowerEnergy (d - 1)
      (coordinateMarginal (remarkDensity d hd0 ε hε) (Finset.univ.erase i)) = 0 := by
    refine Finset.sum_eq_zero (fun i _ => ?_)
    rw [remark56_marginal_eq_one d hd0 _ hε (erase_ne_univ' i), inversePowerEnergy_one]
  rw [hrhs, mul_zero] at h
  exact absurd h (not_le.mpr (remark56_spectralEnergy_pos d hd0 hε0 hε))

end BecknerOnofri.V2.Transfer
