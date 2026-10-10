module

public import BecknerOnofri.V2.FiniteState.FamilyJets
public import BecknerOnofri.V2.Reaudit.ScalarBridges.KrawtchoukOrthogonality

@[expose] public section

/-! # The two finite evaluations of the origin entropy expansion, by their printed arguments

(`E_b ℓ² = 144 E_b x² = 12` since `E_b x² = 1/12`; and "reflection `j ↦ 12 - j` preserves `b`,
makes `ℓ` odd and `d` even, hence the cubic coefficient vanishes".)  The statements are those of
`sum_reference_ell_sq` and `sum_reference_cubic` of `V2.FiniteState.OriginEntropy`, which prove them
by 13-term rational evaluation.  This module imports only `FamilyJets` (for `famEll`, `famD2`), so
it can be imported by `OriginEntropy`. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace BecknerOnofri.V2.Reaudit.ScalarBridges

open scoped BigOperators
open BecknerOnofri.HighDim.Spin BecknerOnofri.V2.FiniteState

/-- `E_b ℓ² = 144 E_b x² = 12`, since `E_b x² = 1/12` (orthogonality with `s = r = 1`,
where `A_1 = x`). -/
theorem sum_reference_ell_sq_spins : ∑ j : Count, reference j * famEll j ^ 2 = 12 := by
  have hl : ∀ j : Count, famEll j = 12 * moment ⟨0, by decide⟩ j := by
    intro j
    rw [moment_one_spins, meanCoordinate_eq]; unfold famEll; ring
  have h := reference_moment_orthogonal_spins ⟨0, by decide⟩ ⟨0, by decide⟩
  simp only [if_true] at h
  have e : ∀ j : Count, reference j * famEll j ^ 2 =
      144 * (reference j * (moment ⟨0, by decide⟩ j * moment ⟨0, by decide⟩ j)) := by
    intro j; rw [hl j]; ring
  simp_rw [e]
  rw [← Finset.mul_sum, h]
  norm_num [Nat.choose]

/-- Reflection `j ↦ 12 - j` preserves the reference law `b`. -/
theorem reference_rev (j : Count) : reference j.rev = reference j := by
  unfold reference referenceQ
  push_cast
  congr 2
  rw [Fin.val_rev]
  have hj : j.val ≤ 12 := Nat.lt_succ_iff.mp j.isLt
  have : 12 - j.val = 13 - (j.val + 1) := by omega
  rw [← this]
  exact_mod_cast Nat.choose_symm hj

/-- `ℓ` is odd under reflection. -/
theorem famEll_rev (j : Count) : famEll j.rev = - famEll j := by
  unfold famEll
  rw [Fin.val_rev]
  have hj : j.val ≤ 12 := Nat.lt_succ_iff.mp j.isLt
  have : ((13 - (j.val + 1) : ℕ) : ℝ) = 12 - j.val := by
    rw [show 13 - (j.val + 1) = 12 - j.val by omega, Nat.cast_sub hj]; norm_num
  rw [this]; ring

/-- `d` is even under reflection. -/
theorem famD2_rev (j : Count) : famD2 j.rev = famD2 j := by
  unfold famD2
  rw [Fin.val_rev]
  have hj : j.val ≤ 12 := Nat.lt_succ_iff.mp j.isLt
  have : ((13 - (j.val + 1) : ℕ) : ℝ) = 12 - j.val := by
    rw [show 13 - (j.val + 1) = 12 - j.val by omega, Nat.cast_sub hj]; norm_num
  rw [this]; ring

/-- Reflection kills the cubic coefficient:  `ℓ` odd, `d` even, `b` reflection invariant. -/
theorem sum_reference_cubic_reflection : ∑ j : Count,
    reference j * (famEll j * famD2 j - famEll j ^ 3 / 6) = 0 := by
  set S : ℝ := ∑ j : Count, reference j * (famEll j * famD2 j - famEll j ^ 3 / 6) with hS
  have h : S = ∑ j : Count, reference j.rev * (famEll j.rev * famD2 j.rev - famEll j.rev ^ 3 / 6) :=
    (Equiv.sum_comp Fin.revPerm
      (fun j : Count => reference j * (famEll j * famD2 j - famEll j ^ 3 / 6))).symm
  have h2 : ∀ j : Count, reference j.rev * (famEll j.rev * famD2 j.rev - famEll j.rev ^ 3 / 6) =
      -(reference j * (famEll j * famD2 j - famEll j ^ 3 / 6)) := by
    intro j
    rw [reference_rev, famEll_rev, famD2_rev]; ring
  simp_rw [h2] at h
  rw [Finset.sum_neg_distrib] at h
  linarith

end BecknerOnofri.V2.Reaudit.ScalarBridges
