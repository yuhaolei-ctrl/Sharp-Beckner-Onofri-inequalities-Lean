module

public import BecknerOnofri.V2.Reaudit.Obstruction.FirstShellPrimal
public import BecknerOnofri.SubcriticalGap

@[expose] public section

/-! # Row S006, part (ii), pressure form: the first-shell perturbation

`P_d(β) > 0` for `β > β_s(d)`, proved as printed (`eq:section2-first-shell-free-energy`): test the
free energy on the first-shell density `ρ_t = 1 + t cos(2π x_j)` constructed in `FirstShellPrimal`.

This statement is placed in its own module, upstream of `PressureDuality` and of the variational
quotient, so that every user of the positivity of the pressure above `β_s` (the proof of
`quotient_set_nonempty`, the Theorem 1.2 route, the onset lemmas) runs this single proof; the older
name `HighDim.pressure_pos_of_spectral_lt` is an alias of it. -/

noncomputable section
open MeasureTheory

namespace BecknerOnofri.V2.Reaudit.Obstruction

open BecknerOnofri.HighDim

variable {d : ℕ}

/-- **Printed `eq:section2-first-shell-free-energy` and part (ii), pressure form.** -/
theorem pressure_pos_of_spectralThreshold_lt (hd : 0 < d) {β : ℝ}
    (hβ : spectralThreshold d < β) : 0 < pressure d β := by
  let j : Fin d := ⟨0, hd⟩
  have hσ := spectralThreshold_pos hd
  set σ := spectralThreshold d with hσdef
  set q : ℝ := β / σ - 1 with hq
  have hqpos : 0 < q := by
    rw [hq, sub_pos, one_lt_div hσ]
    exact hβ
  set t : ℝ := min (1 / 2) (q / 16) with ht
  have htpos : 0 < t := lt_min (by norm_num) (by positivity)
  have ht12 : t ≤ 1 / 2 := min_le_left _ _
  have htq : t ≤ q / 16 := min_le_right _ _
  have habs : |t| = t := abs_of_pos htpos
  have htlt : |t| < 1 := by rw [habs]; linarith
  let ρ := firstShellDensity j htlt
  have hfin : ρ.FiniteEntropy := firstShellDensity_finiteEntropy j htlt
  have hent : entropy ρ ≤ t ^ 2 / 4 + 2 * |t| ^ 3 :=
    entropy_firstShell_le j (by rw [habs]; exact ht12)
  have hE : spectralEnergy ρ = ENNReal.ofReal (t ^ 2 / 2) := spectralEnergy_firstShell j htlt
  have hval : pressureValue β ρ =
      ((β / (2 * σ) * (t ^ 2 / 2) - entropy ρ : ℝ) : EReal) := by
    unfold pressureValue
    rw [hE, EReal.coe_ennreal_ofReal, max_eq_left (by positivity), ← EReal.coe_mul,
      ← EReal.coe_sub]
  have hpos : 0 < β / (2 * σ) * (t ^ 2 / 2) - entropy ρ := by
    have hβσ : β / σ = q + 1 := by rw [hq]; ring
    have h1 : β / (2 * σ) * (t ^ 2 / 2) = (q + 1) * t ^ 2 / 4 := by
      rw [show β / (2 * σ) * (t ^ 2 / 2) = (β / σ) * t ^ 2 / 4 by field_simp; ring, hβσ]
    rw [h1, habs] at *
    nlinarith [pow_pos htpos 2, pow_pos htpos 3, mul_pos hqpos (pow_pos htpos 2)]
  have hpv : (0 : EReal) < pressureValue β ρ := by
    rw [hval]
    exact_mod_cast hpos
  exact hpv.trans_le (le_iSup_of_le ρ (le_iSup_of_le hfin le_rfl))

end BecknerOnofri.V2.Reaudit.Obstruction
