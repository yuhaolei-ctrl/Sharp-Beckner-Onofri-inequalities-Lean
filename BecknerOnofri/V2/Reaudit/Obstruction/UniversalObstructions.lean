module

public import BecknerOnofri.V2.Reaudit.Obstruction.ConcentrationObstruction
public import BecknerOnofri.V2.Reaudit.Obstruction.FirstShellPrimal
public import BecknerOnofri.V2.Vocab.ExternalInputs

@[expose] public section

/-! # Row S006: `lem:section2-universal-obstructions`

The two obstructions to the free energy and to the Beckner--Onofri coefficient:

(i) concentration: `P_d(β) = +∞` for `β > 2d`; `C_d(A) = +∞` for `A < A_crit(d)`; and the defect at
    `A = A_crit(d)` is finite *given the critical Adams inequality*
    (`eq:section2-critical-adams`), which enters as the named hypothesis
    `BecknerOnofri.V2.Vocab.CriticalAdamsInput d` and is not proved here;
(ii) first shell: `P_d(β) > 0` for `β > β_s(d)`; `C_d(A) > 0` for `A < A_s(d)`.

Three separate inputs, as in the printed proof: the concentration test (`ConcentrationObstruction`),
the first-shell perturbation (`FirstShellPrimal`), and the sharp critical finiteness
(`CriticalAdamsInput d`).  The passage between pressure and coefficient defect is
`HighDim.pressure_eq_coefficientDefect` (`prop:section2-coefficient-pressure-duality`). -/

noncomputable section
open MeasureTheory

namespace BecknerOnofri.V2.Reaudit.Obstruction

open BecknerOnofri.HighDim

variable {d : ℕ}

/-! ### (ii) the first-shell perturbation -/

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

/-- **Part (ii), coefficient form:** for `A < A_s(d) = 1/(2 (2π)^d)` the optimal additive defect is
strictly positive. -/
theorem coefficientDefect_pos_of_lt_spectralCoefficient (hd : 0 < d) {A : ℝ}
    (hA : A < spectralCoefficient d) : 0 < coefficientDefect d A := by
  have hσ := spectralThreshold_pos hd
  have hs : 0 < spectralCoefficient d := by unfold spectralCoefficient; positivity
  obtain ⟨B, hB, hBs⟩ := exists_between (max_lt hA hs)
  have hBp : 0 < B := (le_max_right A 0).trans_lt hB
  have hAB : A ≤ B := ((le_max_left A 0).trans_lt hB).le
  let β := spectralThreshold d / (2 * B * (2 * Real.pi) ^ d)
  have hβp : 0 < β := by dsimp [β]; positivity
  have hβ : spectralThreshold d < β := by
    dsimp [β]
    rw [lt_div_iff₀ (by positivity : 0 < 2 * B * (2 * Real.pi) ^ d)]
    unfold spectralCoefficient at hBs
    have hpi : 0 < (2 * Real.pi) ^ d := by positivity
    have := (lt_div_iff₀ (by positivity : 0 < 2 * (2 * Real.pi) ^ d)).mp hBs
    nlinarith
  have he : spectralThreshold d / (2 * β * (2 * Real.pi) ^ d) = B := by
    dsimp [β]
    field_simp
  have hpos := pressure_pos_of_spectralThreshold_lt hd hβ
  rw [pressure_eq_coefficientDefect hd hβp, he] at hpos
  exact hpos.trans_le (coefficientDefect_antitone hd hAB)

/-! ### (i) finiteness at the critical coefficient, conditional on the critical Adams inequality -/

/-- **The defect at `A = A_crit(d)` is finite, given `eq:section2-critical-adams`.**  The hypothesis
`CriticalAdamsInput d` is the manuscript's critical Adams inequality (an external input, cited to
Lebedev--Milin for `d = 1` and to Okikiolu for `d ≥ 2`); it is not proved in this file. -/
theorem coefficientDefect_critical_ne_top (hd : 0 < d)
    (hAdams : V2.Vocab.CriticalAdamsInput d) : coefficientDefect d (collapseCoefficient d) ≠ ⊤ := by
  obtain ⟨B, hB⟩ := (V2.Vocab.criticalAdamsInput_iff hd).mp hAdams
  have h : coefficientDefect d (collapseCoefficient d) ≤ (B : EReal) := by
    apply iSup_le fun u => iSup_le fun hu => ?_
    have h1 := hB u hu
    calc logPartition u - ((collapseCoefficient d * potentialEnergy u : ℝ) : EReal)
        ≤ ((collapseCoefficient d * potentialEnergy u + B : ℝ) : EReal) -
            ((collapseCoefficient d * potentialEnergy u : ℝ) : EReal) := EReal.sub_le_sub h1 le_rfl
      _ = (B : EReal) := by
        rw [← EReal.coe_sub]
        congr 1
        ring
  exact ne_top_of_le_ne_top (EReal.coe_ne_top B) h

/-! ### The lemma -/

/-- **`lem:section2-universal-obstructions`.**  For `d ≥ 1`:

1. `β > 2d` implies `P_d(β) = +∞`; `A < A_crit(d)` implies `C_d(A) = +∞`;
2. under the critical Adams inequality (`CriticalAdamsInput d`), `C_d(A_crit(d)) < +∞`;
3. `β > β_s(d)` implies `P_d(β) > 0`; `A < A_s(d)` implies `C_d(A) > 0`. -/
theorem universal_obstructions (hd : 0 < d) :
    (∀ β : ℝ, 2 * (d : ℝ) < β → pressure d β = ⊤) ∧
    (∀ A : ℝ, A < collapseCoefficient d → coefficientDefect d A = ⊤) ∧
    (V2.Vocab.CriticalAdamsInput d → coefficientDefect d (collapseCoefficient d) ≠ ⊤) ∧
    (∀ β : ℝ, spectralThreshold d < β → 0 < pressure d β) ∧
    (∀ A : ℝ, A < spectralCoefficient d → 0 < coefficientDefect d A) :=
  ⟨fun _ hβ => pressure_eq_top_of_critical_lt hd hβ,
   fun _ hA => coefficientDefect_eq_top_of_lt_critical hd hA,
   fun hAdams => coefficientDefect_critical_ne_top hd hAdams,
   fun _ hβ => pressure_pos_of_spectralThreshold_lt hd hβ,
   fun _ hA => coefficientDefect_pos_of_lt_spectralCoefficient hd hA⟩

end BecknerOnofri.V2.Reaudit.Obstruction
