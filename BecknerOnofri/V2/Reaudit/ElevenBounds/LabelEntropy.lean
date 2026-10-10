module

public import BecknerOnofri.V2.Reaudit.ElevenBounds.MutualInfo
public import BecknerOnofri.ElevenConstants

@[expose] public section

/-! # S028: `lem:section4-lattice-label-entropy`, `H_Sh(N|Y) < 1/600`, step by step as printed

The printed proof (P021), for the random variables of `eq:section4-lattice-label-decomposition`:

1. `H_Sh(N|Y) ≤ H_Sh(N) ≤ ∑_j H_Sh(N_j) = 11 H_Sh(N_1)`   (`LabelChain`, `MutualInfo`);
2. the first absolute moment `E|N_1| < 83927/8121093750`      (`expect_abs_rvNj_lt`,
   `eq:section4-label-first-moment-rational`);
3. the comparison with the two-sided geometric law `q_n = (1-r_0)/(1+r_0) r_0^{|n|}`, `r_0 = 2^{-18}`:
   `H_Sh(N_1) ≤ 18 log 2 · E|N_1| + log((1+r_0)/(1-r_0))`      (`H_Sh_rvNj_le_geometric`,
   `eq:section4-geometric-entropy-comparison`);
4. `log 2 < 7/10`, `log((1+r_0)/(1-r_0)) ≤ 2r_0/(1-r_0²)` and the exact rational comparison
   `11 (63/5 · 83927/8121093750 + 2^19/(2^36-1)) < 1/600`        (`label_entropy_final_rational`,
   `eq:section4-label-entropy-final-rational`);
5. conclusion `H_Sh(N|Y) < 1/600`                                  (`condShannon_lt_printed`).

The repository's own comparison `HighDim.Eleven.conditionalLabelEntropy_lt` concludes `< 1/625` (the same
rational expression is `< 1/625`, `HighDim.Eleven.label_entropy_rational`); `condShannon_lt_printed_of_625`
records the rational weakening `1/625 < 1/600`, and `condShannon_lt_printed` is proved by the printed
computation itself (so both constants are available). -/

set_option linter.unusedSectionVars false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators

namespace BecknerOnofri.V2.Reaudit.ElevenBounds

open BecknerOnofri.HighDim
open BecknerOnofri.V2.Eleven.JointLaw

section RV

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → Fin 11 → ℝ}

/-- `E|N_j|` as an integral over `Ω`: it is the first absolute moment of the coordinate label law. -/
theorem expect_abs_rvNj (hX : Measurable X) (hlaw : P.map X = lawEta) (j : Fin 11) :
    ∫ ω, ((rvNj X j ω).natAbs : ℝ) ∂P = HighDim.Eleven.coordinateLabelMoment := by
  have hmeas := measurable_rvNj hX j
  have hf : Measurable (fun m : ℤ => ((m.natAbs : ℕ) : ℝ)) := measurable_from_top
  rw [← integral_map hmeas.aemeasurable hf.aestronglyMeasurable]
  have hnn : 0 ≤ᵐ[P.map (rvNj X j)] fun m : ℤ => ((m.natAbs : ℕ) : ℝ) :=
    Filter.Eventually.of_forall fun m => by positivity
  rw [integral_eq_lintegral_of_nonneg_ae hnn hf.aestronglyMeasurable, lintegral_countable']
  have hs := HighDim.Eleven.coordinateLabel_abs_moment.1
  have hterm (m : ℤ) : ENNReal.ofReal ((m.natAbs : ℕ) : ℝ) * P.map (rvNj X j) {m} =
      ENNReal.ofReal (HighDim.Eleven.coordinateLabelProbability m * ((m.natAbs : ℕ) : ℝ)) := by
    rw [law_rvNj_singleton hX hlaw j m, mul_comm, ENNReal.ofReal_mul
      (HighDim.Eleven.coordinateLabelProbability_nonneg m)]
  simp_rw [hterm]
  rw [← ENNReal.ofReal_tsum_of_nonneg
    (fun m => mul_nonneg (HighDim.Eleven.coordinateLabelProbability_nonneg m) (by positivity)) hs,
    ENNReal.toReal_ofReal (tsum_nonneg fun m =>
      mul_nonneg (HighDim.Eleven.coordinateLabelProbability_nonneg m) (by positivity))]
  rfl

/-- **`eq:section4-label-first-moment-rational`:** `E|N_1| < 83927/8121093750` (each coordinate). -/
theorem expect_abs_rvNj_lt (hX : Measurable X) (hlaw : P.map X = lawEta) (j : Fin 11) :
    ∫ ω, ((rvNj X j ω).natAbs : ℝ) ∂P < 83927 / 8121093750 := by
  rw [expect_abs_rvNj hX hlaw j]
  exact HighDim.Eleven.coordinateLabelMoment_lt

/-- **`eq:section4-geometric-entropy-comparison`:** with `r_0 = 2^{-18}`,
`H_Sh(N_j) ≤ 18 log 2 · E|N_j| + log((1+r_0)/(1-r_0))` (nonnegativity of the relative entropy of the law
of `N_j` with respect to the two-sided geometric law). -/
theorem H_Sh_rvNj_le_geometric (hX : Measurable X) (hlaw : P.map X = lawEta) (j : Fin 11) :
    shannonEntropy (P.map (rvNj X j)) ≤
      18 * Real.log 2 * (∫ ω, ((rvNj X j ω).natAbs : ℝ) ∂P) +
        Real.log ((1 + 1 / 2 ^ 18) / (1 - 1 / 2 ^ 18)) := by
  rw [shannon_rvNj hX hlaw, expect_abs_rvNj hX hlaw j]
  have hh := CountableShannon.entropy_le_geometric_moment
    HighDim.Eleven.coordinateLabelProbability HighDim.Eleven.coordinateLabelProbability_nonneg
    HighDim.Eleven.coordinateLabelProbability_hasSum HighDim.Eleven.coordinateLabel_abs_moment.1
    (by norm_num : (0 : ℝ) < 1 / 2 ^ 18) (by norm_num : (1 : ℝ) / 2 ^ 18 < 1)
  have hl : -Real.log ((1 : ℝ) / 2 ^ 18) = 18 * Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num), Real.log_one, Real.log_pow]
    norm_num
  rw [hl] at hh
  exact hh.2

end RV

/-- **`eq:section4-label-entropy-final-rational`** (printed): `11 (63/5 · 83927/8121093750 +
2^19/(2^36-1)) < 1/600`. -/
theorem label_entropy_final_rational :
    (11 : ℝ) * ((63 / 5) * (83927 / 8121093750) + 2 ^ 19 / (2 ^ 36 - 1)) < 1 / 600 := by
  norm_num

/-- The elementary bounds `eq:section4-elementary-log-bounds`. -/
theorem elementary_log_bounds :
    Real.log 2 < 7 / 10 ∧
      Real.log ((1 + 1 / 2 ^ 18) / (1 - 1 / 2 ^ 18)) ≤ 2 ^ 19 / (2 ^ 36 - 1) := by
  refine ⟨by linarith [Real.log_two_lt_d9], ?_⟩
  have hn := CountableShannon.geometric_log_normalizer (by norm_num : (0 : ℝ) ≤ 1 / 2 ^ 18)
    (by norm_num : (1 : ℝ) / 2 ^ 18 < 1)
  refine hn.trans_eq ?_
  norm_num

section RV2

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → Fin 11 → ℝ}

/-- `11 H_Sh(N_1) < 1/600`, following the printed computation after
`eq:section4-geometric-entropy-comparison`. -/
theorem eleven_H_Sh_rvNj_lt (hX : Measurable X) (hlaw : P.map X = lawEta) :
    11 * shannonEntropy (P.map (rvNj X 0)) < 1 / 600 := by
  have h1 := H_Sh_rvNj_le_geometric hX hlaw 0
  have hm := expect_abs_rvNj_lt hX hlaw 0
  have hm0 : 0 ≤ ∫ ω, ((rvNj X 0 ω).natAbs : ℝ) ∂P := integral_nonneg fun ω => by positivity
  obtain ⟨hl2, hl3⟩ := elementary_log_bounds
  have hb : 18 * Real.log 2 * (∫ ω, ((rvNj X 0 ω).natAbs : ℝ) ∂P) <
      (63 / 5) * (83927 / 8121093750) := by
    calc _ ≤ (63 / 5 : ℝ) * (∫ ω, ((rvNj X 0 ω).natAbs : ℝ) ∂P) :=
          mul_le_mul_of_nonneg_right (by linarith) hm0
      _ < _ := mul_lt_mul_of_pos_left hm (by norm_num)
  have := label_entropy_final_rational
  nlinarith

/-- **`lem:section4-lattice-label-entropy`** (`eq:section4-label-entropy-bound`), for the random
variables of `eq:section4-lattice-label-decomposition`: `H_Sh(N|Y) < 1/600`, by the printed chain
`H_Sh(N|Y) ≤ H_Sh(N) ≤ 11 H_Sh(N_1) < 1/600`. -/
theorem condShannon_lt_printed (hX : Measurable X) (hlaw : P.map X = lawEta) :
    condShannon P (rvN X) (rvY X) < 1 / 600 := by
  obtain ⟨h1, h2, h3⟩ := label_entropy_chain_rv hX hlaw
  have := eleven_H_Sh_rvNj_lt hX hlaw
  linarith

/-- The repository's stronger comparison `H_Sh(N|Y) < 1/625` for the same random variables (the printed
rational expression is `< 1/625`; `HighDim.Eleven.label_entropy_rational`). -/
theorem condShannon_lt_625 (hX : Measurable X) (hlaw : P.map X = lawEta) :
    condShannon P (rvN X) (rvY X) < 1 / 625 := by
  rw [condShannon_eq hX hlaw]
  exact HighDim.Eleven.conditionalLabelEntropy_lt

/-- The rational weakening of the proved `1/625` comparison to the printed `1/600`. -/
theorem condShannon_lt_printed_of_625 (hX : Measurable X) (hlaw : P.map X = lawEta) :
    condShannon P (rvN X) (rvY X) < 1 / 600 :=
  (condShannon_lt_625 hX hlaw).trans (by norm_num)

end RV2

/-- The explicit-sum form (no probability space): `H_Sh(N|Y) = conditionalLabelEntropy < 1/600`. -/
theorem conditionalLabelEntropy_lt_printed : HighDim.Eleven.conditionalLabelEntropy < 1 / 600 :=
  HighDim.Eleven.conditionalLabelEntropy_lt.trans (by norm_num)

end BecknerOnofri.V2.Reaudit.ElevenBounds
