module

public import BecknerOnofri.V2.Eleven.JointLaw

@[expose] public section

/-! # S028: the literal random-variable form of the steps of the printed proof of `lem:section4-lattice-label-entropy`

Printed proof (P021): `H_Sh(N|Y) ≤ H_Sh(N) ≤ ∑_{j=1}^{11} H_Sh(N_j) = 11 H_Sh(N_1)`
(`eq:section4-label-entropy-subadditivity`), where the first step is "the chain rule for entropy and the
nonnegativity of mutual information", the second is subadditivity, and the equality is the invariance of
the law of `X` (hence of `N`) under coordinate permutations.

For an arbitrary probability space `(Ω, P)` carrying a random vector `X` with density `η_{1/5}`
(`P.map X = JointLaw.lawEta`), with `N = ⌊X + 1/2⌋ ∈ ℤ^{11}` (`JointLaw.rvN`) and `Y = X - N` (`JointLaw.rvY`),
this file proves each of those steps for the *random variables* `N`, `Y`, `N_j = (N)_j`:

* `shannon_rvN`, `shannon_rvNj`: the Shannon entropies `H_Sh(N)`, `H_Sh(N_j)` of the laws `P∘N⁻¹`, `P∘N_j⁻¹`
  are the explicit label sums of the repository (`labelEntropy`, the coordinate-label entropy);
* `H_Sh_N_given_Y_le`, `H_Sh_N_le_sum`, `H_Sh_Nj_eq`: the three steps;
* `label_entropy_chain_rv`: `H_Sh(N|Y) ≤ H_Sh(N) ≤ ∑_j H_Sh(N_j) = 11 H_Sh(N_0)`;
* `condShannon_lt_printed`: `H_Sh(N|Y) < 1/600` (`eq:section4-label-entropy-bound`).

`H_Sh(N|Y)` is `JointLaw.condShannon` (the entropy of the regular conditional distribution
`condDistrib N Y P`), identified with the explicit formula by `JointLaw.condShannon_eq`; the
chain rule `H_Sh(N) = H_Sh(N|Y) + I(N;Y)` with the mutual information `I(N;Y) ≥ 0` is in `MutualInfo.lean`. -/

set_option linter.unusedSectionVars false

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

namespace BecknerOnofri.V2.Reaudit.ElevenBounds

open BecknerOnofri.HighDim
open BecknerOnofri.HighDim.Eleven
  (labelProbability labelEntropy conditionalLabelEntropy coordinateLabelProbability labelCube)
open BecknerOnofri.V2.Eleven.JointLaw

section RV

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → Fin 11 → ℝ}

/-- The `j`-th coordinate `N_j ∈ ℤ` of the lattice label `N`. -/
def rvNj (X : Ω → Fin 11 → ℝ) (j : Fin 11) : Ω → ℤ := fun ω => rvN X ω j

theorem measurable_rvN (hX : Measurable X) : Measurable (rvN X) := measurable_labelN.comp hX

theorem measurable_rvNj (hX : Measurable X) (j : Fin 11) : Measurable (rvNj X j) :=
  (measurable_pi_apply j).comp (measurable_rvN hX)

/-- The law of the lattice label: `P(N = n) = ∫_{[-1/2,1/2)^{11}} η_{1/5}(y + n) dy`. -/
theorem law_rvN_singleton (hX : Measurable X) (hlaw : P.map X = lawEta) (n : Frequency 11) :
    P.map (rvN X) {n} = ENNReal.ofReal (labelProbability n) := by
  have h1 : P.map (rvN X) = lawEta.map labelN := by
    rw [← hlaw, Measure.map_map measurable_labelN hX]; rfl
  rw [h1, Measure.map_apply measurable_labelN (MeasurableSet.singleton n)]
  have hg : Measurable (fun z : (Fin 11 → ℝ) × Frequency 11 => ({n} : Set (Frequency 11)).indicator
      (1 : Frequency 11 → ℝ≥0∞) z.2) :=
    (measurable_one.indicator (MeasurableSet.singleton n)).comp measurable_snd
  have hj := lintegral_joint (fun z => ({n} : Set (Frequency 11)).indicator
      (1 : Frequency 11 → ℝ≥0∞) z.2) hg
  rw [HighDim.Eleven.labelProbability_ofReal]
  have e1 : (∫⁻ x, ({n} : Set (Frequency 11)).indicator (1 : Frequency 11 → ℝ≥0∞)
        (labelY x, labelN x).2 ∂lawEta) = lawEta (labelN ⁻¹' {n}) := by
    rw [← lintegral_indicator_one (measurable_labelN (MeasurableSet.singleton n))]
    refine lintegral_congr fun x => ?_
    by_cases h : labelN x = n <;> simp [Set.indicator, h]
  rw [← e1, hj]
  change _ = ∫⁻ y in PeriodizationCube.cube 11, _
  refine setLIntegral_congr_fun (PeriodizationCube.cube_measurable 11) fun y _ => ?_
  rw [tsum_eq_single n]
  · simp
  · intro m hm
    simp [Set.indicator, hm]

/-- The law of the `j`-th coordinate of the label: `P(N_j = m) = ∫_{[-1/2,1/2)} f_1(t + m) dt`, where
`f_1` is the one-coordinate marginal (`eq:section4-one-coordinate-marginal`); the same for every `j`. -/
theorem law_rvNj_singleton (hX : Measurable X) (hlaw : P.map X = lawEta) (j : Fin 11) (m : ℤ) :
    P.map (rvNj X j) {m} = ENNReal.ofReal (coordinateLabelProbability m) := by
  have hmeas : Measurable (rvNj X j) := measurable_rvNj hX j
  have hc : MeasurableSet {n : Frequency 11 | n j = m} := (Set.to_countable _).measurableSet
  have h1 : P.map (rvNj X j) {m} = P.map (rvN X) {n : Frequency 11 | n j = m} := by
    rw [Measure.map_apply hmeas (MeasurableSet.singleton m),
      Measure.map_apply (measurable_rvN hX) hc]
    rfl
  rw [h1, ← Measure.tsum_indicator_apply_singleton _ _ hc]
  have h2 : ∀ n : Frequency 11, ({n : Frequency 11 | n j = m}).indicator
      (fun n => P.map (rvN X) {n}) n = ({n : Frequency 11 | n j = m}).indicator
      (fun n => ENNReal.ofReal (labelProbability n)) n := by
    intro n
    by_cases h : n j = m <;> simp [Set.indicator, h, law_rvN_singleton hX hlaw n]
  simp_rw [h2]
  rw [← (Fin.insertNthEquiv (fun _ => ℤ) j).tsum_eq, ENNReal.tsum_prod']
  rw [tsum_eq_single m]
  · rw [← HighDim.Eleven.labelProbability_coordinate_lsum j m]
    refine tsum_congr fun m' => ?_
    simp [Set.indicator, Fin.insertNthEquiv]
  · intro a ha
    refine ENNReal.tsum_eq_zero.mpr fun m' => ?_
    simp [Set.indicator, Fin.insertNthEquiv, ha]

theorem shannon_rvN (hX : Measurable X) (hlaw : P.map X = lawEta) :
    shannonEntropy (P.map (rvN X)) = labelEntropy := by
  unfold shannonEntropy labelEntropy
  rw [← tsum_neg]
  refine tsum_congr fun n => ?_
  rw [law_rvN_singleton hX hlaw n, ENNReal.toReal_ofReal (HighDim.Eleven.labelProbability_nonneg n),
    Real.negMulLog_eq_neg]

/-- `H_Sh(N_j)` is the explicit coordinate-label entropy, for every `j`. -/
theorem shannon_rvNj (hX : Measurable X) (hlaw : P.map X = lawEta) (j : Fin 11) :
    shannonEntropy (P.map (rvNj X j)) =
      -(∑' m : ℤ, coordinateLabelProbability m * Real.log (coordinateLabelProbability m)) := by
  unfold shannonEntropy
  rw [← tsum_neg]
  refine tsum_congr fun m => ?_
  rw [law_rvNj_singleton hX hlaw j m, ENNReal.toReal_ofReal (HighDim.Eleven.coordinateLabelProbability_nonneg m),
    Real.negMulLog_eq_neg]

/-- **Invariance under coordinate permutations**: `H_Sh(N_j) = H_Sh(N_0)` for every `j`. -/
theorem H_Sh_Nj_eq (hX : Measurable X) (hlaw : P.map X = lawEta) (j : Fin 11) :
    shannonEntropy (P.map (rvNj X j)) = shannonEntropy (P.map (rvNj X 0)) := by
  rw [shannon_rvNj hX hlaw, shannon_rvNj hX hlaw]

/-- **Chain rule + nonnegative mutual information, first step of
`eq:section4-label-entropy-subadditivity`:** `H_Sh(N | Y) ≤ H_Sh(N)`. -/
theorem H_Sh_N_given_Y_le (hX : Measurable X) (hlaw : P.map X = lawEta) :
    condShannon P (rvN X) (rvY X) ≤ shannonEntropy (P.map (rvN X)) := by
  rw [condShannon_eq hX hlaw, shannon_rvN hX hlaw]
  exact HighDim.Eleven.conditionalLabelEntropy_le_labelEntropy

/-- **Subadditivity, second step of `eq:section4-label-entropy-subadditivity`:**
`H_Sh(N) ≤ ∑_{j=1}^{11} H_Sh(N_j)`. -/
theorem H_Sh_N_le_sum (hX : Measurable X) (hlaw : P.map X = lawEta) :
    shannonEntropy (P.map (rvN X)) ≤ ∑ j : Fin 11, shannonEntropy (P.map (rvNj X j)) := by
  rw [shannon_rvN hX hlaw]
  simp_rw [shannon_rvNj hX hlaw]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]
  exact HighDim.Eleven.labelEntropy_subadditive.2

/-- **`eq:section4-label-entropy-subadditivity` for the random variables `N`, `Y`:**
`H_Sh(N|Y) ≤ H_Sh(N) ≤ ∑_{j=1}^{11} H_Sh(N_j) = 11 H_Sh(N_1)`. -/
theorem label_entropy_chain_rv (hX : Measurable X) (hlaw : P.map X = lawEta) :
    condShannon P (rvN X) (rvY X) ≤ shannonEntropy (P.map (rvN X)) ∧
      shannonEntropy (P.map (rvN X)) ≤ ∑ j : Fin 11, shannonEntropy (P.map (rvNj X j)) ∧
      ∑ j : Fin 11, shannonEntropy (P.map (rvNj X j)) = 11 * shannonEntropy (P.map (rvNj X 0)) := by
  refine ⟨H_Sh_N_given_Y_le hX hlaw, H_Sh_N_le_sum hX hlaw, ?_⟩
  simp_rw [H_Sh_Nj_eq hX hlaw]
  simp

end RV

end BecknerOnofri.V2.Reaudit.ElevenBounds
