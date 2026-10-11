module

public import BecknerOnofri.V2.Reaudit.ElevenBounds.LabelChain
public import BecknerOnofri.ElevenConditionalEntropy

@[expose] public section

/-! # S028: the chain rule `H_Sh(N) = H_Sh(N|Y) + I(N;Y)` and `I(N;Y) ≥ 0`, as random variables

The first step of `eq:section4-label-entropy-subadditivity` is "the chain rule for entropy and
nonnegativity of mutual information".  For the lattice-label decomposition `X = Y + N` of a random vector
with density `η_{1/5}` this file proves, on an arbitrary probability space,

  `H_Sh(N) = H_Sh(N|Y) + I(N;Y)` (`chain_rule_rv`) and `0 ≤ I(N;Y)` (`mutualInfo_nonneg`),

where `H_Sh(N|Y) = JointLaw.condShannon` is the entropy of the regular conditional distribution, and the
mutual information is `I(N;Y) = ∫ D(P_{N|Y=y} ‖ P_N) dP_Y(y)` with the discrete relative entropy
`D(ν‖μ) = ∑_b ν{b} log(ν{b}/μ{b})` (`klDiscrete`, `mutualInfo`).  Its proof is the same Fubini-Tonelli
and Gibbs-inequality argument as in the repository's `conditionalLabelEntropy_le_labelEntropy`, reorganised
so that the defect is the mutual information. -/

set_option linter.unusedSectionVars false

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators

namespace BecknerOnofri.V2.Reaudit.ElevenBounds

open BecknerOnofri.HighDim
open BecknerOnofri.HighDim.Eleven
  (labelProbability labelEntropy conditionalLabelEntropy conditionalLabel labelLogIntegrand
    labelCube periodizedProfile)
open BecknerOnofri.V2.Eleven (periodization11 periodizedProfile_lift')
open BecknerOnofri.V2.Eleven.JointLaw

/-- The discrete relative entropy `D(ν‖μ) = ∑_b ν{b} log(ν{b}/μ{b})` (real-valued; used for laws on a
countable label space with `μ{b} > 0`). -/
def klDiscrete {β : Type*} [MeasurableSpace β] (ν μ : Measure β) : ℝ :=
  ∑' b, (ν {b}).toReal * Real.log ((ν {b}).toReal / (μ {b}).toReal)

/-- The mutual information `I(N;Y) = ∫ D(P_{N|Y=y} ‖ P_N) dP_Y(y)` of random variables `N`, `Y`,
with `P_{N|Y=y} = condDistrib N Y P y` the regular conditional distribution. -/
def mutualInfo {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (N : Ω → Frequency 11) (Y : Ω → Fin 11 → ℝ) : ℝ :=
  ∫ y, klDiscrete (condDistrib N Y P y) (P.map N) ∂(P.map Y)

/-- The explicit relative entropy of the conditional label law `p(·|y)` against the label law `q`. -/
def klKer (y : Fin 11 → ℝ) : ℝ :=
  ∑' n : Frequency 11, pLab n y * Real.log (pLab n y / labelProbability n)

theorem condKer_singleton_toReal (y : Fin 11 → ℝ) (n : Frequency 11) :
    (condKer y {n}).toReal = pLab n y := by
  rw [condKer_apply, condLaw_apply]
  have : ∑' m : Frequency 11, ENNReal.ofReal (pLab m y) * ({n} : Set (Frequency 11)).indicator 1 m =
      ENNReal.ofReal (pLab n y) := by
    rw [tsum_eq_single n]
    · simp
    · intro m hm; simp [hm]
  rw [this, ENNReal.toReal_ofReal (pLab_nonneg n y)]

theorem klDiscrete_condKer {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → Fin 11 → ℝ} (hX : Measurable X) (hlaw : P.map X = lawEta) (y : Fin 11 → ℝ) :
    klDiscrete (condKer y) (P.map (rvN X)) = klKer y := by
  unfold klDiscrete klKer
  refine tsum_congr fun n => ?_
  rw [condKer_singleton_toReal, law_rvN_singleton hX hlaw n,
    ENNReal.toReal_ofReal (HighDim.Eleven.labelProbability_nonneg n)]

/-- Pointwise: for `y` in the fundamental cube with a summable cross term,
`ρ_*(y) · D(p(·|y)‖q) = ρ_*(y) ∑ p log p - ∑_n η(y+n) log q(n)` and `D(p(·|y)‖q) ≥ 0` (Gibbs). -/
theorem klKer_pointwise {y : Fin 11 → ℝ} (hy : y ∈ labelCube)
    (hs : Summable (fun n => labelLogIntegrand n y)) :
    0 ≤ klKer y ∧
      periodization11 y * klKer y =
        periodization11 y * (∑' n : Frequency 11, conditionalLabel y n *
          Real.log (conditionalLabel y n)) - ∑' n, labelLogIntegrand n y := by
  have hρ : 0 < periodization11 y := periodization11_pos y
  have hρe : periodizedProfile (fun i => (y i : UnitAddCircle)) = periodization11 y := by
    rw [periodizedProfile_lift']
  have hpl (n : Frequency 11) : pLab n y = conditionalLabel y n := (conditionalLabel_eq_pLab y n).symm
  have hmass : HasSum (conditionalLabel y) 1 :=
    (HighDim.Eleven.conditionalLabel_mass hy) ▸ (HighDim.Eleven.conditionalLabel_summable y).hasSum
  have hcross : Summable (fun n => conditionalLabel y n * Real.log (labelProbability n)) := by
    simp_rw [HighDim.Eleven.conditional_cross_term]
    exact hs.div_const _
  have h := CountableShannon.entropy_comparison (conditionalLabel y) labelProbability
    (fun n => (HighDim.Eleven.conditionalLabel_pos y n).le) HighDim.Eleven.labelProbability_pos hmass
    HighDim.Eleven.labelProbability_hasSum hcross
  have hkl : klKer y = (∑' n, conditionalLabel y n * Real.log (conditionalLabel y n)) -
      ∑' n, conditionalLabel y n * Real.log (labelProbability n) := by
    unfold klKer
    rw [← h.1.tsum_sub hcross]
    refine tsum_congr fun n => ?_
    rw [hpl, Real.log_div (HighDim.Eleven.conditionalLabel_pos y n).ne'
      (HighDim.Eleven.labelProbability_pos n).ne']
    ring
  refine ⟨?_, ?_⟩
  · rw [hkl]; linarith [h.2]
  · rw [hkl, mul_sub]
    congr 1
    simp_rw [HighDim.Eleven.conditional_cross_term, hρe]
    rw [tsum_div_const, mul_div_cancel₀ _ hρ.ne']

section RV

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → Fin 11 → ℝ}

theorem mutualInfo_eq_integral (hX : Measurable X) (hlaw : P.map X = lawEta) :
    mutualInfo P (rvN X) (rvY X) = ∫ y, klKer y ∂lawY := by
  unfold mutualInfo
  rw [map_rvY hX hlaw]
  have h := condDistrib_eq hX hlaw
  rw [map_rvY hX hlaw] at h
  refine integral_congr_ae ?_
  filter_upwards [h] with y hy
  rw [hy, klDiscrete_condKer hX hlaw]

theorem integral_klKer :
    ∫ y, klKer y ∂lawY = labelEntropy - conditionalLabelEntropy := by
  unfold lawY
  have hρ' : Measurable (fun y : Fin 11 → ℝ => ENNReal.ofReal (periodization11 y)) :=
    ENNReal.measurable_ofReal.comp measurable_periodization11
  rw [integral_withDensity_eq_integral_toReal_smul hρ'
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  have hae : (fun y => (ENNReal.ofReal (periodization11 y)).toReal • klKer y) =ᵐ[volume.restrict
      (PeriodizationCube.cube 11)] fun y =>
      periodizedProfile (fun i => (y i : UnitAddCircle)) * (∑' n : Frequency 11,
        conditionalLabel y n * Real.log (conditionalLabel y n)) - ∑' n, labelLogIntegrand n y := by
    filter_upwards [ae_restrict_mem (PeriodizationCube.cube_measurable 11),
      HighDim.Eleven.labelLogIntegrand_series.1] with y hy hs
    rw [ENNReal.toReal_ofReal (periodization11_pos y).le, smul_eq_mul,
      (klKer_pointwise hy hs).2, periodizedProfile_lift']
  rw [integral_congr_ae hae]
  have h2 := integral_sub (μ := volume.restrict labelCube)
    HighDim.Eleven.conditional_entropy_integrable HighDim.Eleven.labelLogIntegrand_series.2
  refine h2.trans ?_
  rw [HighDim.Eleven.labelLogIntegrand_series_integral]
  unfold conditionalLabelEntropy labelEntropy
  ring

/-- **`I(N;Y) ≥ 0`.** -/
theorem mutualInfo_nonneg (hX : Measurable X) (hlaw : P.map X = lawEta) :
    0 ≤ mutualInfo P (rvN X) (rvY X) := by
  rw [mutualInfo_eq_integral hX hlaw]
  have h : ∀ᵐ y ∂(volume.restrict (PeriodizationCube.cube 11)), 0 ≤ klKer y := by
    filter_upwards [ae_restrict_mem (PeriodizationCube.cube_measurable 11),
      HighDim.Eleven.labelLogIntegrand_series.1] with y hy hs
    exact (klKer_pointwise hy hs).1
  exact integral_nonneg_of_ae ((withDensity_absolutelyContinuous _ _).ae_le h)

/-- **The chain rule `H_Sh(N) = H_Sh(N|Y) + I(N;Y)`** for the lattice-label decomposition. -/
theorem chain_rule_rv (hX : Measurable X) (hlaw : P.map X = lawEta) :
    shannonEntropy (P.map (rvN X)) =
      condShannon P (rvN X) (rvY X) + mutualInfo P (rvN X) (rvY X) := by
  rw [shannon_rvN hX hlaw, condShannon_eq hX hlaw, mutualInfo_eq_integral hX hlaw, integral_klKer]
  ring

/-- `H_Sh(N|Y) ≤ H_Sh(N)`, from the chain rule and the nonnegativity of the mutual information
(the first step of `eq:section4-label-entropy-subadditivity`, literally as printed). -/
theorem H_Sh_N_given_Y_le_of_chain (hX : Measurable X) (hlaw : P.map X = lawEta) :
    condShannon P (rvN X) (rvY X) ≤ shannonEntropy (P.map (rvN X)) := by
  rw [chain_rule_rv hX hlaw]
  linarith [mutualInfo_nonneg hX hlaw]

/-- **`eq:section4-label-entropy-subadditivity` for the random variables `N`, `Y`, with the first step
proved as printed** (chain rule and nonnegativity of the mutual information,
`H_Sh_N_given_Y_le_of_chain`): `H_Sh(N|Y) ≤ H_Sh(N) ≤ ∑_{j=1}^{11} H_Sh(N_j) = 11 H_Sh(N_1)`.
The statement is that of `label_entropy_chain_rv` (`LabelChain`), whose first step goes through the
repository's explicit-sum comparison `conditionalLabelEntropy_le_labelEntropy`. -/
theorem label_entropy_chain_rv_printed (hX : Measurable X) (hlaw : P.map X = lawEta) :
    condShannon P (rvN X) (rvY X) ≤ shannonEntropy (P.map (rvN X)) ∧
      shannonEntropy (P.map (rvN X)) ≤ ∑ j : Fin 11, shannonEntropy (P.map (rvNj X j)) ∧
      ∑ j : Fin 11, shannonEntropy (P.map (rvNj X j)) = 11 * shannonEntropy (P.map (rvNj X 0)) := by
  refine ⟨H_Sh_N_given_Y_le_of_chain hX hlaw, H_Sh_N_le_sum hX hlaw, ?_⟩
  simp_rw [H_Sh_Nj_eq hX hlaw]
  simp

end RV

end BecknerOnofri.V2.Reaudit.ElevenBounds
