module

public import BecknerOnofri.V2.Eleven.PeriodizationSeries
public import BecknerOnofri.V2.Eleven.Estimates
public import BecknerOnofri.PeriodizationCube
public import BecknerOnofri.ElevenConditionalEntropy
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.Probability.Kernel.CondDistrib

@[expose] public section

/-! # Lemma 4.3 (`lem:section4-periodization-entropy-identity`), probabilistic form

Let `X` be a random vector in `ℝ^{11}` with density `η_{1/5}`, `X = Y + N` with `Y ∈ [-1/2,1/2)^{11}`
and `N ∈ ℤ^{11}` (`eq:section4-lattice-label-decomposition`).  This file proves, for an arbitrary
probability space carrying such an `X`:

* the joint law of `(Y,N)` is `ν ⊗ₘ κ`, where `ν` is the law of `Y` (a measure on the cube with
  density `ρ_*`) and `κ_y = Σ_n p(n|y) δ_n`, `p(n|y) = η_{1/5}(y+n)/ρ_*(y)`
  (`eq:section4-conditional-label-law`);
* `Y` has density `ρ_*` (`JointLaw.law_Y`);
* `condDistrib N Y P = κ` `ν`-a.e., so the conditional Shannon entropy
  `H_Sh(N|Y) := ∫ H(condDistrib N Y P y) d(P∘Y⁻¹)(y)` is the explicit formula
  `eq:section4-conditional-entropy-formula` (`= HighDim.Eleven.conditionalLabelEntropy`);
* the identity `Ent(ρ_*) = Ent_ℝ(η_{1/5}) + H_Sh(N|Y)` and the bound `H_Sh(N|Y) < 1/600` for this
  probabilistic `H_Sh`.

Route difference: the chain rule `eq:section4-entropy-chain-rule-proof` and the estimates
`H(N|Y) ≤ H(N) ≤ Σ H(N_j) = 11 H(N_1)` are not re-proved at the level of random variables; the
existing explicit-sum versions are transported to `H_Sh` by the identification above. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace BecknerOnofri.V2.Eleven

open BecknerOnofri.HighDim
open BecknerOnofri.HighDim.Eleven (euclideanProfile periodizedProfile)

namespace JointLaw

/-- The law of the random vector `X` with density `η_{1/5}`. -/
def lawEta : Measure (Fin 11 → ℝ) :=
  volume.withDensity (fun x => ENNReal.ofReal (euclideanProfile x))

/-- The lattice label `N(x) = ⌊x + 1/2⌋ ∈ ℤ^{11}` (so that `x - N(x) ∈ [-1/2,1/2)^{11}`). -/
def labelN (x : Fin 11 → ℝ) : Frequency 11 := fun i => ⌊x i + 1 / 2⌋

/-- The representative `Y = X - N ∈ [-1/2,1/2)^{11}`. -/
def labelY (x : Fin 11 → ℝ) : Fin 11 → ℝ := fun i => x i - (labelN x i : ℝ)

theorem measurable_labelN : Measurable labelN := by
  refine measurable_pi_iff.2 fun i => ?_
  exact (Int.measurable_floor.comp ((measurable_pi_apply i).add_const _))

theorem measurable_labelY : Measurable labelY := by
  refine measurable_pi_iff.2 fun i => ?_
  exact (measurable_pi_apply i).sub (measurable_from_top.comp
    ((measurable_pi_apply i).comp measurable_labelN))

theorem labelN_add {y : Fin 11 → ℝ} (hy : y ∈ PeriodizationCube.cube 11) (n : Frequency 11) :
    labelN (fun i => y i + (n i : ℝ)) = n := by
  funext i
  have h := hy i (mem_univ i)
  simp only [labelN, Int.floor_eq_iff]
  constructor <;> linarith [h.1, h.2]

theorem labelY_add {y : Fin 11 → ℝ} (hy : y ∈ PeriodizationCube.cube 11) (n : Frequency 11) :
    labelY (fun i => y i + (n i : ℝ)) = y := by
  funext i
  simp [labelY, labelN_add hy n]

theorem labelY_mem_cube (x : Fin 11 → ℝ) : labelY x ∈ PeriodizationCube.cube 11 := by
  intro i _
  have h1 := Int.floor_le (x i + 1 / 2)
  have h2 := Int.lt_floor_add_one (x i + 1 / 2)
  simp only [labelY, labelN]
  constructor <;> linarith

theorem labelY_add_labelN (x : Fin 11 → ℝ) :
    (fun i => labelY x i + (labelN x i : ℝ)) = x := by
  funext i; simp [labelY]

/-- `lawEta` is a probability measure. -/
theorem lawEta_univ : lawEta Set.univ = 1 := by
  unfold lawEta
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal HighDim.Eleven.euclideanProfile_integrable
      (Filter.Eventually.of_forall fun x => (HighDim.Eleven.euclideanProfile_pos x).le),
    HighDim.Eleven.euclideanProfile_integral]
  simp

instance : IsProbabilityMeasure lawEta := ⟨lawEta_univ⟩

/-! ### The master formula for the joint law of `(Y,N)` -/

/-- For measurable `g ≥ 0`: `E g(Y,N) = ∫_{cube} Σ_n g(y,n) η_{1/5}(y+n) dy`
(unfolding the fundamental cube, `PeriodizationCube.unfold_lintegral`). -/
theorem lintegral_joint (g : (Fin 11 → ℝ) × Frequency 11 → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ x, g (labelY x, labelN x) ∂lawEta =
      ∫⁻ y in PeriodizationCube.cube 11, ∑' n : Frequency 11,
        g (y, n) * ENNReal.ofReal (euclideanProfile (fun i => y i + (n i : ℝ))) := by
  have hmeas : Measurable (fun x : Fin 11 → ℝ => g (labelY x, labelN x)) :=
    hg.comp (measurable_labelY.prodMk measurable_labelN)
  have hη : Measurable (fun x : Fin 11 → ℝ => ENNReal.ofReal (euclideanProfile x)) :=
    ENNReal.measurable_ofReal.comp HighDim.Eleven.euclideanProfile_continuous.measurable
  unfold lawEta
  rw [lintegral_withDensity_eq_lintegral_mul _ hη hmeas]
  have hF : Measurable (fun x : Fin 11 → ℝ =>
      (ENNReal.ofReal (euclideanProfile x)) * g (labelY x, labelN x)) := hη.mul hmeas
  rw [show (fun x => ((fun x => ENNReal.ofReal (euclideanProfile x)) * fun x => g (labelY x, labelN x)) x)
      = fun x => (ENNReal.ofReal (euclideanProfile x)) * g (labelY x, labelN x) from rfl,
    ← PeriodizationCube.unfold_lintegral 11 _ hF]
  refine setLIntegral_congr_fun (PeriodizationCube.cube_measurable 11) fun y hy => ?_
  refine tsum_congr fun n => ?_
  rw [labelN_add hy n, labelY_add hy n, mul_comm]

/-! ### `ρ_*`, the conditional label law and the kernel -/

theorem summable_term (y : Fin 11 → ℝ) : Summable (fun n : Frequency 11 => termProfile n y) := by
  obtain ⟨v, hv, hb⟩ := periodization_M_test ‖y‖ (norm_nonneg _) 0
  refine Summable.of_norm_bounded hv fun n => ?_
  have := hb n y le_rfl
  rwa [norm_iteratedFDeriv_zero] at this

theorem hasSum_term (y : Fin 11 → ℝ) :
    HasSum (fun n : Frequency 11 => termProfile n y) (periodization11 y) :=
  (summable_term y).hasSum

theorem termProfile_pos (n : Frequency 11) (y : Fin 11 → ℝ) : 0 < termProfile n y :=
  HighDim.Eleven.euclideanProfile_pos _

theorem periodization11_pos (y : Fin 11 → ℝ) : 0 < periodization11 y :=
  (summable_term y).tsum_pos (fun n => (termProfile_pos n y).le) 0 (termProfile_pos 0 y)

theorem measurable_periodization11 : Measurable periodization11 :=
  periodization11_contDiff.continuous.measurable

theorem measurable_termProfile (n : Frequency 11) : Measurable (termProfile n) :=
  (termProfile_contDiff n).continuous.measurable

/-- The conditional probability `p(n|y) = η_{1/5}(y+n)/ρ_*(y)` (`eq:section4-conditional-label-law`). -/
def pLab (n : Frequency 11) (y : Fin 11 → ℝ) : ℝ := termProfile n y / periodization11 y

theorem pLab_nonneg (n : Frequency 11) (y : Fin 11 → ℝ) : 0 ≤ pLab n y :=
  div_nonneg (termProfile_pos n y).le (periodization11_pos y).le

theorem hasSum_pLab (y : Fin 11 → ℝ) : HasSum (fun n => pLab n y) 1 := by
  have := (hasSum_term y).div_const (periodization11 y)
  rwa [div_self (periodization11_pos y).ne'] at this

theorem measurable_pLab (n : Frequency 11) : Measurable (pLab n) :=
  (measurable_termProfile n).div measurable_periodization11

/-- The conditional law of the label given `Y = y`: `Σ_n p(n|y) δ_n`. -/
def condLaw (y : Fin 11 → ℝ) : Measure (Frequency 11) :=
  Measure.sum fun n => ENNReal.ofReal (pLab n y) • Measure.dirac n

theorem condLaw_apply (y : Fin 11 → ℝ) (s : Set (Frequency 11)) :
    condLaw y s = ∑' n : Frequency 11, ENNReal.ofReal (pLab n y) * s.indicator 1 n := by
  have hs : MeasurableSet s := s.to_countable.measurableSet
  unfold condLaw
  rw [Measure.sum_apply _ hs]
  refine tsum_congr fun n => ?_
  rw [Measure.smul_apply, Measure.dirac_apply' _ hs, smul_eq_mul]

theorem condLaw_univ (y : Fin 11 → ℝ) : condLaw y Set.univ = 1 := by
  rw [condLaw_apply]
  simp only [Set.indicator_univ, Pi.one_apply, mul_one]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => pLab_nonneg n y) (hasSum_pLab y).summable,
    (hasSum_pLab y).tsum_eq]
  simp

/-- The conditional-law kernel. -/
def condKer : Kernel (Fin 11 → ℝ) (Frequency 11) where
  toFun := condLaw
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun s _ => ?_
    simp only [condLaw_apply]
    exact Measurable.tsum fun n =>
      (ENNReal.measurable_ofReal.comp (measurable_pLab n)).mul_const _

theorem condKer_apply (y : Fin 11 → ℝ) : condKer y = condLaw y := rfl

instance : IsMarkovKernel condKer := ⟨fun y => ⟨by rw [condKer_apply]; exact condLaw_univ y⟩⟩

/-- The law of `Y`: density `ρ_*` on the cube (`Y` has density `ρ_*`). -/
def lawY : Measure (Fin 11 → ℝ) :=
  (volume.restrict (PeriodizationCube.cube 11)).withDensity fun y => ENNReal.ofReal (periodization11 y)

instance : SFinite lawY := by unfold lawY; infer_instance

/-- **The joint law of `(Y,N)` is `ν ⊗ₘ κ`.** -/
theorem map_joint_eq_compProd :
    lawEta.map (fun x => (labelY x, labelN x)) = lawY ⊗ₘ condKer := by
  refine Measure.ext fun S hS => ?_
  have hmeasYN : Measurable (fun x : Fin 11 → ℝ => (labelY x, labelN x)) :=
    measurable_labelY.prodMk measurable_labelN
  have hind : Measurable (S.indicator (1 : (Fin 11 → ℝ) × Frequency 11 → ℝ≥0∞)) :=
    measurable_one.indicator hS
  have hL : lawEta.map (fun x => (labelY x, labelN x)) S =
      ∫⁻ x, S.indicator (1 : (Fin 11 → ℝ) × Frequency 11 → ℝ≥0∞) (labelY x, labelN x) ∂lawEta := by
    rw [Measure.map_apply hmeasYN hS, ← lintegral_indicator_one (hmeasYN hS)]
    refine lintegral_congr fun x => ?_
    by_cases h : (labelY x, labelN x) ∈ S <;> simp [Set.indicator, h]
  rw [hL, lintegral_joint _ hind, Measure.compProd_apply hS]
  unfold lawY
  have hρ' : Measurable (fun y : Fin 11 → ℝ => ENNReal.ofReal (periodization11 y)) :=
    ENNReal.measurable_ofReal.comp measurable_periodization11
  rw [lintegral_withDensity_eq_lintegral_mul _ hρ' (Kernel.measurable_kernel_prodMk_left hS)]
  refine setLIntegral_congr_fun (PeriodizationCube.cube_measurable 11) fun y _ => ?_
  have hρy := periodization11_pos y
  show _ = ENNReal.ofReal (periodization11 y) * condKer y (Prod.mk y ⁻¹' S)
  rw [condKer_apply, condLaw_apply, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun n => ?_
  have e : S.indicator (1 : (Fin 11 → ℝ) × Frequency 11 → ℝ≥0∞) (y, n) =
      (Prod.mk y ⁻¹' S).indicator 1 n := by
    by_cases h : (y, n) ∈ S <;> simp [Set.indicator, h]
  rw [e, ← mul_assoc, ← ENNReal.ofReal_mul hρy.le, mul_comm (ENNReal.ofReal _) ((Prod.mk y ⁻¹' S).indicator 1 n)]
  congr 2
  unfold pLab
  field_simp
  rfl

/-! ### Marginal law of `Y`, regular conditional distribution of `N` given `Y` -/

theorem map_labelY : lawEta.map labelY = lawY := by
  have h := congrArg Measure.fst map_joint_eq_compProd
  rw [Measure.fst_compProd] at h
  rw [← h, Measure.fst, Measure.map_map measurable_fst
    (measurable_labelY.prodMk measurable_labelN)]
  rfl

/-- Shannon entropy `Σ_b -p_b log p_b` of a (discrete) law. -/
def shannonEntropy {β : Type*} [MeasurableSpace β] (m : Measure β) : ℝ :=
  ∑' b : β, Real.negMulLog (m {b}).toReal

/-- The conditional Shannon entropy `H_Sh(N|Y) = ∫ H(P(N ∈ · | Y = y)) dP_Y(y)`, with the regular
conditional distribution `condDistrib N Y P`. -/
def condShannon {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (N : Ω → Frequency 11) (Y : Ω → Fin 11 → ℝ) : ℝ :=
  ∫ y, shannonEntropy (condDistrib N Y P y) ∂(P.map Y)

section Probabilistic

set_option linter.unusedSectionVars false

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → Fin 11 → ℝ}

/-- The lattice label `N = ⌊X + 1/2⌋` of the random vector `X`. -/
def rvN (X : Ω → Fin 11 → ℝ) : Ω → Frequency 11 := labelN ∘ X

/-- The representative `Y = X - N ∈ [-1/2,1/2)^{11}` of the random vector `X`. -/
def rvY (X : Ω → Fin 11 → ℝ) : Ω → Fin 11 → ℝ := labelY ∘ X

theorem map_rvY (hX : Measurable X) (hlaw : P.map X = lawEta) : P.map (rvY X) = lawY := by
  rw [← map_labelY, ← hlaw, Measure.map_map measurable_labelY hX]
  rfl

theorem map_rv_joint (hX : Measurable X) (hlaw : P.map X = lawEta) :
    P.map (fun ω => (rvY X ω, rvN X ω)) = lawY ⊗ₘ condKer := by
  rw [← map_joint_eq_compProd, ← hlaw,
    Measure.map_map (measurable_labelY.prodMk measurable_labelN) hX]
  rfl

/-- **The conditional law of the lattice label** (`eq:section4-conditional-label-law`):
`condDistrib N Y P = Σ_n p(n|y) δ_n` for `P_Y`-almost every `y`. -/
theorem condDistrib_eq (hX : Measurable X) (hlaw : P.map X = lawEta) :
    condDistrib (rvN X) (rvY X) P =ᵐ[P.map (rvY X)] condKer := by
  have hY : Measurable (rvY X) := measurable_labelY.comp hX
  have hN : Measurable (rvN X) := measurable_labelN.comp hX
  refine condDistrib_ae_eq_of_measure_eq_compProd hY.aemeasurable hN.aemeasurable ?_
  rw [map_rvY hX hlaw]
  exact map_rv_joint hX hlaw

theorem shannonEntropy_condKer (y : Fin 11 → ℝ) :
    shannonEntropy (condKer y) = ∑' n : Frequency 11, Real.negMulLog (pLab n y) := by
  unfold shannonEntropy
  refine tsum_congr fun n => ?_
  rw [condKer_apply, condLaw_apply]
  have : ∑' m : Frequency 11, ENNReal.ofReal (pLab m y) * ({n} : Set (Frequency 11)).indicator 1 m =
      ENNReal.ofReal (pLab n y) := by
    rw [tsum_eq_single n]
    · simp
    · intro m hm; simp [hm]
  rw [this, ENNReal.toReal_ofReal (pLab_nonneg n y)]

theorem conditionalLabel_eq_pLab (y : Fin 11 → ℝ) (n : Frequency 11) :
    HighDim.Eleven.conditionalLabel y n = pLab n y := by
  unfold HighDim.Eleven.conditionalLabel pLab
  rw [periodizedProfile_lift']
  rfl

/-- **`H_Sh(N|Y)` is the explicit formula `eq:section4-conditional-entropy-formula`.** -/
theorem condShannon_eq (hX : Measurable X) (hlaw : P.map X = lawEta) :
    condShannon P (rvN X) (rvY X) = HighDim.Eleven.conditionalLabelEntropy := by
  unfold condShannon
  rw [map_rvY hX hlaw]
  have h1 : ∫ y, shannonEntropy (condDistrib (rvN X) (rvY X) P y) ∂lawY =
      ∫ y, shannonEntropy (condKer y) ∂lawY := by
    have := condDistrib_eq hX hlaw
    rw [map_rvY hX hlaw] at this
    refine integral_congr_ae ?_
    filter_upwards [this] with y hy
    rw [hy]
  rw [h1]
  unfold lawY
  have hρ' : Measurable (fun y : Fin 11 → ℝ => ENNReal.ofReal (periodization11 y)) :=
    ENNReal.measurable_ofReal.comp measurable_periodization11
  rw [integral_withDensity_eq_integral_toReal_smul hρ' (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  unfold HighDim.Eleven.conditionalLabelEntropy
  rw [← integral_neg]
  refine integral_congr_ae ?_
  refine Filter.eventually_of_mem (ae_restrict_mem (PeriodizationCube.cube_measurable 11)) fun y _ => ?_
  dsimp only
  rw [ENNReal.toReal_ofReal (periodization11_pos y).le, smul_eq_mul, shannonEntropy_condKer,
    periodizedProfile_lift', ← mul_neg, ← tsum_neg]
  congr 2
  funext n
  rw [Real.negMulLog_eq_neg, conditionalLabel_eq_pLab]

/-- **`Y` has density `ρ_*` modulo `ℤ^{11}`**: the law of the class of `Y` on the torus is
`ρ_* · m_{11}`. -/
theorem map_torus_rvY (hX : Measurable X) (hlaw : P.map X = lawEta) :
    P.map (fun ω => fun i => ((rvY X ω i : ℝ) : UnitAddCircle)) =
      (torusMeasure 11).withDensity fun t => ENNReal.ofReal (periodizedProfile t) := by
  set π : (Fin 11 → ℝ) → Torus 11 := fun y => fun i => ((y i : ℝ) : UnitAddCircle) with hπ
  have hπm : Measurable π := by
    refine measurable_pi_iff.2 fun i => ?_
    exact (AddCircle.measurable_mk' (a := (1 : ℝ))).comp (measurable_pi_apply i)
  have hmp := PeriodizationCube.quotient_measurePreserving 11
  have hg : Measurable fun t : Torus 11 => ENNReal.ofReal (periodizedProfile t) :=
    ENNReal.measurable_ofReal.comp HighDim.Eleven.periodizedProfile_measurable
  have e : (fun ω => fun i => ((rvY X ω i : ℝ) : UnitAddCircle)) = π ∘ rvY X := rfl
  have hY : Measurable (rvY X) := measurable_labelY.comp hX
  rw [e, ← Measure.map_map hπm hY, map_rvY hX hlaw]
  refine Measure.ext fun A hA => ?_
  rw [Measure.map_apply hπm hA, withDensity_apply _ hA, ← lintegral_indicator hA]
  unfold lawY
  rw [withDensity_apply _ (hπm hA), ← lintegral_indicator (hπm hA)]
  have hind : Measurable (A.indicator fun t : Torus 11 => ENNReal.ofReal (periodizedProfile t)) :=
    hg.indicator hA
  rw [← hmp.lintegral_comp hind]
  refine lintegral_congr fun y => ?_
  by_cases h : π y ∈ A
  · have h' : y ∈ π ⁻¹' A := h
    rw [Set.indicator_of_mem h', Set.indicator_of_mem h]
    simp only [hπ]
    rw [← periodizedProfile_lift' y]
  · have h' : y ∉ π ⁻¹' A := h
    rw [Set.indicator_of_notMem h', Set.indicator_of_notMem h]

/-- **`eq:section4-periodization-entropy-identity`** for the lattice-label decomposition of a random
vector `X` with density `η_{1/5}`:
`Ent(ρ_*) = Ent_{ℝ^{11}}(η_{1/5}) + H_Sh(N|Y)`, with `H_Sh(N|Y)` the conditional Shannon entropy
defined through the regular conditional distribution `condDistrib N Y P`. -/
theorem periodization_entropy_identity (ρ : ProbabilityDensity 11)
    (hρ : ρ.value = periodizedProfile) (hX : Measurable X) (hlaw : P.map X = lawEta) :
    entropy ρ = (∫ x, etaEps (1 / 5) x * Real.log (etaEps (1 / 5) x)) +
      condShannon P (rvN X) (rvY X) := by
  rw [condShannon_eq hX hlaw]
  exact BecknerOnofri.V2.Eleven.periodization_entropy_identity ρ hρ

/-- **`lem:section4-lattice-label-entropy`**: `H_Sh(N|Y) < 1/600` (the repository proves `< 1/625`). -/
theorem condShannon_lt (hX : Measurable X) (hlaw : P.map X = lawEta) :
    condShannon P (rvN X) (rvY X) < 1 / 600 := by
  rw [condShannon_eq hX hlaw]
  exact label_entropy_lt

end Probabilistic

/-- `lawEta` is the measure with density `η_{1/5}` in terms of the rescaled profile. -/
theorem lawEta_eq : lawEta = volume.withDensity (fun x => ENNReal.ofReal (etaEps (1 / 5) x)) := by
  unfold lawEta; rw [etaEps_fifth]

/-- The canonical realization: the identity map on `(ℝ^{11}, lawEta)` is a random vector with
density `η_{1/5}`, so the statements above are not vacuous. -/
theorem canonical_space : (MeasureTheory.Measure.map (id : (Fin 11 → ℝ) → Fin 11 → ℝ) lawEta = lawEta) ∧
    IsProbabilityMeasure lawEta := ⟨Measure.map_id, inferInstance⟩

end JointLaw
