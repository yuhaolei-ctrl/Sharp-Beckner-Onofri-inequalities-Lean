module

public import BecknerOnofri.V2.Channel.Prop512
public import BecknerOnofri.SpinProductDefinitions
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

@[expose] public section

/-!
# The joint law of positions and spins (SpinChannel package, S044 / U15)

Printed construction (`eq:section5-global-channel`): sample `x` from the probability measure
`ρ dm_{12}`; conditionally on `x`, choose independent spins `σ_i ∈ {-1,1}` with
`P(σ_i = 1 | x) = (1 + cos 2πx_i)/2`.  The joint probability measure of the positions and spins is
`jointLaw ρ = positionLaw ρ ⊗ₘ spinKernel` on `Torus 12 × (Fin 12 → Bool)` (`true = +1`).
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Function
open scoped BigOperators ENNReal
namespace BecknerOnofri.V2.Reaudit.SpinChannel
open BecknerOnofri.HighDim BecknerOnofri.HighDim.Spin BecknerOnofri.HighDim.EntropyShearer

/-- Spin configurations `σ ∈ {-1,1}^{12}`, with `true` standing for `+1`. -/
abbrev Spins := Fin 12 → Bool

/-- The space of positions and spins. -/
abbrev JointSpace := Torus 12 × Spins

/-- The probability that a spin with cosine `c` equals `b`: `(1 + c)/2` for `+1`, `(1 - c)/2` for `-1`. -/
def bernW (c : ℝ) (b : Bool) : ℝ := if b then (1 + c) / 2 else (1 - c) / 2

/-- The conditional probability `P(σ = s | x) = ∏_i (1 ± cos 2πx_i)/2` of the independent spins. -/
def spinWeight (x : Torus 12) (s : Spins) : ℝ := ∏ j, bernW (torusCosines x j) (s j)

theorem bernW_nonneg {c : ℝ} (hc : |c| ≤ 1) (b : Bool) : 0 ≤ bernW c b := by
  have h := abs_le.mp hc
  cases b <;> simp [bernW] <;> linarith

theorem bernW_add (c : ℝ) : bernW c true + bernW c false = 1 := by
  simp [bernW]; ring

theorem spinWeight_nonneg (x : Torus 12) (s : Spins) : 0 ≤ spinWeight x s :=
  Finset.prod_nonneg fun j _ => bernW_nonneg (torusCosines_bound x j) _

/-- The product formula: summing the independent-spin weights against a product of one-variable
functions factorizes. -/
theorem sum_spinWeight_mul_prod (x : Torus 12) (F : Fin 12 → Bool → ℝ) :
    ∑ s : Spins, spinWeight x s * ∏ j, F j (s j) =
      ∏ j, (bernW (torusCosines x j) true * F j true + bernW (torusCosines x j) false * F j false) := by
  have h : ∀ s : Spins, spinWeight x s * ∏ j, F j (s j) =
      ∏ j, (bernW (torusCosines x j) (s j) * F j (s j)) := by
    intro s; unfold spinWeight; rw [Finset.prod_mul_distrib]
  simp_rw [h]
  rw [← Fintype.prod_sum (fun j (b : Bool) => bernW (torusCosines x j) b * F j b)]
  simp

theorem sum_spinWeight (x : Torus 12) : ∑ s : Spins, spinWeight x s = 1 := by
  have := sum_spinWeight_mul_prod x (fun _ _ => 1)
  simpa [bernW_add] using this


/-! ## The spin kernel -/

/-- The conditional law of the spins given the positions, as a finite mixture of Dirac masses. -/
def spinMeasure (x : Torus 12) : Measure Spins :=
  ∑ s : Spins, ENNReal.ofReal (spinWeight x s) • Measure.dirac s

/-- One independent spin with `P(+1) = (1 + c)/2`. -/
def bern (c : ℝ) : Measure Bool :=
  ENNReal.ofReal (bernW c true) • Measure.dirac true +
    ENNReal.ofReal (bernW c false) • Measure.dirac false

instance (c : ℝ) : IsFiniteMeasure (bern c) where
  measure_univ_lt_top := by
    simp only [bern, Measure.add_apply, Measure.smul_apply, smul_eq_mul, Measure.dirac_apply_of_mem (Set.mem_univ _), mul_one]
    exact ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top, ENNReal.ofReal_lt_top⟩

theorem spinMeasure_singleton (x : Torus 12) (s : Spins) :
    spinMeasure x {s} = ENNReal.ofReal (spinWeight x s) := by
  unfold spinMeasure
  rw [Measure.coe_finsetSum, Finset.sum_apply]
  simp [Measure.dirac_apply', Set.indicator, Finset.sum_ite_eq']

theorem bern_singleton (c : ℝ) (b : Bool) : bern c {b} = ENNReal.ofReal (bernW c b) := by
  cases b <;> simp [bern, Measure.dirac_apply']

/-- Independence of the spins: given `x`, the spin vector has the product law
`⊗_i Bern((1 + cos 2πx_i)/2)`. -/
theorem spinMeasure_eq_pi (x : Torus 12) :
    spinMeasure x = Measure.pi (fun j => bern (torusCosines x j)) := by
  refine Measure.ext_of_singleton fun s => ?_
  rw [spinMeasure_singleton, Measure.pi_singleton]
  simp only [bern_singleton]
  unfold spinWeight
  rw [ENNReal.ofReal_prod_of_nonneg]
  intro j _
  exact bernW_nonneg (torusCosines_bound x j) _

theorem measurable_spinMeasure_apply (t : Set Spins) : Measurable (fun x : Torus 12 => spinMeasure x t) := by
  have : (fun x : Torus 12 => spinMeasure x t) =
      fun x => ∑ s : Spins, ENNReal.ofReal (spinWeight x s) * t.indicator 1 s := by
    funext x
    unfold spinMeasure
    rw [Measure.coe_finsetSum, Finset.sum_apply]
    simp only [Measure.smul_apply, smul_eq_mul]
    congr 1; funext s
    rw [Measure.dirac_apply' _ (MeasurableSet.of_discrete)]
  rw [this]
  refine Finset.measurable_sum _ fun s _ => ?_
  refine Measurable.mul ?_ measurable_const
  refine ENNReal.measurable_ofReal.comp ?_
  unfold spinWeight bernW torusCosines
  refine Finset.measurable_prod _ fun j _ => ?_
  split_ifs <;> fun_prop

/-- The spin kernel `x ↦ ⊗_i Bern((1 + cos 2πx_i)/2)`. -/
def spinKernel : Kernel (Torus 12) Spins where
  toFun := spinMeasure
  measurable' := Measure.measurable_of_measurable_coe _ fun t _ => measurable_spinMeasure_apply t

@[simp] theorem spinKernel_apply (x : Torus 12) : spinKernel x = spinMeasure x := rfl

instance : IsMarkovKernel spinKernel where
  isProbabilityMeasure x := by
    refine ⟨?_⟩
    rw [spinKernel_apply]
    have : (Set.univ : Set Spins) = ⋃ s : Spins, {s} := by ext; simp
    unfold spinMeasure
    rw [Measure.coe_finsetSum, Finset.sum_apply]
    simp only [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply_of_mem (Set.mem_univ _), mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun s _ => spinWeight_nonneg x s), sum_spinWeight]
    simp


/-! ## The joint law -/

/-- The position marginal `ρ dm_{12}`. -/
def positionLaw (ρ : ProbabilityDensity 12) : Measure (Torus 12) :=
  (torusMeasure 12).withDensity fun x => ENNReal.ofReal (ρ.value x)

instance (ρ : ProbabilityDensity 12) : IsProbabilityMeasure (positionLaw ρ) where
  measure_univ := by
    unfold positionLaw
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal ρ.integrable ρ.nonneg, ρ.mass]
    simp

theorem integral_positionLaw (ρ : ProbabilityDensity 12) (g : Torus 12 → ℝ) :
    ∫ x, g x ∂positionLaw ρ = ∫ x, ρ.value x * g x ∂torusMeasure 12 := by
  unfold positionLaw
  rw [integral_withDensity_eq_integral_toReal_smul₀
    (ρ.integrable.aemeasurable.ennreal_ofReal) (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [ρ.nonneg] with x hx
  rw [ENNReal.toReal_ofReal hx]
  rfl

/-- **The joint probability measure `P_ρ` of positions and spins** (`eq:section5-global-channel`):
`x ∼ ρ dm_{12}`, then independent spins with `P(σ_i = 1 | x) = (1 + cos 2πx_i)/2`. -/
def jointLaw (ρ : ProbabilityDensity 12) : Measure JointSpace := positionLaw ρ ⊗ₘ spinKernel

instance (ρ : ProbabilityDensity 12) : IsProbabilityMeasure (jointLaw ρ) := by
  unfold jointLaw; infer_instance

/-- The positions `x_i` as random variables on `(JointSpace, P_ρ)`. -/
def posCoord (i : Fin 12) (ω : JointSpace) : UnitAddCircle := ω.1 i
/-- The spins `σ_i ∈ {-1, 1}` as real random variables. -/
def spinCoord (i : Fin 12) (ω : JointSpace) : ℝ := if ω.2 i then 1 else -1
/-- The cosines `C_i = cos 2πx_i`. -/
def cosCoord (i : Fin 12) (ω : JointSpace) : ℝ := torusCosines ω.1 i

/-- The spin marginal `ν_ρ` of the joint law. -/
def spinLaw (ρ : ProbabilityDensity 12) : Measure Spins := (jointLaw ρ).map Prod.snd

instance (ρ : ProbabilityDensity 12) : IsProbabilityMeasure (spinLaw ρ) := by
  unfold spinLaw; infer_instance

theorem jointLaw_map_fst (ρ : ProbabilityDensity 12) : (jointLaw ρ).map Prod.fst = positionLaw ρ := by
  have := Measure.fst_compProd (positionLaw ρ) spinKernel
  rwa [Measure.fst] at this

/-- Bounded measurable test functions on the joint space. -/
def BM (h : JointSpace → ℝ) : Prop := Measurable h ∧ ∃ B : ℝ, ∀ ω, ‖h ω‖ ≤ B

theorem BM.integrable {h : JointSpace → ℝ} (hh : BM h) (μ : Measure JointSpace) [IsFiniteMeasure μ] :
    Integrable h μ := by
  obtain ⟨hm, B, hB⟩ := hh
  exact Integrable.of_bound hm.aestronglyMeasurable B (Filter.Eventually.of_forall hB)

theorem BM.const (c : ℝ) : BM (fun _ => c) := ⟨measurable_const, ‖c‖, fun _ => le_rfl⟩

theorem BM.mul {f g : JointSpace → ℝ} (hf : BM f) (hg : BM g) : BM (fun ω => f ω * g ω) := by
  obtain ⟨hfm, A, hA⟩ := hf
  obtain ⟨hgm, B, hB⟩ := hg
  refine ⟨hfm.mul hgm, A * B, fun ω => ?_⟩
  rw [norm_mul]
  exact mul_le_mul (hA ω) (hB ω) (norm_nonneg _) ((norm_nonneg _).trans (hA ω))

theorem BM.add {f g : JointSpace → ℝ} (hf : BM f) (hg : BM g) : BM (fun ω => f ω + g ω) := by
  obtain ⟨hfm, A, hA⟩ := hf
  obtain ⟨hgm, B, hB⟩ := hg
  exact ⟨hfm.add hgm, A + B, fun ω => (norm_add_le _ _).trans (add_le_add (hA ω) (hB ω))⟩

/-- **Integration against the joint law.**  `E_P[h] = ∫ ρ(x) ∑_s P(σ = s | x) h(x, s) dm(x)`. -/
theorem integral_jointLaw (ρ : ProbabilityDensity 12) {h : JointSpace → ℝ}
    (hh : Integrable h (jointLaw ρ)) :
    ∫ ω, h ω ∂jointLaw ρ =
      ∫ x, ρ.value x * ∑ s : Spins, spinWeight x s * h (x, s) ∂torusMeasure 12 := by
  unfold jointLaw at hh ⊢
  rw [Measure.integral_compProd hh, integral_positionLaw]
  apply integral_congr_ae
  filter_upwards [] with x
  congr 1
  rw [spinKernel_apply, spinMeasure]
  have hint : ∀ s : Spins, Integrable (fun b => h (x, b)) (ENNReal.ofReal (spinWeight x s) • Measure.dirac s) := by
    intro s
    exact (integrable_dirac enorm_lt_top).smul_measure ENNReal.ofReal_ne_top
  rw [integral_finsetSum_measure (fun s _ => hint s)]
  apply Finset.sum_congr rfl
  intro s _
  rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (spinWeight_nonneg x s)]
  rfl


/-! ## Marginals, cube moments, and the bridge to `Spin.channelLaw` -/

theorem BM.of_position {g : Torus 12 → ℝ} (hg : BoundedMeasurable g) : BM (fun ω => g ω.1) := by
  obtain ⟨hm, B, hB⟩ := hg
  exact ⟨hm.comp measurable_fst, B, fun ω => hB ω.1⟩

theorem BM.of_spin (g : Spins → ℝ) : BM (fun ω => g ω.2) := by
  classical
  obtain ⟨B, hB⟩ := (Set.finite_range g).bddAbove.imp fun _ h => h
  refine ⟨(measurable_of_finite g).comp measurable_snd, (Finset.univ.sup' ⟨fun _ => true, Finset.mem_univ _⟩ (fun s => ‖g s‖)), fun ω => ?_⟩
  exact Finset.le_sup' (fun s => ‖g s‖) (Finset.mem_univ ω.2)

/-- `E_P[g(x)] = ∫ ρ g dm`: the position marginal of `P_ρ` is `ρ dm_{12}`. -/
theorem integral_jointLaw_position (ρ : ProbabilityDensity 12) {g : Torus 12 → ℝ}
    (hg : BoundedMeasurable g) :
    ∫ ω, g ω.1 ∂jointLaw ρ = ∫ x, ρ.value x * g x ∂torusMeasure 12 := by
  rw [integral_jointLaw ρ ((BM.of_position hg).integrable _)]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [← Finset.sum_mul, sum_spinWeight, one_mul]

/-- `E_P[∏_{i∈S} σ_i] = ∫ ρ ∏_{i∈S} cos 2πx_i dm` (`eq:section5-global-cube-moments`, first equality). -/
theorem integral_jointLaw_prod_spin (ρ : ProbabilityDensity 12) (S : Finset (Fin 12)) :
    ∫ ω, ∏ i ∈ S, spinCoord i ω ∂jointLaw ρ =
      ∫ x, ρ.value x * ∏ i ∈ S, torusCosines x i ∂torusMeasure 12 := by
  have hBM : BM (fun ω : JointSpace => ∏ i ∈ S, spinCoord i ω) := by
    have := BM.of_spin (fun s : Spins => ∏ i ∈ S, (if s i then (1 : ℝ) else -1))
    simpa [spinCoord] using this
  rw [integral_jointLaw ρ (hBM.integrable _)]
  apply integral_congr_ae
  filter_upwards [] with x
  congr 1
  have key := sum_spinWeight_mul_prod x (fun j b => if j ∈ S then (if b then (1 : ℝ) else -1) else 1)
  have e1 : ∀ s : Spins, ∏ j, (if j ∈ S then (if s j then (1 : ℝ) else -1) else 1) =
      ∏ i ∈ S, spinCoord i (x, s) := by
    intro s
    simp [spinCoord, Finset.prod_ite_mem]
  simp_rw [e1] at key
  rw [key]
  have e2 : ∀ j, (bernW (torusCosines x j) true * (if j ∈ S then (if true then (1 : ℝ) else -1) else 1) +
      bernW (torusCosines x j) false * (if j ∈ S then (if false then (1 : ℝ) else -1) else 1)) =
      if j ∈ S then torusCosines x j else 1 := by
    intro j
    by_cases hj : j ∈ S <;> simp [hj, bernW] <;> ring
  refine (Finset.prod_congr rfl (fun j _ => e2 j)).trans ?_
  simp [Finset.prod_ite_mem]

/-- The probability that the spin vector equals `s`. -/
theorem spinLaw_real_singleton (ρ : ProbabilityDensity 12) (s : Spins) :
    (spinLaw ρ).real {s} = ∫ x, ρ.value x * spinWeight x s ∂torusMeasure 12 := by
  have h1 : (spinLaw ρ).real {s} =
      ∫ ω, (fun ω : JointSpace => if ω.2 = s then (1 : ℝ) else 0) ω ∂jointLaw ρ := by
    have h2 := integral_indicator_one (μ := jointLaw ρ) (measurable_snd (measurableSet_singleton s))
    have h3 : (fun ω : JointSpace => if ω.2 = s then (1 : ℝ) else 0) =
        (Prod.snd ⁻¹' {s} : Set JointSpace).indicator 1 := by
      funext ω; simp [Set.indicator]
    rw [h3, h2]
    simp [spinLaw, measureReal_def, Measure.map_apply measurable_snd (measurableSet_singleton s)]
  rw [h1]
  have hBM : BM (fun ω : JointSpace => if ω.2 = s then (1 : ℝ) else 0) :=
    BM.of_spin (fun t : Spins => if t = s then (1 : ℝ) else 0)
  rw [integral_jointLaw ρ (hBM.integrable _)]
  apply integral_congr_ae
  filter_upwards [] with x
  congr 1
  rw [Finset.sum_eq_single s]
  · simp
  · intro t _ hts; simp [hts]
  · simp

/-- The positive-spin set of a spin vector, as a configuration in the sense of `Spin.Configuration`. -/
def posSet (s : Spins) : Configuration := Finset.univ.filter fun j => s j = true

theorem spinWeight_eq_channel (x : Torus 12) (s : Spins) :
    spinWeight x s = channel (torusCosines x) (posSet s) := by
  unfold spinWeight channel
  rw [← Finset.prod_mul_prod_compl (posSet s) (fun j => bernW (torusCosines x j) (s j))]
  congr 1
  · apply Finset.prod_congr rfl
    intro j hj
    have : s j = true := by simpa [posSet] using hj
    simp [bernW, this]
  · apply Finset.prod_congr rfl
    intro j hj
    have : s j = false := by simpa [posSet] using hj
    simp [bernW, this]

/-- `ν_ρ({s}) = channelLaw ρ (posSet s)`: the spin marginal of the joint law is the repository's spin law. -/
theorem spinLaw_real_singleton_eq_channelLaw (ρ : ProbabilityDensity 12) (s : Spins) :
    (spinLaw ρ).real {s} = channelLaw ρ (posSet s) := by
  rw [spinLaw_real_singleton]
  unfold channelLaw
  apply integral_congr_ae
  filter_upwards [] with x
  rw [spinWeight_eq_channel]

end BecknerOnofri.V2.Reaudit.SpinChannel
