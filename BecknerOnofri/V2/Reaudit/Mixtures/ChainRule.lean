module

public import BecknerOnofri.V2.Section3.Marginal

@[expose] public section

/-! # The relative-entropy chain rule for the one-point marginals (S023)

`eq:mixture-entropy-decomposition` of the manuscript:
`Ent(ρ) = ∑_i Ent(ρ_i) + H(ρ | ∏_i ρ_i) ≥ ∑_i Ent(ρ_i)`,
for an arbitrary finite-entropy probability density `ρ` on `𝕋^d` (no mixture structure is used).
The relative entropy `H(ρ | ∏ ρ_i) = ∫ ρ log (ρ / ∏ ρ_i)` is the explicit integral
`relEntropyToProduct`; its nonnegativity is Gibbs' inequality `a log (a/b) ≥ a - b` and the identity of
total masses `∫ ∏ ρ_i(x_i) = 1`.  The absolute continuity of `ρ m_d` with respect to `(∏ ρ_i) m_d`
(`ρ(x) > 0 → ρ_i(x_i) > 0`, almost everywhere) and the finiteness of `∫ ρ log ρ_i(x_i)` are proved
here (`pos_ae`, `pairing_integrable`).  No Shearer-type inequality is used. -/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal

namespace BecknerOnofri.V2.Reaudit.Mixtures
open BecknerOnofri.HighDim BecknerOnofri.V2.Section3 BecknerOnofri.V2.Vocab

variable {n : ℕ}

/-- Normalised Haar measure on the circle. -/
abbrev haarC : Measure UnitAddCircle := AddCircle.haarAddCircle

theorem circleMarginal_measurable (ρ : ProbabilityDensity (n + 1)) (hm : Measurable ρ.value)
    (i : Fin (n + 1)) : Measurable (circleMarginal ρ i) :=
  Legacy.D10.coordinateMarginal_measurable
    (μ := fun _ : Fin (n + 1) => (AddCircle.haarAddCircle : Measure UnitAddCircle)) hm i

/-- Fubini pairing of a density against an unbounded function of one coordinate, when the
integrand `ρ_i g` of the marginal is integrable. -/
theorem pairing_integrable (ρ : ProbabilityDensity (n + 1)) (hm : Measurable ρ.value)
    (i : Fin (n + 1)) {g : UnitAddCircle → ℝ} (hg : Measurable g)
    (h : Integrable (fun y => circleMarginal ρ i y * g y) haarC) :
    Integrable (fun x : Torus (n + 1) => ρ.value x * g (x i)) (torusMeasure (n + 1)) ∧
      ∫ x, ρ.value x * g (x i) ∂torusMeasure (n + 1) =
        ∫ y, circleMarginal ρ i y * g y ∂haarC := by
  let μ : Fin (n + 1) → Measure UnitAddCircle := fun _ => haarC
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => UnitAddCircle) i
  have he : MeasurePreserving e.symm (haarC.prod (Measure.pi fun j : Fin n => haarC))
      (torusMeasure (n + 1)) := (measurePreserving_piFinSuccAbove μ i).symm
  have hi : Integrable (fun z => ρ.value (e.symm z))
      (haarC.prod (Measure.pi fun j : Fin n => haarC)) :=
    (he.integrable_comp_emb e.symm.measurableEmbedding).mpr ρ.integrable
  have hnn : ∀ᵐ z ∂(haarC.prod (Measure.pi fun j : Fin n => haarC)), 0 ≤ ρ.value (e.symm z) :=
    he.quasiMeasurePreserving.ae ρ.nonneg
  have hnn' := Measure.ae_ae_of_ae_prod hnn
  have hmn := circleMarginal_nonneg_ae ρ i
  have hmeasF : Measurable (fun z : UnitAddCircle × (Fin n → UnitAddCircle) =>
      ρ.value (e.symm z) * g z.1) :=
    (hm.comp e.symm.measurable).mul (hg.comp measurable_fst)
  have hdef (y : UnitAddCircle) : circleMarginal ρ i y =
      ∫ z', ρ.value (e.symm (y, z')) ∂(Measure.pi fun j : Fin n => haarC) := rfl
  have hF : Integrable (fun z : UnitAddCircle × (Fin n → UnitAddCircle) =>
      ρ.value (e.symm z) * g z.1) (haarC.prod (Measure.pi fun j : Fin n => haarC)) := by
    rw [integrable_prod_iff hmeasF.aestronglyMeasurable]
    refine ⟨?_, ?_⟩
    · filter_upwards [hi.prod_right_ae] with y hy
      exact hy.mul_const (g y)
    · refine (h.norm).congr ?_
      filter_upwards [hnn', hmn] with y hy hmy
      have h1 : ∫ z', ‖ρ.value (e.symm (y, z')) * g y‖ ∂(Measure.pi fun j : Fin n => haarC) =
          ∫ z', ρ.value (e.symm (y, z')) * ‖g y‖ ∂(Measure.pi fun j : Fin n => haarC) := by
        apply integral_congr_ae
        filter_upwards [hy] with z' hz'
        rw [norm_mul, Real.norm_of_nonneg hz']
      rw [h1, integral_mul_const, ← hdef, norm_mul, Real.norm_of_nonneg hmy]
  have hsymm (z : UnitAddCircle × (Fin n → UnitAddCircle)) : e.symm z i = z.1 := by
    simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply]
  have hcomp : (fun x : Torus (n + 1) => ρ.value x * g (x i)) ∘ e.symm =
      fun z => ρ.value (e.symm z) * g z.1 := by
    funext z
    simp only [Function.comp_apply, hsymm]
  refine ⟨(he.integrable_comp_emb e.symm.measurableEmbedding).mp (by rw [hcomp]; exact hF), ?_⟩
  calc ∫ x, ρ.value x * g (x i) ∂torusMeasure (n + 1)
      = ∫ z, (fun x : Torus (n + 1) => ρ.value x * g (x i)) (e.symm z)
          ∂(haarC.prod (Measure.pi fun j : Fin n => haarC)) :=
        (he.integral_comp' (fun x : Torus (n + 1) => ρ.value x * g (x i))).symm
    _ = ∫ z, ρ.value (e.symm z) * g z.1 ∂(haarC.prod (Measure.pi fun j : Fin n => haarC)) := by
        simp only [hsymm]
    _ = ∫ y, ∫ z', ρ.value (e.symm (y, z')) * g y ∂(Measure.pi fun j : Fin n => haarC) ∂haarC :=
        integral_prod _ hF
    _ = ∫ y, circleMarginal ρ i y * g y ∂haarC := by
        congr 1; funext y; rw [integral_mul_const, hdef]

/-- Absolute continuity of `ρ m_d` with respect to `(∏ ρ_i) m_d`, one coordinate at a time:
almost everywhere, `ρ(x) > 0` forces `ρ_i(x_i) > 0`. -/
theorem pos_ae (ρ : ProbabilityDensity (n + 1)) (hm : Measurable ρ.value) (i : Fin (n + 1)) :
    ∀ᵐ x ∂torusMeasure (n + 1), 0 < ρ.value x → 0 < circleMarginal ρ i (x i) := by
  set B : Set UnitAddCircle := {y | circleMarginal ρ i y ≤ 0} with hBdef
  have hB : MeasurableSet B := measurableSet_le (circleMarginal_measurable ρ hm i) measurable_const
  set u : UnitAddCircle → ℝ := B.indicator (fun _ => (1 : ℝ)) with hu
  have humeas : Measurable u := measurable_const.indicator hB
  have hub : ∀ y, ‖u y‖ ≤ 1 := by
    intro y; simp only [hu, Set.indicator]; split_ifs <;> simp
  have hpair := Legacy.D10.coordinateMarginal_pairing
    (μ := fun _ : Fin (n + 1) => (AddCircle.haarAddCircle : Measure UnitAddCircle))
    (rho := ρ.value) ρ.integrable i humeas hub
  have hR : ∫ y, circleMarginal ρ i y * u y ∂haarC ≤ 0 := by
    apply integral_nonpos
    intro y
    by_cases h : y ∈ B
    · have h' : circleMarginal ρ i y ≤ 0 := h
      simp only [hu, Set.indicator_of_mem h, mul_one, Pi.zero_apply]
      exact h'
    · simp [hu, Set.indicator_of_notMem h]
  have hint : Integrable (fun x : Torus (n + 1) => ρ.value x * u (x i)) (torusMeasure (n + 1)) := by
    exact ρ.integrable.mul_bdd (c := 1) (humeas.comp (measurable_pi_apply i)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => hub _)
  have hnn : 0 ≤ᵐ[torusMeasure (n + 1)] fun x => ρ.value x * u (x i) := by
    filter_upwards [ρ.nonneg] with x hx
    apply mul_nonneg hx
    simp only [hu, Set.indicator]; split_ifs <;> norm_num
  have hL : 0 ≤ ∫ x, ρ.value x * u (x i) ∂torusMeasure (n + 1) := integral_nonneg_of_ae hnn
  have hz : ∫ x, ρ.value x * u (x i) ∂torusMeasure (n + 1) = 0 :=
    le_antisymm (by rw [show (torusMeasure (n + 1)) = Measure.pi _ from rfl, hpair]; exact hR) hL
  have h0 := (integral_eq_zero_iff_of_nonneg_ae hnn hint).mp hz
  filter_upwards [h0] with x hx hρx
  by_contra hle
  push Not at hle
  have : u (x i) = 1 := by
    have hmem : x i ∈ B := hle
    simp only [hu, Set.indicator_of_mem hmem]
  simp only [Pi.zero_apply, this, mul_one] at hx
  exact absurd hx hρx.ne'

/-- The product of the one-point marginals, `x ↦ ∏_i ρ_i(x_i)`. -/
def marginalProduct (ρ : ProbabilityDensity (n + 1)) (x : Torus (n + 1)) : ℝ :=
  ∏ i, circleMarginal ρ i (x i)

/-- The relative entropy `H(ρ | ∏_i ρ_i) = ∫ ρ log (ρ / ∏_i ρ_i)` of `ρ m_d` with respect to the
product of its one-point marginals, written as `∫ ρ (log ρ - ∑_i log ρ_i(x_i))` (on the set
`{ρ > 0}` the two forms agree, and the complement does not contribute). -/
def relEntropyToProduct (ρ : ProbabilityDensity (n + 1)) : ℝ :=
  ∫ x, ρ.value x * (Real.log (ρ.value x) - ∑ i, Real.log (circleMarginal ρ i (x i)))
    ∂torusMeasure (n + 1)

/-- The entropy of the `i`-th circle marginal, `∫ ρ_i log ρ_i`. -/
def circleEntropy (ρ : ProbabilityDensity (n + 1)) (i : Fin (n + 1)) : ℝ :=
  ∫ y, circleMarginal ρ i y * Real.log (circleMarginal ρ i y) ∂haarC

theorem circleEntropy_eq (ρ : ProbabilityDensity (n + 1)) (i : Fin (n + 1))
    (hρ : ρ.FiniteEntropy) : circleEntropy ρ i = entropy (axisDensity ρ i) := by
  have hF := (circleMarginal_entropy_integrable ρ i hρ).aestronglyMeasurable
  unfold entropy circleEntropy
  simp_rw [axisDensity_value]
  exact (integral_comp_eval (μ := fun _ : Fin 1 => (AddCircle.haarAddCircle : Measure UnitAddCircle))
      (i := (0 : Fin 1)) (f := fun y => circleMarginal ρ i y * Real.log (circleMarginal ρ i y)) hF).symm

/-- **Chain rule for relative entropy, measurable representative.** -/
theorem entropy_chain_rule_meas (ρ : ProbabilityDensity (n + 1)) (hm : Measurable ρ.value)
    (hρ : ρ.FiniteEntropy) :
    0 ≤ relEntropyToProduct ρ ∧
      entropy ρ = ∑ i, circleEntropy ρ i + relEntropyToProduct ρ := by
  have hmeas (i : Fin (n + 1)) := circleMarginal_measurable ρ hm i
  have hρ' : Integrable (fun x => ρ.value x * Real.log (ρ.value x)) (torusMeasure (n + 1)) := hρ
  have hpair (i : Fin (n + 1)) :=
    pairing_integrable ρ hm i (g := fun y => Real.log (circleMarginal ρ i y))
      (Real.measurable_log.comp (hmeas i)) (circleMarginal_entropy_integrable ρ i hρ)
  have hnn_i (i : Fin (n + 1)) : ∀ᵐ x ∂torusMeasure (n + 1), 0 ≤ circleMarginal ρ i (x i) :=
    (measurePreserving_eval (fun _ : Fin (n + 1) =>
      (AddCircle.haarAddCircle : Measure UnitAddCircle)) i).quasiMeasurePreserving.ae
      (circleMarginal_nonneg_ae ρ i)
  -- integrability of the marginal product and its total mass
  have hqint : Integrable (marginalProduct ρ) (torusMeasure (n + 1)) :=
    Integrable.fintype_prod (f := fun i y => circleMarginal ρ i y)
      (μ := fun _ : Fin (n + 1) => haarC) (fun i => circleMarginal_integrable ρ i)
  have hqmass : ∫ x, marginalProduct ρ x ∂torusMeasure (n + 1) = 1 := by
    unfold marginalProduct
    rw [show torusMeasure (n + 1) = Measure.pi (fun _ : Fin (n + 1) => haarC) from rfl,
      integral_fintype_prod_eq_prod (f := fun i y => circleMarginal ρ i y)]
    simp [circleMarginal_mass]
  -- the integrand
  have hT : Integrable (fun x : Torus (n + 1) => ρ.value x * (Real.log (ρ.value x) -
      ∑ i, Real.log (circleMarginal ρ i (x i)))) (torusMeasure (n + 1)) := by
    have := hρ'.sub (integrable_finsetSum Finset.univ (fun i _ => (hpair i).1))
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.sub_apply, Finset.mul_sum, mul_sub]
  have hTval : relEntropyToProduct ρ = entropy ρ - ∑ i, circleEntropy ρ i := by
    unfold relEntropyToProduct entropy circleEntropy
    have : (fun x : Torus (n + 1) => ρ.value x * (Real.log (ρ.value x) -
        ∑ i, Real.log (circleMarginal ρ i (x i)))) =
        fun x => ρ.value x * Real.log (ρ.value x) -
          ∑ i, ρ.value x * Real.log (circleMarginal ρ i (x i)) := by
      funext x; simp only [Finset.mul_sum, mul_sub]
    rw [this, integral_sub hρ' (integrable_finsetSum Finset.univ (fun i _ => (hpair i).1)),
      integral_finsetSum Finset.univ (fun i _ => (hpair i).1)]
    congr 1
    exact Finset.sum_congr rfl (fun i _ => (hpair i).2)
  refine ⟨?_, by rw [hTval]; ring⟩
  -- Gibbs' inequality
  have hpt : ∀ᵐ x ∂torusMeasure (n + 1), ρ.value x - marginalProduct ρ x ≤
      ρ.value x * (Real.log (ρ.value x) - ∑ i, Real.log (circleMarginal ρ i (x i))) := by
    have hpos : ∀ᵐ x ∂torusMeasure (n + 1), ∀ i, 0 < ρ.value x → 0 < circleMarginal ρ i (x i) :=
      ae_all_iff.mpr (fun i => pos_ae ρ hm i)
    have hall : ∀ᵐ x ∂torusMeasure (n + 1), ∀ i, 0 ≤ circleMarginal ρ i (x i) :=
      ae_all_iff.mpr hnn_i
    filter_upwards [ρ.nonneg, hpos, hall] with x hx hp ha
    rcases hx.eq_or_lt with h0 | hpos'
    · rw [← h0]
      have : 0 ≤ marginalProduct ρ x := Finset.prod_nonneg (fun i _ => ha i)
      simp [this]
    · have hq : ∀ i, 0 < circleMarginal ρ i (x i) := fun i => hp i hpos'
      have hqpos : 0 < marginalProduct ρ x := Finset.prod_pos (fun i _ => hq i)
      have hlog : Real.log (marginalProduct ρ x) = ∑ i, Real.log (circleMarginal ρ i (x i)) :=
        Real.log_prod (fun i _ => (hq i).ne')
      rw [← hlog]
      have h1 := Real.log_le_sub_one_of_pos (div_pos hqpos hpos')
      rw [Real.log_div hqpos.ne' hpos'.ne', div_sub_one hpos'.ne'] at h1
      have h2 := mul_le_mul_of_nonneg_left h1 hpos'.le
      rw [mul_div_cancel₀ _ hpos'.ne'] at h2
      linarith
  have := integral_mono_ae (ρ.integrable.sub hqint) hT hpt
  simp only [Pi.sub_apply] at this
  rw [integral_sub ρ.integrable hqint, ρ.mass, hqmass] at this
  unfold relEntropyToProduct
  simpa using this

theorem circleMarginal_congr_ae {ρ ρ' : ProbabilityDensity (n + 1)}
    (h : ρ.value =ᵐ[torusMeasure (n + 1)] ρ'.value) (i : Fin (n + 1)) :
    ∀ᵐ y ∂haarC, circleMarginal ρ i y = circleMarginal ρ' i y := by
  let μ : Fin (n + 1) → Measure UnitAddCircle := fun _ => haarC
  have he : MeasurePreserving (MeasurableEquiv.piFinSuccAbove
      (fun _ : Fin (n + 1) => UnitAddCircle) i).symm
      (haarC.prod (Measure.pi fun j : Fin n => haarC)) (torusMeasure (n + 1)) :=
    (measurePreserving_piFinSuccAbove μ i).symm
  have h' := Measure.ae_ae_of_ae_prod (he.quasiMeasurePreserving.ae h)
  filter_upwards [h'] with y hy
  exact integral_congr_ae hy

/-- **Chain rule for relative entropy** (`eq:mixture-entropy-decomposition`): for every
finite-entropy probability density on `𝕋^{n+1}`,
`Ent(ρ) = ∑_i Ent(ρ_i) + H(ρ | ∏_i ρ_i)` with `H(ρ | ∏_i ρ_i) ≥ 0`. -/
theorem entropy_chain_rule (ρ : ProbabilityDensity (n + 1)) (hρ : ρ.FiniteEntropy) :
    0 ≤ relEntropyToProduct ρ ∧
      entropy ρ = ∑ i, circleEntropy ρ i + relEntropyToProduct ρ := by
  have hmeasf : Measurable (ρ.integrable.aestronglyMeasurable.mk ρ.value) :=
    ρ.integrable.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hae : ρ.value =ᵐ[torusMeasure (n + 1)] ρ.integrable.aestronglyMeasurable.mk ρ.value :=
    ρ.integrable.aestronglyMeasurable.ae_eq_mk
  let ρ' : ProbabilityDensity (n + 1) :=
    { value := ρ.integrable.aestronglyMeasurable.mk ρ.value
      nonneg := by filter_upwards [ρ.nonneg, hae] with x h1 h2; rw [← h2]; exact h1
      integrable := ρ.integrable.congr hae
      mass := by rw [← integral_congr_ae hae]; exact ρ.mass }
  have hent : entropy ρ' = entropy ρ := by
    unfold entropy
    exact integral_congr_ae (by filter_upwards [hae] with x hx; rw [show ρ'.value x = ρ.value x from hx.symm])
  have hfin' : ρ'.FiniteEntropy := by
    unfold ProbabilityDensity.FiniteEntropy at hρ ⊢
    refine hρ.congr ?_
    filter_upwards [hae] with x hx
    rw [show ρ'.value x = ρ.value x from hx.symm]
  have hmarg (i : Fin (n + 1)) := circleMarginal_congr_ae (ρ := ρ) (ρ' := ρ') hae i
  have hcirc (i : Fin (n + 1)) : circleEntropy ρ i = circleEntropy ρ' i := by
    unfold circleEntropy
    exact integral_congr_ae (by filter_upwards [hmarg i] with y hy; rw [hy])
  have hrel : relEntropyToProduct ρ = relEntropyToProduct ρ' := by
    unfold relEntropyToProduct
    have hall : ∀ᵐ x ∂torusMeasure (n + 1), ∀ i, circleMarginal ρ i (x i) = circleMarginal ρ' i (x i) :=
      ae_all_iff.mpr (fun i => (measurePreserving_eval (fun _ : Fin (n + 1) =>
        (AddCircle.haarAddCircle : Measure UnitAddCircle)) i).quasiMeasurePreserving.ae (hmarg i))
    refine integral_congr_ae ?_
    filter_upwards [hae, hall] with x hx hx2
    rw [show ρ'.value x = ρ.value x from hx.symm]
    simp only [hx2]
  obtain ⟨h1, h2⟩ := entropy_chain_rule_meas ρ' hmeasf hfin'
  refine ⟨hrel ▸ h1, ?_⟩
  rw [← hent, hrel, h2]
  simp only [hcirc]

/-- The sum of the one-point marginal entropies is bounded by the entropy (consequence of the
chain rule and `H ≥ 0`). -/
theorem sum_circleEntropy_le (ρ : ProbabilityDensity (n + 1)) (hρ : ρ.FiniteEntropy) :
    ∑ i, circleEntropy ρ i ≤ entropy ρ := by
  obtain ⟨h1, h2⟩ := entropy_chain_rule ρ hρ
  linarith

/-- `eq:circle-marginal-fourier-control` by the chain rule (identical in type to
`Section3.axis_marginal_bound`, whose proof uses Shearer's inequality with `r = 1`). -/
theorem axis_marginal_bound_chain {d : ℕ} (hd : 0 < d) (ρ : ProbabilityDensity d)
    (hρ : ρ.FiniteEntropy) :
    (∀ i : Fin d, Summable (axisTerm ρ i)) ∧
      ∑ i : Fin d, ∑' j, axisTerm ρ i j ≤ entropy ρ := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd.ne'
  have hcirc (i : Fin (n + 1)) :
      Summable (axisTerm ρ i) ∧ ∑' j, axisTerm ρ i j ≤ circleEntropy ρ i := by
    have h := lemma_3_2_finite (axisDensity ρ i) (axisDensity_finiteEntropy ρ i hρ)
    rw [circleTerm_axisDensity, ← entropy_eq_toReal_torusEntropy _ (axisDensity_finiteEntropy ρ i hρ),
      ← circleEntropy_eq ρ i hρ] at h
    exact h
  exact ⟨fun i => (hcirc i).1,
    (Finset.sum_le_sum fun i _ => (hcirc i).2).trans (sum_circleEntropy_le ρ hρ)⟩

#print axioms entropy_chain_rule
#print axioms axis_marginal_bound_chain

end BecknerOnofri.V2.Reaudit.Mixtures