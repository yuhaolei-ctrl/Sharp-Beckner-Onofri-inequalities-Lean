module

public import Legacy.D10.Analytic

@[expose] public section

/-!
# Actual coordinate marginals and entropy subadditivity

The marginals here are Fubini integrals, not abstract functions with postulated
pairing identities. We prove entropy subadditivity for a measurable density
bounded above and bounded away from zero. This includes the smooth positive
Euler densities used by the analytic paper proof, once their compactness
bounds have been supplied. No Euler existence or smoothness result is claimed
in this file.
-/

open MeasureTheory
open scoped BigOperators

namespace Legacy.D10

section Bounds

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

theorem integrable_of_measurable_norm_bound {f : X → ℝ} {B : ℝ}
    (hf : Measurable f) (hB : ∀ x, ‖f x‖ ≤ B) : Integrable f μ := by
  apply (integrable_const B).mono' hf.aestronglyMeasurable
  exact Filter.Eventually.of_forall hB

/-- A positive interval gives a uniform bound on the logarithm. -/
theorem norm_log_le_of_bounds {c B r : ℝ} (hc : 0 < c)
    (hcr : c ≤ r) (hrB : r ≤ B) :
    ‖Real.log r‖ ≤ |Real.log c| + |Real.log B| := by
  have hr : 0 < r := lt_of_lt_of_le hc hcr
  have hlow : Real.log c ≤ Real.log r := Real.log_le_log hc hcr
  have hupp : Real.log r ≤ Real.log B := Real.log_le_log hr hrB
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · linarith [neg_abs_le (Real.log c), abs_nonneg (Real.log B)]
  · linarith [le_abs_self (Real.log B), abs_nonneg (Real.log c)]

end Bounds

section Binary

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- The first marginal is the actual integral over the second variable. -/
noncomputable def firstMarginal (rho : X × Y → ℝ) (x : X) : ℝ := ∫ y, rho (x, y) ∂ν

theorem firstMarginal_measurable {rho : X × Y → ℝ} (hr : Measurable rho) :
    Measurable (firstMarginal (ν := ν) rho) :=
  hr.stronglyMeasurable.integral_prod_right'.measurable

theorem firstMarginal_mass {rho : X × Y → ℝ}
    (hr : Integrable rho (μ.prod ν)) :
    (∫ x, firstMarginal (ν := ν) rho x ∂μ) = ∫ z, rho z ∂μ.prod ν :=
  (integral_prod rho hr).symm

/-- Bounds pass to genuine marginals on a probability space. -/
theorem firstMarginal_bounds {rho : X × Y → ℝ} {c B : ℝ}
    (hr : Measurable rho) (hc : 0 ≤ c)
    (hlow : ∀ z, c ≤ rho z) (hupp : ∀ z, rho z ≤ B) (x : X) :
    c ≤ firstMarginal (ν := ν) rho x ∧ firstMarginal (ν := ν) rho x ≤ B := by
  have hi : Integrable (fun y => rho (x, y)) ν := by
    apply integrable_of_measurable_norm_bound (B := B)
      (hr.comp (measurable_const.prodMk measurable_id))
    intro y
    change ‖rho (x, y)‖ ≤ B
    rw [Real.norm_eq_abs, abs_of_nonneg (hc.trans (hlow _))]
    exact hupp _
  constructor
  · have h := integral_mono (integrable_const c) hi (fun y => hlow (x, y))
    simpa [firstMarginal] using h
  · have h := integral_mono hi (integrable_const B) (fun y => hupp (x, y))
    simpa [firstMarginal] using h

/-- The defining marginal pairing identity is proved by Fubini. -/
theorem firstMarginal_pairing {rho : X × Y → ℝ} {u : X → ℝ} {B : ℝ}
    (hr : Integrable rho (μ.prod ν)) (hu : Measurable u)
    (hB : ∀ x, ‖u x‖ ≤ B) :
    (∫ z, rho z * u z.1 ∂μ.prod ν) =
      ∫ x, firstMarginal (ν := ν) rho x * u x ∂μ := by
  have hi : Integrable (fun z => rho z * u z.1) (μ.prod ν) :=
    hr.mul_bdd (hu.comp measurable_fst).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun z => hB z.1))
  rw [integral_prod _ hi]
  simp only [integral_mul_const, firstMarginal]

end Binary

section Coordinate

variable {n : ℕ} {X : Fin (n + 1) → Type*} [∀ i, MeasurableSpace (X i)]
    {μ : (i : Fin (n + 1)) → Measure (X i)} [∀ i, IsProbabilityMeasure (μ i)]

/-- A coordinate marginal is obtained by integrating all remaining
coordinates in the canonical product decomposition at that coordinate. -/
noncomputable def coordinateMarginal
    (rho : ((i : Fin (n + 1)) → X i) → ℝ) (i : Fin (n + 1)) (y : X i) : ℝ :=
  ∫ z : (j : Fin n) → X (i.succAbove j),
    rho ((MeasurableEquiv.piFinSuccAbove X i).symm (y, z))
    ∂Measure.pi (fun j => μ (i.succAbove j))

theorem coordinateMarginal_measurable
    {rho : ((i : Fin (n + 1)) → X i) → ℝ} (hr : Measurable rho)
    (i : Fin (n + 1)) : Measurable (coordinateMarginal (μ := μ) rho i) :=
  firstMarginal_measurable (hr.comp (MeasurableEquiv.piFinSuccAbove X i).symm.measurable)

theorem coordinateMarginal_mass
    {rho : ((i : Fin (n + 1)) → X i) → ℝ}
    (hr : Integrable rho (Measure.pi μ)) (i : Fin (n + 1)) :
    (∫ y, coordinateMarginal (μ := μ) rho i y ∂μ i) =
      ∫ x, rho x ∂Measure.pi μ := by
  let e := MeasurableEquiv.piFinSuccAbove X i
  have he := (measurePreserving_piFinSuccAbove μ i).symm
  have hi : Integrable (fun z => rho (e.symm z))
      ((μ i).prod (Measure.pi fun j => μ (i.succAbove j))) :=
    (he.integrable_comp_emb e.symm.measurableEmbedding).mpr hr
  calc
    _ = ∫ z, rho (e.symm z) ∂(μ i).prod (Measure.pi fun j => μ (i.succAbove j)) :=
      firstMarginal_mass hi
    _ = ∫ x, rho x ∂Measure.pi μ := he.integral_comp' rho

theorem coordinateMarginal_bounds
    {rho : ((i : Fin (n + 1)) → X i) → ℝ} {c B : ℝ}
    (hr : Measurable rho) (hc : 0 ≤ c)
    (hlow : ∀ x, c ≤ rho x) (hupp : ∀ x, rho x ≤ B)
    (i : Fin (n + 1)) (y : X i) :
    c ≤ coordinateMarginal (μ := μ) rho i y ∧
      coordinateMarginal (μ := μ) rho i y ≤ B :=
  firstMarginal_bounds (hr.comp (MeasurableEquiv.piFinSuccAbove X i).symm.measurable)
    hc (fun _ => hlow _) (fun _ => hupp _) y

theorem coordinateMarginal_pairing
    {rho : ((i : Fin (n + 1)) → X i) → ℝ}
    (hr : Integrable rho (Measure.pi μ)) (i : Fin (n + 1))
    {u : X i → ℝ} {B : ℝ} (hu : Measurable u) (hB : ∀ y, ‖u y‖ ≤ B) :
    (∫ x, rho x * u (x i) ∂Measure.pi μ) =
      ∫ y, coordinateMarginal (μ := μ) rho i y * u y ∂μ i := by
  let e := MeasurableEquiv.piFinSuccAbove X i
  have he := (measurePreserving_piFinSuccAbove μ i).symm
  have hi : Integrable (fun z => rho (e.symm z))
      ((μ i).prod (Measure.pi fun j => μ (i.succAbove j))) :=
    (he.integrable_comp_emb e.symm.measurableEmbedding).mpr hr
  calc
    _ = ∫ z, rho (e.symm z) * u ((e.symm z) i)
        ∂(μ i).prod (Measure.pi fun j => μ (i.succAbove j)) :=
      (he.integral_comp' (fun x => rho x * u (x i))).symm
    _ = ∫ z, rho (e.symm z) * u z.1
        ∂(μ i).prod (Measure.pi fun j => μ (i.succAbove j)) := by
      congr 1
      funext z
      simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply]
    _ = ∫ y, coordinateMarginal (μ := μ) rho i y * u y ∂μ i :=
      firstMarginal_pairing hi hu hB

/-- Entropy subadditivity for the actual coordinate marginals of an arbitrary
correlated density bounded above and away from zero. Every marginal and every
integral in the conclusion has been constructed explicitly. -/
theorem entropy_subadditivity_of_bounds
    {rho : ((i : Fin (n + 1)) → X i) → ℝ} {c B : ℝ}
    (hr : Measurable rho) (hc : 0 < c)
    (hlow : ∀ x, c ≤ rho x) (hupp : ∀ x, rho x ≤ B)
    (hmass : (∫ x, rho x ∂Measure.pi μ) = 1) :
    (∑ i, ∫ y, coordinateMarginal (μ := μ) rho i y *
      Real.log (coordinateMarginal (μ := μ) rho i y) ∂μ i) ≤
      ∫ x, rho x * Real.log (rho x) ∂Measure.pi μ := by
  have hri : Integrable rho (Measure.pi μ) := by
    apply integrable_of_measurable_norm_bound hr
    intro x
    rw [Real.norm_eq_abs, abs_of_pos (hc.trans_le (hlow x))]
    exact hupp x
  have hlog : Measurable (fun x => Real.log (rho x)) := Real.measurable_log.comp hr
  have hlogB : ∀ x, ‖Real.log (rho x)‖ ≤ |Real.log c| + |Real.log B| :=
    fun x => norm_log_le_of_bounds hc (hlow x) (hupp x)
  have hentropy : Integrable (fun x => rho x * Real.log (rho x)) (Measure.pi μ) :=
    hri.mul_bdd hlog.aestronglyMeasurable (Filter.Eventually.of_forall hlogB)
  let m := coordinateMarginal (μ := μ) rho
  have hm (i : Fin (n + 1)) : Measurable (m i) := coordinateMarginal_measurable hr i
  have hmb (i : Fin (n + 1)) (y : X i) : c ≤ m i y ∧ m i y ≤ B :=
    coordinateMarginal_bounds hr hc.le hlow hupp i y
  have hmp (i : Fin (n + 1)) (y : X i) : 0 < m i y := hc.trans_le (hmb i y).1
  have hmu (i : Fin (n + 1)) : Measurable (fun y => Real.log (m i y)) :=
    Real.measurable_log.comp (hm i)
  have hmub (i : Fin (n + 1)) (y : X i) :
      ‖Real.log (m i y)‖ ≤ |Real.log c| + |Real.log B| :=
    norm_log_le_of_bounds hc (hmb i y).1 (hmb i y).2
  have h := tensor_entropy_variational
    (Filter.Eventually.of_forall (fun x => (hc.trans_le (hlow x)).le)) hmass hri hentropy
    (fun i y => Real.log (m i y)) (fun _ => |Real.log c| + |Real.log B|) hmu hmub
  have hZ (i : Fin (n + 1)) :
      (∫ y, Real.exp (Real.log (m i y)) ∂μ i) = 1 := by
    simp_rw [Real.exp_log (hmp i _)]
    exact (coordinateMarginal_mass hri i).trans hmass
  have hpair (i : Fin (n + 1)) :
      (∫ x, rho x * Real.log (m i (x i)) ∂Measure.pi μ) =
      ∫ y, m i y * Real.log (m i y) ∂μ i :=
    coordinateMarginal_pairing hri i (hmu i) (hmub i)
  simpa only [hZ, Real.log_one, sub_zero, hpair] using h

end Coordinate

section ActualTorus

/-- An actual one-coordinate marginal of a dimension-ten probability density,
with the unit-mass circle Haar measure used in the endpoint normalization. -/
noncomputable def torusCoordinateMarginal10
    (rho : Legacy.TorusEndpoint.ProbabilityDensity 10) (i : Fin 10) : UnitAddCircle → ℝ :=
  coordinateMarginal (n := 9) (μ := fun _ => AddCircle.haarAddCircle) rho.value i

/-- The entropy subadditivity statement used by the dimension-ten argument.
No independence of the density or of any latent mixture coordinates is needed. -/
theorem torus_entropy_subadditivity10
    (rho : Legacy.TorusEndpoint.ProbabilityDensity 10) {c B : ℝ}
    (hr : Measurable rho.value) (hc : 0 < c)
    (hlow : ∀ x, c ≤ rho.value x) (hupp : ∀ x, rho.value x ≤ B) :
    (∑ i : Fin 10, ∫ y : UnitAddCircle,
      torusCoordinateMarginal10 rho i y * Real.log (torusCoordinateMarginal10 rho i y)
        ∂AddCircle.haarAddCircle) ≤ Legacy.TorusEndpoint.densityEntropy rho.value := by
  exact entropy_subadditivity_of_bounds (n := 9)
    (μ := fun _ => AddCircle.haarAddCircle) hr hc hlow hupp rho.mass

/-- In particular the required bounds are derived, rather than assumed,
for any actual continuous strictly positive torus density. -/
theorem torus_entropy_subadditivity10_of_continuous_pos
    (rho : Legacy.TorusEndpoint.ProbabilityDensity 10)
    (hr : Continuous rho.value) (hpos : ∀ x, 0 < rho.value x) :
    (∑ i : Fin 10, ∫ y : UnitAddCircle,
      torusCoordinateMarginal10 rho i y * Real.log (torusCoordinateMarginal10 rho i y)
        ∂AddCircle.haarAddCircle) ≤ Legacy.TorusEndpoint.densityEntropy rho.value := by
  obtain ⟨xmin, _, hmin⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty hr.continuousOn
  obtain ⟨xmax, _, hmax⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hr.continuousOn
  exact torus_entropy_subadditivity10 rho hr.measurable (hpos xmin)
    (fun x => hmin (Set.mem_univ x)) (fun x => hmax (Set.mem_univ x))

end ActualTorus

end Legacy.D10
