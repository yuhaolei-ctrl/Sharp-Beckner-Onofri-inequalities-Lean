import Legacy.D10.AnalyticCircleMarginals

/-! Actual coordinate marginals and the axis entropy estimate in every
positive dimension. This is an axis estimate, not the full endpoint. -/

open MeasureTheory Legacy.TorusEndpoint
open scoped BigOperators

namespace Legacy.BecknerOnofri.TorusMarginals
open Legacy.D10
variable {n : ℕ}

noncomputable def torusCoordinateMarginal
    (rho : ProbabilityDensity (n+1)) (i : Fin (n+1)) : UnitAddCircle → ℝ :=
  coordinateMarginal (μ := fun _ => AddCircle.haarAddCircle) rho.value i

theorem torus_entropy_subadditivity_of_continuous_pos
    (rho : ProbabilityDensity (n+1)) (hr : Continuous rho.value)
    (hpos : ∀ x, 0 < rho.value x) :
    (∑ i : Fin (n+1), ∫ y : UnitAddCircle,
      torusCoordinateMarginal rho i y * Real.log (torusCoordinateMarginal rho i y)
        ∂AddCircle.haarAddCircle) ≤ densityEntropy rho.value := by
  obtain ⟨xmin, _, hmin⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty hr.continuousOn
  obtain ⟨xmax, _, hmax⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hr.continuousOn
  exact entropy_subadditivity_of_bounds (μ := fun _ : Fin (n+1) => AddCircle.haarAddCircle)
    hr.measurable (hpos xmin) (fun x => hmin (Set.mem_univ x))
    (fun x => hmax (Set.mem_univ x)) rho.mass

/-- The Fubini marginal has a genuine finite-entropy probability-density
representative on the one-dimensional torus. -/
theorem exists_torusMarginalDensity
    (rho : ProbabilityDensity (n+1)) (hr : Continuous rho.value)
    (hpos : ∀ x, 0 < rho.value x) (i : Fin (n+1)) :
    ∃ m : ProbabilityDensity 1,
      m.value = (fun x => torusCoordinateMarginal rho i (x 0)) ∧ m.FiniteEntropy := by
  obtain ⟨xmin, _, hmin⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty hr.continuousOn
  obtain ⟨xmax, _, hmax⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hr.continuousOn
  let c := rho.value xmin
  let B := rho.value xmax
  have hc : 0 < c := hpos xmin
  have hm : Measurable (torusCoordinateMarginal rho i) :=
    coordinateMarginal_measurable (μ := fun _ : Fin (n+1) => AddCircle.haarAddCircle) hr.measurable i
  have hb (y : UnitAddCircle) :
      c ≤ torusCoordinateMarginal rho i y ∧ torusCoordinateMarginal rho i y ≤ B :=
    coordinateMarginal_bounds hr.measurable hc.le
      (fun x => hmin (Set.mem_univ x)) (fun x => hmax (Set.mem_univ x)) i y
  have hmi : Integrable (torusCoordinateMarginal rho i) AddCircle.haarAddCircle := by
    apply integrable_of_measurable_norm_bound (B := B) hm
    intro y
    rw [Real.norm_eq_abs, abs_of_pos (hc.trans_le (hb y).1)]
    exact (hb y).2
  let m : ProbabilityDensity 1 := {
    value := fun x => torusCoordinateMarginal rho i (x 0)
    nonneg := Filter.Eventually.of_forall (fun x => (hc.trans_le (hb (x 0)).1).le)
    integrable := integrable_comp_eval (μ := fun _ : Fin 1 => AddCircle.haarAddCircle) hmi
    mass := by
      change (∫ x : Legacy.TorusEndpoint.Torus 1, torusCoordinateMarginal rho i (x 0)
        ∂Measure.pi (fun _ : Fin 1 => AddCircle.haarAddCircle)) = 1
      rw [integral_comp_eval (μ := fun _ : Fin 1 => AddCircle.haarAddCircle)
        (i := (0 : Fin 1)) hm.aestronglyMeasurable]
      exact (coordinateMarginal_mass (μ := fun _ : Fin (n+1) => AddCircle.haarAddCircle)
        rho.integrable i).trans rho.mass }
  refine ⟨m, rfl, ?_⟩
  have hlog : Measurable (fun x : Legacy.TorusEndpoint.Torus 1 => Real.log (m.value x)) :=
    Real.measurable_log.comp (hm.comp (measurable_pi_apply 0))
  exact m.integrable.mul_bdd hlog.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x =>
      norm_log_le_of_bounds hc (hb (x 0)).1 (hb (x 0)).2))

/-- A selected actual marginal density; its value is uniquely fixed by the
Fubini definition, irrespective of the choice used to select its proofs. -/
noncomputable def torusMarginalDensity
    (rho : ProbabilityDensity (n+1)) (hr : Continuous rho.value)
    (hpos : ∀ x, 0 < rho.value x) (i : Fin (n+1)) : ProbabilityDensity 1 :=
  Classical.choose (exists_torusMarginalDensity rho hr hpos i)

@[simp] theorem torusMarginalDensity_value
    (rho : ProbabilityDensity (n+1)) (hr : Continuous rho.value)
    (hpos : ∀ x, 0 < rho.value x) (i : Fin (n+1)) :
    (torusMarginalDensity rho hr hpos i).value =
      (fun x => torusCoordinateMarginal rho i (x 0)) :=
  (Classical.choose_spec (exists_torusMarginalDensity rho hr hpos i)).1

theorem torusMarginalDensity_finiteEntropy
    (rho : ProbabilityDensity (n+1)) (hr : Continuous rho.value)
    (hpos : ∀ x, 0 < rho.value x) (i : Fin (n+1)) :
    (torusMarginalDensity rho hr hpos i).FiniteEntropy :=
  (Classical.choose_spec (exists_torusMarginalDensity rho hr hpos i)).2

theorem torusMarginalDensity_entropy
    (rho : ProbabilityDensity (n+1)) (hr : Continuous rho.value)
    (hpos : ∀ x, 0 < rho.value x) (i : Fin (n+1)) :
    densityEntropy (torusMarginalDensity rho hr hpos i).value =
      ∫ y : UnitAddCircle, torusCoordinateMarginal rho i y *
        Real.log (torusCoordinateMarginal rho i y) ∂AddCircle.haarAddCircle := by
  unfold densityEntropy
  rw [torusMarginalDensity_value]
  have hm := coordinateMarginal_measurable (μ := fun _ : Fin (n+1) => AddCircle.haarAddCircle)
    hr.measurable i
  exact integral_comp_eval (μ := fun _ : Fin 1 => AddCircle.haarAddCircle)
    ((hm.mul (Real.measurable_log.comp hm)).aestronglyMeasurable)

/-- The entropy inequality expressed using genuine one-dimensional density
objects, so it connects directly to `CircleEntropy.entropy_bound`. -/
theorem torusMarginalDensity_entropy_sum_le
    (rho : ProbabilityDensity (n+1)) (hr : Continuous rho.value)
    (hpos : ∀ x, 0 < rho.value x) :
    (∑ i : Fin (n+1), densityEntropy (torusMarginalDensity rho hr hpos i).value) ≤
      densityEntropy rho.value := by
  simpa only [torusMarginalDensity_entropy] using
    torus_entropy_subadditivity_of_continuous_pos rho hr hpos

/-- An arbitrary integer frequency supported in one coordinate. -/
def axisFrequency {d : ℕ} (i : Fin d) (k : Frequency 1) : Frequency d :=
  Pi.single i (k 0)

theorem mFourier_axis (i : Fin (n+1)) (k : Frequency 1) (x : Legacy.TorusEndpoint.Torus (n+1)) :
    UnitAddTorus.mFourier (-(axisFrequency i k)) x =
      UnitAddTorus.mFourier (-k) (fun _ : Fin 1 => x i) := by
  rw [UnitAddTorus.mFourier_neg, UnitAddTorus.mFourier_neg]
  rw [axisFrequency, Legacy.D10.mFourier_single_int]
  congr 1
  simp [UnitAddTorus.mFourier]

/-- Fubini pairing in the one-dimensional torus representation. -/
theorem torusMarginalDensity_pairing
    (rho : ProbabilityDensity (n+1)) (hr : Continuous rho.value)
    (hpos : ∀ x, 0 < rho.value x) (i : Fin (n+1))
    {u : Legacy.TorusEndpoint.Torus 1 → ℝ} {B : ℝ}
    (hu : Measurable u) (hB : ∀ x, ‖u x‖ ≤ B) :
    (∫ x, rho.value x * u (fun _ : Fin 1 => x i) ∂torusMeasure (n+1)) =
      ∫ y, (torusMarginalDensity rho hr hpos i).value y * u y ∂torusMeasure 1 := by
  have hdiag : Measurable (fun y : UnitAddCircle => (fun _ : Fin 1 => y)) := by
    fun_prop
  have hm := coordinateMarginal_measurable (μ := fun _ : Fin (n+1) => AddCircle.haarAddCircle)
    hr.measurable i
  have he (x : Legacy.TorusEndpoint.Torus 1) : (fun _ : Fin 1 => x 0) = x := by
    funext j
    have hj : j = 0 := Subsingleton.elim _ _
    simp [hj]
  calc
    _ = ∫ y : UnitAddCircle, torusCoordinateMarginal rho i y *
        u (fun _ : Fin 1 => y) ∂AddCircle.haarAddCircle :=
      coordinateMarginal_pairing (μ := fun _ : Fin (n+1) => AddCircle.haarAddCircle)
        rho.integrable i (hu.comp hdiag) (fun _ => hB _)
    _ = ∫ x : Legacy.TorusEndpoint.Torus 1, torusCoordinateMarginal rho i (x 0) *
        u (fun _ : Fin 1 => x 0) ∂torusMeasure 1 := by
      exact (integral_comp_eval (μ := fun _ : Fin 1 => AddCircle.haarAddCircle)
        ((hm.mul (hu.comp hdiag)).aestronglyMeasurable)).symm
    _ = _ := by
      simp only [torusMarginalDensity_value, he]

/-- The Fourier coefficient of an actual marginal equals the corresponding
axis Fourier coefficient of the original joint density. -/
theorem torusMarginalDensity_fourier
    (rho : ProbabilityDensity (n+1)) (hr : Continuous rho.value)
    (hpos : ∀ x, 0 < rho.value x) (i : Fin (n+1)) (k : Frequency 1) :
    densityFourier (torusMarginalDensity rho hr hpos i).value k =
      densityFourier rho.value (axisFrequency i k) := by
  apply Complex.ext
  · rw [← densityFourier_re_moment, ← densityFourier_re_moment]
    symm
    have h := torusMarginalDensity_pairing rho hr hpos i
      (fourierRealFeature_measurable (k, false)) (fourierRealFeature_bound (k, false))
    simpa only [fourierRealFeature, Bool.false_eq_true, if_false, mFourier_axis] using h
  · rw [← densityFourier_im_moment, ← densityFourier_im_moment]
    symm
    have h := torusMarginalDensity_pairing rho hr hpos i
      (fourierRealFeature_measurable (k, true)) (fourierRealFeature_bound (k, true))
    simpa only [fourierRealFeature, if_true, mFourier_axis] using h

/-- The actual full-circle weight of an axis Fourier mode, including both
positive and negative frequencies. -/
noncomputable def axisEnergyTerm {d : ℕ} (rho : ProbabilityDensity d)
    (i : Fin d) (k : NonzeroFrequency 1) : ℝ :=
  CircleEntropy.weight k.val * ‖densityFourier rho.value (axisFrequency i k.val)‖ ^ 2

/-- The complete axis Fourier spectrum is summable and bounded by twice the
joint entropy. This is an unconditional estimate for continuous strictly
positive joint densities; it is not the full full endpoint. -/
theorem axis_entropy_bound_succ
    (rho : ProbabilityDensity (n+1)) (hr : Continuous rho.value)
    (hpos : ∀ x, 0 < rho.value x) :
    (∀ i : Fin (n+1), Summable (axisEnergyTerm rho i)) ∧
    (∑ i : Fin (n+1), ∑' k : NonzeroFrequency 1, axisEnergyTerm rho i k) ≤
      2 * densityEntropy rho.value := by
  have hcircle (i : Fin (n+1)) := CircleEntropy.entropy_bound
    (torusMarginalDensity rho hr hpos i) (torusMarginalDensity_finiteEntropy rho hr hpos i)
  have hs (i : Fin (n+1)) : Summable (axisEnergyTerm rho i) := by
    change Summable (fun k : NonzeroFrequency 1 => CircleEntropy.weight k.val *
      ‖densityFourier rho.value (axisFrequency i k.val)‖ ^ 2)
    simpa only [torusMarginalDensity_fourier] using (hcircle i).1
  refine ⟨hs, ?_⟩
  calc
    _ ≤ ∑ i : Fin (n+1), 2 * densityEntropy (torusMarginalDensity rho hr hpos i).value := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [axisEnergyTerm, torusMarginalDensity_fourier] using (hcircle i).2
    _ = 2 * ∑ i : Fin (n+1), densityEntropy (torusMarginalDensity rho hr hpos i).value := by
      rw [Finset.mul_sum]
    _ ≤ 2 * densityEntropy rho.value :=
      mul_le_mul_of_nonneg_left (torusMarginalDensity_entropy_sum_le rho hr hpos) (by norm_num)


/-- Every actual continuous strictly positive density in positive dimension
has summable axis spectrum, bounded by twice its joint entropy. -/
theorem axis_entropy_bound {d : ℕ} (hd : 0 < d)
    (rho : ProbabilityDensity d) (hr : Continuous rho.value)
    (hpos : ∀ x, 0 < rho.value x) :
    (∀ i : Fin d, Summable (axisEnergyTerm rho i)) ∧
    (∑ i : Fin d, ∑' k : NonzeroFrequency 1, axisEnergyTerm rho i k) ≤
      2 * densityEntropy rho.value := by
  cases d with
  | zero => omega
  | succ n => exact axis_entropy_bound_succ rho hr hpos

#print axioms axis_entropy_bound
#print axioms torusMarginalDensity_fourier
#print axioms torusMarginalDensity_entropy_sum_le
end Legacy.BecknerOnofri.TorusMarginals
