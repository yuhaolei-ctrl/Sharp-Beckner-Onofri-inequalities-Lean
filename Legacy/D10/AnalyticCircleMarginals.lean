module

public import Legacy.D10.AnalyticMarginals
public import Legacy.D10.CircleEntropy

@[expose] public section

/-!
# The actual axis Fourier bound on the ten-dimensional torus

We construct each genuine marginal as `ProbabilityDensity 1`, identify its
Fourier coefficients with the corresponding axis coefficients of the original
density, and combine the unconditional circle entropy theorem with entropy
subadditivity. This proves an axis estimate, not the full endpoint estimate.
-/

open MeasureTheory Legacy.TorusEndpoint
open scoped BigOperators

namespace Legacy.D10

/-- The Fubini marginal has a genuine finite-entropy probability-density
representative on the one-dimensional torus. -/
theorem exists_torusMarginalDensity10
    (rho : ProbabilityDensity 10) (hr : Continuous rho.value)
    (hpos : ∀ x, 0 < rho.value x) (i : Fin 10) :
    ∃ m : ProbabilityDensity 1,
      m.value = (fun x => torusCoordinateMarginal10 rho i (x 0)) ∧ m.FiniteEntropy := by
  obtain ⟨xmin, _, hmin⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty hr.continuousOn
  obtain ⟨xmax, _, hmax⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hr.continuousOn
  let c := rho.value xmin
  let B := rho.value xmax
  have hc : 0 < c := hpos xmin
  have hm : Measurable (torusCoordinateMarginal10 rho i) :=
    coordinateMarginal_measurable (μ := fun _ : Fin 10 => AddCircle.haarAddCircle) hr.measurable i
  have hb (y : UnitAddCircle) :
      c ≤ torusCoordinateMarginal10 rho i y ∧ torusCoordinateMarginal10 rho i y ≤ B :=
    coordinateMarginal_bounds hr.measurable hc.le
      (fun x => hmin (Set.mem_univ x)) (fun x => hmax (Set.mem_univ x)) i y
  have hmi : Integrable (torusCoordinateMarginal10 rho i) AddCircle.haarAddCircle := by
    apply integrable_of_measurable_norm_bound (B := B) hm
    intro y
    rw [Real.norm_eq_abs, abs_of_pos (hc.trans_le (hb y).1)]
    exact (hb y).2
  let m : ProbabilityDensity 1 := {
    value := fun x => torusCoordinateMarginal10 rho i (x 0)
    nonneg := Filter.Eventually.of_forall (fun x => (hc.trans_le (hb (x 0)).1).le)
    integrable := integrable_comp_eval (μ := fun _ : Fin 1 => AddCircle.haarAddCircle) hmi
    mass := by
      change (∫ x : Legacy.TorusEndpoint.Torus 1, torusCoordinateMarginal10 rho i (x 0)
        ∂Measure.pi (fun _ : Fin 1 => AddCircle.haarAddCircle)) = 1
      rw [integral_comp_eval (μ := fun _ : Fin 1 => AddCircle.haarAddCircle)
        (i := (0 : Fin 1)) hm.aestronglyMeasurable]
      exact (coordinateMarginal_mass (μ := fun _ : Fin 10 => AddCircle.haarAddCircle)
        rho.integrable i).trans rho.mass }
  refine ⟨m, rfl, ?_⟩
  have hlog : Measurable (fun x : Legacy.TorusEndpoint.Torus 1 => Real.log (m.value x)) :=
    Real.measurable_log.comp (hm.comp (measurable_pi_apply 0))
  exact m.integrable.mul_bdd hlog.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x =>
      norm_log_le_of_bounds hc (hb (x 0)).1 (hb (x 0)).2))

/-- A selected actual marginal density; its value is uniquely fixed by the
Fubini definition, irrespective of the choice used to select its proofs. -/
noncomputable def torusMarginalDensity10
    (rho : ProbabilityDensity 10) (hr : Continuous rho.value)
    (hpos : ∀ x, 0 < rho.value x) (i : Fin 10) : ProbabilityDensity 1 :=
  Classical.choose (exists_torusMarginalDensity10 rho hr hpos i)

@[simp] theorem torusMarginalDensity10_value
    (rho : ProbabilityDensity 10) (hr : Continuous rho.value)
    (hpos : ∀ x, 0 < rho.value x) (i : Fin 10) :
    (torusMarginalDensity10 rho hr hpos i).value =
      (fun x => torusCoordinateMarginal10 rho i (x 0)) :=
  (Classical.choose_spec (exists_torusMarginalDensity10 rho hr hpos i)).1

theorem torusMarginalDensity10_finiteEntropy
    (rho : ProbabilityDensity 10) (hr : Continuous rho.value)
    (hpos : ∀ x, 0 < rho.value x) (i : Fin 10) :
    (torusMarginalDensity10 rho hr hpos i).FiniteEntropy :=
  (Classical.choose_spec (exists_torusMarginalDensity10 rho hr hpos i)).2

theorem torusMarginalDensity10_entropy
    (rho : ProbabilityDensity 10) (hr : Continuous rho.value)
    (hpos : ∀ x, 0 < rho.value x) (i : Fin 10) :
    densityEntropy (torusMarginalDensity10 rho hr hpos i).value =
      ∫ y : UnitAddCircle, torusCoordinateMarginal10 rho i y *
        Real.log (torusCoordinateMarginal10 rho i y) ∂AddCircle.haarAddCircle := by
  unfold densityEntropy
  rw [torusMarginalDensity10_value]
  have hm := coordinateMarginal_measurable (μ := fun _ : Fin 10 => AddCircle.haarAddCircle)
    hr.measurable i
  exact integral_comp_eval (μ := fun _ : Fin 1 => AddCircle.haarAddCircle)
    ((hm.mul (Real.measurable_log.comp hm)).aestronglyMeasurable)

/-- The entropy inequality expressed using genuine one-dimensional density
objects, so it connects directly to `CircleEntropy.entropy_bound`. -/
theorem torusMarginalDensity10_entropy_sum_le
    (rho : ProbabilityDensity 10) (hr : Continuous rho.value)
    (hpos : ∀ x, 0 < rho.value x) :
    (∑ i : Fin 10, densityEntropy (torusMarginalDensity10 rho hr hpos i).value) ≤
      densityEntropy rho.value := by
  simpa only [torusMarginalDensity10_entropy] using
    torus_entropy_subadditivity10_of_continuous_pos rho hr hpos

/-- An arbitrary integer frequency supported in one coordinate. -/
def axisFrequency10 (i : Fin 10) (k : Frequency 1) : Frequency 10 :=
  Pi.single i (k 0)

/-- The multivariate character of an axis frequency is the corresponding
circle character. -/
theorem mFourier_single_int {d : ℕ} (i : Fin d) (z : ℤ) (x : Legacy.TorusEndpoint.Torus d) :
    UnitAddTorus.mFourier (Pi.single i z) x = fourier z (x i) := by
  classical
  change (∏ j : Fin d, fourier ((Pi.single i z : Fin d → ℤ) j) (x j)) = _
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _ hji
    simp [Pi.single_eq_of_ne hji]
  · simp

theorem mFourier_axis10 (i : Fin 10) (k : Frequency 1) (x : Legacy.TorusEndpoint.Torus 10) :
    UnitAddTorus.mFourier (-(axisFrequency10 i k)) x =
      UnitAddTorus.mFourier (-k) (fun _ : Fin 1 => x i) := by
  rw [UnitAddTorus.mFourier_neg, UnitAddTorus.mFourier_neg]
  rw [axisFrequency10, mFourier_single_int]
  congr 1
  simp [UnitAddTorus.mFourier]

/-- Fubini pairing in the one-dimensional torus representation. -/
theorem torusMarginalDensity10_pairing
    (rho : ProbabilityDensity 10) (hr : Continuous rho.value)
    (hpos : ∀ x, 0 < rho.value x) (i : Fin 10)
    {u : Legacy.TorusEndpoint.Torus 1 → ℝ} {B : ℝ}
    (hu : Measurable u) (hB : ∀ x, ‖u x‖ ≤ B) :
    (∫ x, rho.value x * u (fun _ : Fin 1 => x i) ∂torusMeasure 10) =
      ∫ y, (torusMarginalDensity10 rho hr hpos i).value y * u y ∂torusMeasure 1 := by
  have hdiag : Measurable (fun y : UnitAddCircle => (fun _ : Fin 1 => y)) := by
    fun_prop
  have hm := coordinateMarginal_measurable (μ := fun _ : Fin 10 => AddCircle.haarAddCircle)
    hr.measurable i
  have he (x : Legacy.TorusEndpoint.Torus 1) : (fun _ : Fin 1 => x 0) = x := by
    funext j
    have hj : j = 0 := Subsingleton.elim _ _
    simp [hj]
  calc
    _ = ∫ y : UnitAddCircle, torusCoordinateMarginal10 rho i y *
        u (fun _ : Fin 1 => y) ∂AddCircle.haarAddCircle :=
      coordinateMarginal_pairing (μ := fun _ : Fin 10 => AddCircle.haarAddCircle)
        rho.integrable i (hu.comp hdiag) (fun _ => hB _)
    _ = ∫ x : Legacy.TorusEndpoint.Torus 1, torusCoordinateMarginal10 rho i (x 0) *
        u (fun _ : Fin 1 => x 0) ∂torusMeasure 1 := by
      exact (integral_comp_eval (μ := fun _ : Fin 1 => AddCircle.haarAddCircle)
        ((hm.mul (hu.comp hdiag)).aestronglyMeasurable)).symm
    _ = _ := by
      simp only [torusMarginalDensity10_value, he]

/-- The Fourier coefficient of an actual marginal equals the corresponding
axis Fourier coefficient of the original joint density. -/
theorem torusMarginalDensity10_fourier
    (rho : ProbabilityDensity 10) (hr : Continuous rho.value)
    (hpos : ∀ x, 0 < rho.value x) (i : Fin 10) (k : Frequency 1) :
    densityFourier (torusMarginalDensity10 rho hr hpos i).value k =
      densityFourier rho.value (axisFrequency10 i k) := by
  apply Complex.ext
  · rw [← densityFourier_re_moment, ← densityFourier_re_moment]
    symm
    have h := torusMarginalDensity10_pairing rho hr hpos i
      (fourierRealFeature_measurable (k, false)) (fourierRealFeature_bound (k, false))
    simpa only [fourierRealFeature, Bool.false_eq_true, if_false, mFourier_axis10] using h
  · rw [← densityFourier_im_moment, ← densityFourier_im_moment]
    symm
    have h := torusMarginalDensity10_pairing rho hr hpos i
      (fourierRealFeature_measurable (k, true)) (fourierRealFeature_bound (k, true))
    simpa only [fourierRealFeature, if_true, mFourier_axis10] using h

/-- The actual full-circle weight of an axis Fourier mode, including both
positive and negative frequencies. -/
noncomputable def axisEnergyTerm10 (rho : ProbabilityDensity 10)
    (i : Fin 10) (k : NonzeroFrequency 1) : ℝ :=
  CircleEntropy.weight k.val * ‖densityFourier rho.value (axisFrequency10 i k.val)‖ ^ 2

/-- The complete axis Fourier spectrum is summable and bounded by twice the
joint entropy. This is an unconditional estimate for continuous strictly
positive joint densities; it is not the full dimension-ten endpoint. -/
theorem axis_entropy_bound10
    (rho : ProbabilityDensity 10) (hr : Continuous rho.value)
    (hpos : ∀ x, 0 < rho.value x) :
    (∀ i : Fin 10, Summable (axisEnergyTerm10 rho i)) ∧
    (∑ i : Fin 10, ∑' k : NonzeroFrequency 1, axisEnergyTerm10 rho i k) ≤
      2 * densityEntropy rho.value := by
  have hcircle (i : Fin 10) := CircleEntropy.entropy_bound
    (torusMarginalDensity10 rho hr hpos i) (torusMarginalDensity10_finiteEntropy rho hr hpos i)
  have hs (i : Fin 10) : Summable (axisEnergyTerm10 rho i) := by
    change Summable (fun k : NonzeroFrequency 1 => CircleEntropy.weight k.val *
      ‖densityFourier rho.value (axisFrequency10 i k.val)‖ ^ 2)
    simpa only [torusMarginalDensity10_fourier] using (hcircle i).1
  refine ⟨hs, ?_⟩
  calc
    _ ≤ ∑ i : Fin 10, 2 * densityEntropy (torusMarginalDensity10 rho hr hpos i).value := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [axisEnergyTerm10, torusMarginalDensity10_fourier] using (hcircle i).2
    _ = 2 * ∑ i : Fin 10, densityEntropy (torusMarginalDensity10 rho hr hpos i).value := by
      rw [Finset.mul_sum]
    _ ≤ 2 * densityEntropy rho.value :=
      mul_le_mul_of_nonneg_left (torusMarginalDensity10_entropy_sum_le rho hr hpos) (by norm_num)

end Legacy.D10
