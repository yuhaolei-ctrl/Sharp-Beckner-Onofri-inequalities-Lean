import BecknerOnofri.CoordinateCircleProjection

/-! Fubini pairing against integrable, possibly unbounded circle functions.
This removes the bounded-test restriction when using a singular Green kernel. -/
noncomputable section
open MeasureTheory Legacy.TorusEndpoint
namespace BecknerOnofri.AdamsEndpoint
open Legacy.BecknerOnofri.TorusMarginals Legacy.D10

theorem continuous_norm_bound {d : ℕ} {f : Torus d → ℝ} (hf : Continuous f) :
    ∃ B : ℝ, ∀ x, ‖f x‖ ≤ B := by
  obtain ⟨x, _, hx⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hf.norm.continuousOn
  exact ⟨‖f x‖, fun y => hx (Set.mem_univ y)⟩

theorem torusMarginalDensity_measurable {n : ℕ}
    (rho : ProbabilityDensity (n+1)) (hr : Continuous rho.value)
    (hpos : ∀ x, 0 < rho.value x) (i : Fin (n+1)) :
    Measurable (torusMarginalDensity rho hr hpos i).value := by
  rw [torusMarginalDensity_value]
  exact (coordinateMarginal_measurable
    (μ := fun _ : Fin (n+1) => AddCircle.haarAddCircle) hr.measurable i).comp
      (measurable_pi_apply 0)

theorem torusMarginalDensity_norm_bound {n : ℕ}
    (rho : ProbabilityDensity (n+1)) (hr : Continuous rho.value)
    (hpos : ∀ x, 0 < rho.value x) (i : Fin (n+1)) {B : ℝ}
    (hB : ∀ x, ‖rho.value x‖ ≤ B) (y : Torus 1) :
    ‖(torusMarginalDensity rho hr hpos i).value y‖ ≤ B := by
  rw [torusMarginalDensity_value]
  unfold torusCoordinateMarginal coordinateMarginal
  simpa using (norm_integral_le_of_norm_le_const
    (μ := Measure.pi (fun _ : Fin n => (AddCircle.haarAddCircle : Measure UnitAddCircle)))
    (ae_of_all _ (fun z : Fin n → UnitAddCircle => hB
      ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => UnitAddCircle) i).symm (y 0,z)))))

theorem torusMarginalDensity_memLp {n : ℕ}
    (rho : ProbabilityDensity (n+1)) (hr : Continuous rho.value)
    (hpos : ∀ x, 0 < rho.value x) (i : Fin (n+1)) :
    MemLp (torusMarginalDensity rho hr hpos i).value 2 (torusMeasure 1) := by
  obtain ⟨B,hB⟩ := continuous_norm_bound hr
  exact MemLp.of_bound (torusMarginalDensity_measurable rho hr hpos i).aestronglyMeasurable B
    (ae_of_all _ (torusMarginalDensity_norm_bound rho hr hpos i hB))

theorem torusMarginalDensity_pairing_integrable {n : ℕ}
    (rho : ProbabilityDensity (n+1)) (hr : Continuous rho.value)
    (hpos : ∀ x, 0 < rho.value x) (i : Fin (n+1))
    (u : Torus 1 → ℝ) (hu : Measurable u) (hui : Integrable u (torusMeasure 1)) :
    (∫ x, rho.value x * u (coordinateCircle i x) ∂torusMeasure (n+1)) =
      ∫ y, (torusMarginalDensity rho hr hpos i).value y * u y ∂torusMeasure 1 := by
  obtain ⟨B,hB⟩ := continuous_norm_bound hr
  have hi := ((coordinateCircle_measurePreserving i).integrable_comp_of_integrable hui).bdd_mul
    hr.aestronglyMeasurable (ae_of_all _ hB)
  have hdiag : Measurable (fun y : UnitAddCircle => (fun _ : Fin 1 => y)) := by fun_prop
  have hm := coordinateMarginal_measurable (μ := fun _ : Fin (n+1) => AddCircle.haarAddCircle)
    hr.measurable i
  have he (x : Torus 1) : (fun _ : Fin 1 => x 0) = x := by
    funext j
    have hj : j = 0 := Subsingleton.elim _ _
    simp [hj]
  calc
    _ = ∫ y : UnitAddCircle, torusCoordinateMarginal rho i y *
        u (fun _ : Fin 1 => y) ∂AddCircle.haarAddCircle :=
      coordinateMarginal_pairing_of_integrable rho.value i (fun y => u (fun _ => y)) hi
    _ = ∫ x : Torus 1, torusCoordinateMarginal rho i (x 0) *
        u (fun _ : Fin 1 => x 0) ∂torusMeasure 1 :=
      (integral_comp_eval (μ := fun _ : Fin 1 => AddCircle.haarAddCircle)
        ((hm.mul (hu.comp hdiag)).aestronglyMeasurable)).symm
    _ = _ := by simp only [torusMarginalDensity_value, he]

#print axioms torusMarginalDensity_memLp
#print axioms torusMarginalDensity_pairing_integrable
end BecknerOnofri.AdamsEndpoint
