import Legacy.BecknerOnofri.TorusMarginals

/-! The actual coordinate map from a product torus to the one-dimensional
Haar torus, including its measure-preserving property. -/
noncomputable section
open MeasureTheory Legacy.TorusEndpoint
namespace BecknerOnofri.AdamsEndpoint

def coordinateCircle {d : ℕ} (i : Fin d) (x : Torus d) : Torus 1 := fun _ => x i

theorem coordinateCircle_measurePreserving {d : ℕ} (i : Fin d) :
    MeasurePreserving (coordinateCircle i) (torusMeasure d) (torusMeasure 1) := by
  have he := (measurePreserving_piUnique
    (fun _ : Fin 1 => (AddCircle.haarAddCircle : Measure UnitAddCircle))).symm
  exact he.comp (measurePreserving_eval
    (fun _ : Fin d => (AddCircle.haarAddCircle : Measure UnitAddCircle)) i)

theorem coordinateMarginal_pairing_of_integrable {n : ℕ}
    (rho : Torus (n+1) → ℝ) (i : Fin (n+1)) (u : UnitAddCircle → ℝ)
    (hi : Integrable (fun x => rho x * u (x i)) (torusMeasure (n+1))) :
    (∫ x, rho x * u (x i) ∂torusMeasure (n+1)) =
      ∫ y, Legacy.D10.coordinateMarginal (μ := fun _ => AddCircle.haarAddCircle) rho i y * u y
        ∂AddCircle.haarAddCircle := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => UnitAddCircle) i
  have he := (measurePreserving_piFinSuccAbove
    (fun _ : Fin (n+1) => (AddCircle.haarAddCircle : Measure UnitAddCircle)) i).symm
  have hprod := (he.integrable_comp_emb e.symm.measurableEmbedding).mpr hi
  change Integrable (fun z => rho (e.symm z) * u ((e.symm z) i))
    (AddCircle.haarAddCircle.prod (torusMeasure n)) at hprod
  calc
    _ = ∫ z, rho (e.symm z) * u ((e.symm z) i)
        ∂AddCircle.haarAddCircle.prod (torusMeasure n) :=
      (he.integral_comp' (fun x => rho x * u (x i))).symm
    _ = ∫ y, Legacy.D10.coordinateMarginal (μ := fun _ => AddCircle.haarAddCircle) rho i y * u y
        ∂AddCircle.haarAddCircle := by
      rw [integral_prod _ hprod]
      simp [e,MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv,
        integral_mul_const,Legacy.D10.coordinateMarginal,torusMeasure]
      rfl

#print axioms coordinateCircle_measurePreserving
#print axioms coordinateMarginal_pairing_of_integrable
end BecknerOnofri.AdamsEndpoint
