import BecknerOnofri.DistributionMonotoneUniqueness
import BecknerOnofri.PolarizationMetricGeometry
import Legacy.BecknerOnofri.SteinerSelection

/-! On the one-dimensional torus, the actual Steiner property is radial
monotonicity, and equal distributions determine a unique continuous function. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Legacy.TorusEndpoint
namespace BecknerOnofri.PolarizationL1
open Legacy.BecknerOnofri SteinerFromPolarization

lemma torus_one_ext {x y : Torus 1} (h : x 0=y 0) : x=y := by
  funext i
  have hi : i=0 := Subsingleton.elim _ _
  simpa only [hi] using h

def radiusPoint (t : ℝ) : Torus 1 := fun _ => (t : UnitAddCircle)

lemma steiner_radius_value {f : Torus 1 → ℝ} (hf : SteinerSelection.Steiner f)
    (x : Torus 1) : f (radiusPoint ‖x 0‖)=f x := by
  let t : ℝ := AddCircle.equivIoc 1 (-(1/2 : ℝ)) (x 0)
  have ht : -(1/2 : ℝ)<t ∧ t≤1/2 := by
    have h := (AddCircle.equivIoc 1 (-(1/2 : ℝ)) (x 0)).property
    exact ⟨h.1,by linarith [h.2]⟩
  have hcoe : (t : UnitAddCircle)=x 0 := AddCircle.coe_equivIoc
  have hn : ‖x 0‖=|t| := by
    rw [← hcoe]
    exact circle_norm_small (abs_le.mpr ⟨ht.1.le,ht.2⟩)
  by_cases hp : 0≤t
  · congr 1
    apply torus_one_ext
    simpa only [radiusPoint,hn,abs_of_nonneg hp] using hcoe
  · have he : radiusPoint ‖x 0‖=Function.update x 0 (-x 0) := by
      apply torus_one_ext
      simp only [radiusPoint,hn,abs_of_neg (lt_of_not_ge hp),Function.update_self,
        AddCircle.coe_neg,hcoe]
    rw [he]
    exact hf.1 0 x

theorem steiner_antitone_radius {f : Torus 1 → ℝ} (hf : SteinerSelection.Steiner f) :
    ∀ x y,‖x 0‖≤‖y 0‖ → f y≤f x := by
  intro x y hxy
  have hslice (t : ℝ) : slice (0 : Torus 1) 0 t=radiusPoint t :=
    torus_one_ext (by simp [slice,radiusPoint])
  have hx : ‖x 0‖∈Icc (0 : ℝ) (1/2) :=
    ⟨norm_nonneg _,by simpa using AddCircle.norm_le_half_period 1 (x := x 0) (by norm_num)⟩
  have hy : ‖y 0‖∈Icc (0 : ℝ) (1/2) :=
    ⟨norm_nonneg _,by simpa using AddCircle.norm_le_half_period 1 (x := y 0) (by norm_num)⟩
  have h := hf.2 (0 : Torus 1) 0 hx hy hxy
  simpa only [hslice,steiner_radius_value hf] using h

theorem steiner_eq_of_identDistrib {f g : Torus 1 → ℝ}
    (hf : Continuous f) (hg : Continuous g)
    (hfS : SteinerSelection.Steiner f) (hgS : SteinerSelection.Steiner g)
    (hD : IdentDistrib f g (torusMeasure 1) (torusMeasure 1)) : f=g := by
  haveI : (torusMeasure 1).IsOpenPosMeasure := by
    rw [torusMeasure_explicit]
    infer_instance
  apply Measure.eq_of_ae_eq (μ := torusMeasure 1) ?_ hf hg
  exact DistributionLimit.ae_eq_of_identDistrib_antitone_radius (fun x : Torus 1 => ‖x 0‖)
    hf.measurable hg.measurable hD (steiner_antitone_radius hfS) (steiner_antitone_radius hgS)

#print axioms steiner_antitone_radius
#print axioms steiner_eq_of_identDistrib
end BecknerOnofri.PolarizationL1
