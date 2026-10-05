import BecknerOnofri.CircleComparison

/-! The profile need only be continuous on its physical domain [-1,1].
A continuous clamped extension preserves the actual density and all moments. -/
noncomputable section
open MeasureTheory Set
namespace BecknerOnofri.HighDim.CircleScalar

theorem circle_comparison_on (F : ℝ → ℝ) (t : ℝ)
    (hcF : ContinuousOn F (Icc (-1:ℝ) 1)) (hF : ConvexOn ℝ (Icc (-1:ℝ) 1) F)
    (hinc : MonotoneOn F (Icc (-1:ℝ) 1))
    (hmass : (∫ x : UnitAddCircle,Real.exp (F ((fourier 1 x).re)) ∂AddCircle.haarAddCircle)=1)
    (hm : (∫ x : UnitAddCircle,Real.exp (F ((fourier 1 x).re))*(fourier 1 x).re
      ∂AddCircle.haarAddCircle)=t) :
    0≤t ∧ t<1 ∧
    besselMoment 2 (parameter t)≤
      (∫ x : UnitAddCircle,Real.exp (F ((fourier 1 x).re))*(fourier 2 x).re ∂AddCircle.haarAddCircle) ∧
    |(∫ x : UnitAddCircle,Real.exp (F ((fourier 1 x).re))*(fourier 3 x).re ∂AddCircle.haarAddCircle)-
      besselMoment 3 (parameter t)|≤
      6*((∫ x : UnitAddCircle,Real.exp (F ((fourier 1 x).re))*(fourier 2 x).re ∂AddCircle.haarAddCircle)-
        besselMoment 2 (parameter t)) ∧
    rate t≤∫ x : UnitAddCircle,Real.exp (F ((fourier 1 x).re))*
      Real.log (Real.exp (F ((fourier 1 x).re))) ∂AddCircle.haarAddCircle := by
  let K : ℝ → ℝ := fun x => max (-1:ℝ) (min 1 x)
  let G : ℝ → ℝ := fun x => F (K x)
  have hK (x : ℝ) : K x ∈ Icc (-1:ℝ) 1 := by
    refine ⟨le_max_left _ _,max_le (by norm_num) (min_le_left _ _)⟩
  have hKeq {x : ℝ} (hx : x ∈ Icc (-1:ℝ) 1) : K x=x := by
    dsimp only [K]
    rw [min_eq_right hx.2,max_eq_right hx.1]
  have hG {x : ℝ} (hx : x ∈ Icc (-1:ℝ) 1) : G x=F x := by
    change F (K x)=F x
    rw [hKeq hx]
  have hcG : Continuous G := hcF.comp_continuous (by dsimp [K]; fun_prop) hK
  have hconvG : ConvexOn ℝ (Icc (-1:ℝ) 1) G := hF.congr (fun _ hx => (hG hx).symm)
  have hincG : MonotoneOn G (Icc (-1:ℝ) 1) := by
    intro x hx y hy hxy
    rw [hG hx,hG hy]
    exact hinc hx hy hxy
  have hpoint (x : UnitAddCircle) : G ((fourier 1 x).re)=F ((fourier 1 x).re) :=
    hG (abs_le.mp (circle_cosine_bound x))
  have hmassG : (∫ x : UnitAddCircle,Real.exp (G ((fourier 1 x).re)) ∂AddCircle.haarAddCircle)=1 := by
    simpa only [hpoint] using hmass
  have hmG : (∫ x : UnitAddCircle,Real.exp (G ((fourier 1 x).re))*(fourier 1 x).re
      ∂AddCircle.haarAddCircle)=t := by simpa only [hpoint] using hm
  have h := circle_comparison G t hcG hconvG hincG hmassG hmG
  simpa only [hpoint] using h

#print axioms circle_comparison_on
end BecknerOnofri.HighDim.CircleScalar
