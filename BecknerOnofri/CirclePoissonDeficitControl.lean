import BecknerOnofri.CirclePoissonDeficit
import BecknerOnofri.CirclePoissonLimit
import Mathlib.Analysis.Calculus.Deriv.MeanValue

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
namespace BecknerOnofri.HighDim.CirclePoisson

theorem smooth_deficit_control (p : Torus 1 → ℝ) (hp : Continuous p)
    (hpos : ∀ x,0<p x) (he : ∀ x,p (-x)=p x) (hm : (∫ x,p x ∂torusMeasure 1)=1)
    (hsmooth : ContDiff ℝ 3 (fun x : ℝ => p (fun _ => (x:UnitAddCircle)))) :
    let r : ℕ → ℝ := fun n =>
      (UnitAddTorus.mFourierCoeff (fun x => (p x:ℂ)) (fun _ => (n:ℤ))).re
    let D : ℝ → ℝ := fun t =>
      (∫ x,torusFlow t p x*Real.log (torusFlow t p x) ∂torusMeasure 1)-
        ∑' n : ℕ,Real.exp (-2*(n+1:ℝ)*t)*(r (n+1))^2/(n+1:ℝ)
    AntitoneOn D (Ioi (0:ℝ)) ∧ (∀ s : ℝ,0<s → 0≤D s) ∧ Tendsto D atTop (nhds 0) := by
  dsimp only
  let r : ℕ → ℝ := fun n =>
    (UnitAddTorus.mFourierCoeff (fun x => (p x:ℂ)) (fun _ => (n:ℤ))).re
  let D : ℝ → ℝ := fun t =>
    (∫ x,torusFlow t p x*Real.log (torusFlow t p x) ∂torusMeasure 1)-
      ∑' n : ℕ,Real.exp (-2*(n+1:ℝ)*t)*(r (n+1))^2/(n+1:ℝ)
  have hd (s : ℝ) (hs : 0<s) : DifferentiableAt ℝ D s :=
    (smooth_deficit_dissipation p hp hpos he hm hsmooth s hs).1.differentiableAt
  have hder (s : ℝ) (hs : 0<s) : deriv D s≤0 := by
    have h := smooth_deficit_dissipation p hp hpos he hm hsmooth s hs
    dsimp only at h
    have hnonneg : 0≤-deriv D s := le_trans
      (mul_nonneg (div_nonneg (by norm_num) (sub_nonneg.mpr h.2.1.le))
        (tsum_nonneg (fun n => sq_nonneg _))) h.2.2
    linarith
  have hmD : AntitoneOn D (Ioi (0:ℝ)) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ioi (0:ℝ))
      (fun s hs => (hd s hs).continuousAt.continuousWithinAt)
    · intro s hs
      simp only [interior_Ioi] at hs
      exact (hd s hs).differentiableWithinAt
    · intro s hs
      simp only [interior_Ioi] at hs
      exact hder s hs
  have hlim : Tendsto D atTop (nhds 0) := deficit_tendsto_zero p hp hpos he hm
  refine ⟨hmD,?_,hlim⟩
  intro s hs
  apply le_of_tendsto hlim
  filter_upwards [eventually_ge_atTop s] with t ht
  exact hmD hs (hs.trans_le ht) ht

#print axioms smooth_deficit_control
end BecknerOnofri.HighDim.CirclePoisson
