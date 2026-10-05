import BecknerOnofri.CircleTailMonotonicity
import BecknerOnofri.CircleGammaMinimum

/-! The analytic reduction of the entire final mean range to the source's
single scalar lower enclosure at t=0.999. That numerical enclosure remains
a separate certificate obligation. -/
noncomputable section
namespace BecknerOnofri.HighDim.CircleScalar

theorem tailBase_le_gamma (t : ℝ) (ht : 0≤t) (ht1 : t<1) : tailBase t≤gamma t := by
  obtain ⟨x,_,he⟩ := (gamma_constrained_minimum t ht ht1).1
  have hb0 := weight_initial_lower 1 ht ht1
  have hc0 := weight_initial_lower 2 ht ht1
  norm_num at hb0 hc0
  have hb : 0≤weight 1 t := by linarith
  have hc : 0≤weight 2 t := by linarith
  have hx : 0≤cost (633/2000) ((27/40)*weight 1 t) ((27/40)*weight 2 t)
      (6-t) (6*besselMoment 2 (parameter t)-besselMoment 3 (parameter t)) (t^2) x := by
    unfold cost
    positivity
  dsimp only at he
  unfold tailBase
  linarith

theorem gamma_final_range_lower (t : ℝ) (ht : (999/1000:ℝ)≤t) (ht1 : t<1) :
    tailBase (999/1000)≤gamma t := by
  have hm := tailBase_mono (show (999/1000:ℝ) ∈ Set.Ico (999/1000) 1 by norm_num)
    (show t ∈ Set.Ico (999/1000) 1 from ⟨ht,ht1⟩) ht
  exact hm.trans (tailBase_le_gamma t (by linarith) ht1)

#print axioms gamma_final_range_lower
end BecknerOnofri.HighDim.CircleScalar
