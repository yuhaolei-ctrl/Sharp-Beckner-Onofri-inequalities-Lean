module

public import BecknerOnofri.CircleGammaDefinitions
public import BecknerOnofri.CircleScalarCandidates
public import BecknerOnofri.CircleWeightSeries

@[expose] public section

/-! Semantic identification of the four-candidate definition of γ with
exactly the constrained minimum in the manuscript. -/
noncomputable section
open Set
namespace BecknerOnofri.HighDim.CircleScalar

theorem gamma_constrained_minimum (t : ℝ) (ht : 0≤t) (ht1 : t<1) :
    IsLeast ((fun a : ℝ => (33/100)*rate t+(67/100)*t^2-2*Spin.binaryCost t+
      cost (157/500) ((67/100)*weight 1 t) ((67/100)*weight 2 t)
        (6-t) (6*besselMoment 2 (parameter t)-besselMoment 3 (parameter t)) (t^2) a) ''
      Ici (besselMoment 2 (parameter t))) (gamma t) := by
  let m := besselMoment 2 (parameter t)
  let L := 6*m-besselMoment 3 (parameter t)
  have hb := weight_initial_lower 1 ht ht1
  have hc := weight_initial_lower 2 ht ht1
  norm_num at hb hc
  obtain ⟨a,ha,he⟩ := candidateMinimum_attained (157/500) ((67/100)*weight 1 t)
    ((67/100)*weight 2 t) (6-t) L (t^2) m
  constructor
  · refine ⟨a,ha,?_⟩
    unfold gamma
    dsimp [L,m] at he
    simpa only [he]
  · rintro x ⟨a,ha,rfl⟩
    have he := candidateMinimum_le (157/500) ((67/100)*weight 1 t)
      ((67/100)*weight 2 t) (6-t) L (t^2) m a (by norm_num)
      (by linarith) (by linarith) (by linarith) ha
    unfold gamma
    dsimp [L,m] at he
    linarith

#print axioms gamma_constrained_minimum
end BecknerOnofri.HighDim.CircleScalar
