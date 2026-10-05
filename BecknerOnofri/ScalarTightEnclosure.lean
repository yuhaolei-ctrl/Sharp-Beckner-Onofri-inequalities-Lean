module

public import BecknerOnofri.ScalarRoundedEnclosure

@[expose] public section

namespace BecknerOnofri.HighDim.ScalarCertificate

noncomputable def FunctionEnclosure.tightMin {a b : ℝ} {f g : ℝ → ℝ}
    (ef : FunctionEnclosure a b f) (eg : FunctionEnclosure a b g) :
    FunctionEnclosure a b (fun x => min (f x) (g x)) where
  value := ⟨min ef.value.lower eg.value.lower,min ef.value.upper eg.value.upper⟩
  slope := ef.slope.hull eg.slope
  value_mem := by
    intro x hx
    have hf := ef.value_mem x hx
    have hg := eg.value_mem x hx
    simp only [RationalInterval.Contains,Rat.cast_min]
    exact ⟨min_le_min hf.1 hg.1,min_le_min hf.2 hg.2⟩
  slope_bounds := (ef.pointwiseMin eg).slope_bounds

noncomputable def FunctionEnclosure.tightMax {a b : ℝ} {f g : ℝ → ℝ}
    (ef : FunctionEnclosure a b f) (eg : FunctionEnclosure a b g) :
    FunctionEnclosure a b (fun x => max (f x) (g x)) where
  value := ⟨max ef.value.lower eg.value.lower,max ef.value.upper eg.value.upper⟩
  slope := ef.slope.hull eg.slope
  value_mem := by
    intro x hx
    have hf := ef.value_mem x hx
    have hg := eg.value_mem x hx
    simp only [RationalInterval.Contains,Rat.cast_max]
    exact ⟨max_le_max hf.1 hg.1,max_le_max hf.2 hg.2⟩
  slope_bounds := (ef.pointwiseMax eg).slope_bounds

#print axioms FunctionEnclosure.tightMax
end BecknerOnofri.HighDim.ScalarCertificate
