module

public import BecknerOnofri.EntropyTailDefinitions

@[expose] public section

noncomputable section
open MeasureTheory
namespace BecknerOnofri.HighDim.EntropyTail

/-- The manuscript's actual shifted Mellin integral G(η). -/
def heatIntegral (η : ℝ) : ℝ :=
  (1/120) * ∫ s : ℝ in Set.Ioi η, (s-η)^5 * heatComplement s

end BecknerOnofri.HighDim.EntropyTail
