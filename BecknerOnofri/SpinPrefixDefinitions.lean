import BecknerOnofri.SpinChannelDefinitions

noncomputable section
open scoped BigOperators

namespace BecknerOnofri.HighDim.Spin

/-- Likelihood of the first `k` spins conditional on the full angle vector.
The later entries of `σ` do not occur in this finite product. -/
def prefixLikelihood (k : ℕ) (σ : Configuration) (x : Torus 12) : ℝ :=
  ∏ j ∈ Finset.univ.filter (fun j : Fin 12 => j.val < k),
    if j ∈ σ then (1 + torusCosines x j) / 2 else (1 - torusCosines x j) / 2

end BecknerOnofri.HighDim.Spin
