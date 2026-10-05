import BecknerOnofri.EntropyTailDefinitions

/-! Pure definitions of the correlated cosine mixtures in the manuscript.
No Fourier estimate, scalar certificate, or entropy inequality is assumed. -/
noncomputable section
open scoped BigOperators
namespace BecknerOnofri.HighDim.EntropyTail

def cosineTensor (N : Fin 12 → ℕ) (x : Torus 12) : ℝ :=
  ∏ i : Fin 12, Complex.normSq (1+fourier 1 (x i))^(N i)/((2*N i).choose (N i) : ℝ)

def countableCosineMixture (w : ℕ → ℝ) (N : ℕ → Fin 12 → ℕ) (x : Torus 12) : ℝ :=
  ∑' n, w n*cosineTensor (N n) x

end BecknerOnofri.HighDim.EntropyTail
