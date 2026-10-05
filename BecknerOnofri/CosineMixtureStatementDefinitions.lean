import BecknerOnofri.CoordinateMarginalDefinitions

/-! Trusted definitions for the manuscript's unrestricted cosine-power mixtures
and the inverse-power energy of a retained coordinate marginal. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace BecknerOnofri.HighDim

def cosinePowerShape (n : ℕ) (x : UnitAddCircle) : ℝ :=
  Complex.normSq (1 + fourier 1 x)^n / ((2*n).choose n:ℝ)

def countableCosineMixture {d : ℕ} (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ) (x : Torus d) : ℝ :=
  ∑' n, w n * ∏ i, cosinePowerShape (N n i) (x i)

def IsCountableCosineMixture {d : ℕ} (ρ : ProbabilityDensity d) : Prop :=
  ∃ (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ),
    (∀ n, 0 ≤ w n) ∧ HasSum w 1 ∧ ρ.value =ᵐ[torusMeasure d] countableCosineMixture w N

/-- Q_r of a function on the ambient torus. For a coordinate marginal, all
nonzero Fourier coefficients lie in the retained coordinates. -/
def inversePowerEnergy {d : ℕ} (r : ℕ) (f : Torus d → ℝ) : ℝ≥0∞ :=
  ∑' k : NonzeroFrequency d,
    ENNReal.ofReal ((frequencyLength k.val ^ r)⁻¹ * ‖fourierCoeff f k.val‖^2)

end BecknerOnofri.HighDim
