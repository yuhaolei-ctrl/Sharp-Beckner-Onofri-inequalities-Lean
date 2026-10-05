module

public import BecknerOnofri.ReflectionSymmetry
public import BecknerOnofri.ReducedAxisDerivative

@[expose] public section

/-! The full complex first-shell equation really restricts to one real
equation on the symmetric diagonal, by actual torus symmetries. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter
open scoped Topology ComplexConjugate
namespace BecknerOnofri.HighDim.RealDiagonalReduction
open ContinuousGibbs ContinuousFirstShell ContinuousSymmetry GreenLocalBranch ReducedEquation
open ReducedCubicExpansion

def firstIndex {d : ℕ} (hd : 12 ≤ d) : Fin d := ⟨0,by omega⟩

def diagonalEmbedding (d : ℕ) : ℝ × ℝ →L[ℝ] ℝ × Coordinates d :=
  (ContinuousLinearMap.id ℝ ℝ).prodMap (realDiagonal d)

@[simp] theorem diagonalEmbedding_apply (d : ℕ) (x : ℝ × ℝ) :
    diagonalEmbedding d x = (x.1,realDiagonal d x.2) := rfl

theorem diagonalEmbedding_tendsto (d : ℕ) :
    Tendsto (diagonalEmbedding d) (𝓝 (1,0)) (𝓝 (1,(0 : Coordinates d))) := by
  simpa only [diagonalEmbedding_apply, map_zero] using
    (diagonalEmbedding d).continuous.continuousAt.tendsto (x := ((1,0) : ℝ × ℝ))

@[simp] theorem permutation_realDiagonal {d : ℕ} (σ : Equiv.Perm (Fin d)) (t : ℝ) :
    permuteCoordinates σ (realDiagonal d t) = realDiagonal d t := rfl

@[simp] theorem conjugate_realDiagonal (d : ℕ) (t : ℝ) :
    conjugateCoordinates (realDiagonal d t) = realDiagonal d t := by
  ext i
  simp only [conjugateCoordinates_apply, realDiagonal_apply, Complex.conj_ofReal]

/-- The actual real scalar equation, taken from the full actual reduced map. -/
def diagonalResidual {d : ℕ} (hd : 12 ≤ d) (x : ℝ × ℝ) : ℝ :=
  (reduced hd (x.1,realDiagonal d x.2) (firstIndex hd)).re

theorem diagonalResidual_analytic {d : ℕ} (hd : 12 ≤ d) :
    AnalyticAt ℝ (diagonalResidual hd) (1,0) := by
  have he := (diagonalEmbedding d).analyticAt ((1,0) : ℝ × ℝ)
  have ho : AnalyticAt ℝ (reduced hd) (diagonalEmbedding d (1,0)) := by
    simpa only [diagonalEmbedding_apply, map_zero] using reduced_analytic hd
  have hr := ho.comp he
  let ev : Coordinates d →L[ℝ] ℝ := Complex.reCLM.comp (ContinuousLinearMap.proj (firstIndex hd))
  have hh := (ev.analyticAt (reduced hd (diagonalEmbedding d (1,0)))).comp
    (f := fun x : ℝ × ℝ => reduced hd (diagonalEmbedding d x))
    (x := ((1,0) : ℝ × ℝ)) (by convert! hr using 1)
  convert! hh using 1

/-- All entries on the real symmetric diagonal are the same real number.
The reality follows from spatial inversion, not a restriction on solutions. -/
theorem reduced_realDiagonal {d : ℕ} (hd : 12 ≤ d) :
    ∀ᶠ x : ℝ × ℝ in 𝓝 (1,0),
      reduced hd (x.1,realDiagonal d x.2) = realDiagonal d (diagonalResidual hd x) := by
  filter_upwards [(diagonalEmbedding_tendsto d).eventually (reduced_permutation hd),
    (diagonalEmbedding_tendsto d).eventually (reduced_reflection hd)] with x hp hr
  simp only [diagonalEmbedding_apply, conjugate_realDiagonal] at hr
  ext i
  have hc : reduced hd (x.1,realDiagonal d x.2) i =
      reduced hd (x.1,realDiagonal d x.2) (firstIndex hd) := by
    have hh := hp (Equiv.swap i (firstIndex hd))
    simp only [diagonalEmbedding_apply, permutation_realDiagonal] at hh
    simpa only [permuteCoordinates, Equiv.swap_apply_left] using congrFun hh i
  have him : (reduced hd (x.1,realDiagonal d x.2) i).im = 0 := by
    have hh := congrArg Complex.im (congrFun hr i)
    simp only [conjugateCoordinates_apply, Complex.conj_im] at hh
    linarith
  apply Complex.ext
  · change (reduced hd (x.1,realDiagonal d x.2) i).re =
      (reduced hd (x.1,realDiagonal d x.2) (firstIndex hd)).re
    exact congrArg Complex.re hc
  · simpa only [realDiagonal_apply, Complex.ofReal_im] using him

theorem reduced_realDiagonal_zero_iff {d : ℕ} (hd : 12 ≤ d) :
    ∀ᶠ x : ℝ × ℝ in 𝓝 (1,0),
      reduced hd (x.1,realDiagonal d x.2) = 0 ↔ diagonalResidual hd x = 0 := by
  filter_upwards [reduced_realDiagonal hd] with x hx
  rw [hx]
  constructor
  · intro hh
    have hi := congrFun hh (firstIndex hd)
    simpa only [realDiagonal_apply, Pi.zero_apply, Complex.ofReal_eq_zero] using hi
  · intro hh
    rw [hh, map_zero]

theorem diagonalResidual_axis {d : ℕ} (hd : 12 ≤ d) :
    ∀ᶠ μ in 𝓝 (1:ℝ), diagonalResidual hd (μ,0) = 0 := by
  filter_upwards [potential_axis hd] with μ hμ
  simp only [diagonalResidual, map_zero, reduced, hμ, normalized_zero,
    coordinates_one, smul_zero, sub_zero, Pi.zero_apply, Complex.zero_re]

theorem diagonalResidual_derivative_axis {d : ℕ} (hd : 12 ≤ d) :
    ∀ᶠ μ in 𝓝 (1:ℝ), HasDerivAt (fun t => diagonalResidual hd (μ,t)) (1-μ) 0 :=
  reduced_diagonal_derivative_axis hd (firstIndex hd)

theorem diagonalResidual_odd {d : ℕ} (hd : 12 ≤ d) :
    ∀ᶠ x : ℝ × ℝ in 𝓝 (1,0), diagonalResidual hd (x.1,-x.2) = -diagonalResidual hd x := by
  filter_upwards [(diagonalEmbedding_tendsto d).eventually (reduced_neg hd)] with x hx
  have hh := congrArg (fun z : Coordinates d => (z (firstIndex hd)).re) hx
  simpa only [diagonalEmbedding_apply, diagonalResidual, map_neg, Pi.neg_apply,
    Complex.neg_re] using hh

theorem diagonalResidual_cubic {d : ℕ} (hd : 12 ≤ d) :
    (fun t : ℝ => diagonalResidual hd (1,t) - kappa d*t^3)
      =O[𝓝 0] (fun t : ℝ => ‖t‖^5) :=
  reduced_diagonal_cubic_expansion_fifth hd (firstIndex hd)

#print axioms diagonalResidual_analytic
#print axioms reduced_realDiagonal
#print axioms reduced_realDiagonal_zero_iff
end BecknerOnofri.HighDim.RealDiagonalReduction
