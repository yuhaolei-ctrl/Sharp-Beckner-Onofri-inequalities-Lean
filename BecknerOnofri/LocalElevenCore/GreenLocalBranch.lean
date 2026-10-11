module

public import BecknerOnofri.LocalElevenContinuousInverse
public import BecknerOnofri.GreenLocalBranch
public import BecknerOnofri.ContinuousComplement
public import BecknerOnofri.LocalElevenContinuousInverse
public import BecknerOnofri.AnalyticAxisBound
public import BecknerOnofri.LocalElevenCore.GreenLocalBranchCore
public import BecknerOnofri.V2.Reaudit.Sobolev.CorrectionFromSobolev

@[expose] public section

/-! An unconditional analytic complement map for the actual torus Gibbs
Euler equation, in all cosine and sine first-shell directions. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Topology
namespace BecknerOnofri.HighDim.LocalEleven.GreenLocalBranch

open BecknerOnofri.HighDim.GreenLocalBranch hiding correction correction_analytic correction_axis correction_base correction_derivative_zero correction_quadratic correction_solves correction_unique exists_analytic_complement green_assembly green_first_complement_zero linearPart_eq zero_axis_of_unique

open ContinuousGibbs ContinuousFirstShell ContinuousComplement

/-- The complete first-shell parameter space is d complex coordinates.  The map is the analytic
graph of the Sobolev implicit-function theorem on `K^⊥ ⊂ H^d` (manuscript Section 5,
`subsec:section5-lyapunov-schmidt`), viewed in the continuous functions; see
`V2.Reaudit.Sobolev.exists_analytic_complement_sobolev`. -/
theorem exists_analytic_complement {d : ℕ} (hd : 11 ≤ d) :
    ∃ ψ : ℝ × Coordinates d → complement d,
      AnalyticAt ℝ ψ (1, 0) ∧ ψ (1, 0) = 0 ∧
      HasFDerivAt (𝕜 := ℝ) ψ 0 (1, 0) ∧
      (∀ᶠ x in 𝓝 (1, (0 : Coordinates d)),
        projectedEquation (greenContinuous d) (x, ψ x) = 0) ∧
      (∀ᶠ x in 𝓝 ((1, (0 : Coordinates d)), (0 : complement d)),
        projectedEquation (greenContinuous d) x = 0 ↔ ψ x.1 = x.2) :=
  BecknerOnofri.V2.Reaudit.Sobolev.exists_analytic_complement_sobolev hd

/-- Local uniqueness forces the complementary correction to vanish on the
uniform branch for every nearby value of the parameter. -/
theorem zero_axis_of_unique {d : ℕ} {ψ : ℝ × Coordinates d → complement d}
    (hunique : ∀ᶠ x in 𝓝 ((1, (0 : Coordinates d)), (0 : complement d)),
      projectedEquation (greenContinuous d) x = 0 ↔ ψ x.1 = x.2) :
    ∀ᶠ μ in 𝓝 (1 : ℝ), ψ (μ, 0) = 0 := by
  have ht : Filter.Tendsto (fun μ : ℝ => ((μ, (0 : Coordinates d)), (0 : complement d)))
      (𝓝 1) (𝓝 ((1, (0 : Coordinates d)), (0 : complement d))) :=
    (continuous_id.prodMk continuous_const |>.prodMk continuous_const).continuousAt
  filter_upwards [ht.eventually hunique] with μ hμ
  apply hμ.mp
  simp [projectedEquation, reconstruction_apply]

/-- The local analytic correction: the Sobolev graph `HsC.toComplement ∘ graph`. -/
def correction {d : ℕ} (hd : 11 ≤ d) : ℝ × Coordinates d → complement d :=
  BecknerOnofri.V2.Reaudit.Sobolev.sobolevCorrection hd

theorem correction_analytic {d : ℕ} (hd : 11 ≤ d) :
    AnalyticAt ℝ (correction hd) (1, 0) :=
  (BecknerOnofri.V2.Reaudit.Sobolev.sobolevCorrection_spec hd).1

@[simp] theorem correction_base {d : ℕ} (hd : 11 ≤ d) : correction hd (1, 0) = 0 :=
  (BecknerOnofri.V2.Reaudit.Sobolev.sobolevCorrection_spec hd).2.1

theorem correction_derivative_zero {d : ℕ} (hd : 11 ≤ d) :
    HasFDerivAt (𝕜 := ℝ) (correction hd) 0 (1, 0) :=
  (BecknerOnofri.V2.Reaudit.Sobolev.sobolevCorrection_spec hd).2.2.1

theorem correction_solves {d : ℕ} (hd : 11 ≤ d) :
    ∀ᶠ x in 𝓝 (1, (0 : Coordinates d)),
      projectedEquation (greenContinuous d) (x, correction hd x) = 0 :=
  (BecknerOnofri.V2.Reaudit.Sobolev.sobolevCorrection_spec hd).2.2.2.1

theorem correction_unique {d : ℕ} (hd : 11 ≤ d) :
    ∀ᶠ x in 𝓝 ((1, (0 : Coordinates d)), (0 : complement d)),
      projectedEquation (greenContinuous d) x = 0 ↔ correction hd x.1 = x.2 :=
  (BecknerOnofri.V2.Reaudit.Sobolev.sobolevCorrection_spec hd).2.2.2.2

theorem correction_axis {d : ℕ} (hd : 11 ≤ d) :
    ∀ᶠ μ in 𝓝 (1 : ℝ), correction hd (μ, 0) = 0 :=
  zero_axis_of_unique (correction_unique hd)

/-- Mixed quadratic estimate for the actual local correction; the pure
parameter-square term is absent because the uniform branch is exact. -/
theorem correction_quadratic {d : ℕ} (hd : 11 ≤ d) :
    correction hd =O[𝓝 (1, (0 : Coordinates d))]
      (fun x => ‖x.2‖^2 + |x.1-1| * ‖x.2‖) := by
  simpa only [Real.norm_eq_abs] using analytic_axis_bound (correction_analytic hd)
    (correction_derivative_zero hd) (correction_axis hd)


#print axioms exists_analytic_complement
#print axioms zero_axis_of_unique
#print axioms correction_quadratic
end BecknerOnofri.HighDim.LocalEleven.GreenLocalBranch
