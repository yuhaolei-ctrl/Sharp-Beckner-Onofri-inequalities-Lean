module

public import BecknerOnofri.ContinuousComplement
public import BecknerOnofri.ContinuousComplementInverse
public import BecknerOnofri.AnalyticAxisBound

@[expose] public section

/-! An unconditional analytic complement map for the actual torus Gibbs
Euler equation, in all cosine and sine first-shell directions. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Topology
namespace BecknerOnofri.HighDim.GreenLocalBranch
open ContinuousGibbs ContinuousFirstShell ContinuousComplement

theorem green_assembly {d : ℕ} (hd : 0 < d) (z : Coordinates d) :
    greenContinuous d (assembly d z) = assembly d z := by
  apply coefficient_ext
  intro k
  rw [coefficient_green hd]
  by_cases hk : InFirstShell k
  · have hs : latticeSquare k = 1 := (latticeSquare_eq_one_iff k).mpr hk
    have h0 : k ≠ 0 := by
      intro he
      have hz := (latticeSquare_eq_zero_iff k).mpr he
      omega
    simp [h0, frequencyLength_pow_eq, hs]
  · have hc : coefficient k (assembly d z) = 0 := by
      rw [← projection_assembly z]
      exact coefficient_projection_off_shell _ k hk
    simp [hc]

theorem green_first_complement_zero {d : ℕ} (hd : 0 < d) (z : Coordinates d) :
    complementMap d (greenContinuous d (assembly d z)) = 0 := by
  rw [green_assembly hd]
  apply Subtype.ext
  change complementProjection d (assembly d z) = 0
  rw [complementProjection_apply, meanProjection_apply, mean_assembly, projection_assembly]
  simp

theorem linearPart_eq {d : ℕ} (hd : 0 < d) :
    linearPart (greenContinuous d) = continuousComplementGreen hd := by
  apply ContinuousLinearMap.ext
  intro w
  apply Subtype.ext
  exact complementProjection_eq_self (greenContinuous_mem_complement hd w)

/-- The complete first-shell parameter space is d complex coordinates; the map
is obtained from the actual analytic Gibbs map and the proved Green inverse. -/
theorem exists_analytic_complement {d : ℕ} (hd : 12 ≤ d) :
    ∃ ψ : ℝ × Coordinates d → complement d,
      AnalyticAt ℝ ψ (1, 0) ∧ ψ (1, 0) = 0 ∧
      HasFDerivAt (𝕜 := ℝ) ψ 0 (1, 0) ∧
      (∀ᶠ x in 𝓝 (1, (0 : Coordinates d)),
        projectedEquation (greenContinuous d) (x, ψ x) = 0) ∧
      (∀ᶠ x in 𝓝 ((1, (0 : Coordinates d)), (0 : complement d)),
        projectedEquation (greenContinuous d) x = 0 ↔ ψ x.1 = x.2) := by
  apply exists_analytic_solution (greenContinuous d) (green_first_complement_zero (by omega))
    (continuousComplementContinuousLinearEquiv hd (by norm_num : (0:ℝ) ≤ 1)
      (by norm_num : (1:ℝ) ≤ 2))
  rw [linearPart_eq (by omega)]
  exact continuousComplementContinuousLinearEquiv_one hd

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

/-- A fixed choice of the local analytic correction supplied by the theorem. -/
def correction {d : ℕ} (hd : 12 ≤ d) : ℝ × Coordinates d → complement d :=
  (exists_analytic_complement hd).choose

theorem correction_analytic {d : ℕ} (hd : 12 ≤ d) :
    AnalyticAt ℝ (correction hd) (1, 0) :=
  (exists_analytic_complement hd).choose_spec.1

@[simp] theorem correction_base {d : ℕ} (hd : 12 ≤ d) : correction hd (1, 0) = 0 :=
  (exists_analytic_complement hd).choose_spec.2.1

theorem correction_derivative_zero {d : ℕ} (hd : 12 ≤ d) :
    HasFDerivAt (𝕜 := ℝ) (correction hd) 0 (1, 0) :=
  (exists_analytic_complement hd).choose_spec.2.2.1

theorem correction_solves {d : ℕ} (hd : 12 ≤ d) :
    ∀ᶠ x in 𝓝 (1, (0 : Coordinates d)),
      projectedEquation (greenContinuous d) (x, correction hd x) = 0 :=
  (exists_analytic_complement hd).choose_spec.2.2.2.1

theorem correction_unique {d : ℕ} (hd : 12 ≤ d) :
    ∀ᶠ x in 𝓝 ((1, (0 : Coordinates d)), (0 : complement d)),
      projectedEquation (greenContinuous d) x = 0 ↔ correction hd x.1 = x.2 :=
  (exists_analytic_complement hd).choose_spec.2.2.2.2

theorem correction_axis {d : ℕ} (hd : 12 ≤ d) :
    ∀ᶠ μ in 𝓝 (1 : ℝ), correction hd (μ, 0) = 0 :=
  zero_axis_of_unique (correction_unique hd)

/-- Mixed quadratic estimate for the actual local correction; the pure
parameter-square term is absent because the uniform branch is exact. -/
theorem correction_quadratic {d : ℕ} (hd : 12 ≤ d) :
    correction hd =O[𝓝 (1, (0 : Coordinates d))]
      (fun x => ‖x.2‖^2 + |x.1-1| * ‖x.2‖) := by
  simpa only [Real.norm_eq_abs] using analytic_axis_bound (correction_analytic hd)
    (correction_derivative_zero hd) (correction_axis hd)


#print axioms exists_analytic_complement
#print axioms zero_axis_of_unique
#print axioms correction_quadratic
end BecknerOnofri.HighDim.GreenLocalBranch
