import BecknerOnofri.ContinuousFirstShell
import BecknerOnofri.ComplementImplicit

/-! The genuine normalized Gibbs nonlinearity in the full first-shell and
continuous complement coordinates. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Topology
namespace BecknerOnofri.HighDim.ContinuousComplement
open ContinuousGibbs ContinuousFirstShell

/-- The actual real potential with all complex first-shell coordinates. -/
def reconstruction (d : ℕ) : Coordinates d × complement d →L[ℝ] Space d :=
  (assembly d).comp (ContinuousLinearMap.fst ℝ _ _) +
    (complement d).subtypeL.comp (ContinuousLinearMap.snd ℝ _ _)

@[simp] theorem reconstruction_apply {d : ℕ} (z : Coordinates d) (w : complement d) :
    reconstruction d (z, w) = assembly d z + (w : Space d) := rfl

@[simp] theorem mean_reconstruction {d : ℕ} (x : Coordinates d × complement d) :
    mean d (reconstruction d x) = 0 := by
  change mean d (assembly d x.1 + (x.2 : Space d)) = 0
  have hw : mean d (x.2 : Space d) = 0 := x.2.property.1
  rw [map_add, mean_assembly, hw, add_zero]

@[simp] theorem center_reconstruction {d : ℕ} (x : Coordinates d × complement d) :
    center d (reconstruction d x) = reconstruction d x := by
  ext y
  simp only [center_apply, mean_reconstruction, sub_zero]

/-- The nonlinear part of the actual complement equation after Green preconditioning. -/
def remainder {d : ℕ} (G : Space d →L[ℝ] Space d)
    (x : Coordinates d × complement d) : complement d :=
  complementMap d (G (nonlinearRemainder (reconstruction d x)))

theorem remainder_analytic {d : ℕ} (G : Space d →L[ℝ] Space d)
    (x : Coordinates d × complement d) : AnalyticAt ℝ (remainder G) x := by
  have hi : AnalyticAt ℝ (reconstruction d) x := by
    exact ContinuousLinearMap.analyticAt (𝕜 := ℝ) (E := Coordinates d × complement d)
      (F := Space d) (reconstruction d) x
  have h1 := (nonlinearRemainder_analytic (reconstruction d x)).comp hi
  have ho : AnalyticAt ℝ ((complementMap d).comp G)
      (nonlinearRemainder (reconstruction d x)) :=
    ContinuousLinearMap.analyticAt (𝕜 := ℝ) (E := Space d) (F := complement d) _ _
  convert! ho.comp (f := fun y : Coordinates d × complement d =>
    nonlinearRemainder (reconstruction d y)) h1 using 1

@[simp] theorem remainder_zero {d : ℕ} (G : Space d →L[ℝ] Space d) : remainder G 0 = 0 := by
  simp [remainder]

theorem hasFDerivAt_remainder_zero {d : ℕ} (G : Space d →L[ℝ] Space d) :
    HasFDerivAt (𝕜 := ℝ) (remainder G) 0 (0 : Coordinates d × complement d) := by
  have h0 : HasFDerivAt (𝕜 := ℝ) nonlinearRemainder 0
      (reconstruction d (0 : Coordinates d × complement d)) := by
    simpa only [map_zero] using ContinuousGibbs.hasFDerivAt_remainder_zero d
  have h1 := h0.comp (0 : Coordinates d × complement d) (reconstruction d).hasFDerivAt
  have ho : HasFDerivAt (𝕜 := ℝ) ((complementMap d).comp G)
      ((complementMap d).comp G) (nonlinearRemainder (reconstruction d 0)) :=
    ContinuousLinearMap.hasFDerivAt (𝕜 := ℝ) (E := Space d) (F := complement d) _
  have h3 := HasFDerivAt.comp (𝕜 := ℝ) (G := complement d) (F := Space d) (f := fun y : Coordinates d × complement d =>
    nonlinearRemainder (reconstruction d y)) (0 : Coordinates d × complement d) ho h1
  convert! h3 using 1 <;> simp [remainder]

/-- The actual restriction of the preconditioner to the complement. -/
def linearPart {d : ℕ} (G : Space d →L[ℝ] Space d) : complement d →L[ℝ] complement d :=
  (complementMap d).comp (G.comp (complement d).subtypeL)

def projectedEquation {d : ℕ} (G : Space d →L[ℝ] Space d)
    (x : (ℝ × Coordinates d) × complement d) : complement d :=
  x.2 - x.1.1 • complementMap d (G (normalized (reconstruction d (x.1.2, x.2)) - 1))

theorem projectedEquation_eq {d : ℕ} (G : Space d →L[ℝ] Space d)
    (hG : ∀ z, complementMap d (G (assembly d z)) = 0)
    (x : (ℝ × Coordinates d) × complement d) :
    projectedEquation G x = ComplementImplicit.equation (linearPart G) (remainder G) x := by
  have hr : normalized (reconstruction d (x.1.2, x.2)) - 1 =
      reconstruction d (x.1.2, x.2) + nonlinearRemainder (reconstruction d (x.1.2, x.2)) := by
    rw [nonlinearRemainder, center_reconstruction]
    abel
  unfold projectedEquation
  rw [hr]
  simp only [map_add, reconstruction_apply, hG, zero_add,
    ComplementImplicit.equation, linearPart, ContinuousLinearMap.comp_apply,
    Submodule.subtypeL_apply, remainder]

/-- The implicit map solves the genuine projected Gibbs equation. The inverse
and first-shell compatibility are explicit hypotheses discharged by the actual
Green operator in the application. -/
theorem exists_analytic_solution {d : ℕ} (G : Space d →L[ℝ] Space d)
    (hG : ∀ z, complementMap d (G (assembly d z)) = 0)
    (e : complement d ≃L[ℝ] complement d)
    (he : (e : complement d →L[ℝ] complement d) =
      ContinuousLinearMap.id ℝ (complement d) - linearPart G) :
    ∃ ψ : ℝ × Coordinates d → complement d,
      AnalyticAt ℝ ψ (1, 0) ∧ ψ (1, 0) = 0 ∧
      HasFDerivAt (𝕜 := ℝ) ψ 0 (1, 0) ∧
      (∀ᶠ x in 𝓝 (1, (0 : Coordinates d)), projectedEquation G (x, ψ x) = 0) ∧
      (∀ᶠ x in 𝓝 ((1, (0 : Coordinates d)), (0 : complement d)),
        projectedEquation G x = 0 ↔ ψ x.1 = x.2) := by
  simpa only [projectedEquation_eq G hG] using
    ComplementImplicit.exists_analytic_complement (linearPart G) (remainder G)
      (remainder_analytic G 0) (remainder_zero G) (hasFDerivAt_remainder_zero G) e he

#print axioms exists_analytic_solution
end BecknerOnofri.HighDim.ContinuousComplement
