module

public import BecknerOnofri.V2.Reaudit.Sobolev.Complement
public import BecknerOnofri.ComplementImplicit
public import BecknerOnofri.AnalyticAxisBound
public import Mathlib.Analysis.Calculus.ImplicitContDiff

@[expose] public section

/-! # Stage C(i): the Lyapunov--Schmidt complement graph `w(τ, v)` in `H^s`

Section 5, `subsec:section5-lyapunov-schmidt` (up to `eq:section5-complement-equation`).  Fix
`d ≥ 11` and `s > d/2`.  On the Banach algebra `Hs d s = H^s(𝕋^d)` (Stage A) the complement
equation is
`w - τ P_{K^⊥} T (e^{v+w}/∫e^{v+w} - 1) = 0`, `v = v(z) ∈ K`, `w ∈ K^⊥`,
(`eq:section5-complement-equation` after applying the isomorphism `(2π)^d (-Δ)^{-d/2}`, which is
`T = greenH` here), the linearization at `(1, 0, 0)` is `Id - P_{K^⊥} T` on `K^⊥` which is
invertible with the explicit multiplier of `Complement.lean`, and the analytic implicit-function
theorem (`ComplementImplicit.exists_analytic_complement`, a generic Banach-space statement) gives
the analytic graph `w : 𝒰 → K^⊥` with `w(1,0) = 0`, local uniqueness, `w(τ, 0) = 0`,
`D_v w(τ, 0) = 0` and `w = O(‖z‖²)` in the `H^s` norm. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter Asymptotics
open scoped ENNReal Topology ContDiff

namespace BecknerOnofri.V2.Reaudit.Sobolev
open BecknerOnofri.HighDim ContinuousGibbs ContinuousFirstShell ContinuousComplement

variable {d : ℕ} {s : ℝ} [SobolevIndex d s]

/-! ## The complement equation on `H^s` -/

/-- The complement equation `w - τ P_{K^⊥} T (ρ_{v+w} - 1)` of `eq:section5-complement-equation`
(after applying `(2π)^d (-Δ)^{-d/2}` to its two sides, i.e. in `H^s_0`). -/
def complementEq (d : ℕ) (s : ℝ) [SobolevIndex d s] (τ : ℝ) (z : Coordinates d) (w : HsC d s) :
    HsC d s :=
  w - τ • Hs.complMap d s (Hs.greenH d s (Hs.gibbs (Hs.reconstructionH d s (z, w)) - 1))

/-- The nonlinear part of the complement equation. -/
def HsC.remainder (d : ℕ) (s : ℝ) [SobolevIndex d s] (x : Coordinates d × HsC d s) : HsC d s :=
  Hs.complMap d s (Hs.greenH d s (Hs.gibbsRemainder (Hs.reconstructionH d s x)))

theorem HsC.remainder_analytic (x : Coordinates d × HsC d s) :
    AnalyticAt ℝ (HsC.remainder d s) x := by
  have hi : AnalyticAt ℝ (Hs.reconstructionH d s) x := (Hs.reconstructionH d s).analyticAt x
  have h1 := (Hs.gibbsRemainder_analytic (Hs.reconstructionH d s x)).comp hi
  have ho : AnalyticAt ℝ ((Hs.complMap d s).comp (Hs.greenH d s))
      (Hs.gibbsRemainder (Hs.reconstructionH d s x)) :=
    ContinuousLinearMap.analyticAt _ _
  exact AnalyticAt.comp (g := ⇑((Hs.complMap d s).comp (Hs.greenH d s)))
    (f := Hs.gibbsRemainder ∘ Hs.reconstructionH d s) ho h1

@[simp] theorem HsC.remainder_zero : HsC.remainder d s 0 = 0 := by
  simp [HsC.remainder]

theorem HsC.hasFDerivAt_remainder_zero :
    HasFDerivAt (𝕜 := ℝ) (HsC.remainder d s) 0 (0 : Coordinates d × HsC d s) := by
  have h0 : HasFDerivAt (𝕜 := ℝ) (Hs.gibbsRemainder : Hs d s → Hs d s) 0
      (Hs.reconstructionH d s (0 : Coordinates d × HsC d s)) := by
    simpa only [map_zero] using Hs.hasFDerivAt_gibbsRemainder_zero (d := d) (s := s)
  have h1 := h0.comp (0 : Coordinates d × HsC d s) (Hs.reconstructionH d s).hasFDerivAt
  have ho : HasFDerivAt (𝕜 := ℝ) ((Hs.complMap d s).comp (Hs.greenH d s))
      ((Hs.complMap d s).comp (Hs.greenH d s))
      (Hs.gibbsRemainder (Hs.reconstructionH d s (0 : Coordinates d × HsC d s))) :=
    ContinuousLinearMap.hasFDerivAt _
  have h3 := HasFDerivAt.comp (𝕜 := ℝ) (0 : Coordinates d × HsC d s) ho h1
  convert! h3 using 1; simp

/-- The complement equation has the form `w - τ (T_c w + R(z, w))` used by the abstract
implicit-function lemma. -/
theorem complementEq_eq (τ : ℝ) (z : Coordinates d) (w : HsC d s) :
    complementEq d s τ z w =
      ComplementImplicit.equation (HsC.linearPart d s) (HsC.remainder d s) ((τ, z), w) := by
  have hr : Hs.gibbs (Hs.reconstructionH d s (z, w)) - 1 =
      Hs.reconstructionH d s (z, w) + Hs.gibbsRemainder (Hs.reconstructionH d s (z, w)) := by
    rw [Hs.gibbsRemainder, Hs.center_reconstructionH]
    abel
  unfold complementEq ComplementImplicit.equation
  rw [hr]
  simp only [map_add, Hs.reconstructionH_apply, Hs.complMap_greenH_assemblyH, zero_add,
    HsC.linearPart, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, HsC.remainder]

/-! ## The graph -/

/-- **Existence of the analytic complement graph in `H^s`** (analytic implicit-function theorem on
the Banach space `K^⊥ ⊂ H^s`): an analytic `w : ℝ × ℂ^d → K^⊥` near `(1, 0)`,
`w(1, 0) = 0`, with `Dw(1, 0) = 0`, solving the complement equation, and locally unique. -/
theorem exists_graph (hd11 : 11 ≤ d) :
    ∃ ψ : ℝ × Coordinates d → HsC d s,
      AnalyticAt ℝ ψ (1, 0) ∧ ψ (1, 0) = 0 ∧ HasFDerivAt (𝕜 := ℝ) ψ 0 (1, 0) ∧
      (∀ᶠ x in 𝓝 (1, (0 : Coordinates d)), complementEq d s x.1 x.2 (ψ x) = 0) ∧
      (∀ᶠ x in 𝓝 ((1, (0 : Coordinates d)), (0 : HsC d s)),
        complementEq d s x.1.1 x.1.2 x.2 = 0 ↔ ψ x.1 = x.2) := by
  have h := ComplementImplicit.exists_analytic_complement (HsC.linearPart d s) (HsC.remainder d s)
    (HsC.remainder_analytic 0) HsC.remainder_zero HsC.hasFDerivAt_remainder_zero
    (HsC.equiv hd11 (μ := 1) (by norm_num) (by norm_num))
    (by ext w : 1; simp)
  simpa only [complementEq_eq] using h

/-- The (fixed) analytic complement graph `w(τ, z)` in `H^s`. -/
def graph (hd11 : 11 ≤ d) : ℝ × Coordinates d → HsC d s := (exists_graph (s := s) hd11).choose

theorem graph_analytic (hd11 : 11 ≤ d) : AnalyticAt ℝ (graph (s := s) hd11) (1, 0) :=
  (exists_graph (s := s) hd11).choose_spec.1

@[simp] theorem graph_base (hd11 : 11 ≤ d) : graph (s := s) hd11 (1, 0) = 0 :=
  (exists_graph (s := s) hd11).choose_spec.2.1

theorem graph_derivative_zero (hd11 : 11 ≤ d) :
    HasFDerivAt (𝕜 := ℝ) (graph (s := s) hd11) 0 (1, 0) :=
  (exists_graph (s := s) hd11).choose_spec.2.2.1

theorem graph_solves (hd11 : 11 ≤ d) :
    ∀ᶠ x in 𝓝 (1, (0 : Coordinates d)), complementEq d s x.1 x.2 (graph hd11 x) = 0 :=
  (exists_graph (s := s) hd11).choose_spec.2.2.2.1

theorem graph_unique (hd11 : 11 ≤ d) :
    ∀ᶠ x in 𝓝 ((1, (0 : Coordinates d)), (0 : HsC d s)),
      complementEq d s x.1.1 x.1.2 x.2 = 0 ↔ graph hd11 x.1 = x.2 :=
  (exists_graph (s := s) hd11).choose_spec.2.2.2.2

/-- On the uniform axis `z = 0` the complement equation is solved by `w = 0`, so by local uniqueness
`w(τ, 0) = 0` for `τ` near `1`. -/
theorem graph_axis (hd11 : 11 ≤ d) : ∀ᶠ τ in 𝓝 (1 : ℝ), graph (s := s) hd11 (τ, 0) = 0 := by
  have ht : Tendsto (fun τ : ℝ => ((τ, (0 : Coordinates d)), (0 : HsC d s)))
      (𝓝 1) (𝓝 ((1, (0 : Coordinates d)), (0 : HsC d s))) :=
    (continuous_id.prodMk continuous_const |>.prodMk continuous_const).continuousAt
  filter_upwards [ht.eventually (graph_unique (s := s) hd11)] with τ hτ
  apply hτ.mp
  simp [complementEq]

end BecknerOnofri.V2.Reaudit.Sobolev
