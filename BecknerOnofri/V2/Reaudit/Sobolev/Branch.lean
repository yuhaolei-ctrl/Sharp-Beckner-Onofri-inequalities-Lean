module

public import BecknerOnofri.V2.Reaudit.Sobolev.Reduction
public import BecknerOnofri.V2.Reaudit.Sobolev.CorrectionFromSobolev
public import BecknerOnofri.LocalElevenCore.SobolevQuadraticTrustedBridge
public import BecknerOnofri.LocalElevenCore.QuarticTrustedBridge
public import BecknerOnofri.LocalElevenCore.ComplexFirstShellMoments

@[expose] public section

/-! # Stages C(ii) and D: the Sobolev graph, its quadratic term and quartic expansion

`lem:section5-quartic-reduction` (S054) for the graph `w(τ, z)` of `Reduction.lean`, which lives
in the Banach algebra `H^s`.

* Stage D (`graph_toComplement`): the `H^s` graph, viewed in `C(𝕋^d)` through the inclusion
  `HsC.toComplement`, coincides near `(1, 0)` with
  `LocalEleven.GreenLocalBranch.correction`.  Since `correction` is now *defined* as the Sobolev
  graph for `s = d` (`CorrectionFromSobolev.lean`), for `s = d` this is a restatement
  (`graph_toComplement_self`); for general `s > d/2` it follows from the uniqueness clause of
  `correction` (`correction_unique`).
* `graph_quadratic` is the native `H^s` statement `D_v w(τ, 0) = 0`, i.e.
  `w = O(‖z‖² + |τ-1| ‖z‖)` in the `H^s` norm.
* `section5_quartic_reduction` assembles the three assertions of the lemma. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter Asymptotics
open scoped ENNReal Topology ContDiff

namespace BecknerOnofri.V2.Reaudit.Sobolev
open BecknerOnofri.HighDim ContinuousGibbs ContinuousFirstShell ContinuousComplement

variable {d : ℕ} {s : ℝ} [SobolevIndex d s]

/-! ## Compatibility with the continuous-function equation

`toComplement_complementEq` (the inclusion `H^s_{K^⊥} → C(𝕋^d)_{K^⊥}` intertwines the `H^s`
complement equation with the continuous projected equation) now lives in
`CorrectionFromSobolev.lean`, below `GreenLocalBranch`. -/

/-! ## Stage D: identification with the continuous-function graph -/

/-- **Identification of the two graphs.**  Near `(1, 0)` the `H^s` complement graph and the
continuous-function complement graph `GreenLocalBranch.correction` coincide (as elements of
`K^⊥ ⊂ C(𝕋^d)`). -/
theorem graph_toComplement (hd11 : 11 ≤ d) :
    ∀ᶠ x in 𝓝 (1, (0 : Coordinates d)),
      HsC.toComplement d s (graph hd11 x) = LocalEleven.GreenLocalBranch.correction hd11 x := by
  have hg : ContinuousAt (graph (s := s) hd11) (1, 0) := (graph_analytic (s := s) hd11).continuousAt
  have hc : ContinuousAt (fun x : ℝ × Coordinates d =>
      (x, HsC.toComplement d s (graph hd11 x))) (1, 0) :=
    continuousAt_id.prodMk ((HsC.toComplement d s).continuous.continuousAt.comp hg)
  have hv : (fun x : ℝ × Coordinates d => (x, HsC.toComplement d s (graph hd11 x))) (1, 0) =
      ((1, (0 : Coordinates d)), (0 : complement d)) := by simp
  have hc' : Tendsto (fun x : ℝ × Coordinates d => (x, HsC.toComplement d s (graph hd11 x)))
      (𝓝 (1, 0)) (𝓝 ((1, (0 : Coordinates d)), (0 : complement d))) := by
    rw [← hv]; exact hc
  filter_upwards [hc'.eventually (LocalEleven.GreenLocalBranch.correction_unique hd11),
    graph_solves (s := s) hd11] with x hu hs
  have h0 : projectedEquation (greenContinuous d)
      (x, HsC.toComplement d s (graph hd11 x)) = 0 := by
    rw [← toComplement_complementEq, hs, map_zero]
  exact (hu.mp h0).symm

/-- For `s = d` the continuous-function graph `GreenLocalBranch.correction` *is* the Sobolev graph
`HsC.toComplement ∘ graph` (definitionally): the identification is a restatement. -/
theorem graph_toComplement_self [SobolevIndex d (d : ℝ)] (hd11 : 11 ≤ d) (x : ℝ × Coordinates d) :
    HsC.toComplement d (d : ℝ) (graph hd11 x) = LocalEleven.GreenLocalBranch.correction hd11 x :=
  rfl

/-- The reconstructed potential is the same function for the two graphs. -/
theorem reconstructionH_graph (hd11 : 11 ≤ d) :
    ∀ᶠ x in 𝓝 (1, (0 : Coordinates d)),
      (Hs.reconstructionH d s (x.2, graph hd11 x)).val =
        LocalEleven.ReducedEquation.potential hd11 x := by
  filter_upwards [graph_toComplement (s := s) hd11] with x hx
  rw [Hs.reconstructionH_val]
  simp only [LocalEleven.ReducedEquation.potential]
  rw [hx]

/-! ## `D_v w (τ, 0) = 0` in the `H^s` norm -/

/-- Differentiating the complement equation at `v = 0` gives `D_v w(τ, 0) = 0`; quantitatively
`w(τ, z) = O(‖z‖² + |τ-1| ‖z‖)` in the (native) `H^s` norm. -/
theorem graph_quadratic (hd11 : 11 ≤ d) :
    graph (s := s) hd11 =O[𝓝 (1, (0 : Coordinates d))]
      (fun x => ‖x.2‖ ^ 2 + |x.1 - 1| * ‖x.2‖) := by
  simpa only [Real.norm_eq_abs] using
    BecknerOnofri.analytic_axis_bound (graph_analytic hd11) (graph_derivative_zero hd11)
      (graph_axis hd11)

theorem HsC.norm_eq (w : HsC d s) : ‖w‖ = ‖(w : Hs d s)‖ := rfl

/-! ## The explicit quadratic term `w_2` -/

/-- `w_2(v)` as an element of `K^⊥ ⊂ H^s`: the manuscript's
`½ ((2π)^{-d}(-Δ)^{d/2} - Id)^{-1} P_{K^⊥}(v²)` (`eq:section5-quadratic-slaving`). -/
def quadraticTermH (hd11 : 11 ≤ d) (z : Coordinates d) : HsC d s :=
  ⟨Hs.mk (LocalEleven.QuadraticSlaving.quadraticCorrection hd11 z).val
    (LocalEleven.QuadraticSlaving.quadraticCorrection_inSobolev hd11 s z), (LocalEleven.QuadraticSlaving.quadraticCorrection hd11 z).property⟩

@[simp] theorem toComplement_quadraticTermH (hd11 : 11 ≤ d) (z : Coordinates d) :
    HsC.toComplement d s (quadraticTermH hd11 z) = LocalEleven.QuadraticSlaving.quadraticCorrection hd11 z :=
  Subtype.ext rfl

/-! ## The statement of `lem:section5-quartic-reduction` -/

open LocalReductionStatement in
/-- **`lem:section5-quartic-reduction`** for a complement graph `ψ : ℝ × ℂ^d → K^⊥ ⊂ H^s`:

1. `∫ v³ = 0`  (`eq:section5-no-cubic-resonance`);
2. the quadratic term of `w(1, v)` has the explicit Fourier coefficients
   `1/(2(|k|^d - 1)) \widehat{v²}(k)` on `K^⊥`-frequencies
   (`eq:section5-quadratic-slaving`), and `w(1, z) - w_2(z) = O(‖z‖³)` in `H^s`
   (`eq:section5-complement-Taylor-expansions`);
3. the reduced functional `Φ_{d,τ}(v + w(τ, v))` equals `δ S + Q_{4,d} + O(S³ + |δ| S²)`,
   `δ = 1 - 1/τ`, `S = Σ |z_j|²` (`eq:section5-reduced-expansion`). -/
def Section5QuarticReduction (d : ℕ) (s : ℝ) [SobolevIndex d s]
    (ψ : ℝ × Coordinates d → HsC d s) : Prop :=
  (∀ z : Coordinates d, mean d ((assembly d z) ^ 3) = 0) ∧
  (∃ q : Coordinates d → HsC d s,
    QuadraticSlavingCoefficients (fun z => HsC.toComplement d s (q z)) ∧
    ((fun z : Coordinates d => ‖ψ (1, z) - q z‖) =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖ ^ 3))) ∧
  ((fun x : ℝ × Coordinates d =>
      (dualFunctional (x.1 * spectralThreshold d) (Hs.reconstructionH d s (x.2, ψ x)).val).toReal -
        (1 - 1 / x.1) * mass x.2 - quartic x.2)
    =O[𝓝 (1, (0 : Coordinates d))] (fun x => mass x.2 ^ 3 + |1 - 1 / x.1| * mass x.2 ^ 2))

open LocalReductionStatement in
/-- **S054, `lem:section5-quartic-reduction`**, for the Sobolev complement graph `graph hd11`
(`d ≥ 11`, `s > d/2`).  Items 2 and 3 are transported from the continuous-function graph through
`graph_toComplement`. -/
theorem section5_quartic_reduction (hd11 : 11 ≤ d) :
    Section5QuarticReduction d s (graph (s := s) hd11) := by
  refine ⟨fun z => LocalEleven.QuadraticModes.assembly_third_moment z, ?_, ?_⟩
  · refine ⟨quadraticTermH hd11, ?_, ?_⟩
    · have : (fun z => HsC.toComplement d s (quadraticTermH (s := s) hd11 z)) =
          LocalEleven.QuadraticSlaving.quadraticCorrection hd11 := funext fun z => toComplement_quadraticTermH hd11 z
      rw [this]
      exact LocalEleven.quadratic_slaving_coefficients hd11
    · have hz : Tendsto (fun z : Coordinates d => ((1 : ℝ), z)) (𝓝 0) (𝓝 (1, 0)) :=
        (continuous_const.prodMk continuous_id).tendsto' _ _ (by simp)
      have h1 := LocalEleven.QuadraticSlaving.correction_quadratic_expansion_all_sobolev hd11 s
      have h2 := h1.const_mul_left (BecknerOnofri.V2.Onset.sobolevAlgConst d s)
      refine h2.congr' ?_ (Eventually.of_forall fun _ => rfl)
      filter_upwards [hz.eventually (graph_toComplement (s := s) hd11)] with z hzz
      have e : HsC.toComplement d s (graph hd11 (1, z) - quadraticTermH hd11 z) =
          LocalEleven.QuadraticSlaving.sliceCorrection hd11 z -
            LocalEleven.QuadraticSlaving.quadraticCorrection hd11 z := by
        rw [map_sub, hzz, toComplement_quadraticTermH]; rfl
      have e' := congrArg (fun w : complement d => (w : Space d)) e
      symm
      rw [HsC.norm_eq, Hs.norm_eq]
      exact congrArg (fun f : Space d => BecknerOnofri.V2.Onset.sobolevAlgConst d s * sobolevNorm s ⇑f) e'
  · have h := LocalEleven.UniformComplementBounds.physicalReducedEnergy_quartic_paper hd11
    refine h.congr' ?_ (Eventually.of_forall fun _ => rfl)
    filter_upwards [reconstructionH_graph (s := s) hd11] with x hx
    rw [hx]
    rfl

end BecknerOnofri.V2.Reaudit.Sobolev
