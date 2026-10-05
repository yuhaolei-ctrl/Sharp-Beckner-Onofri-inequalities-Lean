module

public import Mathlib.Analysis.Calculus.ImplicitContDiff
public import Mathlib.Analysis.Analytic.Constructions

@[expose] public section

/-! Analytic complement equation with an actual invertible linear part.
This lemma constructs the local implicit map; applying it to the torus still
requires the concrete projection and Green inverse constructed separately. -/
noncomputable section
open scoped Topology ContDiff
namespace BecknerOnofri.ComplementImplicit

variable {K W : Type*} [NormedAddCommGroup K] [NormedSpace ℝ K] [CompleteSpace K]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]

def equation (T : W →L[ℝ] W) (R : K × W → W) (x : (ℝ × K) × W) : W :=
  x.2 - x.1.1 • (T x.2 + R (x.1.2, x.2))

theorem exists_analytic_complement (T : W →L[ℝ] W) (R : K × W → W)
    (hR : AnalyticAt ℝ R 0) (hR0 : R 0 = 0)
    (hR' : HasFDerivAt (𝕜 := ℝ) R 0 0)
    (e : W ≃L[ℝ] W) (he : (e : W →L[ℝ] W) = ContinuousLinearMap.id ℝ W - T) :
    ∃ ψ : ℝ × K → W, AnalyticAt ℝ ψ (1, 0) ∧ ψ (1, 0) = 0 ∧
      HasFDerivAt (𝕜 := ℝ) ψ 0 (1, 0) ∧
      (∀ᶠ x in 𝓝 (1, (0 : K)), equation T R (x, ψ x) = 0) ∧
      (∀ᶠ x in 𝓝 ((1, (0 : K)), (0 : W)), equation T R x = 0 ↔ ψ x.1 = x.2) := by
  let μP : ((ℝ × K) × W) →L[ℝ] ℝ :=
    (ContinuousLinearMap.fst ℝ ℝ K).comp (ContinuousLinearMap.fst ℝ (ℝ × K) W)
  let vP : ((ℝ × K) × W) →L[ℝ] K :=
    (ContinuousLinearMap.snd ℝ ℝ K).comp (ContinuousLinearMap.fst ℝ (ℝ × K) W)
  let wP : ((ℝ × K) × W) →L[ℝ] W := ContinuousLinearMap.snd ℝ (ℝ × K) W
  let vw : ((ℝ × K) × W) →L[ℝ] K × W := vP.prod wP
  let x₀ : (ℝ × K) × W := ((1, 0), 0)
  have hx : vw x₀ = 0 := rfl
  have hR00 : R ((0 : K), (0 : W)) = 0 := hR0
  have hf0 : equation T R x₀ = 0 := by
    change (0 : W) - 1 • (T 0 + R 0) = 0
    simp [hR0]
  have hRa : AnalyticAt ℝ (fun x => R (vw x)) x₀ := by
    have hr : AnalyticAt ℝ R (vw x₀) := hR
    exact hr.comp (vw.analyticAt x₀)
  have hfa : AnalyticAt ℝ (equation T R) x₀ :=
    (wP.analyticAt x₀).sub ((μP.analyticAt x₀).smul (((T.comp wP).analyticAt x₀).add hRa))
  have hRd : HasFDerivAt (fun x => R (vw x)) (0 : ((ℝ × K) × W) →L[ℝ] W) x₀ := by
    have h := hR'.comp x₀ vw.hasFDerivAt
    convert! h using 1 <;> simp
  have hTd := (T.comp wP).hasFDerivAt (x := x₀)
  have hmul := (μP.hasFDerivAt (x := x₀)).smul (hTd.add hRd)
  have hfd : HasFDerivAt (equation T R) ((e : W →L[ℝ] W).comp wP) x₀ := by
    convert! (wP.hasFDerivAt (x := x₀)).sub hmul using 1
    rw [he]
    apply ContinuousLinearMap.ext
    intro y
    simp [μP, vP, wP, vw, x₀, hR00]
  have hpartial : (fderiv ℝ (equation T R) x₀).comp (ContinuousLinearMap.inr ℝ (ℝ × K) W) =
      (e : W →L[ℝ] W) := by
    rw [hfd.fderiv]
    apply ContinuousLinearMap.ext
    intro y
    simp [wP]
  have hinv : ((fderiv ℝ (equation T R) x₀).comp
      (ContinuousLinearMap.inr ℝ (ℝ × K) W)).IsInvertible := by
    rw [hpartial]
    exact ContinuousLinearMap.isInvertible_equiv
  have hc : ContDiffAt ℝ ω (equation T R) x₀ := hfa.contDiffAt
  have hn : (ω : ℕ∞ω) ≠ 0 := by simp
  let ψ := hc.implicitFunction hn hinv
  refine ⟨ψ, (hc.contDiffAt_implicitFunction hn hinv).analyticAt,
    hc.implicitFunction_apply_self hn hinv, ?_, ?_, ?_⟩
  · have h := (hc.hasStrictFDerivAt_implicitFunction hn hinv).hasFDerivAt
    change HasFDerivAt (𝕜 := ℝ) ψ _ x₀.1 at h
    convert! h using 1
    rw [hfd.fderiv]
    have hz : wP.comp (ContinuousLinearMap.inl ℝ (ℝ × K) W) = 0 := by
      apply ContinuousLinearMap.ext
      intro y
      simp [wP]
    simp only [ContinuousLinearMap.comp_assoc, hz, ContinuousLinearMap.comp_zero,
      ContinuousLinearMap.zero_comp, neg_zero]
  · simpa only [hf0] using hc.eventually_apply_implicitFunction hn hinv
  · simpa only [hf0] using hc.eventually_apply_eq_iff_implicitFunction hn hinv

#print axioms exists_analytic_complement
end BecknerOnofri.ComplementImplicit
