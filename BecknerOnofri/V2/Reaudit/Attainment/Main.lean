module

public import BecknerOnofri.V2.Reaudit.Attainment.AdamsInput
public import BecknerOnofri.V2.Reaudit.Attainment.Regularity

@[expose] public section

/-! # Subcritical attainment and regularity (`prop:section2-subcritical-attainment`; row S010)

Statement (manuscript): for `0 < β < 2d` and `A = (2 β c_d)⁻¹ > A_crit(d)`, the supremum defining
`C_d(A)` is attained by a mean-zero `u ∈ H^{d/2}`, the supremum defining `P_d(β)` is attained by a
probability density, every extremizing density is smooth and strictly positive, and
`u ∈ C^∞`.  At `β = 2d` the same conclusion holds whenever the endpoint supremum is attained.

Printed proof: direct method for the potential functional (`DirectMethod.lean`), then
`cor:section2-extremizer-correspondence` (`Correspondence.lean`, `Regularity.lean`).

The Adams-type input used by the direct method is the hypothesis `CriticalAdamsAboveThreshold d`
(for each `a > A_crit` a bound `log ∫ e^u ≤ a ‖u‖² + B`).  It follows from the printed critical
Adams inequality `CriticalAdamsInput d` (`criticalAdamsAboveThreshold_of_input`) and is also proved
outright (`criticalAdamsAboveThreshold_unconditional`); the three versions of the theorem below
differ only in how this hypothesis is supplied. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped Topology ENNReal

namespace BecknerOnofri.V2.Reaudit.Attainment
open BecknerOnofri.HighDim BecknerOnofri.V2.Vocab

variable {d : ℕ}

/-- `Gap.coefficient` is an involution on positive reals. -/
theorem coefficient_coefficient (hd : 0 < d) {β : ℝ} (hβ : 0 < β) :
    Gap.coefficient d (Gap.coefficient d β) = β := by
  have hσ := spectralThreshold_pos' hd
  have hc : (0 : ℝ) < (2 * Real.pi) ^ d := pow_pos (by positivity) d
  unfold Gap.coefficient
  field_simp

/-- `A = (2 β c_d)⁻¹ > A_crit(d) = 1/(4 d c_d)` exactly when `β < 2d`. -/
theorem collapseCoefficient_lt_iff (hd : 0 < d) {β : ℝ} (hβ : 0 < β) :
    collapseCoefficient d < Gap.coefficient d β ↔ β < 2 * d := by
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have hc := kernelConstant_pos hd
  rw [gapCoefficient_eq hd hβ, collapseCoefficient_eq hd, one_div]
  rw [inv_lt_inv₀ (by positivity) (by positivity)]
  constructor <;> intro h <;> nlinarith

/-- The three equivalent forms of "attained": the maximizer of `C_d(A)` gives a minimizer of the
free energy and conversely (`cor:section2-extremizer-correspondence` (i), (ii)). -/
theorem exists_maximizer_iff_exists_minimizer (hd : 0 < d) {A : ℝ} (hA : 0 < A) :
    (∃ u, IsCoefficientMaximizer d A u) ↔ ∃ ρ : ProbabilityDensity d,
      IsGlobalMinimizer (Gap.coefficient d A) ρ := by
  constructor
  · rintro ⟨u, hmax⟩
    exact ⟨normalizedGibbsDensity hd u hmax.1 hmax.2.1,
      ((coefficientMaximizer_iff hd hA hmax.1 hmax.2.1).1 hmax).1⟩
  · rintro ⟨ρ, hρ⟩
    exact ⟨_, ((densityMinimizer_iff hd hA ρ hρ.1).1 hρ).1⟩

/-- **Proposition 2.7, existence part** (`prop:section2-subcritical-attainment`), for a given Adams
hypothesis: for `A > A_crit(d)` the supremum `C_d(A)` is attained and finite. -/
theorem exists_coefficient_maximizer' (hd : 0 < d) (hAd : CriticalAdamsAboveThreshold d) {A : ℝ}
    (hA : collapseCoefficient d < A) :
    ∃ u : Torus d → ℝ, IsCoefficientMaximizer d A u ∧
      coefficientDefect d A = ((coefficientValue A u : ℝ) : EReal) := by
  obtain ⟨u, hu, hm, hmax⟩ := exists_coefficient_maximizer hd hAd hA
  have h : IsCoefficientMaximizer d A u := ⟨hu, hm, hmax⟩
  exact ⟨u, h, ((isCoefficientMaximizer_iff hd A u).1 h).2.2⟩

/-- **Proposition 2.7** (`prop:section2-subcritical-attainment`), all assertions, for a given Adams
hypothesis `CriticalAdamsAboveThreshold d`.  Here `0 < β < 2d` and `A = Gap.coefficient d β =
(2 β c_d)⁻¹`.

1. `C_d(A)` is attained by a mean-zero `u ∈ H^{d/2}`;
2. `P_d(β)` is attained: some density is a global minimizer of the free energy `-P`;
3. every global minimizer `ρ` equals almost everywhere a smooth, strictly positive function;
4. every maximizing potential `u` equals almost everywhere a smooth function. -/
theorem subcritical_attainment_of_adams (hd : 0 < d) (hAd : CriticalAdamsAboveThreshold d)
    {β : ℝ} (hβ0 : 0 < β) (hβ : β < 2 * d) :
    (∃ u : Torus d → ℝ, IsCoefficientMaximizer d (Gap.coefficient d β) u) ∧
    (∃ ρ : ProbabilityDensity d, IsGlobalMinimizer β ρ) ∧
    (∀ ρ : ProbabilityDensity d, IsGlobalMinimizer β ρ →
      ∃ q : Torus d → ℝ, ρ.value =ᵐ[torusMeasure d] q ∧ SmoothOnTorus q ∧ ∀ x, 0 < q x) ∧
    (∀ u : Torus d → ℝ, IsCoefficientMaximizer d (Gap.coefficient d β) u →
      ∃ v : Torus d → ℝ, v =ᵐ[torusMeasure d] u ∧ SmoothOnTorus v) := by
  have hA0 : 0 < Gap.coefficient d β := Gap.coefficient_pos hd hβ0
  have hAcrit := (collapseCoefficient_lt_iff hd hβ0).2 hβ
  have hback := coefficient_coefficient hd hβ0
  obtain ⟨u, hu, hm, hmax⟩ := exists_coefficient_maximizer hd hAd hAcrit
  have hmaxA : IsCoefficientMaximizer d (Gap.coefficient d β) u := ⟨hu, hm, hmax⟩
  refine ⟨⟨u, hmaxA⟩, ?_, ?_, ?_⟩
  · obtain ⟨ρ, hρ⟩ := (exists_maximizer_iff_exists_minimizer hd hA0).1 ⟨u, hmaxA⟩
    rw [hback] at hρ
    exact ⟨ρ, hρ⟩
  · intro ρ hρ
    rw [← hback] at hρ
    obtain ⟨v, -, hvs, -, -, hvp, hρv⟩ := densityMinimizer_regularity hd hA0 ρ hρ
    exact ⟨normalizedGibbs v, hρv, normalizedGibbs_smooth hvs, hvp⟩
  · intro u hu
    obtain ⟨v, hvu, hvs, -⟩ := maximizer_regularity hd hA0 hu
    exact ⟨v, hvu, hvs⟩

/-- **Proposition 2.7 under the printed critical Adams inequality** `CriticalAdamsInput d`
(`eq:section2-critical-adams`), the hypothesis named in `V2.Vocab.ExternalInputs`. -/
theorem subcritical_attainment_of_criticalAdamsInput (hd : 0 < d)
    (hAdams : BecknerOnofri.V2.Vocab.CriticalAdamsInput d) {β : ℝ} (hβ0 : 0 < β)
    (hβ : β < 2 * d) :
    (∃ u : Torus d → ℝ, IsCoefficientMaximizer d (Gap.coefficient d β) u) ∧
    (∃ ρ : ProbabilityDensity d, IsGlobalMinimizer β ρ) ∧
    (∀ ρ : ProbabilityDensity d, IsGlobalMinimizer β ρ →
      ∃ q : Torus d → ℝ, ρ.value =ᵐ[torusMeasure d] q ∧ SmoothOnTorus q ∧ ∀ x, 0 < q x) ∧
    (∀ u : Torus d → ℝ, IsCoefficientMaximizer d (Gap.coefficient d β) u →
      ∃ v : Torus d → ℝ, v =ᵐ[torusMeasure d] u ∧ SmoothOnTorus v) :=
  subcritical_attainment_of_adams hd (criticalAdamsAboveThreshold_of_input hd hAdams) hβ0 hβ

/-- **Proposition 2.7, unconditional.**  The Adams-type bound the direct method needs holds for every
coefficient strictly above `A_crit(d)` by the repository's rough exponential bound, so no external
input is required. -/
theorem subcritical_attainment (hd : 0 < d) {β : ℝ} (hβ0 : 0 < β) (hβ : β < 2 * d) :
    (∃ u : Torus d → ℝ, IsCoefficientMaximizer d (Gap.coefficient d β) u) ∧
    (∃ ρ : ProbabilityDensity d, IsGlobalMinimizer β ρ) ∧
    (∀ ρ : ProbabilityDensity d, IsGlobalMinimizer β ρ →
      ∃ q : Torus d → ℝ, ρ.value =ᵐ[torusMeasure d] q ∧ SmoothOnTorus q ∧ ∀ x, 0 < q x) ∧
    (∀ u : Torus d → ℝ, IsCoefficientMaximizer d (Gap.coefficient d β) u →
      ∃ v : Torus d → ℝ, v =ᵐ[torusMeasure d] u ∧ SmoothOnTorus v) :=
  subcritical_attainment_of_adams hd (criticalAdamsAboveThreshold_unconditional hd) hβ0 hβ

/-- **Endpoint clause** of `prop:section2-subcritical-attainment` (and, for every `β > 0`,
the regularity statement of `cor:section2-extremizer-correspondence` (iii)): for any `β > 0`
(in particular `β = 2d`), if either supremum is attained then both are, and every extremizing
density and potential is smooth (and the density strictly positive). -/
theorem attained_extremizers_regular (hd : 0 < d) {β : ℝ} (hβ0 : 0 < β)
    (hatt : (∃ u : Torus d → ℝ, IsCoefficientMaximizer d (Gap.coefficient d β) u) ∨
      ∃ ρ : ProbabilityDensity d, IsGlobalMinimizer β ρ) :
    (∃ u : Torus d → ℝ, IsCoefficientMaximizer d (Gap.coefficient d β) u) ∧
    (∃ ρ : ProbabilityDensity d, IsGlobalMinimizer β ρ) ∧
    (∀ ρ : ProbabilityDensity d, IsGlobalMinimizer β ρ →
      ∃ q : Torus d → ℝ, ρ.value =ᵐ[torusMeasure d] q ∧ SmoothOnTorus q ∧ ∀ x, 0 < q x) ∧
    (∀ u : Torus d → ℝ, IsCoefficientMaximizer d (Gap.coefficient d β) u →
      ∃ v : Torus d → ℝ, v =ᵐ[torusMeasure d] u ∧ SmoothOnTorus v) := by
  have hA0 : 0 < Gap.coefficient d β := Gap.coefficient_pos hd hβ0
  have hback := coefficient_coefficient hd hβ0
  have hiff := exists_maximizer_iff_exists_minimizer hd hA0
  rw [hback] at hiff
  have hboth : (∃ u : Torus d → ℝ, IsCoefficientMaximizer d (Gap.coefficient d β) u) ∧
      ∃ ρ : ProbabilityDensity d, IsGlobalMinimizer β ρ := by
    rcases hatt with h | h
    · exact ⟨h, hiff.1 h⟩
    · exact ⟨hiff.2 h, h⟩
  refine ⟨hboth.1, hboth.2, ?_, ?_⟩
  · intro ρ hρ
    rw [← hback] at hρ
    obtain ⟨v, -, hvs, -, -, hvp, hρv⟩ := densityMinimizer_regularity hd hA0 ρ hρ
    exact ⟨normalizedGibbs v, hρv, normalizedGibbs_smooth hvs, hvp⟩
  · intro u hu
    obtain ⟨v, hvu, hvs, -⟩ := maximizer_regularity hd hA0 hu
    exact ⟨v, hvu, hvs⟩

/-- **Smooth initial minimizer for the coordinate rearrangement** (`lem:coordinate-rearranged-minimizer`,
row S012): for `0 < β < 2d` there is a global minimizer of the free energy that is a smooth,
strictly positive function (a genuine `ProbabilityDensity` whose value is smooth). -/
theorem exists_smooth_positive_minimizer (hd : 0 < d) {β : ℝ} (hβ0 : 0 < β) (hβ : β < 2 * d) :
    ∃ ρ : ProbabilityDensity d, IsGlobalMinimizer β ρ ∧ SmoothOnTorus ρ.value ∧
      ∀ x, 0 < ρ.value x := by
  obtain ⟨-, ⟨ρ0, hρ0⟩, hreg, -⟩ := subcritical_attainment hd hβ0 hβ
  obtain ⟨q, hq, hqs, hqp⟩ := hreg ρ0 hρ0
  let ρ : ProbabilityDensity d :=
    { value := q
      nonneg := Filter.Eventually.of_forall fun x => (hqp x).le
      integrable := ρ0.integrable.congr hq
      mass := by rw [← integral_congr_ae hq]; exact ρ0.mass }
  exact ⟨ρ, (OptimizerDuality.minimizer_congr_ae hq β).1 hρ0, hqs, hqp⟩

end BecknerOnofri.V2.Reaudit.Attainment
