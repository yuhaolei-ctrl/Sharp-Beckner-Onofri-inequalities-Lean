module

public import BecknerOnofri.V2.Reaudit.Obstruction.CircleRearrangementPrinted
public import BecknerOnofri.CircleRearrangementDefinitions

@[expose] public section

/-! # Row S011: the printed circle rearrangement lemma in the form used by Lemma 2.9

`Obstruction.circle_rearrangement_printed` is `lem:circle-rearrangement` for an abstract symmetric
decreasing rearrangement.  The coordinate rearrangement of Section 2 (`V2.Rearrangement`) uses the
canonical layer-cake representative `Circle.realRearrange f` (the a.e.-defined function
`x ↦ ∫₀^∞ 1[2‖x‖ < m{f > t}] dt`).  `circle_rearrangement_aligned` is the printed lemma specialized to this
representative, with the interaction written as `Circle.interaction`:

1. `Circle.realRearrange f` is equimeasurable with `f`;
2. the Riesz inequality `Circle.interaction q f g ≤ Circle.interaction q f* g*`;
3. `f ≤ g` a.e. implies `f* ≤ g*` a.e.;
4. `‖f* - g*‖₁ ≤ ‖f - g‖₁`.

Items 2-4 are `circle_rearrangement_printed` (Riesz inequality by the repository's polarization
argument for the cited theorem of Burchard--Hajaiej, items 3, 4 by the printed layer-cake argument). -/

noncomputable section
open MeasureTheory ProbabilityTheory Legacy.TorusEndpoint

namespace BecknerOnofri.V2.Reaudit.Obstruction
open BecknerOnofri.PolarizationL1 BecknerOnofri.DistributionLimit

/-- The layer-cake representative `Circle.realRearrange f` is a symmetric decreasing rearrangement
of `f` in the printed sense. -/
theorem isSymmDecrRearr_realRearrange {f : Torus 1 → ℝ} (hf : Integrable f (torusMeasure 1))
    (hf0 : ∀ᵐ x ∂torusMeasure 1, 0 ≤ f x) : IsSymmDecrRearr f (Circle.realRearrange f) :=
  have h := layer_toReal_isRearrangementLimit hf hf0
  ⟨h.identDistrib hf, h.radial⟩

theorem circle_rearrangement_aligned (f g : Torus 1 → ℝ)
    (hf : Integrable f (torusMeasure 1)) (hg : Integrable g (torusMeasure 1))
    (hf0 : ∀ᵐ x ∂torusMeasure 1, 0 ≤ f x) (hg0 : ∀ᵐ x ∂torusMeasure 1, 0 ≤ g x)
    (q : UnitAddCircle → ℝ) {C : ℝ} (hq0 : ∀ z, 0 ≤ q z) (hqC : ∀ z, q z ≤ C)
    (hq : ∀ x y, ‖x‖ ≤ ‖y‖ → q y ≤ q x) :
    IdentDistrib (Circle.realRearrange f) f (torusMeasure 1) (torusMeasure 1) ∧
    IdentDistrib (Circle.realRearrange g) g (torusMeasure 1) (torusMeasure 1) ∧
    Circle.interaction q f g ≤
      Circle.interaction q (Circle.realRearrange f) (Circle.realRearrange g) ∧
    (f ≤ᵐ[torusMeasure 1] g →
      Circle.realRearrange f ≤ᵐ[torusMeasure 1] Circle.realRearrange g) ∧
    (∫ x, |Circle.realRearrange f x - Circle.realRearrange g x| ∂torusMeasure 1) ≤
      ∫ x, |f x - g x| ∂torusMeasure 1 := by
  have hF := isSymmDecrRearr_realRearrange hf hf0
  have hG := isSymmDecrRearr_realRearrange hg hg0
  obtain ⟨h1, h2, h3⟩ := circle_rearrangement_printed hf hg hf0 hg0 hF hG q hq0 hqC hq
  have e : ∀ u v : Torus 1 → ℝ, Circle.interaction q u v =
      ∫ p : Torus 1 × Torus 1, u p.1 * q (p.1 0 - p.2 0) * v p.2
        ∂(torusMeasure 1).prod (torusMeasure 1) := by
    intro u v
    unfold Circle.interaction
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    ring
  exact ⟨hF.identDistrib, hG.identDistrib, by rw [e, e]; exact h1, h2, h3⟩

#print axioms circle_rearrangement_aligned

end BecknerOnofri.V2.Reaudit.Obstruction
