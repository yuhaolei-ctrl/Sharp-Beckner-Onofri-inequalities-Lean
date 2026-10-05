module

public import BecknerOnofri.CoordinateRearrangementAE

@[expose] public section

noncomputable section
open MeasureTheory
namespace BecknerOnofri.HighDim.CoordinateRearrangementStatement

lemma CanonicalChain.toAE {d : ℕ} {is : List (Fin d)} {f g : Torus d → ℝ}
    (h : CanonicalChain is f g) : AECanonicalChain is f g := by
  induction h with
  | nil => exact .nil Filter.EventuallyEq.rfl
  | cons hs _ ih => exact .cons (Filter.Eventually.of_forall hs) ih

lemma AECanonicalStep.congr_left {d : ℕ} {i : Fin d} {f f' g : Torus d → ℝ}
    (h : AECanonicalStep i f g) (he : f' =ᵐ[torusMeasure d] f) :
    AECanonicalStep i f' g := by
  filter_upwards [h,circleFiber_congr_ae i he] with x hx heq
  rw [realRearrange_congr_ae heq]
  exact hx

lemma AECanonicalChain.congr_left {d : ℕ} {is : List (Fin d)} {f f' g : Torus d → ℝ}
    (h : AECanonicalChain is f g) (he : f' =ᵐ[torusMeasure d] f) :
    AECanonicalChain is f' g := by
  cases h with
  | nil hh => exact .nil (he.trans hh)
  | cons hs ht => exact .cons (hs.congr_left he) ht

#print axioms AECanonicalChain.congr_left
end BecknerOnofri.HighDim.CoordinateRearrangementStatement
