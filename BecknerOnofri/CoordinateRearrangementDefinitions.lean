module

public import BecknerOnofri.CircleRearrangementDefinitions
public import BecknerOnofri.Definitions

@[expose] public section

/-! Literal fiberwise canonical circle rearrangements and their finite
successive application in the original coordinate order. -/
noncomputable section
open MeasureTheory
namespace BecknerOnofri.HighDim.CoordinateRearrangementStatement

def circleFiber {d : ℕ} (i : Fin d) (f : Torus d → ℝ) (x : Torus d) : Torus 1 → ℝ :=
  fun z => f (Function.update x i (z 0))

def CanonicalStep {d : ℕ} (i : Fin d) (f g : Torus d → ℝ) : Prop :=
  ∀ x, Circle.realRearrange (circleFiber i f x) =ᵐ[torusMeasure 1] circleFiber i g x

inductive CanonicalChain {d : ℕ} : List (Fin d) → (Torus d → ℝ) → (Torus d → ℝ) → Prop
  | nil (f : Torus d → ℝ) : CanonicalChain [] f f
  | cons {i : Fin d} {is : List (Fin d)} {f h g : Torus d → ℝ} :
      CanonicalStep i f h → CanonicalChain is h g → CanonicalChain (i::is) f g

def SuccessiveSteiner {d : ℕ} (f g : Torus d → ℝ) : Prop :=
  CanonicalChain (List.finRange d) f g

/-- The canonical circle rearrangement on almost every coordinate fiber;
this is the natural definition for arbitrary finite-entropy representatives. -/
def AECanonicalStep {d : ℕ} (i : Fin d) (f g : Torus d → ℝ) : Prop :=
  ∀ᵐ x ∂torusMeasure d,
    Circle.realRearrange (circleFiber i f x) =ᵐ[torusMeasure 1] circleFiber i g x

inductive AECanonicalChain {d : ℕ} : List (Fin d) → (Torus d → ℝ) → (Torus d → ℝ) → Prop
  | nil {f g : Torus d → ℝ} : f =ᵐ[torusMeasure d] g → AECanonicalChain [] f g
  | cons {i : Fin d} {is : List (Fin d)} {f h g : Torus d → ℝ} :
      AECanonicalStep i f h → AECanonicalChain is h g → AECanonicalChain (i::is) f g

def AESuccessiveSteiner {d : ℕ} (f g : Torus d → ℝ) : Prop :=
  AECanonicalChain (List.finRange d) f g

end BecknerOnofri.HighDim.CoordinateRearrangementStatement
