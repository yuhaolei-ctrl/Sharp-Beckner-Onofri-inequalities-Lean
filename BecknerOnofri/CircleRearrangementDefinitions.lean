import Legacy.TorusEndpoint.TorusFourier
import Mathlib.Probability.IdentDistrib
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! Transparent mathematical objects used by the trusted circle statement.
There are no existence assumptions or proof certificates in these definitions. -/
noncomputable section
open MeasureTheory Set Legacy.TorusEndpoint
open scoped ENNReal
namespace BecknerOnofri.Circle

/-- The layer-cake rearrangement on a circle of Haar mass one. The centered
arc with radius rank r has Haar measure r. -/
def rearrange (f : Torus 1 → ℝ) (x : Torus 1) : ℝ≥0∞ :=
  ∫⁻ t in Ioi (0 : ℝ),
    if ENNReal.ofReal (2*‖x 0‖)<torusMeasure 1 {y | t<f y} then 1 else 0

/-- Real representative, meaningful almost everywhere for integrable input;
the theorem separately proves finiteness almost everywhere. -/
def realRearrange (f : Torus 1 → ℝ) (x : Torus 1) : ℝ := (rearrange f x).toReal

def interaction (q : UnitAddCircle → ℝ) (f g : Torus 1 → ℝ) : ℝ :=
  ∫ p : Torus 1 × Torus 1,q (p.1 0-p.2 0)*f p.1*g p.2
    ∂(torusMeasure 1).prod (torusMeasure 1)

end BecknerOnofri.Circle
