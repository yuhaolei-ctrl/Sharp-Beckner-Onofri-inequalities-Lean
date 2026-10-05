import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Finset.Sort

/-! Exact definitions from §5.2.5 of the manuscript dated 2026-09-21.
All matrix entries are generated from their binomial formulas. The domain
contains every feasible thirteen-state law, without an optimizer assumption. -/
open scoped BigOperators
namespace BecknerOnofri.HighDim.Spin

abbrev Count := Fin 13
abbrev Order := Fin 12

def referenceQ (j : Count) : ℚ := ((12:ℕ).choose j.val : ℚ)/4096
def meanCoordinateQ (j : Count) : ℚ := (2*(j.val:ℚ)-12)/12

/-- The range of `l` enforces the convention that negative binomial indices
contribute zero; ordinary `Nat.choose` handles the other out-of-range indices. -/
def momentQ (s : Order) (j : Count) : ℚ :=
  (∑ l ∈ Finset.range (s.val+2),
    (-1:ℚ)^l * ((12-j.val).choose l : ℚ) * (j.val.choose (s.val+1-l) : ℚ)) /
      ((12:ℕ).choose (s.val+1) : ℚ)

def weightQ (s : Order) : ℚ :=
  ((12:ℕ).choose (s.val+1) : ℚ)*2^s.val/(s.val+1:ℚ)^6

def interactionQ (i j : Count) : ℚ :=
  ∑ s : Order, weightQ s * momentQ s i * momentQ s j

def quadraticQ (q : Count → ℚ) : ℚ :=
  ∑ i : Count, ∑ j : Count, q i * interactionQ i j * q j

def vertexQ (i j k : Count) (r : Count) : ℚ :=
  if r=i then (meanCoordinateQ k-meanCoordinateQ j)/(2*(meanCoordinateQ k-meanCoordinateQ i))
  else if r=j then -1/2
  else if r=k then (meanCoordinateQ j-meanCoordinateQ i)/(2*(meanCoordinateQ k-meanCoordinateQ i))
  else 0

/-- Sparse evaluation of the quadratic form at the manuscript's three-point vertex. -/
def vertexEnergyQ (i j k : Count) : ℚ :=
  ∑ s : Order, weightQ s *
    (momentQ s i * ((k.val:ℚ)-j.val)/(2*((k.val:ℚ)-i.val)) - momentQ s j/2 +
      momentQ s k * ((j.val:ℚ)-i.val)/(2*((k.val:ℚ)-i.val)))^2

def correctionVQ (j : Count) : ℚ :=
  if j=0 then 1 else if j=1 then -12/11 else if j=12 then 1/11 else 0

def correctionZQ (j : Count) : ℚ :=
  if j=12 then 6/11 else if j=1 then -6/11 else 0

def smallMeanQ : ℚ := 1/16
def smallCoefficientQ (l : Fin 11) : ℚ :=
  ∑ s : Order, if l.val+2 ≤ s.val+1 then
    weightQ s * ((s.val+1).choose (l.val+2):ℚ) *
      smallMeanQ^(2*(s.val+1)-(l.val+2)-2) else 0
def varianceConstantQ : ℚ :=
  4 * ∑ l : Fin 11, smallCoefficientQ l^2/((12:ℕ).choose (l.val+2):ℚ)
def oscillationConstantQ : ℚ :=
  4 * ∑ l : Fin 11, smallCoefficientQ l*(1+smallMeanQ)^(l.val+2)
def smallMarginQ : ℚ :=
  2-(∑ s : Order, if 2 ≤ s.val+1 then weightQ s*smallMeanQ^(2*(s.val+1)-4) else 0)-
    ((5/2)*varianceConstantQ)/(1-5*smallMeanQ^2*oscillationConstantQ)+9/10

noncomputable section
def reference (j : Count) : ℝ := referenceQ j
def meanCoordinate (j : Count) : ℝ := meanCoordinateQ j
def moment (s : Order) (j : Count) : ℝ := momentQ s j
def weight (s : Order) : ℝ := weightQ s
def interaction (i j : Count) : ℝ := interactionQ i j
def quadratic (q : Count → ℝ) : ℝ :=
  ∑ i : Count, ∑ j : Count, q i * interaction i j * q j
def relativeEntropy (p q : Count → ℝ) : ℝ :=
  ∑ j : Count, p j * Real.log (p j/q j)
def functional (p : Count → ℝ) : ℝ := 2*relativeEntropy p reference-quadratic p
def mean (p : Count → ℝ) : ℝ := ∑ j : Count, meanCoordinate j*p j
def Feasible (p : Count → ℝ) : Prop :=
  (∀ j, 0≤p j) ∧ (∑ j : Count,p j)=1 ∧ p 0≤1/4096
def FeasibleAt (t : ℝ) (p : Count → ℝ) : Prop := Feasible p ∧ mean p=t

end
end BecknerOnofri.HighDim.Spin
