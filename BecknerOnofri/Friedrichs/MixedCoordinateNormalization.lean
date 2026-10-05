module

public import BecknerOnofri.Friedrichs.MixedCoordinateBasis

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace BecknerOnofri.Friedrichs.MixedSpatial
open Legacy.BecknerOnofri

def coordinateFrequency : ℕ → ℕ → ℕ
  | 0,n => match periodicIndex n with | .inl k => k | .inr k => k+1
  | m+1,n => n+(m+1)

def coordinateOdd : ℕ → ℕ → Bool
  | 0,n => match periodicIndex n with | .inl _ => false | .inr _ => true
  | _+1,_ => false

def coordinateScalar : ℕ → ℕ → ℝ
  | 0,n => (Real.sqrt (PeriodicBasis.normSquared (periodicIndex n)))⁻¹
  | m+1,n => (Real.sqrt (JacobiEigenfunctions.normSquared (m+1) n))⁻¹

lemma coordinateScalar_ne_zero (m n : ℕ) : coordinateScalar m n≠0 := by
  cases m with
  | zero => exact inv_ne_zero (ne_of_gt (Real.sqrt_pos.mpr (PeriodicBasis.normSquared_pos _)))
  | succ m => exact inv_ne_zero (ne_of_gt (Real.sqrt_pos.mpr (JacobiEigenfunctions.normSquared_pos _ _)))

lemma coordinateFunction_eq_raw (m n : ℕ) (t : ℝ) :
    coordinateFunction m n t=coordinateScalar m n*
      fullEigenprofile m (coordinateFrequency m n) (coordinateOdd m n) t := by
  cases m with
  | zero =>
    cases hk : periodicIndex n <;>
      simp [coordinateFunction,coordinateScalar,coordinateFrequency,coordinateOdd,hk,
        fullEigenprofile,PeriodicBasis.rawFunction]
  | succ m =>
    simp [coordinateFunction,coordinateScalar,coordinateFrequency,coordinateOdd,fullEigenprofile,
      JacobiEigenfunctions.normalizedFunction,JacobiEigenfunctions.eigenfunction,JacobiEigenfunctions.polynomial]

#print axioms coordinateFunction_eq_raw
end BecknerOnofri.Friedrichs.MixedSpatial
