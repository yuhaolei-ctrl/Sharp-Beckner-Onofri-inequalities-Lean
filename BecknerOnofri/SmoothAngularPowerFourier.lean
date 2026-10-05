import BecknerOnofri.RealComplementOperator
import BecknerOnofri.SmoothAngularPower

/-! The real smooth angular-power representative has exactly the prescribed
Fourier multiplier. Taking its real part loses no component. -/
noncomputable section
open scoped ComplexConjugate
namespace BecknerOnofri.SmoothTorus
open HighDim

theorem angularPowerSeries_conj {d : ℕ} (u : Torus d → ℝ) (s : ℝ) (x : Torus d) :
    conj (Legacy.TorusEndpoint.absoluteFourierSeries
      (fun k => ((frequencyLength k^(2*s):ℝ):ℂ)*fourierCoeff u k) x) =
      Legacy.TorusEndpoint.absoluteFourierSeries
        (fun k => ((frequencyLength k^(2*s):ℝ):ℂ)*fourierCoeff u k) x := by
  unfold Legacy.TorusEndpoint.absoluteFourierSeries
  rw [Complex.conj_tsum]
  calc
    _ = ∑' k : Frequency d, ((frequencyLength (-k)^(2*s):ℝ):ℂ)*
        fourierCoeff u (-k)*UnitAddTorus.mFourier (-k) x := by
      apply tsum_congr
      intro k
      simp only [frequencyLength_neg,fourierCoeff_conjugate u k,UnitAddTorus.mFourier_neg,
        map_mul,Complex.conj_ofReal]
    _ = _ := (Equiv.neg (Frequency d)).tsum_eq
      (fun k => ((frequencyLength k^(2*s):ℝ):ℂ)*fourierCoeff u k*UnitAddTorus.mFourier k x)

theorem angularPower_cast {d : ℕ} (u : Torus d → ℝ) (s : ℝ) (x : Torus d) :
    (angularPower s u x : ℂ) = Legacy.TorusEndpoint.absoluteFourierSeries
      (fun k => ((frequencyLength k^(2*s):ℝ):ℂ)*fourierCoeff u k) x := by
  apply Complex.ext
  · rfl
  · have h := congrArg Complex.im (angularPowerSeries_conj u s x)
    simp only [Complex.conj_im] at h
    change 0 = _
    linarith

theorem angularPower_fourier {d : ℕ} {u : Torus d → ℝ} (hu : SmoothOnTorus u)
    (s : ℝ) (hs : 0 ≤ s) (k : Frequency d) :
    fourierCoeff (angularPower s u) k =
      ((frequencyLength k^(2*s):ℝ):ℂ)*fourierCoeff u k := by
  unfold HighDim.fourierCoeff
  simp_rw [angularPower_cast]
  change UnitAddTorus.mFourierCoeff
    (Legacy.TorusEndpoint.absoluteFourierSeries
      (fun k => ((frequencyLength k^(2*s):ℝ):ℂ)*HighDim.fourierCoeff u k)) k = _
  apply Legacy.TorusEndpoint.absoluteFourierSeries_coefficient
  exact (Legacy.BecknerOnofri.RadialWiener.radialSummable_zero _).mp
    (smooth_positive_power_moments hu (2*s) (by positivity) 0)

#print axioms angularPower_fourier
end BecknerOnofri.SmoothTorus
