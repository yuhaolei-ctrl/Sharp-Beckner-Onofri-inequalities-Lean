module

public import BecknerOnofri.SmoothTorusSobolev
public import BecknerOnofri.AngularRealPowerDomain
public import Legacy.BecknerOnofri.SmoothFourier

@[expose] public section

/-! Positive angular spectral powers of raw smooth torus functions.
This discharges the rapid-decay premise in the spectral intertwining theorem.
It does not identify the tensor operator with a Friedrichs form closure. -/
noncomputable section
namespace BecknerOnofri.SmoothTorus
open HighDim
open Legacy.BecknerOnofri.RadialWiener

theorem smooth_positive_power_moments {d : ℕ} {u : Torus d → ℝ}
    (hu : SmoothOnTorus u) (t : ℝ) (ht : 0 ≤ t) (m : ℕ) :
    RadialSummable (fun k => ((frequencyLength k ^ t : ℝ) : ℂ) * fourierCoeff u k) m :=
  AngularRealPower.real_power_radialSummable t ht _ (smooth_fourier_moments hu) m

def angularPower {d : ℕ} (s : ℝ) (u : Torus d → ℝ) (x : Torus d) : ℝ :=
  (Legacy.TorusEndpoint.absoluteFourierSeries
    (fun k => ((frequencyLength k ^ (2*s) : ℝ) : ℂ) * fourierCoeff u k) x).re

theorem angularPower_smooth {d : ℕ} {u : Torus d → ℝ} (hu : SmoothOnTorus u)
    (s : ℝ) (hs : 0 ≤ s) : SmoothOnTorus (angularPower s u) :=
  Complex.reCLM.contDiff.comp
    (Legacy.BecknerOnofri.SmoothFourier.series_contDiff _
      (smooth_positive_power_moments hu (2*s) (by positivity)))

theorem spectral_intertwining_of_smooth {d : ℕ} {u : Torus d → ℝ}
    (hu : SmoothOnTorus u) (s : ℝ) (hs : 0<s)
    (is : List (Fin d)) (his : is ≠ []) :
    AngularRealPower.PowerGraph
      (Legacy.BecknerOnofri.AngularMixedTerms.countIndex is)
      (Legacy.BecknerOnofri.AngularSpectralIntertwining.countIndex_ne_zero is his) s hs
      (Legacy.BecknerOnofri.AngularMixedL2.vector (fourierCoeff u) is)
      (Legacy.BecknerOnofri.AngularMixedL2.vector
        (fun k => ((frequencyLength k^(2*s):ℝ):ℂ)*fourierCoeff u k) is) :=
  AngularRealPower.positive_intertwining_of_rapid s hs _ (smooth_fourier_moments hu) is his

#print axioms angularPower_smooth
#print axioms spectral_intertwining_of_smooth
end BecknerOnofri.SmoothTorus
