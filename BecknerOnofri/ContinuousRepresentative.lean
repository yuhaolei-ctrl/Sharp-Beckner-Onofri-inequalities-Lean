module

public import BecknerOnofri.OnsetContinuousNorm

@[expose] public section

/-! The real continuous Fourier representative of a Wiener `L²` potential. This is split out of
`ContinuousOptimizers` so that the general Sobolev embedding does not depend on the Euler-equation
regularity modules. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped Topology BigOperators
namespace BecknerOnofri.HighDim.ContinuousOptimizers
open ContinuousGibbs ContinuousFirstShell OnsetContinuous
open Legacy.BecknerOnofri.TorusSobolev
open Legacy.BecknerOnofri.SubcriticalAttainment Legacy.BecknerOnofri.SubcriticalEuler
open Legacy.BecknerOnofri.WienerFourier

/-- The actual real continuous Fourier representative of a Wiener L² potential. -/
def realRepresentative {d : ℕ} (u : TorusL2 d)
    (hs : Summable (fun k => ‖fourierIsometry d u k‖)) : Space d :=
  ⟨fun x => (representative u x).re, Complex.continuous_re.comp (representative_continuous u hs)⟩

theorem realRepresentative_ae {d : ℕ} (u : TorusL2 d)
    (hs : Summable (fun k => ‖fourierIsometry d u k‖)) :
    (realRepresentative u hs : Torus d → ℝ) =ᵐ[torusMeasure d] RawAttainment.realValue u := by
  filter_upwards [representative_ae_eq u hs] with x hx
  exact congrArg Complex.re hx

theorem toL2_realRepresentative {d : ℕ} (u : TorusL2 d)
    (hs : Summable (fun k => ‖fourierIsometry d u k‖)) (hr : RealPotential u) :
    toL2 d (realRepresentative u hs) = u := by
  apply Lp.ext
  filter_upwards [toL2_ae (realRepresentative u hs), realRepresentative_ae u hs, hr] with x hx he hi
  rw [hx, he]
  apply Complex.ext
  · rfl
  · simpa only [Complex.ofReal_im] using hi.symm

end BecknerOnofri.HighDim.ContinuousOptimizers
