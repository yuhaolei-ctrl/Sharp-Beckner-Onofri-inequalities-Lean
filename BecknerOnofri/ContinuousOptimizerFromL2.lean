module

public import BecknerOnofri.OptimizerDuality

@[expose] public section

/-! Regularize a specified Hilbert-space optimizer, preserving that exact L2
class and comparison with the full raw critical-Sobolev domain. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
namespace BecknerOnofri.HighDim.ContinuousOptimizers
open ContinuousGibbs ContinuousFirstShell GraphRegularity
open Legacy.BecknerOnofri.TorusSobolev Legacy.BecknerOnofri.SubcriticalAttainment
open Legacy.BecknerOnofri.SubcriticalEuler

lemma continuous_optimizer_of_L2 {d : ℕ} (hd : 0 < d) {β : ℝ} (hβ : 0 < β)
    (U : TorusL2 d) (hU : Admissible U)
    (hmax : ∀ V : TorusL2 d, Admissible V →
      functional (spectralThreshold d/(2*β)) V ≤ functional (spectralThreshold d/(2*β)) U) :
    ∃ u : Space d, toL2 d u = U ∧ InCriticalSobolev u ∧ MeanZero u ∧ SmoothOnTorus u ∧
      (∀ s : ℝ, InSobolev s u) ∧
      (∀ v : Torus d → ℝ, InCriticalSobolev v → dualFunctional β v ≤ dualFunctional β u) := by
  have hσ := spectralThreshold_pos hd
  have hA : 0 < spectralThreshold d/(2*β) := by positivity
  have hC : 0 < Legacy.BecknerOnofri.endpointConstant d := div_pos (Nat.cast_pos.mpr hd) hσ
  have hR := GenericAttainment.rough_bound hd
    (by positivity : 0 < Legacy.BecknerOnofri.endpointConstant d/2)
    (by linarith : Legacy.BecknerOnofri.endpointConstant d/2 < Legacy.BecknerOnofri.endpointConstant d)
  have hs := maximizer_fourier_summable hd hR hA hU hmax
  let u := realRepresentative U hs
  have huL : toL2 d u = U := toL2_realRepresentative U hs hU.1
  have huadm : Admissible (toL2 d u) := by rw [huL]; exact hU
  have hu := inCriticalSobolev_of_toL2 u huadm
  have hm := meanZero_of_toL2 u huadm
  have huradial (m : ℕ) : Radial m u := by
    have hh := maximizer_radialSummable hd hR hA hU hmax m
    simpa only [Radial, Legacy.BecknerOnofri.RadialWiener.RadialSummable, coefficient_apply, huL] using hh
  refine ⟨u,huL,hu,hm,smooth_of_radial u huradial,inSobolev_of_radial u huradial,?_⟩
  intro v hv
  rw [OnsetRaw.dualFunctional_eq_normalized hd β v hv, dualFunctional_eq_toL2 hd β u hu hm, huL]
  have hadm := Legacy.BecknerOnofri.SobolevCentering.center_admissible hd
    (Bridge.potentialLp_real v hv.1) (Bridge.potentialLp_summable hd v hv)
  exact_mod_cast hmax _ hadm

#print axioms continuous_optimizer_of_L2
end BecknerOnofri.HighDim.ContinuousOptimizers
