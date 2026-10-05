import BecknerOnofri.LocalElevenCore.SquaredReducedHessian
import BecknerOnofri.LocalElevenCore.ActiveFactorDifferential

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter
open scoped Topology
namespace BecknerOnofri.HighDim.LocalEleven.SquaredReducedEnergy
open AmplitudeLinearization ActiveAmplitudeFactor

/-- The exact row difference of the actual squared-coordinate Hessian on the
equal-active-amplitude locus. The quotient is the analytic one obtained from
the actual reduced Euler equation. -/
theorem hessian_row_difference {d : ℕ} (hd : 11≤d) (I : Finset (Fin d))
    (i j : Fin d) (hi : i∈I) (hj : j∈I) {H : Input d → ℝ}
    (hH : AnalyticAt ℝ H (1,0))
    (he : ∀ᶠ x : Input d in 𝓝 (1,0),
      factor hd i x-factor hd j x=(x.2 i^2-x.2 j^2)*H x) :
    ∀ᶠ x : ℝ × Amplitudes d in 𝓝 (1,0), (∀ k∈I,0<x.2 k) → x.2 i=x.2 j →
      ∀ h : Amplitudes d,
      hessianMap hd I x.1 x.2 h i-hessianMap hd I x.1 x.2 h j =
        -(H (x.1,sqrtLift I x.2)/x.1)*(h i-h j) := by
  have ht : Tendsto (fun x : ℝ × Amplitudes d => (x.1,sqrtLift I x.2))
      (𝓝 (1,0)) (𝓝 (1,0)) := by
    have hc : Continuous (fun x : ℝ × Amplitudes d => (x.1,sqrtLift I x.2)) :=
      continuous_fst.prodMk ((sqrtLift_continuous I).comp continuous_snd)
    simpa only [sqrtLift_zero] using hc.tendsto ((1,0) : ℝ × Amplitudes d)
  have hμ : ∀ᶠ x : ℝ × Amplitudes d in 𝓝 (1,0),x.1≠0 :=
    (continuous_fst : Continuous (fun x : ℝ × Amplitudes d => x.1)).continuousAt.tendsto.eventually
      (eventually_ne_nhds (by norm_num : (1:ℝ)≠0))
  filter_upwards [ht.eventually (differential_squared_difference hd i j hH he),hμ]
    with x hx hμx hr hrEq h
  have hsame : sqrtLift I x.2 i=sqrtLift I x.2 j := by simp only [sqrtLift,if_pos hi,if_pos hj,hrEq]
  have hh := hx hsame (0,sqrtDerivative I x.2 h)
  simp only [hessianMap_apply,if_pos hi,if_pos hj]
  calc
    _ = -(1/x.1)*(fderiv ℝ (factor hd i) (x.1,sqrtLift I x.2) (0,sqrtDerivative I x.2 h)-
      fderiv ℝ (factor hd j) (x.1,sqrtLift I x.2) (0,sqrtDerivative I x.2 h)) := by ring
    _ = -(1/x.1)*(2*Real.sqrt (x.2 i)*
      (h i/(2*Real.sqrt (x.2 i))-h j/(2*Real.sqrt (x.2 i)))*H (x.1,sqrtLift I x.2)) := by
      rw [hh]
      simp only [sqrtLift,if_pos hi,sqrtDerivative_apply,if_pos hj,← hrEq]
    _ = _ := by
      have hs : Real.sqrt (x.2 i)≠0 := (Real.sqrt_pos.mpr (hr i hi)).ne'
      field_simp
      <;> ring

#print axioms hessian_row_difference
end BecknerOnofri.HighDim.LocalEleven.SquaredReducedEnergy
