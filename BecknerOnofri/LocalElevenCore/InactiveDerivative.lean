import BecknerOnofri.LocalElevenCore.InactiveFactorSign
import BecknerOnofri.LocalElevenCore.GraphHessian

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter
open scoped Topology
namespace BecknerOnofri.HighDim.LocalEleven.ActiveAmplitudeFactor
open ContinuousFirstShell AmplitudeLinearization RescaledReducedEquation ReducedEquation

/-- Differentiating the analytic coordinate factor at an inactive coordinate.
The derivative here is the actual reduced Jacobian, not the cubic model. -/
theorem inactive_derivative {d : ℕ} (hd : 11≤d) (j : Fin d) :
    ∀ᶠ x : Input d in 𝓝 (1,0),x.2 j=0 →
      (fderiv ℝ (fun z => reduced hd (x.1,z)) (realCoordinates d x.2)
        (realCoordinates d (Pi.single j 1)) j).re=factor hd j x := by
  filter_upwards [(scalar_eq_coordinate_mul_factor hd j).eventually_nhds,
    (factor_analytic hd j).eventually_analyticAt,
    (realEmbedding_tendsto d).eventually (reduced_analytic hd).eventually_analyticAt]
    with x he ha hr hz
  let ev : Coordinates d →L[ℝ] ℝ := Complex.reCLM.comp (ContinuousLinearMap.proj j)
  let ins : Amplitudes d →L[ℝ] Input d := ContinuousLinearMap.inr ℝ ℝ (Amplitudes d)
  have hins : HasFDerivAt (fun z : Amplitudes d => (x.1,z)) ins x.2 := by
    convert! (hasFDerivAt_const x.1 x.2).prodMk (hasFDerivAt_id x.2) using 1
  have hinc : HasFDerivAt (fun z : Coordinates d => (x.1,z))
      (ContinuousLinearMap.inr ℝ ℝ (Coordinates d)) (realCoordinates d x.2) := by
    convert! (hasFDerivAt_const x.1 (realCoordinates d x.2)).prodMk
      (hasFDerivAt_id (realCoordinates d x.2)) using 1
  change AnalyticAt ℝ (reduced hd) (x.1,realCoordinates d x.2) at hr
  have hR : DifferentiableAt ℝ (fun z => reduced hd (x.1,z)) (realCoordinates d x.2) :=
    hr.differentiableAt.comp (realCoordinates d x.2) hinc.differentiableAt
  have hleft : HasFDerivAt (fun z : Amplitudes d => scalar hd j (x.1,z))
      (ev.comp ((fderiv ℝ (fun z => reduced hd (x.1,z)) (realCoordinates d x.2)).comp
        (realCoordinates d))) x.2 := by
    exact ev.hasFDerivAt.comp x.2 (hR.hasFDerivAt.comp x.2 (realCoordinates d).hasFDerivAt)
  have hG : HasFDerivAt (fun z : Amplitudes d => factor hd j (x.1,z))
      ((fderiv ℝ (factor hd j) x).comp ins) x.2 := ha.differentiableAt.hasFDerivAt.comp x.2 hins
  have hright := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) j).hasFDerivAt.mul hG
  have heq : (fun z : Amplitudes d => scalar hd j (x.1,z)) =ᶠ[𝓝 x.2]
      (fun z => z j*factor hd j (x.1,z)) := by
    filter_upwards [hins.continuousAt.tendsto.eventually he] with z hz
    exact hz
  have hu := hleft.unique (hright.congr_of_eventuallyEq heq)
  have h := congrArg (fun L : Amplitudes d →L[ℝ] ℝ => L (Pi.single j 1)) hu
  simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.proj_apply,
    ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul,
    Pi.single_eq_same,hz,zero_mul,add_zero,zero_add,mul_one,ev,Complex.reCLM_apply,Prod.mk.eta] using h

#print axioms inactive_derivative
end BecknerOnofri.HighDim.LocalEleven.ActiveAmplitudeFactor
