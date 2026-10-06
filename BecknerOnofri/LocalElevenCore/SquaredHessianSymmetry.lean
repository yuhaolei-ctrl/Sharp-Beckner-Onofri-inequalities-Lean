module

public import BecknerOnofri.LocalElevenCore.SquaredReducedHessian
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter
open scoped Topology BigOperators
namespace BecknerOnofri.HighDim.LocalEleven.SquaredReducedEnergy
open AmplitudeLinearization ActiveAmplitudeFactor RealReducedEnergy

/-- Schwarz symmetry is proved for the actual differentiated energy; it is
not imposed as a property of an approximate matrix. -/
theorem hessian_pairing_symmetric {d : ℕ} (hd : 11≤d) (I : Finset (Fin d)) :
    ∀ᶠ x : ℝ × Amplitudes d in 𝓝 (1,0), (∀ i∈I,0<x.2 i) → ∀ h k : Amplitudes d,
      (∑ i,k i*hessianMap hd I x.1 x.2 h i) =
        (∑ i,h i*hessianMap hd I x.1 x.2 k i) := by
  have ht : Tendsto (fun x : ℝ × Amplitudes d => (x.1,sqrtLift I x.2))
      (𝓝 (1,0)) (𝓝 (1,0)) := by
    have hc : Continuous (fun x : ℝ × Amplitudes d => (x.1,sqrtLift I x.2)) :=
      continuous_fst.prodMk ((sqrtLift_continuous I).comp continuous_snd)
    simpa only [sqrtLift_zero] using hc.tendsto ((1,0) : ℝ × Amplitudes d)
  have ha : ∀ᶠ x : ℝ × Amplitudes d in 𝓝 (1,0),∀ i,AnalyticAt ℝ (factor hd i) x :=
    Filter.eventually_all.mpr (fun i => (factor_analytic hd i).eventually_analyticAt)
  filter_upwards [(hasFDerivAt_value hd I).eventually_nhds,ht.eventually ha] with x hx hax hr h k
  have hp : ∀ᶠ r : Amplitudes d in 𝓝 x.2,∀ i∈I,0<r i := by
    apply Filter.eventually_all.mpr
    intro i
    by_cases hi : i∈I
    · filter_upwards [(continuous_apply i).continuousAt.tendsto.eventually
        (lt_mem_nhds (hr i hi))] with r hr'
      exact fun _ => hr'
    · exact Filter.Eventually.of_forall (fun _ h => False.elim (hi h))
  have hs : Tendsto (fun r : Amplitudes d => (x.1,r)) (𝓝 x.2) (𝓝 x) :=
    (continuous_const.prodMk continuous_id).continuousAt
  have he : ∀ᶠ r in 𝓝 x.2,HasFDerivAt (value hd I x.1) (gradient hd I x.1 r) r := by
    filter_upwards [hs.eventually hx,hp] with r hx' hr'
    exact hx' hr'
  simpa only [ContinuousLinearMap.comp_apply,dotDual_apply] using
    second_derivative_symmetric_of_eventually_of_real he
      (hasFDerivAt_gradient_of_analytic hd I hr hax) h k

/-- In particular the actual active-amplitude matrix is symmetric entrywise. -/
theorem hessian_entries_symmetric {d : ℕ} (hd : 11≤d) (I : Finset (Fin d)) :
    ∀ᶠ x : ℝ × Amplitudes d in 𝓝 (1,0), (∀ i∈I,0<x.2 i) → ∀ i j : Fin d,
      hessianMap hd I x.1 x.2 (Pi.single i 1) j =
        hessianMap hd I x.1 x.2 (Pi.single j 1) i := by
  filter_upwards [hessian_pairing_symmetric hd I] with x hx hr i j
  simpa only [Pi.single_apply,ite_mul,one_mul,zero_mul,Finset.sum_ite_eq,
    Finset.sum_ite_eq',Finset.mem_univ,ite_true] using hx hr (Pi.single i 1) (Pi.single j 1)

#print axioms hessian_entries_symmetric
end BecknerOnofri.HighDim.LocalEleven.SquaredReducedEnergy
