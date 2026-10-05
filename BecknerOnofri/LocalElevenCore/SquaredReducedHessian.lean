module

public import BecknerOnofri.LocalElevenCore.SquaredReducedEnergy

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter
open scoped Topology
namespace BecknerOnofri.HighDim.LocalEleven.SquaredReducedEnergy
open AmplitudeLinearization ActiveAmplitudeFactor RealReducedEnergy

def hessianMap {d : ℕ} (hd : 11≤d) (I : Finset (Fin d)) (μ : ℝ) (r : Amplitudes d) :
    Amplitudes d →L[ℝ] Amplitudes d :=
  ContinuousLinearMap.pi (fun i => if i∈I then
    (-(1/μ)) • (fderiv ℝ (factor hd i) (μ,sqrtLift I r)).comp
      ((0 : Amplitudes d →L[ℝ] ℝ).prod (sqrtDerivative I r)) else 0)

@[simp] theorem hessianMap_apply {d : ℕ} (hd : 11≤d) (I : Finset (Fin d))
    (μ : ℝ) (r h : Amplitudes d) (i : Fin d) :
    hessianMap hd I μ r h i=if i∈I then
      -(1/μ)*fderiv ℝ (factor hd i) (μ,sqrtLift I r) (0,sqrtDerivative I r h) else 0 := by
  simp only [hessianMap,ContinuousLinearMap.pi_apply]
  split_ifs <;> rfl

lemma hasFDerivAt_gradient_of_analytic {d : ℕ} (hd : 11≤d) (I : Finset (Fin d))
    {μ : ℝ} {r : Amplitudes d} (hr : ∀ i∈I,0<r i)
    (ha : ∀ i, AnalyticAt ℝ (factor hd i) (μ,sqrtLift I r)) :
    HasFDerivAt (gradient hd I μ) ((dotDual d).comp (hessianMap hd I μ r)) r := by
  have hin := (hasFDerivAt_const μ r).prodMk (hasFDerivAt_sqrtLift I hr)
  have hv : HasFDerivAt
      (fun r : Amplitudes d => fun i => if i∈I then -(1/μ)*factor hd i (μ,sqrtLift I r) else 0)
      (hessianMap hd I μ r) r := by
    apply hasFDerivAt_pi.mpr
    intro i
    by_cases hi : i∈I
    · simpa only [hessianMap,if_pos hi,Function.comp_def] using
        (((ha i).differentiableAt.hasFDerivAt.comp r hin).const_mul (-(1/μ)))
    · simpa only [hessianMap,if_neg hi] using (hasFDerivAt_const (0:ℝ) r)
  exact (dotDual d).hasFDerivAt.comp r hv

/-- Identification with the second Frechet derivative of the actual reduced
energy, on every sufficiently small positive active orthant. -/
theorem second_fderiv_value {d : ℕ} (hd : 11≤d) (I : Finset (Fin d)) :
    ∀ᶠ x : ℝ × Amplitudes d in 𝓝 (1,0), (∀ i∈I,0<x.2 i) →
      fderiv ℝ (fun r => fderiv ℝ (value hd I x.1) r) x.2 =
        (dotDual d).comp (hessianMap hd I x.1 x.2) := by
  have ht : Tendsto (fun x : ℝ × Amplitudes d => (x.1,sqrtLift I x.2))
      (𝓝 (1,0)) (𝓝 (1,0)) := by
    have hc : Continuous (fun x : ℝ × Amplitudes d => (x.1,sqrtLift I x.2)) :=
      continuous_fst.prodMk ((sqrtLift_continuous I).comp continuous_snd)
    simpa only [sqrtLift_zero] using hc.tendsto ((1,0) : ℝ × Amplitudes d)
  have ha : ∀ᶠ x : ℝ × Amplitudes d in 𝓝 (1,0),∀ i, AnalyticAt ℝ (factor hd i) x :=
    Filter.eventually_all.mpr (fun i => (factor_analytic hd i).eventually_analyticAt)
  filter_upwards [(hasFDerivAt_value hd I).eventually_nhds,ht.eventually ha] with x hx hax hr
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
  have he : (fun r => fderiv ℝ (value hd I x.1) r) =ᶠ[𝓝 x.2] gradient hd I x.1 := by
    filter_upwards [hs.eventually hx,hp] with r hx' hr'
    exact (hx' hr').fderiv
  rw [he.fderiv_eq]
  exact (hasFDerivAt_gradient_of_analytic hd I hr hax).fderiv

#print axioms second_fderiv_value
end BecknerOnofri.HighDim.LocalEleven.SquaredReducedEnergy
