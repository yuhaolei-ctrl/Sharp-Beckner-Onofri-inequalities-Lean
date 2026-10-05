import BecknerOnofri.LocalElevenCore.RealReducedEnergyGradient
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! The actual reduced energy in squared active-amplitude coordinates.
All derivatives are obtained by the chain rule on the positive orthant. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter
open scoped Topology BigOperators
namespace BecknerOnofri.HighDim.LocalEleven.SquaredReducedEnergy
open AmplitudeLinearization ActiveAmplitudeFactor RealReducedEnergy

def sqrtLift {d : ℕ} (I : Finset (Fin d)) (r : Amplitudes d) : Amplitudes d :=
  fun i => if i∈I then Real.sqrt (r i) else 0

def sqrtDerivative {d : ℕ} (I : Finset (Fin d)) (r : Amplitudes d) :
    Amplitudes d →L[ℝ] Amplitudes d :=
  ContinuousLinearMap.pi (fun i => if i∈I then
    (1/(2*Real.sqrt (r i))) • ContinuousLinearMap.proj i else 0)

@[simp] theorem sqrtDerivative_apply {d : ℕ} (I : Finset (Fin d)) (r h : Amplitudes d) (i : Fin d) :
    sqrtDerivative I r h i=if i∈I then h i/(2*Real.sqrt (r i)) else 0 := by
  simp only [sqrtDerivative,ContinuousLinearMap.pi_apply]
  split_ifs <;> simp [div_eq_mul_inv,mul_comm]

theorem sqrtLift_continuous {d : ℕ} (I : Finset (Fin d)) : Continuous (sqrtLift I) := by
  apply continuous_pi
  intro i
  by_cases hi : i∈I
  · simpa only [sqrtLift,if_pos hi,Function.comp_def] using Real.continuous_sqrt.comp (continuous_apply i)
  · simpa only [sqrtLift,if_neg hi] using (continuous_const : Continuous (fun _ : Amplitudes d => (0:ℝ)))

@[simp] theorem sqrtLift_zero {d : ℕ} (I : Finset (Fin d)) : sqrtLift I 0=0 := by
  funext i
  simp [sqrtLift]

theorem hasFDerivAt_sqrtLift {d : ℕ} (I : Finset (Fin d)) {r : Amplitudes d}
    (hr : ∀ i∈I,0<r i) : HasFDerivAt (sqrtLift I) (sqrtDerivative I r) r := by
  apply hasFDerivAt_pi.mpr
  intro i
  by_cases hi : i∈I
  · simpa only [sqrtLift,sqrtDerivative,ContinuousLinearMap.pi_apply,if_pos hi,ContinuousLinearMap.proj_apply] using
      ((ContinuousLinearMap.proj i : Amplitudes d →L[ℝ] ℝ).hasFDerivAt (x := r)).sqrt (hr i hi).ne'
  · simpa only [sqrtLift,sqrtDerivative,ContinuousLinearMap.pi_apply,if_neg hi] using
      (hasFDerivAt_const (0:ℝ) r)

def value {d : ℕ} (hd : 11≤d) (I : Finset (Fin d)) (μ : ℝ) (r : Amplitudes d) : ℝ :=
  RealReducedEnergy.energy hd μ (sqrtLift I r)

def gradient {d : ℕ} (hd : 11≤d) (I : Finset (Fin d)) (μ : ℝ) (r : Amplitudes d) :
    Amplitudes d →L[ℝ] ℝ :=
  dotDual d (fun i => if i∈I then -(1/μ)*factor hd i (μ,sqrtLift I r) else 0)

lemma gradient_chain {d : ℕ} (hd : 11≤d) (I : Finset (Fin d)) {μ : ℝ}
    (hμ : μ≠0) {r : Amplitudes d} (hr : ∀ i∈I,0<r i)
    (hf : ∀ i, scalar hd i (μ,sqrtLift I r)=(sqrtLift I r i)*factor hd i (μ,sqrtLift I r)) :
    (RealReducedEnergy.gradient hd μ (sqrtLift I r)).comp (sqrtDerivative I r)=gradient hd I μ r := by
  apply ContinuousLinearMap.ext
  intro h
  rw [ContinuousLinearMap.comp_apply,RealReducedEnergy.gradient_apply]
  change -(2/μ)*(∑ i,sqrtDerivative I r h i*scalar hd i (μ,sqrtLift I r)) = _
  simp only [gradient,dotDual_apply,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [sqrtDerivative_apply,hf i]
  by_cases hi : i∈I
  · simp only [sqrtLift,if_pos hi]
    have hs : Real.sqrt (r i)≠0 := (Real.sqrt_pos.mpr (hr i hi)).ne'
    field_simp
    <;> ring
  · simp only [sqrtLift,if_neg hi,zero_mul,mul_zero]

/-- The gradient is that of the actual energy, rather than an independently
defined formal reduced polynomial. -/
theorem hasFDerivAt_value {d : ℕ} (hd : 11≤d) (I : Finset (Fin d)) :
    ∀ᶠ x : ℝ × Amplitudes d in 𝓝 (1,0), (∀ i∈I,0<x.2 i) →
      HasFDerivAt (value hd I x.1) (gradient hd I x.1 x.2) x.2 := by
  have ht : Tendsto (fun x : ℝ × Amplitudes d => (x.1,sqrtLift I x.2))
      (𝓝 (1,0)) (𝓝 (1,0)) := by
    have hc : Continuous (fun x : ℝ × Amplitudes d => (x.1,sqrtLift I x.2)) :=
      continuous_fst.prodMk ((sqrtLift_continuous I).comp continuous_snd)
    simpa only [sqrtLift_zero] using hc.tendsto ((1,0) : ℝ × Amplitudes d)
  have hf : ∀ᶠ x : ℝ × Amplitudes d in 𝓝 (1,0),∀ i,
      scalar hd i x=x.2 i*factor hd i x :=
    Filter.eventually_all.mpr (fun i => scalar_eq_coordinate_mul_factor hd i)
  have hμ : ∀ᶠ x : ℝ × Amplitudes d in 𝓝 (1,0),x.1≠0 :=
    (continuous_fst : Continuous (fun x : ℝ × Amplitudes d => x.1)).continuousAt.tendsto.eventually (eventually_ne_nhds (by norm_num : (1:ℝ)≠0))
  filter_upwards [ht.eventually (RealReducedEnergy.hasFDerivAt_energy hd),ht.eventually hf,hμ]
    with x hx hfx hμx hr
  have hh := hx.comp x.2 (hasFDerivAt_sqrtLift I hr)
  rw [gradient_chain hd I hμx hr hfx] at hh
  exact hh

#print axioms hasFDerivAt_value
end BecknerOnofri.HighDim.LocalEleven.SquaredReducedEnergy
