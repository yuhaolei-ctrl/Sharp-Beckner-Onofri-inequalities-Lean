module

public import BecknerOnofri.LocalElevenCore.ActiveHessianAmplitudeSpectrum

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter Asymptotics
open scoped Topology
namespace BecknerOnofri.HighDim.LocalEleven.SquaredReducedEnergy
open AmplitudeLinearization ActiveAmplitudeFactor

theorem quadratic_remainder_sqrt {r F : ℝ → ℝ} {c : ℝ}
    (hr : AnalyticAt ℝ r 0) (hr0 : r 0=0)
    (hp : ∀ᶠ δ in 𝓝[>] (0:ℝ),0<r δ)
    (ho : (fun t => F t-c) =O[𝓝 (0:ℝ)] (fun t => ‖t‖^2)) :
    (fun δ => F (Real.sqrt (r δ))-c) =O[𝓝[>] (0:ℝ)] (fun δ => ‖δ‖) := by
  have ht : Tendsto (fun δ => Real.sqrt (r δ)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    simpa only [hr0,Real.sqrt_zero] using hr.continuousAt.sqrt.tendsto.mono_left
      (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
  have hrb : r =O[𝓝[>] (0:ℝ)] (fun δ => ‖δ‖) := by
    simpa only [hr0,sub_zero] using hr.differentiableAt.isBigO_sub.norm_right.mono
      (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
  have hs : (fun δ => ‖Real.sqrt (r δ)‖^2) =O[𝓝[>] (0:ℝ)] (fun δ => ‖δ‖) := by
    apply hrb.congr' ?_ Filter.EventuallyEq.rfl
    filter_upwards [hp] with δ hδ
    simp only [Real.norm_eq_abs,sq_abs,Real.sq_sqrt hδ.le]
  exact (ho.comp_tendsto ht).trans hs

/-- Transfer of the actual active Hessian spectrum to the physical parameter
delta=1-1/tau, for any already identified supported squared-amplitude branch. -/
theorem active_physical_spectrum_of_parameter {d : ℕ} (hd : 11≤d) (I : Finset (Fin d))
    (j : Fin d) (hj : j∈I) {r : ℝ → ℝ} (hr : AnalyticAt ℝ r 0) (hr0 : r 0=0)
    (hp : ∀ᶠ δ in 𝓝[>] (0:ℝ),0<r δ ∧
      SubsetDiagonal.parameter hd I j hj (Real.sqrt (r δ))=1/(1-δ)) :
    ∃ R T : ℝ → ℝ,
      ((fun δ => R δ-(2*quarticA d+quarticB d*((I.card:ℝ)-1)))
        =O[𝓝[>] (0:ℝ)] (fun δ => ‖δ‖)) ∧
      ((fun δ => T δ-(2*quarticA d-quarticB d))
        =O[𝓝[>] (0:ℝ)] (fun δ => ‖δ‖)) ∧
      ∀ᶠ δ in 𝓝[>] (0:ℝ),R δ<0 ∧ T δ<0 ∧ R δ≠T δ ∧
        activeHessian hd I (1/(1-δ)) (realLine I (r δ))=
          EquicorrelatedSpectrum.operator (T δ) ((R δ-T δ)/(I.card:ℝ)) ∧
        Module.finrank ℝ ((activeHessian hd I (1/(1-δ)) (realLine I (r δ))).eigenspace (R δ))=1 ∧
        Module.finrank ℝ ((activeHessian hd I (1/(1-δ)) (realLine I (r δ))).eigenspace (T δ))=I.card-1 := by
  obtain ⟨R,T,_,_,hR0,hT0,hRo,hTo,he⟩ := exists_active_amplitude_spectrum hd I j hj
  refine ⟨fun δ => R (Real.sqrt (r δ)),fun δ => T (Real.sqrt (r δ)),?_,?_,?_⟩
  · apply quadratic_remainder_sqrt hr hr0 (hp.mono fun _ h => h.1)
    simpa only [hR0] using hRo
  · apply quadratic_remainder_sqrt hr hr0 (hp.mono fun _ h => h.1)
    simpa only [hT0] using hTo
  · have ht : Tendsto (fun δ => Real.sqrt (r δ)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
      simpa only [hr0,Real.sqrt_zero] using hr.continuousAt.sqrt.tendsto.mono_left
        (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
    filter_upwards [hp,ht.eventually he] with δ hp he
    have h := he (Real.sqrt_pos.mpr hp.1)
    rw [Real.sq_sqrt hp.1.le,hp.2] at h
    exact h

#print axioms active_physical_spectrum_of_parameter
end BecknerOnofri.HighDim.LocalEleven.SquaredReducedEnergy
