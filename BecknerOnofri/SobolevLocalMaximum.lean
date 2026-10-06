module

public import BecknerOnofri.GeneralSobolevEmbedding
public import BecknerOnofri.RawOptimizerCorrespondence

@[expose] public section

noncomputable section
open Filter MeasureTheory
open scoped Topology
namespace BecknerOnofri.HighDim
open ContinuousGibbs

/-- A local maximum on continuous critical-Sobolev representatives is a local
maximum on every raw H^s domain above the Sobolev embedding threshold. -/
theorem sobolev_localMaximum_of_continuous {d : ℕ} (hd : 0<d) (β : ℝ) (u : Space d)
    (hmax : ∀ᶠ v : Space d in 𝓝 u, InCriticalSobolev v → MeanZero v →
      dualFunctional β v≤dualFunctional β u) :
    ∀ s : ℝ,(d:ℝ)/2<s → ∃ r : ℝ,0<r ∧ ∀ v : Torus d → ℝ,
      InSobolev s v → InCriticalSobolev v → MeanZero v →
      InSobolev s (fun x => v x-u x) →
      sobolevNorm s (fun x => v x-u x)<r → dualFunctional β v≤dualFunctional β u := by
  intro s hs
  obtain ⟨ε,hε,hball⟩ := Metric.eventually_nhds_iff.mp hmax
  let C := ‖SobolevEmbedding.inverseScaleLp hd hs‖
  have hC : 0≤C := norm_nonneg _
  refine ⟨ε/(C+1),div_pos hε (by positivity),?_⟩
  intro v hv hc hm hf hn
  obtain ⟨w,hw,hwS,hwB⟩ := SobolevEmbedding.exists_continuous_representative hd hs
    (fun x => v x-u x) hf
  let V : Space d := u+w
  have he : (V : Torus d → ℝ) =ᵐ[torusMeasure d] v := by
    filter_upwards [hw] with x hx
    change u x+w x=v x
    rw [hx]
    ring
  have hVc : InCriticalSobolev V := (Gap.inCriticalSobolev_congr he).mpr hc
  have hVm : MeanZero V := by
    change (∫ x,V x ∂torusMeasure d)=0
    rw [integral_congr_ae he]
    exact hm
  have hdV : dist V u<ε := by
    rw [dist_eq_norm,show V-u=w by dsimp [V]; abel]
    have hnorm : 0≤sobolevNorm s (fun x => v x-u x) := by
      unfold sobolevNorm
      positivity
    have hh := (lt_div_iff₀ (show 0<C+1 by positivity)).mp hn
    change ‖w‖≤C*sobolevNorm s (fun x => v x-u x) at hwB
    nlinarith
  have h := hball hdV hVc hVm
  rwa [OptimizerDuality.dualFunctional_congr_ae β he] at h

#print axioms sobolev_localMaximum_of_continuous
end BecknerOnofri.HighDim
