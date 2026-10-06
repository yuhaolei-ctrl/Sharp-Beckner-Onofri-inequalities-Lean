module

public import BecknerOnofri.SpinMixtureFeasibility

@[expose] public section

/-! A definition-only interface for the trusted challenge: all hypotheses
spell out the actual cosine mixture rather than importing its proof modules. -/
noncomputable section
open scoped BigOperators
namespace BecknerOnofri.HighDim.Spin
open Legacy.D10 Legacy.BecknerOnofri

theorem explicit_mixture_feasible (ρ : ProbabilityDensity 12)
    (w : ℕ → ℝ) (N : ℕ → Fin 12 → ℕ) (hw : ∀ n,0≤w n) (hm : HasSum w 1)
    (hSup : Summable (fun n => w n*∏ i : Fin 12,
      (4:ℝ)^(N n i)/((2*N n i).choose (N n i):ℝ)))
    (hρ : ∀ x,ρ.value x=∑' n,w n*∏ i : Fin 12,
      Complex.normSq (1+fourier 1 (x i))^(N n i)/((2*N n i).choose (N n i):ℝ)) :
    Feasible (countLaw (channelLaw ρ)) := by
  apply channel_count_feasible
  refine ⟨w,N,hw,hm,?_,funext hρ⟩
  have hfour : Complex.normSq (1+1)=4 := by norm_num [Complex.normSq_apply]
  simpa [CosineMixture.tensor,cosinePower,hfour] using hSup

#print axioms explicit_mixture_feasible
end BecknerOnofri.HighDim.Spin
