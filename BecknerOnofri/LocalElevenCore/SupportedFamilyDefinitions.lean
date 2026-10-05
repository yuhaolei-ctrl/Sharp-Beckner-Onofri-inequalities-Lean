module

public import BecknerOnofri.LocalElevenCore.CommonSquaredAmplitude

@[expose] public section

noncomputable section
open Filter Asymptotics
open scoped Topology
namespace BecknerOnofri.HighDim.LocalEleven.SupportedFamily
open SubsetDiagonal LocalReductionStatement

def amplitude {d : ℕ} (hd : 11≤d) (n : ℕ) : ℝ → ℝ :=
  if h : 0<n ∧ n≤d then (exists_common_squared_amplitude hd h.1 h.2).choose else 0

theorem amplitude_spec {d n : ℕ} (hd : 11≤d) (hn : 0<n) (hnd : n≤d) :
    AnalyticAt ℝ (amplitude hd n) 0 ∧ amplitude hd n 0=0 ∧
    HasDerivAt (amplitude hd n) (supportCoefficient d n)⁻¹ 0 ∧
    ((fun δ => amplitude hd n δ-δ/supportCoefficient d n) =O[𝓝 (0:ℝ)] (fun δ => ‖δ‖^2)) ∧
    ∀ I : Finset (Fin d),I.card=n → ∀ j : Fin d,∀ hj : j∈I,
      (∀ᶠ δ in 𝓝[>] (0:ℝ),0<amplitude hd n δ ∧
        parameter hd I j hj (Real.sqrt (amplitude hd n δ))=1/(1-δ)) ∧
      (∀ᶠ t in 𝓝 (0:ℝ),amplitude hd n (1-1/parameter hd I j hj t)=t^2) := by
  simpa only [amplitude,dif_pos (show 0<n ∧ n≤d from ⟨hn,hnd⟩)] using
    (exists_common_squared_amplitude hd hn hnd).choose_spec

def branch {d : ℕ} (hd : 11≤d) (I : Finset (Fin d)) (δ : ℝ) : ContinuousGibbs.Space d :=
  ReducedEquation.potential hd (1/(1-δ),line I (Real.sqrt (amplitude hd I.card δ)))

end BecknerOnofri.HighDim.LocalEleven.SupportedFamily
