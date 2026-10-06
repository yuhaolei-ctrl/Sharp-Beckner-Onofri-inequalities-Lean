module

public import BecknerOnofri.LocalElevenCore.SubsetEnergyFamily
public import BecknerOnofri.AnalyticPitchforkInvertible

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter Asymptotics
open scoped Topology
namespace BecknerOnofri.HighDim.LocalEleven
open SubsetDiagonal LocalReductionStatement

/-- The same analytic function is both the forward and inverse squared amplitude
for every support of a fixed cardinality. -/
theorem exists_common_squared_amplitude {d n : ℕ} (hd : 11≤d) (hn : 0<n) (hnd : n≤d) :
    ∃ r : ℝ → ℝ, AnalyticAt ℝ r 0 ∧ r 0=0 ∧ HasDerivAt r (supportCoefficient d n)⁻¹ 0 ∧
      ((fun δ => r δ-δ/supportCoefficient d n) =O[𝓝 (0:ℝ)] (fun δ => ‖δ‖^2)) ∧
      ∀ I : Finset (Fin d), I.card=n → ∀ j : Fin d, ∀ hj : j∈I,
        (∀ᶠ δ in 𝓝[>] (0:ℝ),0<r δ ∧ parameter hd I j hj (Real.sqrt (r δ))=1/(1-δ)) ∧
        (∀ᶠ t in 𝓝 (0:ℝ), r (1-1/parameter hd I j hj t)=t^2) := by
  obtain ⟨J,hJsub,hJcard⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset (Fin d))) (by simpa using hnd)
  obtain ⟨j,hj⟩ := Finset.card_pos.mp (show 0<J.card by omega)
  let D := pitchforkData hd J j hj
  obtain ⟨r,hr,hr0,hrd,he,hp,hl⟩ := AnalyticPitchfork.exists_invertible_positive_squared_amplitude D
    (coefficient_pos hd J ⟨j,hj⟩)
  have hc : D.coefficient=supportCoefficient d n := by
    simp only [D,pitchforkData,coefficient,supportCoefficient,hJcard]
  refine ⟨r,hr,hr0,?_,?_,?_⟩
  · simpa only [hc] using hrd
  · simpa only [hc] using he
  · intro I hI i hi
    have heq := parameter_eq_of_card_eq hd J I j i hj hi (hJcard.trans hI.symm)
    have ht : Tendsto (fun δ => Real.sqrt (r δ)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
      have h := hr.continuousAt.sqrt.tendsto.mono_left
        (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
      simpa only [hr0,Real.sqrt_zero] using h
    constructor
    · filter_upwards [hp,ht.eventually heq] with δ hp heq
      exact ⟨hp.1,heq.symm.trans hp.2⟩
    · filter_upwards [hl,heq] with t hl heq
      rw [← heq]
      exact hl

#print axioms exists_common_squared_amplitude
end BecknerOnofri.HighDim.LocalEleven
