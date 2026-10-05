module

public import BecknerOnofri.ReducedEquation

@[expose] public section

/-! Every small continuous mean-zero solution of the actual Euler equation
belongs to the uniquely constructed analytic complementary graph. -/
noncomputable section
open Filter
open scoped Topology
namespace BecknerOnofri.HighDim.ReducedEquation
open ContinuousGibbs ContinuousFirstShell ContinuousComplement GreenLocalBranch

theorem reconstruction_of_meanZero {d : ℕ} (u : Space d) (hm : MeanZero u) :
    reconstruction d (coordinates d u,complementMap d u) = u := by
  have he := decomposition u
  rw [meanProjection_apply, show mean d u = 0 from hm] at he
  simpa only [ContinuousMap.const_zero, zero_add, reconstruction_apply] using he.symm

theorem small_full_solution_on_graph {d : ℕ} (hd : 12 ≤ d) :
    ∀ᶠ x : ℝ × Space d in 𝓝 (1,0), MeanZero x.2 → full d x.1 x.2 = 0 →
      x.2 = potential hd (x.1,coordinates d x.2) ∧ reduced hd (x.1,coordinates d x.2) = 0 := by
  have ht : Tendsto (fun x : ℝ × Space d => ((x.1,coordinates d x.2),complementMap d x.2))
      (𝓝 (1,0)) (𝓝 ((1,0),0)) := by
    have hc : Continuous (fun x : ℝ × Space d => ((x.1,coordinates d x.2),complementMap d x.2)) :=
      (continuous_fst.prodMk ((coordinates d).continuous.comp continuous_snd)).prodMk
        ((complementMap d).continuous.comp continuous_snd)
    simpa only [map_zero] using hc.tendsto (1,0)
  filter_upwards [ht.eventually (local_full_iff_reduced hd)] with x hx hm he
  rw [reconstruction_of_meanZero x.2 hm] at hx
  obtain ⟨hw,hr⟩ := hx.mp he
  refine ⟨?_,hr⟩
  rw [potential, hw, reconstruction_of_meanZero x.2 hm]

#print axioms small_full_solution_on_graph
end BecknerOnofri.HighDim.ReducedEquation
