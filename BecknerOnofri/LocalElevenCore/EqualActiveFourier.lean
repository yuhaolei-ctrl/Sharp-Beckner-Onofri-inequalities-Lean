module

public import BecknerOnofri.LocalElevenCore.EqualActiveAmplitudes
public import BecknerOnofri.LocalElevenCore.ContinuousLocalReduction
public import BecknerOnofri.LocalElevenCore.EulerEquation

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter
open scoped Topology
namespace BecknerOnofri.HighDim.LocalEleven
open ContinuousGibbs ContinuousFirstShell ReducedEquation ContinuousSymmetry

theorem reduced_equal_active_fourier {d : ℕ} (hd : 11≤d) :
    ∀ᶠ x : ℝ × Coordinates d in 𝓝 (1,0),reduced hd x=0 →
      ∀ i j : Fin d,x.2 i≠0 → x.2 j≠0 → ‖x.2 i‖^2=‖x.2 j‖^2 := by
  let N : ℝ × Coordinates d → ActiveAmplitudeFactor.Input d := fun x => (x.1,fun i => ‖x.2 i‖)
  have hc : Continuous N := continuous_fst.prodMk
    (continuous_pi (fun i => ((continuous_apply i).comp continuous_snd).norm))
  have hN : N (1,0)=(1,0) := by
    apply Prod.ext
    · rfl
    · funext i
      exact norm_zero
  have ht : Tendsto N (𝓝 (1,0)) (𝓝 (1,0)) := by
    simpa only [hN] using hc.tendsto (1,0)
  filter_upwards [ht.eventually (ActiveAmplitudeFactor.equal_active_squares hd),
    reduced_nonnegative_zero_iff hd] with x he hnorm
  intro hx i j hi hj
  have hr : reduced hd (ActiveAmplitudeFactor.realEmbedding d (N x))=0 := by
    exact hnorm.mpr hx
  exact he hr i j (norm_ne_zero_iff.mpr hi) (norm_ne_zero_iff.mpr hj)

/-- Every sufficiently small actual continuous mean-zero Euler solution has
equal magnitudes in all of its nonzero first-shell modes. -/
theorem small_stationary_equal_active_fourier {d : ℕ} (hd : 11≤d) :
    ∀ᶠ x : ℝ × Space d in 𝓝 (1,0), MeanZero x.2 →
      (∀ k : NonzeroFrequency d,
        ((frequencyLength k.val^d:ℝ):ℂ)*fourierCoeff x.2 k.val =
          (x.1:ℂ)*fourierCoeff (normalizedGibbs x.2) k.val) →
      ∀ i j : Fin d,fourierCoeff x.2 (axisFrequency i)≠0 →
        fourierCoeff x.2 (axisFrequency j)≠0 →
        ‖fourierCoeff x.2 (axisFrequency i)‖^2=‖fourierCoeff x.2 (axisFrequency j)‖^2 := by
  have ht : Tendsto (fun x : ℝ × Space d => (x.1,coordinates d x.2))
      (𝓝 (1,0)) (𝓝 (1,0)) := by
    have hc : Continuous (fun x : ℝ × Space d => (x.1,coordinates d x.2)) :=
      continuous_fst.prodMk ((coordinates d).continuous.comp continuous_snd)
    simpa only [map_zero] using hc.tendsto (1,0)
  filter_upwards [small_full_solution_on_graph hd,ht.eventually (reduced_equal_active_fourier hd)]
    with x hgraph heq
  intro hm hs i j hi hj
  have hf := (full_zero_iff_stationary (by omega) x.1 x.2).mpr ⟨hm,hs⟩
  have hred := (hgraph hm hf).2
  have hi' : coordinates d x.2 i≠0 := by simpa only [coordinates_apply,coefficient_eq_fourierCoeff] using hi
  have hj' : coordinates d x.2 j≠0 := by simpa only [coordinates_apply,coefficient_eq_fourierCoeff] using hj
  simpa only [coordinates_apply,coefficient_eq_fourierCoeff] using heq hred i j hi' hj'

#print axioms small_stationary_equal_active_fourier
end BecknerOnofri.HighDim.LocalEleven
