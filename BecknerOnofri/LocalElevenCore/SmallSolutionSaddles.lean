import BecknerOnofri.LocalElevenCore.RealGraphSaddles
import BecknerOnofri.LocalElevenCore.ContinuousLocalReduction
import BecknerOnofri.LocalElevenCore.EulerEquation
import BecknerOnofri.OptimizerTranslation

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter
open scoped Topology
namespace BecknerOnofri.HighDim.LocalEleven
open ContinuousGibbs ContinuousFirstShell ReducedEquation ContinuousSymmetry
open BecknerOnofri.HighDim.ContinuousSymmetry (translation translation_add translation_zero)

/-- Every small nonzero Euler solution with a missing first-shell coordinate
has both signs of the actual physical second variation. -/
theorem small_stationary_saddle {d : ℕ} (hd : 11≤d) :
    ∀ᶠ x : ℝ × Space d in 𝓝 (1,0),MeanZero x.2 →
      (∀ k : NonzeroFrequency d,
        ((frequencyLength k.val^d:ℝ):ℂ)*fourierCoeff x.2 k.val =
          (x.1:ℂ)*fourierCoeff (normalizedGibbs x.2) k.val) → x.2≠0 →
      (∃ j : Fin d,fourierCoeff x.2 (axisFrequency j)=0) →
      ∃ v q : Space d,InCriticalSobolev v ∧ MeanZero v ∧ InCriticalSobolev q ∧ MeanZero q ∧
        0<secondVariation (x.1*spectralThreshold d) x.2 v ∧
        secondVariation (x.1*spectralThreshold d) x.2 q<0 := by
  let Z : ℝ × Space d → ℝ × Coordinates d := fun x => (x.1,coordinates d x.2)
  have hzcont : Continuous Z := continuous_fst.prodMk ((coordinates d).continuous.comp continuous_snd)
  have hZ : Tendsto Z (𝓝 (1,0)) (𝓝 (1,0)) := by
    simpa only [Z,map_zero] using hzcont.tendsto (1,0)
  let N : ℝ × Coordinates d → ActiveAmplitudeFactor.Input d := fun x => (x.1,fun i => ‖x.2 i‖)
  have hc : Continuous N := continuous_fst.prodMk
    (continuous_pi (fun i => ((continuous_apply i).comp continuous_snd).norm))
  have hN0 : N (1,0)=(1,0) := by
    apply Prod.ext
    · rfl
    · funext i
      exact norm_zero
  have hN : Tendsto N (𝓝 (1,0)) (𝓝 (1,0)) := by
    simpa only [hN0] using hc.tendsto (1,0)
  have hμ : Tendsto (Prod.fst : ℝ × Space d → ℝ) (𝓝 (1,0)) (𝓝 1) := continuous_fst.continuousAt
  filter_upwards [small_full_solution_on_graph hd,
    hZ.eventually (reduced_nonnegative_zero_iff hd),hZ.eventually (potential_translation hd),
    (hN.comp hZ).eventually (ActiveAmplitudeFactor.real_graph_saddle hd),
    hμ.eventually (ReducedCubicExpansion.potential_axis hd)] with x hgraph hnorm htrans hs haxis
  intro hm hEuler hn ⟨j,hj⟩
  have hf := (full_zero_iff_stationary (by omega) x.1 x.2).mpr ⟨hm,hEuler⟩
  obtain ⟨hu,hr⟩ := hgraph hm hf
  have hz : coordinates d x.2≠0 := by
    intro he
    rw [he,haxis] at hu
    exact hn hu
  have hi : ∃ i : Fin d,coordinates d x.2 i≠0 := by
    by_contra h
    apply hz
    funext i
    by_contra hi
    exact h ⟨i,hi⟩
  obtain ⟨i,hi⟩ := hi
  have hred : reduced hd (ActiveAmplitudeFactor.realEmbedding d (N (Z x)))=0 := hnorm.mpr hr
  have hzero : coordinates d x.2 j=0 := by
    simpa only [coordinates_apply,coefficient_eq_fourierCoeff] using hj
  obtain ⟨v,q,hv,hvm,hq,hqm,hvp,hqn⟩ := hs hred
    ⟨i,norm_ne_zero_iff.mpr hi⟩ ⟨j,by change ‖coordinates d x.2 j‖=0; rw [hzero,norm_zero]⟩
  let a := phaseNormalizer (coordinates d x.2)
  let U : Space d := potential hd (ActiveAmplitudeFactor.realEmbedding d (N (Z x)))
  have hp : U=translation a x.2 := by
    have h := htrans a
    rw [phaseNormalizer_spec,← hu] at h
    exact h
  have hinv : translation (-a) U=x.2 := by
    rw [hp,translation_add,add_neg_cancel,translation_zero]
  have hv' : secondVariation (x.1*spectralThreshold d) x.2 (translation (-a) v)=
      secondVariation (x.1*spectralThreshold d) U v := by
    rw [← hinv]
    exact secondVariation_translate _ U v (-a)
  have hq' : secondVariation (x.1*spectralThreshold d) x.2 (translation (-a) q)=
      secondVariation (x.1*spectralThreshold d) U q := by
    rw [← hinv]
    exact secondVariation_translate _ U q (-a)
  refine ⟨translation (-a) v,translation (-a) q,?_,?_,?_,?_,?_,?_⟩
  · exact (inCriticalSobolev_translate_iff v (-a)).mpr hv
  · exact (meanZero_translate_iff v (-a)).mpr hvm
  · exact (inCriticalSobolev_translate_iff q (-a)).mpr hq
  · exact (meanZero_translate_iff q (-a)).mpr hqm
  · rw [hv']
    exact hvp
  · rw [hq']
    exact hqn

#print axioms small_stationary_saddle
end BecknerOnofri.HighDim.LocalEleven
