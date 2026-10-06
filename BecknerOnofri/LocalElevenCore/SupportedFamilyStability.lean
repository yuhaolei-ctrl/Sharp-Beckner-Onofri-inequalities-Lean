module

public import BecknerOnofri.LocalElevenCore.SupportedFullIdentification
public import BecknerOnofri.LocalElevenCore.SmallSolutionSaddles
public import BecknerOnofri.LocalElevenCore.FullModeLocalBranch

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter
open scoped Topology
namespace BecknerOnofri.HighDim.LocalEleven.SupportedFamily
open ContinuousGibbs ContinuousFirstShell

theorem delta_parameter_tendsto : Tendsto (fun δ : ℝ => 1/(1-δ))
    (𝓝[>] (0:ℝ)) (𝓝[>] (1:ℝ)) := by
  have hc : ContinuousAt (fun δ : ℝ => 1/(1-δ)) 0 :=
    continuousAt_const.div (continuousAt_const.sub continuousAt_id) (by norm_num)
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · simpa using hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
  · filter_upwards [self_mem_nhdsWithin,
      (gt_mem_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds] with δ hδ hδ1
    change 0<δ at hδ
    change 1<1/(1-δ)
    exact (one_lt_div (by linarith)).mpr (by linarith)

theorem full_branch_morse_bott {d : ℕ} (hd : 11≤d) :
    ∀ᶠ δ in 𝓝[>] (0:ℝ),
      FullModeMorseBott ((1/(1-δ))*spectralThreshold d) (branch hd Finset.univ δ) := by
  have hσ : 0<spectralThreshold d := Legacy.TorusEndpoint.endpointSigma_pos (by omega)
  have hβ : Tendsto (fun δ : ℝ => (1/(1-δ))*spectralThreshold d)
      (𝓝[>] (0:ℝ)) (𝓝[>] (spectralThreshold d)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · simpa only [one_mul] using
        (tendsto_nhds_of_tendsto_nhdsWithin delta_parameter_tendsto).mul_const (spectralThreshold d)
    · filter_upwards [delta_parameter_tendsto.eventually self_mem_nhdsWithin] with δ hδ
      change spectralThreshold d<(1/(1-δ))*spectralThreshold d
      nlinarith
  have he := delta_parameter_tendsto.eventually (full_branch_identification hd)
  filter_upwards [he,hβ.eventually (PhysicalBranchProperties.physical_branch_properties hd),
    hβ.eventually (FullBranchHessian.physical_hessian_nonpos_kernel hd),
    hβ.eventually (PhysicalNormalCoercivity.physical_normalCoercivity hd),
    hβ.eventually (physical_sobolev_local_maximum hd)] with δ he hb hh hn hmax
  have he' : branch hd Finset.univ δ=
      DiagonalScalarBranch.physicalPotential hd ((1/(1-δ))*spectralThreshold d) := by
    simpa only [one_div_one_div,sub_sub_cancel,
      DiagonalScalarBranch.physicalPotential,mul_div_cancel_right₀ _ hσ.ne'] using he
  rw [he']
  exact ⟨hb.smooth,fun s _ => hb.sobolev s,hb.criticalSobolev,hb.meanZero,hb.stationary,
    hb.fullModes,hb.tangentIndependent,
    fun h hc hm => (hh h hc hm).1,fun h hc hm => (hh h hc hm).2,hn,hmax⟩

theorem proper_branch_saddle {d : ℕ} (hd : 11≤d) (I : Finset (Fin d))
    (hI : I.Nonempty) (hcard : I.card<d) :
    ∀ᶠ δ in 𝓝[>] (0:ℝ),∃ v q : Space d,
      InCriticalSobolev v ∧ MeanZero v ∧ InCriticalSobolev q ∧ MeanZero q ∧
      0<secondVariation ((1/(1-δ))*spectralThreshold d) (branch hd I δ) v ∧
      secondVariation ((1/(1-δ))*spectralThreshold d) (branch hd I δ) q<0 := by
  have hb := (branch_profile hd I hI).1
  have ht := (tendsto_nhds_of_tendsto_nhdsWithin delta_parameter_tendsto).prodMk_nhds hb.1
  filter_upwards [ht.eventually (small_stationary_saddle hd),hb.2] with δ hs hb
  have hsupport := hb.2.2.2.2.2.2.2
  apply hs hb.2.2.2.2.1 hb.2.2.2.2.2.1
  · obtain ⟨i,hi⟩ := hI
    have hn := (hsupport i).mpr hi
    intro hz
    apply hn
    rw [hz,← coefficient_eq_fourierCoeff,map_zero]
  · have hnot : ∃ j : Fin d,j∉I := by
      by_contra h
      have hall : I=Finset.univ := by
        ext i
        simp only [Finset.mem_univ,iff_true]
        by_contra hi
        exact h ⟨i,hi⟩
      simp only [hall,Finset.card_univ,Fintype.card_fin,lt_self_iff_false] at hcard
    obtain ⟨j,hj⟩ := hnot
    exact ⟨j,not_ne_iff.mp (fun hn => hj ((hsupport j).mp hn))⟩

#print axioms full_branch_morse_bott
#print axioms proper_branch_saddle
end BecknerOnofri.HighDim.LocalEleven.SupportedFamily
