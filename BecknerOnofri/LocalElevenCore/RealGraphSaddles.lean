module

public import BecknerOnofri.LocalElevenCore.InactivePositiveDirection
public import BecknerOnofri.LocalElevenCore.ComplementNegativeDirection

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter
open scoped Topology
namespace BecknerOnofri.HighDim.LocalEleven.ActiveAmplitudeFactor
open ContinuousGibbs ContinuousFirstShell ReducedEquation AmplitudeLinearization RescaledReducedEquation

theorem all_inactive_positive_directions {d : ℕ} (hd : 11≤d) :
    ∀ᶠ x : Input d in 𝓝 (1,0),∀ i j : Fin d,i≠j →
      reduced hd (realEmbedding d x)=0 → x.2 i≠0 → x.2 j=0 →
      ∃ v : Space d,InCriticalSobolev v ∧ MeanZero v ∧
        0<secondVariation (x.1*spectralThreshold d) (potential hd (realEmbedding d x)) v := by
  apply Filter.eventually_all.mpr
  intro i
  apply Filter.eventually_all.mpr
  intro j
  by_cases hij : i=j
  · exact Filter.Eventually.of_forall (fun _ hn => False.elim (hn hij))
  · exact (inactive_positive_direction hd i j hij).mono (fun _ h _ => h)

theorem real_graph_saddle {d : ℕ} (hd : 11≤d) :
    ∀ᶠ x : Input d in 𝓝 (1,0),reduced hd (realEmbedding d x)=0 →
      (∃ i : Fin d,x.2 i≠0) → (∃ j : Fin d,x.2 j=0) →
      ∃ v q : Space d,InCriticalSobolev v ∧ MeanZero v ∧ InCriticalSobolev q ∧ MeanZero q ∧
        0<secondVariation (x.1*spectralThreshold d) (potential hd (realEmbedding d x)) v ∧
        secondVariation (x.1*spectralThreshold d) (potential hd (realEmbedding d x)) q<0 := by
  have ht : Tendsto (fun x : Input d => potential hd (realEmbedding d x))
      (𝓝 (1,0)) (𝓝 0) := by
    have h := (potential_analytic hd).continuousAt.tendsto.comp (realEmbedding_tendsto d)
    have hb : potential hd (1,0)=0 := by
      simp [potential,GreenLocalBranch.correction_base]
    simpa only [hb,Function.comp_def] using h
  have hμ : ∀ᶠ x : Input d in 𝓝 (1,0),0<x.1 ∧ x.1<2 :=
    continuous_fst.continuousAt.preimage_mem_nhds (Ioo_mem_nhds (by norm_num) (by norm_num))
  filter_upwards [all_inactive_positive_directions hd,
    ht.eventually (ComplementHessian.exists_negative_direction hd),hμ] with x hp hn hμ
  intro hr ⟨i,hi⟩ ⟨j,hj⟩
  have hij : i≠j := by intro h; subst j; exact hi hj
  obtain ⟨v,hv,hvm,hvp⟩ := hp i j hij hr hi hj
  obtain ⟨q,hq,hqm,hqn⟩ := hn x.1 hμ.1 hμ.2.le
  exact ⟨v,q,hv,hvm,hq,hqm,hvp,hqn⟩

#print axioms real_graph_saddle
end BecknerOnofri.HighDim.LocalEleven.ActiveAmplitudeFactor
