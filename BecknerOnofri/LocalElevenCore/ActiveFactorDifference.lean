module

public import BecknerOnofri.LocalElevenCore.ActivePairCoordinates
public import BecknerOnofri.AnalyticSquaredDifference

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter
open scoped Topology
namespace BecknerOnofri.HighDim.LocalEleven.ActiveAmplitudeFactor

theorem exists_squared_difference_factor {d : ℕ} (hd : 11≤d) (i j : Fin d) (hij : i≠j) :
    ∃ H : Input d → ℝ, AnalyticAt ℝ H (1,0) ∧
      ∀ᶠ x : Input d in 𝓝 (1,0),factor hd i x-factor hd j x=(x.2 i^2-x.2 j^2)*H x := by
  let F : (Input d × ℝ) × ℝ → ℝ := fun x => factor hd i (pairInput i j x)-factor hd j (pairInput i j x)
  have hF : AnalyticAt ℝ F (((1,0),0),0) := by
    have hi : AnalyticAt ℝ (factor hd i) (pairInput i j (((1,0),0),0)) := by
      simpa only [pairInput_base] using factor_analytic hd i
    have hj : AnalyticAt ℝ (factor hd j) (pairInput i j (((1,0),0),0)) := by
      simpa only [pairInput_base] using factor_analytic hd j
    exact (hi.sub hj).comp (f := pairInput i j) ((pairInput i j).analyticAt _)
  have hs : ∀ᶠ x : (Input d × ℝ) × ℝ in 𝓝 (((1,0),0),0),
      F ((x.1.1,x.2),x.1.2) = -F x := by
    filter_upwards [(pairInput_tendsto i j).eventually (factor_permutation hd (Equiv.swap i j) i),
      (pairInput_tendsto i j).eventually (factor_permutation hd (Equiv.swap i j) j)] with x hi hj
    simp only [Equiv.swap_apply_left,Equiv.swap_apply_right] at hi hj
    dsimp only [F]
    rw [pairInput_swap hij,hi,hj]
    ring
  have he : ∀ᶠ x : (Input d × ℝ) × ℝ in 𝓝 (((1,0),0),0),F (x.1,-x.2)=F x := by
    filter_upwards [(pairInput_tendsto i j).eventually (factor_flip hd j i),
      (pairInput_tendsto i j).eventually (factor_flip hd j j)] with x hi hj
    dsimp only [F]
    rw [pairInput_flip hij,hi,hj]
  obtain ⟨H,hH,hfactor⟩ := AnalyticParameterDivision.exists_analytic_squared_difference_factor hF hs he
  have hbase : extractPair i j (1,0)=(((1,0),0),0) := rfl
  have ho : AnalyticAt ℝ H (extractPair i j (1,0)) := by simpa only [hbase] using hH
  refine ⟨fun x => H (extractPair i j x),
    ho.comp (f := extractPair i j) ((extractPair i j).analyticAt _),?_⟩
  have ht : Tendsto (extractPair i j) (𝓝 (1,0)) (𝓝 (((1,0),0),0)) := by
    simpa only [hbase] using (extractPair i j).continuous.tendsto (1,0)
  filter_upwards [ht.eventually hfactor] with x hx
  dsimp only [F] at hx
  rw [pairInput_extractPair] at hx
  simpa only [extractPair_apply] using hx

#print axioms exists_squared_difference_factor
end BecknerOnofri.HighDim.LocalEleven.ActiveAmplitudeFactor
