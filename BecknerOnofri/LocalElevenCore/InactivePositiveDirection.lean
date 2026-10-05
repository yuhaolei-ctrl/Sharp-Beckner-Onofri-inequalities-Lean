import BecknerOnofri.LocalElevenCore.InactiveDerivative

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter
open scoped Topology BigOperators ComplexConjugate
namespace BecknerOnofri.HighDim.LocalEleven.ActiveAmplitudeFactor
open ContinuousGibbs ContinuousFirstShell ContinuousComplement
open AmplitudeLinearization RescaledReducedEquation ReducedEquation GraphHessian

/-- Each inactive coordinate supplies a genuine positive second-variation direction
of the physical functional on a nonzero reduced critical graph. -/
theorem inactive_positive_direction {d : ℕ} (hd : 11≤d) (i j : Fin d) (hij : i≠j) :
    ∀ᶠ x : Input d in 𝓝 (1,0),reduced hd (realEmbedding d x)=0 → x.2 i≠0 → x.2 j=0 →
      ∃ v : Space d,InCriticalSobolev v ∧ MeanZero v ∧
        0<secondVariation (x.1*spectralThreshold d) (potential hd (realEmbedding d x)) v := by
  classical
  have hpos : ∀ᶠ x : Input d in 𝓝 (1,0),0<x.1 :=
    continuous_fst.continuousAt.preimage_mem_nhds (Ioi_mem_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [inactive_factor_negative hd i j hij,inactive_derivative hd j,
    (realEmbedding_tendsto d).eventually (secondVariation_tangentMap hd),
    (realEmbedding_tendsto d).eventually (tangentMap_equation hd),hpos]
    with x hn hjac hH hT hμ
  intro hr hai haj
  let h : Coordinates d := realCoordinates d (Pi.single j 1)
  let v : Space d := tangentMap hd (realEmbedding d x) h
  obtain ⟨w,hw,he,hcrit⟩ := hT h
  have hm : MeanZero v := by
    change MeanZero (tangentMap hd (realEmbedding d x) h)
    rw [hw]
    exact mean_reconstruction _
  have hb : h=Pi.single j (1:ℂ) := by
    ext l
    by_cases hl : l=j <;> simp [h,realCoordinates_apply,Pi.single_apply,hl]
  have heq : (∑ l,conj (h l)*
      (fderiv ℝ (fun z => reduced hd (x.1,z)) (realCoordinates d x.2) h) l).re=factor hd j x := by
    have hs : (∑ l,conj (h l)*
        (fderiv ℝ (fun z => reduced hd (x.1,z)) (realCoordinates d x.2) h) l)=
        (fderiv ℝ (fun z => reduced hd (x.1,z)) (realCoordinates d x.2) h) j := by
      rw [hb]
      simp [Pi.single_apply]
    rw [hs]
    exact hjac haj
  have hvar := hH h
  change secondVariation (x.1*spectralThreshold d) (potential hd (realEmbedding d x)) v = _ at hvar
  change _=-(2/x.1)*(∑ l,conj (h l)*
    (fderiv ℝ (fun z => reduced hd (x.1,z)) (realCoordinates d x.2) h) l).re at hvar
  rw [heq] at hvar
  refine ⟨v,hcrit,hm,?_⟩
  rw [hvar]
  exact mul_pos_of_neg_of_neg (neg_neg_of_pos (div_pos (by norm_num) hμ)) (hn hr hai haj)

#print axioms inactive_positive_direction
end BecknerOnofri.HighDim.LocalEleven.ActiveAmplitudeFactor
