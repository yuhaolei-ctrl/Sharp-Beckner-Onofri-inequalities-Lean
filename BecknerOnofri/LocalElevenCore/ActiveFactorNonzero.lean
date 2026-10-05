module

public import BecknerOnofri.LocalElevenCore.ActiveFactorLine

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter Asymptotics
open scoped Topology
namespace BecknerOnofri.HighDim.LocalEleven.ActiveAmplitudeFactor
open AmplitudeLinearization

theorem squared_difference_factor_value {d : ℕ} (hd : 11≤d) (i j : Fin d) (hij : i≠j)
    {H : Input d → ℝ} (hH : AnalyticAt ℝ H (1,0))
    (he : ∀ᶠ x : Input d in 𝓝 (1,0),factor hd i x-factor hd j x=(x.2 i^2-x.2 j^2)*H x) :
    H (1,0)=quarticB d-2*quarticA d := by
  let path : ℝ → Input d := fun t => (1,twoLine i j t)
  have hc : ContinuousAt path 0 := continuousAt_const.prodMk ((twoLine i j).continuous.continuousAt)
  have ht : Tendsto path (𝓝 0) (𝓝 (1,0)) := by
    simpa only [path,map_zero] using hc.tendsto
  let F : ℝ → ℝ := fun t => scalar hd i (path t)-scalar hd j (path t)/2
  let G : ℝ → ℝ := fun t => -3*H (path t)
  have hH' : ContinuousAt H (path 0) := by
    simpa only [path,map_zero] using hH.continuousAt
  have hG : ContinuousAt G 0 := (hH'.comp hc).const_mul (-3)
  have hfactor : ∀ᶠ t in 𝓝 (0:ℝ),F t=t^3*G t := by
    filter_upwards [ht.eventually he,ht.eventually (scalar_eq_coordinate_mul_factor hd i),
      ht.eventually (scalar_eq_coordinate_mul_factor hd j)] with t hdiff hi hj
    have hi' : (path t).2 i=t := by simp [path]
    have hj' : (path t).2 j=2*t := by simp [path,hij.symm]
    rw [hi',hj'] at hdiff
    rw [hi'] at hi
    rw [hj'] at hj
    dsimp only [F,G]
    calc
      _=t*(factor hd i (path t)-factor hd j (path t)) := by rw [hi,hj]; ring
      _=t*((t^2-(2*t)^2)*H (path t)) := by rw [hdiff]
      _=_ := by ring
  have ho : (fun t => F t-t^3*(-3*(quarticB d-2*quarticA d)))
      =O[𝓝 (0:ℝ)] (fun t => ‖t‖^4) := by
    apply ((scalar_two_line_cubic hd i j hij).trans
      (norm_pow_bigO_of_le (by norm_num : 4≤5))).congr_left
    intro t
    dsimp only [F,path]
    ring
  have hv := AnalyticParameterDivision.power_factor_value hG hfactor ho
  simp only [G,path,map_zero] at hv
  linarith

theorem exists_nonzero_squared_difference_factor {d : ℕ} (hd : 11≤d)
    (i j : Fin d) (hij : i≠j) :
    ∃ H : Input d → ℝ, AnalyticAt ℝ H (1,0) ∧ H (1,0)=quarticB d-2*quarticA d ∧
      ∀ᶠ x : Input d in 𝓝 (1,0),0<H x ∧
        factor hd i x-factor hd j x=(x.2 i^2-x.2 j^2)*H x := by
  obtain ⟨H,hH,he⟩ := exists_squared_difference_factor hd i j hij
  have hv := squared_difference_factor_value hd i j hij hH he
  have hp : 0<H (1,0) := by
    rw [hv]
    have ha := LocalQuartic.quarticA_negative hd
    have hb := LocalQuartic.quarticB_positive hd
    linarith
  exact ⟨H,hH,hv,(hH.continuousAt.tendsto.eventually (lt_mem_nhds hp)).and he⟩

#print axioms exists_nonzero_squared_difference_factor
end BecknerOnofri.HighDim.LocalEleven.ActiveAmplitudeFactor
