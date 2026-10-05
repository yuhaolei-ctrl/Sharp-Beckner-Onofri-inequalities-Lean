import BecknerOnofri.LocalElevenCore.SubsetDiagonal

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter Asymptotics
open scoped Topology BigOperators
namespace BecknerOnofri.HighDim.LocalEleven.SubsetDiagonal
open ContinuousFirstShell ReducedEquation ReducedCubicExpansion

theorem line_square_sum {d : ℕ} (I : Finset (Fin d)) (t : ℝ) :
    (∑ i,‖line I t i‖^2)=(I.card:ℝ)*t^2 := by
  have he (i : Fin d) : ‖line I t i‖^2 = if i∈I then t^2 else 0 := by
    by_cases hi : i∈I <;> simp [line_apply,hi,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  simp_rw [he]
  simp

theorem cubic_line {d : ℕ} (hd : 11≤d) (I : Finset (Fin d)) (j : Fin d)
    (hj : j∈I) (t : ℝ) :
    cubicModel hd (line I t) j = ((coefficient I*t^3 : ℝ):ℂ) := by
  rw [cubicModel_apply,line_square_sum,line_apply,if_pos hj]
  simp only [Complex.norm_real,Real.norm_eq_abs,sq_abs]
  unfold coefficient
  push_cast
  ring

theorem residual_axis {d : ℕ} (hd : 11≤d) (I : Finset (Fin d)) (j : Fin d) :
    ∀ᶠ μ in 𝓝 (1:ℝ),residual hd I j (μ,0)=0 := by
  filter_upwards [potential_axis hd] with μ hμ
  simp only [residual,embedding_apply,map_zero,reduced,hμ,
    ContinuousGibbs.normalized_zero,coordinates_one,smul_zero,sub_zero,
    Pi.zero_apply,Complex.zero_re]

theorem residual_derivative_axis {d : ℕ} (hd : 11≤d) (I : Finset (Fin d))
    (j : Fin d) (hj : j∈I) :
    ∀ᶠ μ in 𝓝 (1:ℝ), HasDerivAt (fun t => residual hd I j (μ,t)) (1-μ) 0 := by
  filter_upwards [reduced_derivative_axis hd] with μ hμ
  have hi : HasFDerivAt (𝕜 := ℝ) (fun t : ℝ => (μ,line I t))
      ((0 : ℝ →L[ℝ] ℝ).prod (line I)) 0 :=
    (hasFDerivAt_const μ (0:ℝ)).prodMk (line I).hasFDerivAt
  let ev : Coordinates d →L[ℝ] ℝ := Complex.reCLM.comp (ContinuousLinearMap.proj j)
  have hμ' : HasFDerivAt (reduced hd)
      ((1-μ) • ContinuousLinearMap.snd ℝ ℝ (Coordinates d)) (μ,line I 0) := by
    simpa only [map_zero] using hμ
  have he := ev.hasFDerivAt (x := reduced hd (μ,line I 0))
  have hh := he.comp (0:ℝ) (hμ'.comp (0:ℝ) hi)
  convert! hh.hasDerivAt using 1
  simp [residual,embedding_apply,ev,ContinuousLinearMap.comp_apply,hj]

theorem residual_odd {d : ℕ} (hd : 11≤d) (I : Finset (Fin d)) (j : Fin d) :
    ∀ᶠ x in 𝓝 ((1,0):ℝ×ℝ),residual hd I j (x.1,-x.2) = -residual hd I j x := by
  filter_upwards [(embedding_tendsto I).eventually (ContinuousSymmetry.reduced_neg hd)] with x hx
  have h := congrArg (fun z : Coordinates d => (z j).re) hx
  simpa only [residual,embedding_apply,map_neg,Pi.neg_apply,Complex.neg_re] using h

theorem residual_cubic {d : ℕ} (hd : 11≤d) (I : Finset (Fin d)) (j : Fin d) (hj : j∈I) :
    (fun t : ℝ => residual hd I j (1,t)-coefficient I*t^3)
      =O[𝓝 0] (fun t => ‖t‖^5) := by
  have ht : Tendsto (line I) (𝓝 (0:ℝ)) (𝓝 (0 : Coordinates d)) := by
    simpa only [map_zero] using (line I).continuous.continuousAt.tendsto (x := (0:ℝ))
  have hb : (fun t : ℝ => reduced hd (1,line I t)-cubicModel hd (line I t))
      =O[𝓝 0] (fun t => ‖t‖^5) := by
    exact ((reduced_cubic_expansion_fifth hd).comp_tendsto ht).trans
      (((line I).isBigO_comp (fun t : ℝ => t) (𝓝 0)).norm_left.norm_right.pow 5)
  let ev : Coordinates d →L[ℝ] ℝ := Complex.reCLM.comp (ContinuousLinearMap.proj j)
  have he := ((ev.isBigO_comp _ _).trans hb)
  apply he.congr_left
  intro t
  simp only [ev,ContinuousLinearMap.comp_apply,ContinuousLinearMap.proj_apply,
    Complex.reCLM_apply,Pi.sub_apply,Complex.sub_re,cubic_line hd I j hj,
    Complex.ofReal_re,residual,embedding_apply]

#print axioms residual_cubic
#print axioms residual_derivative_axis
end BecknerOnofri.HighDim.LocalEleven.SubsetDiagonal
