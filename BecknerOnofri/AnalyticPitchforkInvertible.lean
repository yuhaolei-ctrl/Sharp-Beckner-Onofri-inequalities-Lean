import BecknerOnofri.AnalyticPitchforkSquare

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter Asymptotics
open scoped Topology
namespace BecknerOnofri.AnalyticPitchfork

theorem exists_invertible_positive_squared_amplitude (D : Data) (hD : 0<D.coefficient) :
    ∃ r : ℝ → ℝ, AnalyticAt ℝ r 0 ∧ r 0=0 ∧ HasDerivAt r D.coefficient⁻¹ 0 ∧
      ((fun δ => r δ-δ/D.coefficient) =O[𝓝 (0:ℝ)] (fun δ => ‖δ‖^2)) ∧
      (∀ᶠ δ in 𝓝[>] (0:ℝ),0<r δ ∧ parameter D (Real.sqrt (r δ))=1/(1-δ)) ∧
      (∀ᶠ t in 𝓝 (0:ℝ), r (1-1/parameter D t)=t^2) := by
  obtain ⟨g,hg,hg0,hgd,he⟩ := exists_squared_parameter D
  let H : ℝ → ℝ := fun s => 1-1/g s
  have hH : AnalyticAt ℝ H 0 :=
    analyticAt_const.sub (analyticAt_const.div hg (by rw [hg0]; norm_num))
  have hH0 : H 0=0 := by simp [H,hg0]
  have hHd : HasDerivAt H D.coefficient 0 := by
    convert (hasDerivAt_const (0:ℝ) (1:ℝ)).sub
      ((hasDerivAt_const (0:ℝ) (1:ℝ)).div hgd (by rw [hg0]; norm_num)) using 1 <;>
      first | rfl | simp [H,hg0]
  obtain ⟨r,hr,hr0,hrd,hl,hright⟩ := exists_analytic_scalar_inverse hH hH0 hHd hD.ne'
  have hrpos : ∀ᶠ δ in 𝓝[>] (0:ℝ),0<r δ := by
    filter_upwards [hrd.tendsto_slope_zero_right.eventually (lt_mem_nhds (inv_pos.mpr hD)),
      self_mem_nhdsWithin] with δ hs hδ
    change 0<δ at hδ
    simp only [zero_add,hr0,sub_zero,smul_eq_mul] at hs
    by_contra hn
    have hp := mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr hδ.le) (le_of_not_gt hn)
    linarith
  have ht : Tendsto (fun δ => Real.sqrt (r δ)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have hc : ContinuousAt (fun δ => Real.sqrt (r δ)) 0 := hr.continuousAt.sqrt
    simpa only [hr0,Real.sqrt_zero] using hc.tendsto.mono_left nhdsWithin_le_nhds
  refine ⟨r,hr,hr0,hrd,?_,?_,?_⟩
  · simpa only [hr0,sub_zero,div_eq_mul_inv,mul_comm] using analytic_linear_remainder hr hrd
  · filter_upwards [hrpos,ht.eventually he,hright.filter_mono nhdsWithin_le_nhds]
      with δ hp heq hright
    refine ⟨hp,?_⟩
    rw [Real.sq_sqrt hp.le] at heq
    have hδ : 1-δ=1/g (r δ) := by change 1-1/g (r δ)=δ at hright; linarith
    rw [heq,hδ,one_div_one_div]

  · have ht2 : Tendsto (fun t : ℝ => t^2) (𝓝 0) (𝓝 0) := by
      have hc : Continuous (fun t : ℝ => t^2) := continuous_id.pow 2
      simpa using hc.continuousAt.tendsto (x := (0:ℝ))
    filter_upwards [he,ht2.eventually hl] with t he hl
    simpa only [H,← he] using hl

#print axioms exists_invertible_positive_squared_amplitude
end BecknerOnofri.AnalyticPitchfork
