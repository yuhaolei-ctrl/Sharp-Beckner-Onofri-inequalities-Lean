module

public import BecknerOnofri.LocalElevenCore.SubsetEnergyAlgebra
public import BecknerOnofri.AnalyticPitchforkPositive

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter Asymptotics
open scoped Topology
namespace BecknerOnofri.HighDim.LocalEleven.SubsetDiagonal
open ContinuousFirstShell ReducedQuarticExpansion UniformComplementBounds ReducedEnergyGradient

/-- The full physical functional on any supported graph with the analytic branch
amplitude has the manuscript's cubic error, not merely a formal quartic value. -/
theorem supported_energy_expansion {d : ℕ} (hd : 11≤d) (I : Finset (Fin d))
    (hI : I.Nonempty) {r : ℝ → ℝ} (hr : AnalyticAt ℝ r 0) (hr0 : r 0=0)
    (he : (fun δ => r δ-δ/coefficient I) =O[𝓝 (0:ℝ)] (fun δ => ‖δ‖^2))
    (hp : ∀ᶠ δ in 𝓝[>] (0:ℝ),0<r δ) :
    (fun δ => physicalReducedEnergy hd (1/(1-δ),line I (Real.sqrt (r δ))) -
      (-1/(4*branchQuarticCoefficient d I.card))*δ^2)
        =O[𝓝[>] (0:ℝ)] (fun δ => ‖δ‖^3) := by
  let n : ℝ := I.card
  let c : ℝ := coefficient I
  have hc : c≠0 := (coefficient_pos hd I hI).ne'
  have hrb : r =O[𝓝[>] (0:ℝ)] (fun δ => ‖δ‖) := by
    have h := hr.differentiableAt.isBigO_sub.norm_right
    simpa only [hr0,sub_zero] using h.mono nhdsWithin_le_nhds
  have hδ : (fun δ : ℝ => δ) =O[𝓝[>] (0:ℝ)] (fun δ => ‖δ‖) :=
    (isBigO_refl _ _).norm_right
  have hS : (fun δ => n*r δ) =O[𝓝[>] (0:ℝ)] (fun δ => ‖δ‖) :=
    hrb.const_mul_left n
  have hb : (fun δ => (n*r δ)^3+|δ| *(n*r δ)^2)
      =O[𝓝[>] (0:ℝ)] (fun δ => ‖δ‖^3) := by
    have h1 := hS.pow 3
    have h2 := hδ.norm_left.mul (hS.pow 2)
    have h2' : (fun δ => |δ| *(n*r δ)^2)
        =O[𝓝[>] (0:ℝ)] (fun δ => ‖δ‖^3) := by
      convert h2 using 1 <;> (first | rfl | (ext δ; simp only [Real.norm_eq_abs]; ring))
    exact h1.add h2'
  have ht : Tendsto (fun δ => (1/(1-δ),line I (Real.sqrt (r δ))))
      (𝓝[>] (0:ℝ)) (𝓝 (1,(0 : Coordinates d))) := by
    have hμ : ContinuousAt (fun δ : ℝ => 1/(1-δ)) 0 :=
      continuousAt_const.div (continuousAt_const.sub continuousAt_id) (by norm_num)
    have hz : ContinuousAt (fun δ => line I (Real.sqrt (r δ))) 0 :=
      (line I).continuous.continuousAt.comp (hr.continuousAt.sqrt)
    have h := (hμ.prodMk hz).tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
    simpa only [hr0,Real.sqrt_zero,map_zero,sub_zero,div_one] using h
  have hmain := ((physicalReducedEnergy_quartic_paper hd).comp_tendsto ht)
  have hnorm : (fun δ => squaredAmplitude (line I (Real.sqrt (r δ))))
      =ᶠ[𝓝[>] (0:ℝ)] (fun δ => n*r δ) := by
    filter_upwards [hp] with δ hp
    simp only [squaredAmplitude,line_square_sum,Real.sq_sqrt hp.le,n]
  have hquartic : (fun δ => quarticValue (line I (Real.sqrt (r δ))))
      =ᶠ[𝓝[>] (0:ℝ)] (fun δ => -n*c/2*(r δ)^2) := by
    filter_upwards [hp] with δ hp
    rw [quartic_line,show (Real.sqrt (r δ))^4=((Real.sqrt (r δ))^2)^2 by ring,
      Real.sq_sqrt hp.le]
  have hrem : (fun δ => physicalReducedEnergy hd (1/(1-δ),line I (Real.sqrt (r δ))) -
      δ*(n*r δ)+n*c/2*(r δ)^2) =O[𝓝[>] (0:ℝ)] (fun δ => ‖δ‖^3) := by
    have hb' : (fun δ => (squaredAmplitude (line I (Real.sqrt (r δ))))^3+
        |1-1/(1/(1-δ))| *(squaredAmplitude (line I (Real.sqrt (r δ))))^2)
        =O[𝓝[>] (0:ℝ)] (fun δ => ‖δ‖^3) := by
      apply hb.congr' ?_ Filter.EventuallyEq.rfl
      filter_upwards [hnorm] with δ h
      rw [h,one_div_one_div]
      congr 3 <;> ring
    apply (hmain.trans hb').congr' ?_ Filter.EventuallyEq.rfl
    filter_upwards [hnorm,hquartic] with δ hs hq
    dsimp only [Function.comp_def]
    rw [hs,hq,one_div_one_div]
    ring
  have herror : (fun δ => -n*c/2*(r δ-δ/c)^2)
      =O[𝓝[>] (0:ℝ)] (fun δ => ‖δ‖^3) := by
    have h := ((he.mono (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))).pow 2).const_mul_left (-n*c/2)
    have h' : (fun δ => -n*c/2*(r δ-δ/c)^2)
        =O[𝓝[>] (0:ℝ)] (fun δ => ‖δ‖^4) := by
      convert h using 1 <;> (first | rfl | (ext δ; ring))
    exact h'.trans ((norm_pow_bigO_of_le (by norm_num : 3≤4)).mono nhdsWithin_le_nhds)
  apply (hrem.add herror).congr_left
  intro δ
  rw [← support_pressure_coefficient I hI]
  change _ = _
  dsimp only [n,c]
  field_simp [show coefficient I≠0 from hc]
  <;> ring

#print axioms supported_energy_expansion
end BecknerOnofri.HighDim.LocalEleven.SubsetDiagonal
