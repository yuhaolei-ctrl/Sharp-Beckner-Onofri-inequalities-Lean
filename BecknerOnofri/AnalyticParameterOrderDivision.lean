module

public import BecknerOnofri.AnalyticParameterDivision
public import BecknerOnofri.AnalyticDerivativeOrder

@[expose] public section

/-! Joint analytic division by any finite power of a scalar coordinate,
from actual transverse vanishing order. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter Asymptotics
open scoped Topology
namespace BecknerOnofri.AnalyticParameterDivision

theorem scalar_division_order {f g : ℝ → ℝ} {N : ℕ}
    (hf : AnalyticAt ℝ f 0) (hg : AnalyticAt ℝ g 0)
    (he : ∀ᶠ t in 𝓝 (0:ℝ), f t=t*g t)
    (ho : f =O[𝓝 0] (fun t : ℝ => ‖t‖^(N+1))) :
    g =O[𝓝 0] (fun t : ℝ => ‖t‖^N) := by
  by_cases hN : N=0
  · simpa only [hN,pow_zero] using hg.continuousAt.tendsto.isBigO_one ℝ
  have hder := analytic_deriv_order hf ho
  have hd0 : deriv f 0=0 := by
    have hder' : deriv f =O[𝓝 0] (fun t : ℝ => ‖t-0‖^N) := by simpa only [sub_zero] using hder
    exact hder'.eq_zero_of_norm_pow hN
  have hh : HasDerivAt (fun t : ℝ => t*g t) (g 0) 0 := by
    convert (hasDerivAt_id (0:ℝ)).mul hg.differentiableAt.hasDerivAt using 1 <;> first | rfl | simp
  have hg0 : g 0=0 := (hh.congr_of_eventuallyEq he).deriv.symm.trans hd0
  obtain ⟨C,hC⟩ := ho.exists_pos
  apply IsBigO.of_bound C
  filter_upwards [hC.2.bound,he] with t ht he
  by_cases ht0 : t=0
  · simp [ht0,hg0,hN]
  · rw [he,norm_mul,norm_pow,norm_norm,pow_succ] at ht
    rw [norm_pow,norm_norm]
    apply le_of_mul_le_mul_right (a := ‖t‖) (a0 := norm_pos_iff.mpr ht0)
    calc
      _ = ‖t‖*‖g t‖ := by ring
      _ ≤ C*(‖t‖^N*‖t‖) := ht
      _ = _ := by ring

/-- The value at the removed singularity is the actual leading coefficient. -/
theorem power_factor_value {f g : ℝ → ℝ} {N : ℕ} {c : ℝ}
    (hg : ContinuousAt g 0) (he : ∀ᶠ t in 𝓝 (0:ℝ), f t=t^N*g t)
    (ho : (fun t => f t-t^N*c) =O[𝓝 0] (fun t : ℝ => ‖t‖^(N+1))) : g 0=c := by
  obtain ⟨C,hC⟩ := ho.exists_pos
  have hb : (fun t => g t-c) =O[𝓝[≠] (0:ℝ)] (fun t => t) := by
    apply IsBigO.of_bound C
    filter_upwards [hC.2.bound.filter_mono nhdsWithin_le_nhds,
      he.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with t ht he hne
    have ht0 : t≠0 := by simpa using hne
    have hfactor : f t-t^N*c=t^N*(g t-c) := by rw [he]; ring
    rw [hfactor,norm_mul,norm_pow,norm_pow,norm_norm,pow_succ] at ht
    apply le_of_mul_le_mul_left (a := ‖t‖^N) (a0 := pow_pos (norm_pos_iff.mpr ht0) _)
    calc
      _ ≤ C*(‖t‖^N*‖t‖) := ht
      _ = _ := by ring
  have hzero : Tendsto (fun t => g t-c) (𝓝[≠] (0:ℝ)) (𝓝 0) :=
    hb.trans_tendsto (tendsto_id.mono_left nhdsWithin_le_nhds)
  have hvalue : Tendsto (fun t => g t-c) (𝓝[≠] (0:ℝ)) (𝓝 (g 0-c)) :=
    (hg.tendsto.sub_const c).mono_left nhdsWithin_le_nhds
  have hh := tendsto_nhds_unique hvalue hzero
  exact sub_eq_zero.mp hh

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Analytic Hadamard division of arbitrary finite order with arbitrary real
normed parameters. The only extra input is the actual slice vanishing order. -/
theorem exists_analytic_power_factor {f : E × ℝ → ℝ} {a : E} (N : ℕ)
    (hf : AnalyticAt ℝ f (a,0))
    (ho : ∀ᶠ r in 𝓝 a, (fun t : ℝ => f (r,t)) =O[𝓝 0] (fun t : ℝ => ‖t‖^N)) :
    ∃ g : E × ℝ → ℝ, AnalyticAt ℝ g (a,0) ∧
      ∀ᶠ x in 𝓝 (a,(0:ℝ)), f x=x.2^N*g x := by
  induction N generalizing f with
  | zero => exact ⟨f,hf,Eventually.of_forall (fun x => by simp)⟩
  | succ N ih =>
    have haxis : ∀ᶠ r in 𝓝 a, f (r,0)=0 := by
      filter_upwards [ho] with r hr
      have hr' : (fun t : ℝ => f (r,t)) =O[𝓝 0] (fun t : ℝ => ‖t-0‖^(N+1)) := by
        simpa only [sub_zero] using hr
      exact hr'.eq_zero_of_norm_pow (by omega)
    obtain ⟨q,hq,he⟩ := exists_analytic_factor hf haxis
    have ht : Tendsto (fun r : E => (r,(0:ℝ))) (𝓝 a) (𝓝 (a,(0:ℝ))) :=
      (continuous_id.prodMk continuous_const).continuousAt
    have horder : ∀ᶠ r in 𝓝 a,
        (fun t : ℝ => q (r,t)) =O[𝓝 0] (fun t : ℝ => ‖t‖^N) := by
      filter_upwards [ho,ht.eventually hf.eventually_analyticAt,
        ht.eventually hq.eventually_analyticAt,ht.eventually he.eventually_nhds] with r hr hfr hqr her
      have hi : AnalyticAt ℝ (fun t : ℝ => (r,t)) 0 := analyticAt_const.prod analyticAt_id
      have hslice : Tendsto (fun t : ℝ => (r,t)) (𝓝 0) (𝓝 (r,(0:ℝ))) :=
        (continuous_const.prodMk continuous_id).continuousAt
      exact scalar_division_order (hfr.comp hi) (hqr.comp hi) (hslice.eventually her) hr
    obtain ⟨g,hg,heg⟩ := ih hq horder
    refine ⟨g,hg,?_⟩
    filter_upwards [he,heg] with x hx hqx
    rw [hx,hqx,pow_succ]
    ring

#print axioms exists_analytic_power_factor
end BecknerOnofri.AnalyticParameterDivision
