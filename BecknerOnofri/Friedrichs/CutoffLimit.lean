import BecknerOnofri.Friedrichs.BoundaryCutoff
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! Endpoint cutoffs converge in weighted L2 and their derivative error
vanishes for functions with the genuine linear endpoint vanishing bound. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace BecknerOnofri.Friedrichs

lemma boundaryCutoff_local_one {δ t : ℝ} (hδ : 0<δ)
    (hl : 2*δ<t) (hr : t<Real.pi-2*δ) :
    boundaryCutoff δ =ᶠ[𝓝 t] (fun _ => (1:ℝ)) := by
  filter_upwards [eventually_gt_nhds hl,eventually_lt_nhds hr] with x hx hy
  exact boundaryCutoff_one hδ ⟨hx.le,hy.le⟩

lemma boundaryCutoff_deriv_zero_core {δ t : ℝ} (hδ : 0<δ)
    (hl : 2*δ<t) (hr : t<Real.pi-2*δ) : deriv (boundaryCutoff δ) t=0 := by
  rw [(boundaryCutoff_local_one hδ hl hr).deriv_eq,deriv_const]

lemma boundaryCutoff_eventually_one {t : ℝ} (ht : t∈Ioo 0 Real.pi) :
    ∀ᶠ δ in 𝓝[>] (0:ℝ), boundaryCutoff δ t=1 ∧ deriv (boundaryCutoff δ) t=0 := by
  have hl : (0:ℝ)<t/2 := by linarith [ht.1]
  have hr : (0:ℝ)<(Real.pi-t)/2 := by linarith [ht.2]
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds hl).filter_mono nhdsWithin_le_nhds,
    (eventually_lt_nhds hr).filter_mono nhdsWithin_le_nhds] with δ hδ hleft hright
  have hδ' : 0<δ := hδ
  have h1 : 2*δ<t := by linarith
  have h2 : t<Real.pi-2*δ := by linarith
  exact ⟨boundaryCutoff_one hδ' ⟨h1.le,h2.le⟩,boundaryCutoff_deriv_zero_core hδ' h1 h2⟩

lemma cutoff_weighted_integral_tendsto_zero (f : ℝ → ℝ)
    (hf : IntegrableOn f (Ioo 0 Real.pi)) :
    Tendsto (fun δ : ℝ => ∫ t in Ioo 0 Real.pi,(1-boundaryCutoff δ t)^2*f t)
      (𝓝[>] 0) (𝓝 0) := by
  have hmeas : ∀ᶠ δ : ℝ in 𝓝[>] 0,
      AEStronglyMeasurable (fun t => (1-boundaryCutoff δ t)^2*f t)
        (volume.restrict (Ioo 0 Real.pi)) :=
    Eventually.of_forall (fun δ =>
      ((continuous_const.sub (boundaryCutoff_smooth δ).continuous).pow 2).aestronglyMeasurable.mul
        hf.aestronglyMeasurable)
  have hbound : ∀ᶠ δ : ℝ in 𝓝[>] 0, ∀ᵐ t ∂volume.restrict (Ioo 0 Real.pi),
      ‖(1-boundaryCutoff δ t)^2*f t‖≤|f t| := by
    apply Eventually.of_forall
    intro δ
    apply ae_of_all
    intro t
    have hχ := boundaryCutoff_mem δ t
    have hsq : (1-boundaryCutoff δ t)^2≤1 := by nlinarith [hχ.1,hχ.2]
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (sq_nonneg _)]
    exact mul_le_of_le_one_left (abs_nonneg _) hsq
  have hlim : ∀ᵐ t ∂volume.restrict (Ioo 0 Real.pi),
      Tendsto (fun δ : ℝ => (1-boundaryCutoff δ t)^2*f t) (𝓝[>] 0) (𝓝 (0:ℝ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    apply tendsto_const_nhds.congr'
    filter_upwards [boundaryCutoff_eventually_one ht] with δ hδ
    simp [hδ.1]
  simpa only [integral_zero] using
    tendsto_integral_filter_of_dominated_convergence (fun t => |f t|) hmeas hbound hf.abs hlim

lemma cutoff_derivative_times_vanishing_bound {h : ℝ → ℝ} {C L δ t : ℝ}
    (hC : 0≤C) (hL : 0≤L) (hδ : 0<δ) (ht : t∈Ioo 0 Real.pi)
    (hder : |deriv (boundaryCutoff δ) t|≤C/δ)
    (hleft : |h t|≤L*t) (hright : |h t|≤L*(Real.pi-t)) :
    |deriv (boundaryCutoff δ) t*h t|≤2*C*L := by
  by_cases hcore : 2*δ<t ∧ t<Real.pi-2*δ
  · rw [boundaryCutoff_deriv_zero_core hδ hcore.1 hcore.2,zero_mul,abs_zero]
    positivity
  have hh : |h t|≤2*L*δ := by
    by_cases hl : 2*δ<t
    · have hr : Real.pi-2*δ≤t := le_of_not_gt (fun h => hcore ⟨hl,h⟩)
      nlinarith
    · have hl' : t≤2*δ := le_of_not_gt hl
      nlinarith
  rw [abs_mul]
  calc
    _ ≤ (C/δ)*(2*L*δ) := mul_le_mul hder hh (abs_nonneg _) (div_nonneg hC hδ.le)
    _ = _ := by field_simp <;> ring

lemma cutoff_derivative_energy_tendsto_zero {h : ℝ → ℝ} (hc : Continuous h)
    {L : ℝ} (hL : 0≤L)
    (hvanish : ∀ t∈Ioo 0 Real.pi, |h t|≤L*t ∧ |h t|≤L*(Real.pi-t)) :
    Tendsto (fun δ : ℝ => ∫ t in Ioo 0 Real.pi,(deriv (boundaryCutoff δ) t*h t)^2)
      (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨C,hC,hder⟩ := boundaryCutoff_deriv_bound
  have hmeas : ∀ᶠ δ : ℝ in 𝓝[>] 0,
      AEStronglyMeasurable (fun t => (deriv (boundaryCutoff δ) t*h t)^2)
        (volume.restrict (Ioo 0 Real.pi)) := by
    apply Eventually.of_forall
    intro δ
    have hχ := ((contDiff_infty_iff_deriv.mp (boundaryCutoff_smooth δ)).2).continuous
    exact ((hχ.mul hc).pow 2).aestronglyMeasurable
  have hbound : ∀ᶠ δ : ℝ in 𝓝[>] 0, ∀ᵐ t ∂volume.restrict (Ioo 0 Real.pi),
      ‖(deriv (boundaryCutoff δ) t*h t)^2‖≤(2*C*L)^2 := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr
      (cutoff_derivative_times_vanishing_bound hC hL hδ ht (hder δ hδ t)
        (hvanish t ht).1 (hvanish t ht).2)
  have hlim : ∀ᵐ t ∂volume.restrict (Ioo 0 Real.pi),
      Tendsto (fun δ : ℝ => (deriv (boundaryCutoff δ) t*h t)^2) (𝓝[>] 0) (𝓝 (0:ℝ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    apply tendsto_const_nhds.congr'
    filter_upwards [boundaryCutoff_eventually_one ht] with δ hδ
    simp [hδ.2]
  simpa only [integral_zero] using
    tendsto_integral_filter_of_dominated_convergence (fun _ => (2*C*L)^2) hmeas hbound
      (((continuous_const : Continuous (fun _ : ℝ => (2*C*L)^2)).integrableOn_Icc).mono_set
        Ioo_subset_Icc_self) hlim

#print axioms cutoff_weighted_integral_tendsto_zero
#print axioms cutoff_derivative_energy_tendsto_zero
end BecknerOnofri.Friedrichs
