module

public import Mathlib.Analysis.Analytic.OfScalars
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
open Filter
open scoped Topology NNReal ENNReal
namespace BecknerOnofri.AnalyticEvenSquare

def evenSeries (p : FormalMultilinearSeries ℝ ℝ ℝ) : FormalMultilinearSeries ℝ ℝ ℝ :=
  FormalMultilinearSeries.ofScalars ℝ (fun n => p.coeff (2*n))

theorem evenSeries_radius_pos (p : FormalMultilinearSeries ℝ ℝ ℝ) (hp : 0 < p.radius) :
    0 < (evenSeries p).radius := by
  obtain ⟨C,R,hC,hR,hbound⟩ := p.le_mul_pow_of_radius_pos hp
  let r : ℝ≥0 := ⟨(R^2)⁻¹,by positivity⟩
  have hr : 0 < (r : ℝ≥0∞) := by
    apply ENNReal.coe_pos.mpr
    change 0 < (R^2)⁻¹
    positivity
  apply hr.trans_le
  apply FormalMultilinearSeries.le_radius_of_bound _ C
  intro n
  have he : ‖evenSeries p n‖ = ‖p (2*n)‖ := by
    simp only [evenSeries,FormalMultilinearSeries.ofScalars_norm,
      FormalMultilinearSeries.norm_apply_eq_norm_coef,FormalMultilinearSeries.coeff_ofScalars]
  rw [he]
  calc
    _ ≤ (C*R^(2*n)) * (r:ℝ)^n := mul_le_mul_of_nonneg_right (hbound (2*n)) (by positivity)
    _ = C := by
      change (C*R^(2*n)) * ((R^2)⁻¹)^n = C
      rw [pow_mul, mul_assoc, ← mul_pow, mul_inv_cancel₀ (by positivity : R^2≠0),one_pow,mul_one]

theorem odd_coeff_zero {f : ℝ → ℝ} {p : FormalMultilinearSeries ℝ ℝ ℝ}
    (hp : HasFPowerSeriesAt f p 0) (he : ∀ᶠ t in 𝓝 (0:ℝ), f (-t)=f t) (n : ℕ) :
    p.coeff (2*n+1)=0 := by
  let L : ℝ →L[ℝ] ℝ := -ContinuousLinearMap.id ℝ ℝ
  have hp0 : HasFPowerSeriesAt f p (L 0) := by simpa [L] using hp
  have hn := hp0.compContinuousLinearMap (u := L)
  have hpeq := hn.eq_formalMultilinearSeries_of_eventually hp he
  have hv := congrArg (fun q : FormalMultilinearSeries ℝ ℝ ℝ => q (2*n+1) (fun _ => 1)) hpeq
  have hscale := (p (2*n+1)).map_smul_univ (fun _ => (-1:ℝ)) (fun _ => (1:ℝ))
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,
    smul_eq_mul,neg_mul,one_mul,Pi.one_apply] at hscale
  have hpow : (-1:ℝ)^(2*n+1) = -1 := by simp [pow_add,pow_mul]
  rw [hpow] at hscale
  have hv' : p (2*n+1) (fun _ => (-1:ℝ)) = p.coeff (2*n+1) := by
    exact hv
  change p (2*n+1) (fun _ => -1) = -1*p.coeff (2*n+1) at hscale
  linarith

theorem exists_analytic_square_factor {f : ℝ → ℝ} (hf : AnalyticAt ℝ f 0)
    (he : ∀ᶠ t in 𝓝 (0:ℝ), f (-t)=f t) :
    ∃ g : ℝ → ℝ, AnalyticAt ℝ g 0 ∧ ∀ᶠ t in 𝓝 (0:ℝ), f t=g (t^2) := by
  obtain ⟨p,r,hp⟩ := hf
  let q := evenSeries p
  have hq := q.hasFPowerSeriesOnBall (evenSeries_radius_pos p hp.radius_pos)
  have ho := odd_coeff_zero (show HasFPowerSeriesAt f p 0 from ⟨r,hp⟩) he
  refine ⟨q.sum,hq.analyticAt,?_⟩
  have ht : Tendsto (fun t : ℝ => t^2) (𝓝 0) (𝓝 0) := by
    have hc : Continuous (fun t : ℝ => t^2) := continuous_id.pow 2
    simpa using hc.continuousAt.tendsto (x := (0:ℝ))
  filter_upwards [Metric.eball_mem_nhds (0:ℝ) hp.r_pos,
    ht.eventually (Metric.eball_mem_nhds (0:ℝ) hq.r_pos)] with t htp htq
  have heven : HasSum (fun n => p (2*n) (fun _ => t)) (q.sum (t^2)) := by
    have hqs : HasSum (fun n => q n (fun _ => t^2)) (q.sum (t^2)) := by
      simpa only [zero_add] using hq.hasSum htq
    apply hqs.congr
    intro n
    simp only [FormalMultilinearSeries.apply_eq_pow_smul_coeff,q,evenSeries,
      FormalMultilinearSeries.coeff_ofScalars,smul_eq_mul,pow_mul]
  have hodd : HasSum (fun n => p (2*n+1) (fun _ => t)) 0 := by
    simpa only [FormalMultilinearSeries.apply_eq_pow_smul_coeff,ho,smul_zero] using
      (hasSum_zero : HasSum (fun _ : ℕ => (0:ℝ)) 0)
  have hall := heven.even_add_odd (f := fun n => p n (fun _ => t)) hodd
  have hraw := hp.hasSum htp
  simpa only [zero_add,add_zero] using hraw.unique hall

#print axioms exists_analytic_square_factor
end BecknerOnofri.AnalyticEvenSquare
