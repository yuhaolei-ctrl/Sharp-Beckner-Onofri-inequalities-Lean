module

public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Analytic.ChangeOrigin
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Normed.Module.Multilinear.Curry

@[expose] public section

/-! Jointly analytic division by a scalar coordinate, with Banach parameters. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter
open scoped Topology BigOperators ENNReal NNReal
namespace BecknerOnofri.AnalyticParameterDivision

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private def axisProjection : E × ℝ →L[ℝ] E × ℝ :=
  (ContinuousLinearMap.fst ℝ E ℝ).prod 0

private theorem axisProjection_apply (v : E × ℝ) : axisProjection v = (v.1, 0) := rfl

private theorem axisProjection_norm_le (v : E × ℝ) : ‖axisProjection v‖ ≤ ‖v‖ := by
  simpa [axisProjection_apply, Prod.norm_def] using norm_fst_le v

private def slotMap {n : ℕ} (j : Fin (n+1)) (i : Fin n) : E × ℝ →L[ℝ] E × ℝ :=
  if j.succAbove i < j then ContinuousLinearMap.id ℝ (E × ℝ) else axisProjection

private theorem slotMap_norm_le {n : ℕ} (j : Fin (n+1)) (i : Fin n) :
    ‖slotMap (E := E) j i‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  dsimp only [slotMap]
  split_ifs
  · simp
  · simpa only [one_mul] using axisProjection_norm_le v

private def dividedTerm (p : FormalMultilinearSeries ℝ (E × ℝ) ℝ)
    (n : ℕ) (j : Fin (n+1)) : (E × ℝ) [×n]→L[ℝ] ℝ :=
  ((p (n+1)).curryMid j (0,1)).compContinuousLinearMap (slotMap j)

private def dividedSeries (p : FormalMultilinearSeries ℝ (E × ℝ) ℝ) :
    FormalMultilinearSeries ℝ (E × ℝ) ℝ := fun n => ∑ j : Fin (n+1), dividedTerm p n j

private theorem dividedTerm_norm (p : FormalMultilinearSeries ℝ (E × ℝ) ℝ)
    (n : ℕ) (j : Fin (n+1)) : ‖dividedTerm p n j‖ ≤ ‖p (n+1)‖ := by
  have hprod : (∏ i : Fin n, ‖slotMap (E := E) j i‖) ≤ 1 := by
    simpa using Finset.prod_le_prod₀ (fun i _ => norm_nonneg (slotMap (E := E) j i))
      (fun i _ => slotMap_norm_le (E := E) j i)
  have hcur : ‖(p (n+1)).curryMid j (0,1)‖ ≤ ‖p (n+1)‖ := by
    simpa only [ContinuousMultilinearMap.norm_curryMid, Prod.norm_def, norm_zero, norm_one,
      max_eq_right zero_le_one, mul_one] using
      ((p (n+1)).curryMid j).le_opNorm ((0 : E), (1 : ℝ))
  exact (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
    ((mul_le_mul hcur hprod (by positivity) (norm_nonneg _)).trans_eq (mul_one _))

private theorem dividedSeries_norm (p : FormalMultilinearSeries ℝ (E × ℝ) ℝ) (n : ℕ) :
    ‖dividedSeries p n‖ ≤ (n+1:ℝ) * ‖p (n+1)‖ := by
  calc
    _ ≤ ∑ j : Fin (n+1), ‖dividedTerm p n j‖ := norm_sum_le _ _
    _ ≤ ∑ _ : Fin (n+1), ‖p (n+1)‖ := Finset.sum_le_sum (fun j _ => dividedTerm_norm p n j)
    _ = _ := by simp

private theorem dividedTerm_factor (p : FormalMultilinearSeries ℝ (E × ℝ) ℝ)
    (n : ℕ) (j : Fin (n+1)) (v : E × ℝ) :
    v.2 * dividedTerm p n j (fun _ => v) = p (n+1)
      (fun i => if i < j then v else if j = i then v-axisProjection v else axisProjection v) := by
  have h := congrArg (fun f : (E × ℝ) [×n]→L[ℝ] ℝ => f (fun i => slotMap j i v))
    (((p (n+1)).curryMid j).map_smul v.2 ((0:E), (1:ℝ)))
  simp only [ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.curryMid_apply,
    smul_eq_mul] at h
  change v.2 * ((p (n+1)).curryMid j (0,1) (fun i => slotMap j i v)) = _
  rw [ContinuousMultilinearMap.curryMid_apply, ← h]
  congr 1
  funext i
  induction i using j.succAboveCases with
  | x =>
    rcases v with ⟨v, t⟩
    simp [axisProjection_apply, Prod.smul_mk]
  | p i =>
    have hji : j ≠ j.succAbove i := (Fin.succAbove_ne j i).symm
    simp only [Fin.insertNth_apply_succAbove, slotMap, if_neg hji]
    split_ifs <;> rfl

private theorem dividedSeries_factor (p : FormalMultilinearSeries ℝ (E × ℝ) ℝ)
    (n : ℕ) (v : E × ℝ) :
    v.2 * dividedSeries p n (fun _ => v) =
      p (n+1) (fun _ => v) - p (n+1) (fun _ => axisProjection v) := by
  have h := (p (n+1)).toMultilinearMap.map_sub_map_piecewise
    (fun _ => v) (fun _ => axisProjection v) Finset.univ
  simp only [Finset.piecewise_univ, Finset.mem_univ, true_implies] at h
  rw [dividedSeries, ContinuousMultilinearMap.sum_apply, Finset.mul_sum]
  simpa only [dividedTerm_factor, ContinuousMultilinearMap.coe_coe] using h.symm

private theorem dividedSeries_radius_pos (p : FormalMultilinearSeries ℝ (E × ℝ) ℝ)
    (hp : 0 < p.radius) : 0 < (dividedSeries p).radius := by
  obtain ⟨C, R, hC, hR, hbound⟩ := p.le_mul_pow_of_radius_pos hp
  let r : ℝ≥0 := ⟨(2*R)⁻¹, by positivity⟩
  have hr : 0 < (r : ℝ≥0∞) := by
    apply ENNReal.coe_pos.mpr
    change 0 < (2*R)⁻¹
    positivity
  apply hr.trans_le
  apply FormalMultilinearSeries.le_radius_of_bound _ (C*R)
  intro n
  have hn : (n+1:ℝ) ≤ (2:ℝ)^n := by
    exact_mod_cast (Nat.succ_le_of_lt (Nat.lt_two_pow_self : n < 2^n))
  calc
    ‖dividedSeries p n‖ * (r:ℝ)^n ≤ ((n+1:ℝ) * (C*R^(n+1))) * (r:ℝ)^n := by
      gcongr
      exact (dividedSeries_norm p n).trans (mul_le_mul_of_nonneg_left (hbound (n+1)) (by positivity))
    _ ≤ ((2:ℝ)^n * (C*R^(n+1))) * (r:ℝ)^n := by gcongr
    _ = C*R := by
      change (2^n * (C*R^(n+1))) * ((2*R)⁻¹)^n = C*R
      calc
        _ = C*R * ((2*R)^n * ((2*R)⁻¹)^n) := by rw [pow_succ, mul_pow]; ring
        _ = _ := by rw [← mul_pow, mul_inv_cancel₀ (by positivity : 2*R ≠ 0), one_pow, mul_one]

/-- Analytic divided difference in one scalar coordinate, jointly with arbitrary
normed-space parameters. The quotient is constructed by a convergent series. -/
theorem exists_analytic_coordinate_difference {f : E × ℝ → ℝ} {a : E}
    (hf : AnalyticAt ℝ f (a,0)) :
    ∃ g : E × ℝ → ℝ, AnalyticAt ℝ g (a,0) ∧
      ∀ᶠ x in 𝓝 (a,(0:ℝ)), f x - f (x.1,0) = x.2 * g x := by
  obtain ⟨p, r, hp⟩ := hf
  let q := dividedSeries p
  have hq : HasFPowerSeriesOnBall q.sum q 0 q.radius :=
    q.hasFPowerSeriesOnBall (dividedSeries_radius_pos p hp.radius_pos)
  let g : E × ℝ → ℝ := fun x => q.sum (x-(a,0))
  refine ⟨g, ?_, ?_⟩
  · have hi : AnalyticAt ℝ (fun x : E × ℝ => x-(a,0)) (a,0) :=
      analyticAt_id.sub analyticAt_const
    have ho : AnalyticAt ℝ q.sum ((a,(0:ℝ))-(a,0)) := by
      simpa only [sub_self] using hq.analyticAt
    exact ho.comp (f := fun x : E × ℝ => x-(a,0)) hi
  · have ht : Tendsto (fun x : E × ℝ => x-(a,0)) (𝓝 (a,(0:ℝ))) (𝓝 0) := by
      have hc : Continuous (fun x : E × ℝ => x-(a,0)) := continuous_id.sub continuous_const
      simpa only [sub_self] using hc.tendsto (a,(0:ℝ))
    have htp : Tendsto (fun x : E × ℝ => axisProjection (x-(a,0)))
        (𝓝 (a,(0:ℝ))) (𝓝 0) := by
      simpa only [map_zero, Function.comp_def] using (axisProjection.continuous.tendsto (0 : E × ℝ)).comp ht
    filter_upwards [ht.eventually (Metric.eball_mem_nhds (0 : E × ℝ) hp.r_pos),
      htp.eventually (Metric.eball_mem_nhds (0 : E × ℝ) hp.r_pos),
      ht.eventually (Metric.eball_mem_nhds (0 : E × ℝ) hq.r_pos)] with x hx hpx hqx
    have hxsum := hp.hasSum hx
    have hpxsum := hp.hasSum hpx
    have he0 : p 0 (fun _ => x-(a,0)) = p 0 (fun _ => axisProjection (x-(a,0))) :=
      congrArg (p 0) (Subsingleton.elim _ _)
    have hdiff : HasSum
        (fun n => p (n+1) (fun _ => x-(a,0)) - p (n+1) (fun _ => axisProjection (x-(a,0))))
        (f x - f (x.1,0)) := by
      simpa [Finset.sum_range_one, he0, axisProjection_apply] using
        (hasSum_nat_add_iff' 1).2 (hxsum.sub hpxsum)
    have hquot : HasSum (fun n => x.2 * q n (fun _ => x-(a,0))) (x.2 * g x) := by
      simpa only [zero_add] using (hq.hasSum hqx).mul_left x.2
    apply hdiff.unique
    have heq : (fun n => x.2 * q n (fun _ => x-(a,0))) =
        (fun n => p (n+1) (fun _ => x-(a,0)) - p (n+1) (fun _ => axisProjection (x-(a,0)))) := by
      funext n
      have hs : (x-(a,(0:ℝ))).2 = x.2 := sub_zero x.2
      have hh := dividedSeries_factor p n (x-(a,(0:ℝ)))
      change ((x-(a,(0:ℝ))).2 * q n (fun _ => x-(a,0))) = _ at hh
      rw [hs] at hh
      exact hh
    rwa [← heq]

/-- Parameterized analytic Hadamard division. Local vanishing on the parameter
axis is the only divisibility hypothesis. -/
theorem exists_analytic_factor {f : E × ℝ → ℝ} {a : E}
    (hf : AnalyticAt ℝ f (a,0)) (haxis : ∀ᶠ x in 𝓝 a, f (x,0) = 0) :
    ∃ g : E × ℝ → ℝ, AnalyticAt ℝ g (a,0) ∧
      (∀ᶠ x in 𝓝 (a,(0:ℝ)), f x = x.2 * g x) := by
  obtain ⟨g, hg, he⟩ := exists_analytic_coordinate_difference hf
  refine ⟨g, hg, ?_⟩
  have ha : ∀ᶠ x : E × ℝ in 𝓝 (a,(0:ℝ)), f (x.1,0) = 0 :=
    (continuous_fst.continuousAt : Tendsto (Prod.fst : E × ℝ → E) (𝓝 (a,(0:ℝ))) (𝓝 a)).eventually haxis
  filter_upwards [he, ha] with x hx hax
  simpa only [hax, sub_zero] using hx

/-- Identification of the analytic factor at an axis point with the scalar partial derivative. -/
theorem factor_value {f g : E × ℝ → ℝ} {a : E}
    (hg : AnalyticAt ℝ g (a,0))
    (he : ∀ᶠ x in 𝓝 (a,(0:ℝ)), f x = x.2 * g x) :
    g (a,0) = deriv (fun t : ℝ => f (a,t)) 0 := by
  have hi : AnalyticAt ℝ (fun t : ℝ => (a,t)) 0 := analyticAt_const.prod analyticAt_id
  have hgd : DifferentiableAt ℝ (fun t : ℝ => g (a,t)) 0 := (hg.comp hi).differentiableAt
  have hm := (hasDerivAt_id (0:ℝ)).mul hgd.hasDerivAt
  have hh : HasDerivAt (fun t : ℝ => t * g (a,t)) (g (a,0)) 0 := by
    convert hm using 1 <;> first | rfl | simp
  have ht : Tendsto (fun t : ℝ => (a,t)) (𝓝 0) (𝓝 (a,(0:ℝ))) :=
    (continuous_const.prodMk continuous_id).continuousAt
  exact (hh.congr_of_eventuallyEq (ht.eventually he)).deriv.symm

/-- The derivative identification holds on a whole neighbourhood of the axis point. -/
theorem factor_value_eventually {f g : E × ℝ → ℝ} {a : E}
    (hg : AnalyticAt ℝ g (a,0))
    (he : ∀ᶠ x in 𝓝 (a,(0:ℝ)), f x = x.2 * g x) :
    ∀ᶠ x in 𝓝 a, g (x,0) = deriv (fun t : ℝ => f (x,t)) 0 := by
  have ht : Tendsto (fun x : E => (x,(0:ℝ))) (𝓝 a) (𝓝 (a,(0:ℝ))) :=
    (continuous_id.prodMk continuous_const).continuousAt
  filter_upwards [ht.eventually hg.eventually_analyticAt,
    ht.eventually he.eventually_nhds] with x hx hex
  exact factor_value hx hex

/-- The requested analytic factor, including its actual transverse derivative value. -/
theorem exists_analytic_factor_with_value {f : E × ℝ → ℝ} {a : E}
    (hf : AnalyticAt ℝ f (a,0)) (haxis : ∀ᶠ x in 𝓝 a, f (x,0) = 0) :
    ∃ g : E × ℝ → ℝ, AnalyticAt ℝ g (a,0) ∧
      (∀ᶠ x in 𝓝 (a,(0:ℝ)), f x = x.2 * g x) ∧
      g (a,0) = deriv (fun t : ℝ => f (a,t)) 0 := by
  obtain ⟨g, hg, he⟩ := exists_analytic_factor hf haxis
  exact ⟨g, hg, he, factor_value hg he⟩

#print axioms exists_analytic_factor_with_value

#print axioms dividedSeries_factor
#print axioms dividedSeries_radius_pos
end BecknerOnofri.AnalyticParameterDivision
