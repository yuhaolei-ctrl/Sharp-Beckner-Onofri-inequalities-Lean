import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Asymptotics.Lemmas

/-! Parity improves a fifth-order analytic remainder to sixth order. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter Asymptotics
open scoped Topology
namespace BecknerOnofri
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem norm_pow_bigO_of_le {m n : ℕ} (h : n ≤ m) :
    (fun x : E => ‖x‖^m) =O[𝓝 0] (fun x => ‖x‖^n) := by
  apply IsBigO.of_bound 1
  filter_upwards [Metric.ball_mem_nhds (0:E) (by norm_num : (0:ℝ)<1)] with x hx
  have hx' : ‖x‖ ≤ 1 := le_of_lt (by simpa [Metric.mem_ball, dist_zero_right] using hx)
  simpa only [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg x) _), one_mul] using
    pow_le_pow_of_le_one (norm_nonneg x) hx' h

theorem coefficients_zero_of_order {f : E → F} {p : FormalMultilinearSeries ℝ E F}
    (hp : HasFPowerSeriesAt f p 0) {N : ℕ}
    (hf : f =O[𝓝 0] (fun x => ‖x‖^N)) :
    ∀ n < N, ∀ x, p n (fun _ => x) = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    have hpartial : p.partialSum (n+1) = fun x => p n (fun _ => x) := by
      funext x
      refine Finset.sum_eq_single n (fun j hj hjn => ?_) (fun hj => ?_)
      · have hjlt : j < n := by
          have hjn1 := Finset.mem_range.mp hj
          omega
        exact ih j hjlt (lt_trans hjlt hn) x
      · exact False.elim (hj (Finset.mem_range.mpr (by omega)))
    have htail := hp.isBigO_sub_partialSum_pow (n+1)
    simp only [zero_add, hpartial] at htail
    have hfn := hf.trans (norm_pow_bigO_of_le (E := E) (by omega : n+1 ≤ N))
    have hh : (fun x => p n (fun _ => x)) =O[𝓝 0] (fun x => ‖x‖^(n+1)) := by
      convert! hfn.sub htail using 1
      funext x
      abel
    exact hh.continuousMultilinearMap_apply_eq_zero

/-- A genuine analytic even remainder cannot have a nonzero fifth-order term. -/
theorem analytic_even_fifth_order {f : E → F} (hf : AnalyticAt ℝ f 0)
    (ho : f =O[𝓝 0] (fun x => ‖x‖^5))
    (he : ∀ᶠ x in 𝓝 (0:E), f (-x) = f x) :
    f =O[𝓝 0] (fun x => ‖x‖^6) := by
  obtain ⟨p, hp⟩ := hf
  have hz := coefficients_zero_of_order hp ho
  have hpartial : p.partialSum 6 = fun x => p 5 (fun _ => x) := by
    funext x
    refine Finset.sum_eq_single 5 (fun j hj hjn => ?_) (fun hj => ?_)
    · exact hz j (by have := Finset.mem_range.mp hj; omega) x
    · exact False.elim (hj (by decide))
  have hr : (fun x => f x - p 5 (fun _ => x)) =O[𝓝 0] (fun x => ‖x‖^6) := by
    simpa only [zero_add, hpartial] using hp.isBigO_sub_partialSum_pow 6
  have hneg (x : E) : p 5 (fun _ => -x) = -(p 5 (fun _ => x)) := by
    have hh := (p 5).map_smul_univ (fun _ : Fin 5 => (-1:ℝ)) (fun _ => x)
    norm_num at hh
    exact hh
  have hrneg : (fun x => f x + p 5 (fun _ => x)) =O[𝓝 0] (fun x => ‖x‖^6) := by
    have ht : Tendsto (fun x : E => -x) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_neg.continuousAt (x := (0:E))).tendsto
    apply (hr.comp_tendsto ht).congr'
    · filter_upwards [he] with x hx
      simp only [Function.comp_apply, hx, hneg, sub_neg_eq_add]
    · exact Eventually.of_forall (fun x => by simp)
  have hh := (hr.add hrneg).const_smul_left (1/2:ℝ)
  apply hh.congr_left
  intro x
  have ha : f x - p 5 (fun _ => x) + (f x + p 5 (fun _ => x)) = (2:ℝ) • f x := by
    rw [two_smul]
    abel
  simp only [Pi.smul_apply, ha, smul_smul]
  norm_num

/-- A genuine analytic even remainder cannot have a nonzero third-order term. -/
theorem analytic_even_third_order {f : E → F} (hf : AnalyticAt ℝ f 0)
    (ho : f =O[𝓝 0] (fun x => ‖x‖^3))
    (he : ∀ᶠ x in 𝓝 (0:E), f (-x) = f x) :
    f =O[𝓝 0] (fun x => ‖x‖^4) := by
  obtain ⟨p, hp⟩ := hf
  have hz := coefficients_zero_of_order hp ho
  have hpartial : p.partialSum 4 = fun x => p 3 (fun _ => x) := by
    funext x
    refine Finset.sum_eq_single 3 (fun j hj hjn => ?_) (fun hj => ?_)
    · exact hz j (by have := Finset.mem_range.mp hj; omega) x
    · exact False.elim (hj (by decide))
  have hr : (fun x => f x - p 3 (fun _ => x)) =O[𝓝 0] (fun x => ‖x‖^4) := by
    simpa only [zero_add, hpartial] using hp.isBigO_sub_partialSum_pow 4
  have hneg (x : E) : p 3 (fun _ => -x) = -(p 3 (fun _ => x)) := by
    have hh := (p 3).map_smul_univ (fun _ : Fin 3 => (-1:ℝ)) (fun _ => x)
    norm_num at hh
    exact hh
  have hrneg : (fun x => f x + p 3 (fun _ => x)) =O[𝓝 0] (fun x => ‖x‖^4) := by
    have ht : Tendsto (fun x : E => -x) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_neg.continuousAt (x := (0:E))).tendsto
    apply (hr.comp_tendsto ht).congr'
    · filter_upwards [he] with x hx
      simp only [Function.comp_apply, hx, hneg, sub_neg_eq_add]
    · exact Eventually.of_forall (fun x => by simp)
  have hh := (hr.add hrneg).const_smul_left (1/2:ℝ)
  apply hh.congr_left
  intro x
  have ha : f x - p 3 (fun _ => x) + (f x + p 3 (fun _ => x)) = (2:ℝ) • f x := by
    rw [two_smul]
    abel
  simp only [Pi.smul_apply, ha, smul_smul]
  norm_num

/-- An analytic odd remainder cannot have a nonzero fourth-order term. -/
theorem analytic_odd_fourth_order {f : E → F} (hf : AnalyticAt ℝ f 0)
    (ho : f =O[𝓝 0] (fun x => ‖x‖^4))
    (he : ∀ᶠ x in 𝓝 (0:E), f (-x) = -f x) :
    f =O[𝓝 0] (fun x => ‖x‖^5) := by
  obtain ⟨p, hp⟩ := hf
  have hz := coefficients_zero_of_order hp ho
  have hpartial : p.partialSum 5 = fun x => p 4 (fun _ => x) := by
    funext x
    refine Finset.sum_eq_single 4 (fun j hj hjn => ?_) (fun hj => ?_)
    · exact hz j (by have := Finset.mem_range.mp hj; omega) x
    · exact False.elim (hj (by decide))
  have hr : (fun x => f x - p 4 (fun _ => x)) =O[𝓝 0] (fun x => ‖x‖^5) := by
    simpa only [zero_add, hpartial] using hp.isBigO_sub_partialSum_pow 5
  have hneg (x : E) : p 4 (fun _ => -x) = p 4 (fun _ => x) := by
    have hh := (p 4).map_smul_univ (fun _ : Fin 4 => (-1:ℝ)) (fun _ => x)
    norm_num at hh
    exact hh
  have hrneg : (fun x => -f x - p 4 (fun _ => x)) =O[𝓝 0] (fun x => ‖x‖^5) := by
    have ht : Tendsto (fun x : E => -x) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_neg.continuousAt (x := (0:E))).tendsto
    apply (hr.comp_tendsto ht).congr'
    · filter_upwards [he] with x hx
      simp only [Function.comp_apply, hx, hneg]
    · exact Eventually.of_forall (fun x => by simp)
  have hh := (hr.sub hrneg).const_smul_left (1/2:ℝ)
  apply hh.congr_left
  intro x
  have ha : f x - p 4 (fun _ => x) - (-f x - p 4 (fun _ => x)) = (2:ℝ) • f x := by
    rw [two_smul]
    abel
  simp only [Pi.smul_apply, ha, smul_smul]
  norm_num


#print axioms analytic_even_fifth_order
#print axioms analytic_odd_fourth_order
end BecknerOnofri
