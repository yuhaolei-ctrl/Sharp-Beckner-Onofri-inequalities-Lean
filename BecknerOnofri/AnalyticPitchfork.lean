import BecknerOnofri.AnalyticParameterDivision
import Mathlib.Analysis.Calculus.ImplicitContDiff
import BecknerOnofri.AnalyticEvenOrder

/-! The analytic scalar quotient for a scalar odd residual, with all analytic and Taylor
data explicit and later discharged by the actual supported Euler residual. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter Asymptotics
open scoped Topology ContDiff
namespace BecknerOnofri.AnalyticPitchfork

/-- Analytic scalar data. Applications must prove all fields for the actual residual. -/
structure Data where
  residual : ℝ × ℝ → ℝ
  coefficient : ℝ
  analytic : AnalyticAt ℝ residual (1,0)
  axis : ∀ᶠ μ in 𝓝 (1:ℝ), residual (μ,0)=0
  derivative_axis : ∀ᶠ μ in 𝓝 (1:ℝ),
    HasDerivAt (fun t => residual (μ,t)) (1-μ) 0
  odd : ∀ᶠ x in 𝓝 ((1,0):ℝ×ℝ), residual (x.1,-x.2) = -residual x
  cubic : (fun t => residual (1,t)-coefficient*t^3) =O[𝓝 (0:ℝ)] (fun t => ‖t‖^5)

open AnalyticParameterDivision

private theorem quotient_exists (D : Data) :
    ∃ q : ℝ × ℝ → ℝ, AnalyticAt ℝ q (1,0) ∧
      ∀ᶠ x in 𝓝 ((1,0) : ℝ × ℝ), D.residual x = x.2 * q x :=
  exists_analytic_factor (D.analytic) (D.axis)

def quotient (D : Data) : ℝ × ℝ → ℝ := (quotient_exists D).choose

theorem quotient_analytic (D : Data) :
    AnalyticAt ℝ (quotient D) (1,0) := (quotient_exists D).choose_spec.1

theorem residual_eq_mul_quotient (D : Data) :
    ∀ᶠ x in 𝓝 ((1,0) : ℝ × ℝ), D.residual x = x.2 * quotient D x :=
  (quotient_exists D).choose_spec.2

theorem quotient_axis (D : Data) :
    ∀ᶠ μ in 𝓝 (1:ℝ), quotient D (μ,0) = 1-μ := by
  filter_upwards [factor_value_eventually (quotient_analytic D) (residual_eq_mul_quotient D),
    D.derivative_axis] with μ hq hr
  rw [hq, hr.deriv]

@[simp] theorem quotient_base (D : Data) : quotient D (1,0) = 0 := by
  simpa using (quotient_axis D).self_of_nhds

theorem quotient_even (D : Data) :
    ∀ᶠ x in 𝓝 ((1,0) : ℝ × ℝ), quotient D (x.1,-x.2) = quotient D x := by
  have ht : Tendsto (fun x : ℝ × ℝ => (x.1,-x.2)) (𝓝 (1,0)) (𝓝 (1,0)) := by
    simpa using (continuous_fst.prodMk continuous_snd.neg).continuousAt.tendsto (x := ((1,0):ℝ×ℝ))
  filter_upwards [residual_eq_mul_quotient D, ht.eventually (residual_eq_mul_quotient D),
    D.odd] with x hx hn ho
  by_cases h0 : x.2 = 0
  · congr 1
    exact Prod.ext rfl (by simp [h0])
  · rw [hx, hn, neg_mul] at ho
    exact mul_left_cancel₀ h0 (neg_injective ho)

theorem quotient_critical_expansion (D : Data) :
    (fun t : ℝ => quotient D (1,t) - D.coefficient*t^2) =O[𝓝 0] (fun t : ℝ => ‖t‖^4) := by
  obtain ⟨C,hC⟩ := (D.cubic).exists_pos
  apply IsBigO.of_bound C
  have ht : Tendsto (fun t : ℝ => ((1:ℝ),t)) (𝓝 0) (𝓝 (1,0)) :=
    (continuous_const.prodMk continuous_id).continuousAt
  filter_upwards [hC.2.bound, ht.eventually (residual_eq_mul_quotient D)] with t hb he
  by_cases h0 : t = 0
  · simp [h0]
  · have htpos : 0 < ‖t‖ := norm_pos_iff.mpr h0
    have hmul : D.residual (1,t) - D.coefficient*t^3 =
        t * (quotient D (1,t) - D.coefficient*t^2) := by rw [he]; ring
    rw [hmul, norm_mul] at hb
    simp only [norm_pow, norm_norm] at hb ⊢
    have hpow : ‖t‖^5 = ‖t‖ * ‖t‖^4 := by ring
    rw [hpow] at hb
    apply le_of_mul_le_mul_left (a := ‖t‖) (a0 := htpos)
    calc
      _ ≤ C * (‖t‖ * ‖t‖^4) := hb
      _ = _ := by ring

/-- Actual analytic branch of the parameter as a function of the real first-shell amplitude. -/
theorem exists_parameter_branch (D : Data) :
    ∃ μ : ℝ → ℝ, AnalyticAt ℝ μ 0 ∧ μ 0 = 1 ∧
      (∀ᶠ t in 𝓝 (0:ℝ), quotient D (μ t,t) = 0) ∧
      (∀ᶠ x in 𝓝 ((1,0):ℝ×ℝ), quotient D x = 0 ↔ μ x.2 = x.1) := by
  let f : ℝ × ℝ → ℝ := fun x => quotient D (x.2,x.1)
  have hf : AnalyticAt ℝ f (0,1) := by
    have hi : AnalyticAt ℝ (fun x : ℝ × ℝ => (x.2,x.1)) (0,1) :=
      analyticAt_snd.prod analyticAt_fst
    exact (quotient_analytic D).comp (f := fun x : ℝ × ℝ => (x.2,x.1)) hi
  have hf0 : f (0,1) = 0 := quotient_base D
  have hslice : HasFDerivAt (𝕜 := ℝ) (fun μ : ℝ => f (0,μ))
      (-ContinuousLinearMap.id ℝ ℝ) 1 := by
    have h := (hasFDerivAt_const (𝕜 := ℝ) (1:ℝ) (1:ℝ)).sub (hasFDerivAt_id (𝕜 := ℝ) (1:ℝ))
    have h' : HasFDerivAt (𝕜 := ℝ) (fun μ : ℝ => 1-μ) (-ContinuousLinearMap.id ℝ ℝ) 1 := by
      convert h using 1 <;> first | rfl | simp
    exact h'.congr_of_eventuallyEq (quotient_axis D)
  have hpartial : (fderiv ℝ f (0,1)).comp (ContinuousLinearMap.inr ℝ ℝ ℝ) =
      -ContinuousLinearMap.id ℝ ℝ := by
    exact ((hf.differentiableAt.hasFDerivAt).comp 1
      ((ContinuousLinearMap.inr ℝ ℝ ℝ).hasFDerivAt)).unique hslice
  have hinv : ((fderiv ℝ f (0,1)).comp (ContinuousLinearMap.inr ℝ ℝ ℝ)).IsInvertible := by
    rw [hpartial]
    exact ContinuousLinearMap.isInvertible_equiv
      (f := (LinearIsometryEquiv.neg ℝ (E := ℝ)).toContinuousLinearEquiv)
  have hc : ContDiffAt ℝ ω f (0,1) := hf.contDiffAt
  have hn : (ω : ℕ∞ω) ≠ 0 := by simp
  let μ := hc.implicitFunction hn hinv
  refine ⟨μ, (hc.contDiffAt_implicitFunction hn hinv).analyticAt,
    hc.implicitFunction_apply_self hn hinv, ?_, ?_⟩
  · simpa only [hf0] using hc.eventually_apply_implicitFunction hn hinv
  · have ht : Tendsto (fun x : ℝ × ℝ => (x.2,x.1)) (𝓝 (1,0)) (𝓝 (0,1)) :=
      (continuous_snd.prodMk continuous_fst).continuousAt
    simpa only [hf0] using ht.eventually (hc.eventually_apply_eq_iff_implicitFunction hn hinv)

/-- Fixed analytic parameter branch supplied by the scalar implicit function theorem. -/
def parameter (D : Data) : ℝ → ℝ := (exists_parameter_branch D).choose

theorem parameter_analytic (D : Data) : AnalyticAt ℝ (parameter D) 0 :=
  (exists_parameter_branch D).choose_spec.1

@[simp] theorem parameter_base (D : Data) : parameter D 0 = 1 :=
  (exists_parameter_branch D).choose_spec.2.1

theorem parameter_solves (D : Data) :
    ∀ᶠ t in 𝓝 (0:ℝ), quotient D (parameter D t,t) = 0 :=
  (exists_parameter_branch D).choose_spec.2.2.1

theorem parameter_unique (D : Data) :
    ∀ᶠ x in 𝓝 ((1,0):ℝ×ℝ), quotient D x = 0 ↔ parameter D x.2 = x.1 :=
  (exists_parameter_branch D).choose_spec.2.2.2

theorem parameter_tendsto (D : Data) :
    Tendsto (parameter D) (𝓝 0) (𝓝 1) := by
  simpa only [parameter_base] using (parameter_analytic D).continuousAt.tendsto

theorem parameter_pair_tendsto (D : Data) :
    Tendsto (fun t : ℝ => (parameter D t,t)) (𝓝 0) (𝓝 (1,0)) :=
  (parameter_tendsto D).prodMk_nhds tendsto_id

theorem parameter_even (D : Data) :
    ∀ᶠ t in 𝓝 (0:ℝ), parameter D (-t) = parameter D t := by
  have ht : Tendsto (fun t : ℝ => (parameter D t,-t)) (𝓝 0) (𝓝 (1,0)) := by
    simpa only [neg_zero] using (parameter_tendsto D).prodMk_nhds
      (continuous_neg.continuousAt (x := (0:ℝ))).tendsto
  filter_upwards [parameter_solves D, (parameter_pair_tendsto D).eventually (quotient_even D),
    ht.eventually (parameter_unique D)] with t hs he hu
  exact hu.mp (he.trans hs)

theorem parameter_derivative_zero (D : Data) :
    HasDerivAt (parameter D) 0 0 := by
  have hp := (parameter_analytic D).differentiableAt.hasDerivAt
  have hn : HasDerivAt (fun t : ℝ => parameter D (-t)) (-deriv (parameter D) 0) 0 := by
    have hpn : HasDerivAt (parameter D) (deriv (parameter D) 0) (-(0:ℝ)) := by simpa using hp
    convert hpn.comp 0 (hasDerivAt_neg (0:ℝ)) using 1 <;> first | rfl | simp
  have he := hp.unique (hn.congr_of_eventuallyEq ((parameter_even D).mono (fun _ h => h.symm)))
  have hzero : deriv (parameter D) 0 = 0 := by linarith
  simpa only [hzero] using hp

theorem parameter_quadratic_bound (D : Data) :
    (fun t : ℝ => parameter D t-1) =O[𝓝 0] (fun t : ℝ => ‖t‖^2) := by
  obtain ⟨p,hp⟩ := parameter_analytic D
  have h0 : p 0 (fun _ => (0:ℝ)) = 1 := by
    simpa only [parameter_base] using hp.coeff_zero (fun _ => (0:ℝ))
  have h1 : continuousMultilinearCurryFin1 ℝ ℝ ℝ (p 1) = 0 := by
    convert hp.hasFDerivAt.unique (parameter_derivative_zero D).hasFDerivAt using 1 <;> simp
  have hz (t : ℝ) : p 1 (fun _ => t) = 0 :=
    congrArg (fun L : ℝ →L[ℝ] ℝ => L t) h1
  have hpartial : p.partialSum 2 = fun _ => (1:ℝ) := by
    funext t
    simp only [FormalMultilinearSeries.partialSum, Finset.sum_range_succ, Finset.sum_range_zero,
      zero_add, hz, add_zero]
    convert h0 using 1
    exact congrArg (p 0) (Subsingleton.elim _ _)
  simpa only [zero_add, hpartial] using hp.isBigO_sub_partialSum_pow 2

/-- The implicit parameter has the exact coefficient determined by the cubic
coefficient of the actual reduced equation. -/
theorem parameter_expansion (D : Data) :
    (fun t : ℝ => parameter D t-1-D.coefficient*t^2) =O[𝓝 0] (fun t : ℝ => ‖t‖^4) := by
  let f : ℝ × ℝ → ℝ := fun x => quotient D (1+x.2,x.1)
  have hf : AnalyticAt ℝ f (0,0) := by
    have hi : AnalyticAt ℝ (fun x : ℝ × ℝ => (1+x.2,x.1)) (0,0) :=
      (analyticAt_const.add analyticAt_snd).prod analyticAt_fst
    have ho : AnalyticAt ℝ (quotient D) (1+(0:ℝ),0) := by simpa using quotient_analytic D
    exact ho.comp (f := fun x : ℝ × ℝ => (1+x.2,x.1)) hi
  obtain ⟨g,hg,he⟩ := exists_analytic_coordinate_difference hf
  have Der : HasDerivAt (fun s : ℝ => f (0,s)-f (0,0)) (-1) 0 := by
    have ht : Tendsto (fun s : ℝ => 1+s) (𝓝 0) (𝓝 1) := by
      have hc : Continuous (fun s : ℝ => 1+s) := continuous_const.add continuous_id
      simpa using hc.continuousAt.tendsto (x := (0:ℝ))
    apply (hasDerivAt_neg (0:ℝ)).congr_of_eventuallyEq
    filter_upwards [ht.eventually (quotient_axis D)] with s hs
    change quotient D (1+s,0)-quotient D (1+0,0) = -s
    rw [hs]
    simp only [add_zero, quotient_base]
    ring
  have hg0 : g (0,0) = -1 := by
    exact (factor_value hg he).trans Der.deriv
  let H : ℝ → ℝ := fun t => g (t,parameter D t-1)
  have hH : AnalyticAt ℝ H 0 := by
    have hi : AnalyticAt ℝ (fun t : ℝ => (t,parameter D t-1)) 0 :=
      analyticAt_id.prod ((parameter_analytic D).sub analyticAt_const)
    have ho : AnalyticAt ℝ g ((0:ℝ),parameter D 0-1) := by
      simpa only [parameter_base, sub_self] using hg
    exact ho.comp (f := fun t : ℝ => (t,parameter D t-1)) hi
  have hH0 : H 0 = -1 := by simpa only [H,parameter_base,sub_self] using hg0
  have hHbound : (fun t : ℝ => H t+1) =O[𝓝 0] (fun t : ℝ => ‖t‖) := by
    simpa only [hH0, sub_neg_eq_add, sub_zero] using hH.differentiableAt.isBigO_sub.norm_right
  have hprod : (fun t : ℝ => (parameter D t-1)*(H t+1)) =O[𝓝 0]
      (fun t : ℝ => ‖t‖^3) := by
    convert (parameter_quadratic_bound D).mul hHbound using 1 <;> first | rfl | (funext t; ring)
  have hcrit := (quotient_critical_expansion D).trans
    (norm_pow_bigO_of_le (E := ℝ) (by norm_num : 3 ≤ 4))
  have ht : Tendsto (fun t : ℝ => (t,parameter D t-1)) (𝓝 0) (𝓝 (0,0)) := by
    have hδ : Tendsto (fun t : ℝ => parameter D t-1) (𝓝 0) (𝓝 0) := by
      simpa only [sub_self] using (parameter_tendsto D).sub_const 1
    exact tendsto_id.prodMk_nhds hδ
  have heq : ∀ᶠ t in 𝓝 (0:ℝ),
      parameter D t-1-D.coefficient*t^2 =
        (parameter D t-1)*(H t+1)+(quotient D (1,t)-D.coefficient*t^2) := by
    filter_upwards [ht.eventually he,parameter_solves D] with t he hs
    change quotient D (1+(parameter D t-1),t)-quotient D (1+0,t) =
      (parameter D t-1)*H t at he
    simp only [add_sub_cancel,add_zero,hs] at he
    linarith
  have hthird : (fun t : ℝ => parameter D t-1-D.coefficient*t^2) =O[𝓝 0]
      (fun t : ℝ => ‖t‖^3) :=
    (hprod.add hcrit).congr' (heq.mono (fun _ h => h.symm)) (Eventually.of_forall (fun _ => rfl))
  apply analytic_even_third_order
  · exact ((parameter_analytic D).sub analyticAt_const).sub
      (analyticAt_const.mul (analyticAt_id.pow 2))
  · exact hthird
  · filter_upwards [parameter_even D] with t ht
    simp only [ht,neg_sq]

#print axioms parameter_expansion
#print axioms parameter_derivative_zero
#print axioms parameter_quadratic_bound
#print axioms quotient_critical_expansion
#print axioms exists_parameter_branch
end BecknerOnofri.AnalyticPitchfork
