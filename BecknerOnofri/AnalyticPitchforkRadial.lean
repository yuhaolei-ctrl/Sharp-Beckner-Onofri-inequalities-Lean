import BecknerOnofri.AnalyticPitchfork
import BecknerOnofri.AnalyticEvenQuadratic
import BecknerOnofri.AnalyticParameterOrderDivision
import BecknerOnofri.AnalyticProductFactorUnique

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter Asymptotics
open scoped Topology
namespace BecknerOnofri.AnalyticPitchfork

def amplitudePartial (D : Data) (x : ℝ × ℝ) : ℝ := fderiv ℝ (quotient D) x (0,1)

theorem amplitudePartial_analytic (D : Data) : AnalyticAt ℝ (amplitudePartial D) (1,0) :=
  ((ContinuousLinearMap.apply ℝ ℝ ((0,1) : ℝ × ℝ)).analyticAt _).comp
    (quotient_analytic D).fderiv

theorem amplitudePartial_slice (D : Data) :
    ∀ᶠ x : ℝ × ℝ in 𝓝 (1,0),
      amplitudePartial D x=deriv (fun t => quotient D (x.1,t)) x.2 := by
  filter_upwards [(quotient_analytic D).eventually_analyticAt] with x hx
  have hi := (hasFDerivAt_const (𝕜 := ℝ) x.1 x.2).prodMk (hasFDerivAt_id x.2)
  exact ((hx.differentiableAt.hasFDerivAt.comp x.2 hi).hasDerivAt.deriv).symm

def reverseAmplitude : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).prod (-ContinuousLinearMap.snd ℝ ℝ ℝ)

@[simp] theorem reverseAmplitude_apply (x : ℝ × ℝ) : reverseAmplitude x=(x.1,-x.2) := rfl

theorem reverseAmplitude_tendsto : Tendsto reverseAmplitude (𝓝 (1,0)) (𝓝 (1,0)) := by
  simpa only [reverseAmplitude_apply,neg_zero] using reverseAmplitude.continuous.tendsto (1,0)

theorem amplitudePartial_odd (D : Data) :
    ∀ᶠ x : ℝ × ℝ in 𝓝 (1,0),amplitudePartial D (reverseAmplitude x) = -amplitudePartial D x := by
  filter_upwards [(quotient_even D).eventually_nhds,
    (quotient_analytic D).eventually_analyticAt,
    reverseAmplitude_tendsto.eventually (quotient_analytic D).eventually_analyticAt] with x he hx hn
  have hc := (hn.differentiableAt.hasFDerivAt.comp x reverseAmplitude.hasFDerivAt).congr_of_eventuallyEq
    (he.mono (fun _ h => h.symm))
  have hv := congrArg (fun L : (ℝ × ℝ) →L[ℝ] ℝ => L (0,1))
    (hc.unique hx.differentiableAt.hasFDerivAt)
  change fderiv ℝ (quotient D) (reverseAmplitude x) (0,-1)=amplitudePartial D x at hv
  have hz : ((0,-1) : ℝ × ℝ) = -((0,1) : ℝ × ℝ) := by simp
  rw [hz,map_neg] at hv
  dsimp only [amplitudePartial] at hv ⊢
  linarith

/-- The apparent division by the branch amplitude has an analytic extension;
its value is determined by the proved cubic Taylor coefficient. -/
theorem exists_radial_factor (D : Data) :
    ∃ K : ℝ × ℝ → ℝ, AnalyticAt ℝ K (1,0) ∧ K (1,0)=2*D.coefficient ∧
      (∀ᶠ x : ℝ × ℝ in 𝓝 (1,0),amplitudePartial D x=x.2*K x) ∧
      (∀ᶠ x : ℝ × ℝ in 𝓝 (1,0),K (reverseAmplitude x)=K x) := by
  have ht : Tendsto (fun μ : ℝ => (μ,(0:ℝ))) (𝓝 1) (𝓝 (1,0)) :=
    (continuous_id.prodMk continuous_const).continuousAt
  have hz : ∀ᶠ μ in 𝓝 (1:ℝ),amplitudePartial D (μ,0)=0 := by
    filter_upwards [ht.eventually (amplitudePartial_odd D)] with μ hμ
    simp only [reverseAmplitude_apply,neg_zero] at hμ
    linarith
  obtain ⟨K,hK,he⟩ := AnalyticParameterDivision.exists_analytic_factor
    (amplitudePartial_analytic D) hz
  have hs : Tendsto (fun t : ℝ => ((1:ℝ),t)) (𝓝 0) (𝓝 (1,0)) :=
    (continuous_const.prodMk continuous_id).continuousAt
  have hKs : AnalyticAt ℝ (fun t : ℝ => K (1,t)) 0 :=
    hK.comp (analyticAt_const.prod analyticAt_id)
  have hqs : AnalyticAt ℝ (fun t : ℝ => quotient D (1,t)) 0 :=
    (quotient_analytic D).comp (analyticAt_const.prod analyticAt_id)
  have horder : (fun t : ℝ => deriv (fun t : ℝ => quotient D (1,t)) t - t*(2*D.coefficient))
      =O[𝓝 0] (fun t : ℝ => ‖t‖^2) := by
    have ho := analytic_quadratic_deriv_remainder hqs 0 D.coefficient
      (by simpa only [sub_zero] using quotient_critical_expansion D)
    have ho' := ho.trans (norm_pow_bigO_of_le (by norm_num : 2≤3))
    simpa only [mul_comm] using ho'
  have hK0 : K (1,0)=2*D.coefficient := by
    apply AnalyticParameterDivision.power_factor_value (N := 1) hKs.continuousAt
    · filter_upwards [hs.eventually he,hs.eventually (amplitudePartial_slice D)] with t he hs
      simpa only [pow_one] using hs.symm.trans he
    · simpa only [pow_one] using horder
  refine ⟨K,hK,hK0,he,?_⟩
  have hn : AnalyticAt ℝ (fun x => K (reverseAmplitude x)) (1,0) := by
    have ho : AnalyticAt ℝ K (reverseAmplitude (1,0)) := by
      simpa only [reverseAmplitude_apply,neg_zero] using hK
    exact ho.comp (f := reverseAmplitude) (reverseAmplitude.analyticAt _)
  apply AnalyticParameterDivision.linear_factor_unique (ContinuousLinearMap.snd ℝ ℝ ℝ)
    (e := (0,1)) rfl rfl hn hK
  filter_upwards [he,reverseAmplitude_tendsto.eventually he,amplitudePartial_odd D] with x he hn ho
  change x.2*K (reverseAmplitude x)=x.2*K x
  change amplitudePartial D (reverseAmplitude x)=(-x.2)*K (reverseAmplitude x) at hn
  linarith

#print axioms exists_radial_factor
end BecknerOnofri.AnalyticPitchfork
