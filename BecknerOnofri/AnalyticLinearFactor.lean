module

public import BecknerOnofri.AnalyticTwoCoordinateDivision

@[expose] public section

/-! Analytic division by a nonzero continuous linear functional. This permits
coordinatewise division of the actual finite-dimensional reduced Euler equation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter
open scoped Topology
namespace BecknerOnofri.AnalyticParameterDivision
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_analytic_linear_factor {f : E → ℝ} {a e : E}
    (L : E →L[ℝ] ℝ) (he : L e=1) (ha : L a=0) (hf : AnalyticAt ℝ f a)
    (hzero : ∀ᶠ x in 𝓝 a,L x=0 → f x=0) :
    ∃ g : E → ℝ, AnalyticAt ℝ g a ∧ ∀ᶠ x in 𝓝 a,f x=L x*g x := by
  let P : E × ℝ →L[ℝ] E := ContinuousLinearMap.fst ℝ E ℝ +
    ((ContinuousLinearMap.snd ℝ E ℝ)-L.comp (ContinuousLinearMap.fst ℝ E ℝ)).smulRight e
  have hP (x : E × ℝ) : P x=x.1+(x.2-L x.1) • e := rfl
  have hPa : P (a,0)=a := by rw [hP,ha]; simp
  have hLP (x : E × ℝ) : L (P x)=x.2 := by
    rw [hP,map_add,map_smul,he,smul_eq_mul,mul_one]
    ring
  have hfP : AnalyticAt ℝ (fun x => f (P x)) (a,0) := by
    have hf' : AnalyticAt ℝ f (P (a,0)) := by simpa only [hPa] using hf
    exact hf'.comp (f := P) (P.analyticAt _)
  have ht0 : Tendsto (fun x : E => P (x,0)) (𝓝 a) (𝓝 a) := by
    have hc : Continuous (fun x : E => P (x,0)) := P.continuous.comp
      (continuous_id.prodMk continuous_const)
    simpa only [hPa] using hc.tendsto a
  have hz : ∀ᶠ x in 𝓝 a,f (P (x,0))=0 := by
    filter_upwards [ht0.eventually hzero] with x hx
    exact hx (hLP (x,0))
  obtain ⟨q,hq,hfactor⟩ := exists_analytic_factor hfP hz
  let Q : E →L[ℝ] E × ℝ := (ContinuousLinearMap.id ℝ E).prod L
  have hQ (x : E) : Q x=(x,L x) := rfl
  have hQa : Q a=(a,0) := by rw [hQ,ha]
  have hq' : AnalyticAt ℝ q (Q a) := by simpa only [hQa] using hq
  refine ⟨fun x => q (Q x),hq'.comp (f := Q) (Q.analyticAt _),?_⟩
  have ht : Tendsto Q (𝓝 a) (𝓝 (a,0)) := by
    simpa only [hQa] using Q.continuous.tendsto a
  filter_upwards [ht.eventually hfactor] with x hx
  simpa only [hQ,hP,sub_self,zero_smul,add_zero] using hx

#print axioms exists_analytic_linear_factor
end BecknerOnofri.AnalyticParameterDivision
