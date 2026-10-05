module

public import BecknerOnofri.AnalyticLinearFactor

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter
open scoped Topology
namespace BecknerOnofri.AnalyticParameterDivision
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem linear_factor_zero {g : E → ℝ} {a e : E}
    (L : E →L[ℝ] ℝ) (he : L e=1) (ha : L a=0) (hg : AnalyticAt ℝ g a)
    (hz : ∀ᶠ x in 𝓝 a,L x*g x=0) : ∀ᶠ x in 𝓝 a,g x=0 := by
  let P : E × ℝ →L[ℝ] E := ContinuousLinearMap.fst ℝ E ℝ +
    ((ContinuousLinearMap.snd ℝ E ℝ)-L.comp (ContinuousLinearMap.fst ℝ E ℝ)).smulRight e
  have hP (x : E × ℝ) : P x=x.1+(x.2-L x.1) • e := rfl
  have hPa : P (a,0)=a := by rw [hP,ha]; simp
  have hLP (x : E × ℝ) : L (P x)=x.2 := by
    rw [hP,map_add,map_smul,he,smul_eq_mul,mul_one]
    ring
  have hgP : AnalyticAt ℝ (fun x => g (P x)) (a,0) := by
    have hg' : AnalyticAt ℝ g (P (a,0)) := by simpa only [hPa] using hg
    exact hg'.comp (f := P) (P.analyticAt _)
  have hPt : Tendsto P (𝓝 (a,0)) (𝓝 a) := by
    simpa only [hPa] using P.continuous.tendsto (a,0)
  have hzero : ∀ᶠ x : E × ℝ in 𝓝 (a,0),x.2*g (P x)=0 := by
    filter_upwards [hPt.eventually hz] with x hx
    simpa only [hLP] using hx
  have hqzero := factor_zero hgP hzero
  let Q : E →L[ℝ] E × ℝ := (ContinuousLinearMap.id ℝ E).prod L
  have hQ (x : E) : Q x=(x,L x) := rfl
  have hQa : Q a=(a,0) := by rw [hQ,ha]
  have hQt : Tendsto Q (𝓝 a) (𝓝 (a,0)) := by
    simpa only [hQa] using Q.continuous.tendsto a
  filter_upwards [hQt.eventually hqzero] with x hx
  simpa only [hQ,hP,sub_self,zero_smul,add_zero] using hx

theorem linear_factor_unique {g h : E → ℝ} {a e : E}
    (L : E →L[ℝ] ℝ) (he : L e=1) (ha : L a=0)
    (hg : AnalyticAt ℝ g a) (hh : AnalyticAt ℝ h a)
    (hz : ∀ᶠ x in 𝓝 a,L x*g x=L x*h x) : g =ᶠ[𝓝 a] h := by
  have hzero : ∀ᶠ x in 𝓝 a,L x*(g x-h x)=0 := by
    filter_upwards [hz] with x hx
    rw [mul_sub,hx,sub_self]
  exact (linear_factor_zero L he ha (hg.sub hh) hzero).mono fun _ h => sub_eq_zero.mp h

#print axioms linear_factor_unique
end BecknerOnofri.AnalyticParameterDivision
