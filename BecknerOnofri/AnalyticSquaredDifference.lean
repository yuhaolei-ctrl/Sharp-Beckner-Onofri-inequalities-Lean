module

public import BecknerOnofri.AnalyticTwoCoordinateDivision

@[expose] public section

/-! Analytic squared-amplitude divisibility from permutation and reflection
symmetry, without treating a formal series as a convergent analytic function. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter
open scoped Topology
namespace BecknerOnofri.AnalyticParameterDivision
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_analytic_squared_difference_factor {f : (E × ℝ) × ℝ → ℝ} {a : E}
    (hf : AnalyticAt ℝ f ((a,0),0))
    (hswap : ∀ᶠ x in 𝓝 ((a,0),(0:ℝ)),f ((x.1.1,x.2),x.1.2) = -f x)
    (heven : ∀ᶠ x in 𝓝 ((a,0),(0:ℝ)),f (x.1,-x.2)=f x) :
    ∃ g : (E × ℝ) × ℝ → ℝ, AnalyticAt ℝ g ((a,0),0) ∧
      ∀ᶠ x in 𝓝 ((a,0),(0:ℝ)), f x=(x.1.2^2-x.2^2)*g x := by
  let T : (E × ℝ) × ℝ → (E × ℝ) × ℝ := fun x => ((x.1.1,x.1.2+x.2),x.1.2-x.2)
  let R : (E × ℝ) × ℝ → (E × ℝ) × ℝ := fun x => ((x.1.1,(x.1.2+x.2)/2),(x.1.2-x.2)/2)
  have hp : AnalyticAt ℝ (fun x : (E × ℝ) × ℝ => x.1.1) ((a,0),0) :=
    analyticAt_fst.comp (f := fun x : (E × ℝ) × ℝ => x.1) analyticAt_fst
  have hu : AnalyticAt ℝ (fun x : (E × ℝ) × ℝ => x.1.2) ((a,0),0) :=
    analyticAt_snd.comp (f := fun x : (E × ℝ) × ℝ => x.1) analyticAt_fst
  have hv : AnalyticAt ℝ (fun x : (E × ℝ) × ℝ => x.2) ((a,0),0) := analyticAt_snd
  have hT : AnalyticAt ℝ T ((a,0),0) := (hp.prod (hu.add hv)).prod (hu.sub hv)
  have hR : AnalyticAt ℝ R ((a,0),0) := by
    simpa only [R,div_eq_mul_inv,Pi.mul_apply,Pi.add_apply,Pi.sub_apply] using
      (hp.prod ((hu.add hv).mul analyticAt_const)).prod ((hu.sub hv).mul analyticAt_const)
  have hT0 : T ((a,0),0)=((a,0),0) := by simp [T]
  have hR0 : R ((a,0),0)=((a,0),0) := by simp [R]
  have hf' : AnalyticAt ℝ f (T ((a,0),0)) := by simpa only [hT0] using hf
  have hF := hf'.comp (f := T) hT
  have hdiag : Tendsto (fun x : E × ℝ => ((x.1,x.2),x.2))
      (𝓝 (a,0)) (𝓝 ((a,0),(0:ℝ))) :=
    ((continuous_fst.prodMk continuous_snd).prodMk continuous_snd).continuousAt
  have hz : ∀ᶠ x : E × ℝ in 𝓝 (a,0),f ((x.1,x.2),x.2)=0 := by
    filter_upwards [hdiag.eventually hswap] with x hx
    change f ((x.1,x.2),x.2) = -f ((x.1,x.2),x.2) at hx
    linarith
  have hzeroV : ∀ᶠ x : E × ℝ in 𝓝 (a,0),f (T (x,0))=0 := by
    simpa only [T,add_zero,sub_zero] using hz
  have hzeroU : ∀ᶠ x : E × ℝ in 𝓝 (a,0),f (T ((x.1,0),x.2))=0 := by
    filter_upwards [hz,hdiag.eventually heven] with x hx he
    simpa only [T,zero_add,zero_sub] using he.trans hx
  obtain ⟨g,hg,he⟩ := exists_analytic_two_factor hF hzeroU hzeroV
  have hg' : AnalyticAt ℝ g (R ((a,0),0)) := by simpa only [hR0] using hg
  refine ⟨fun x => g (R x)/4,?_,?_⟩
  · have hc : AnalyticAt ℝ (fun _ : (E × ℝ) × ℝ => (1/4:ℝ)) ((a,0),0) := analyticAt_const
    convert! (hg'.comp (f := R) hR).mul hc using 1
    ext x
    simp only [Pi.mul_apply,Function.comp_def]
    ring
  · have hRt : Tendsto R (𝓝 ((a,0),(0:ℝ))) (𝓝 ((a,0),(0:ℝ))) := by
      simpa only [hR0] using hR.continuousAt.tendsto
    filter_upwards [hRt.eventually he] with x hx
    have hTR : T (R x)=x := by
      apply Prod.ext
      · apply Prod.ext
        · rfl
        · dsimp [T,R]; ring
      · dsimp [T,R]; ring
    change f (T (R x))=(R x).1.2*(R x).2*g (R x) at hx
    rw [hTR] at hx
    rw [hx]
    dsimp only [R]
    ring

#print axioms exists_analytic_squared_difference_factor
end BecknerOnofri.AnalyticParameterDivision
