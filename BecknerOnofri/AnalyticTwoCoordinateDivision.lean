module

public import BecknerOnofri.AnalyticParameterDivision

@[expose] public section

/-! Analytic divisibility by two scalar coordinates, including the coordinate
hyperplanes themselves. This is used for the squared-amplitude difference factor. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter
open scoped Topology
namespace BecknerOnofri.AnalyticParameterDivision
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem factor_zero {g : E × ℝ → ℝ} {a : E} (hg : AnalyticAt ℝ g (a,0))
    (he : ∀ᶠ x in 𝓝 (a,(0:ℝ)),x.2*g x=0) :
    ∀ᶠ x in 𝓝 (a,(0:ℝ)),g x=0 := by
  have hfactor : ∀ᶠ x in 𝓝 (a,(0:ℝ)),(0:ℝ)=x.2*g x := he.mono fun _ h => h.symm
  have haxis := factor_value_eventually hg hfactor
  have ht : Tendsto (Prod.fst : E × ℝ → E) (𝓝 (a,(0:ℝ))) (𝓝 a) :=
    continuous_fst.continuousAt
  filter_upwards [he,ht.eventually haxis] with x hx ha
  by_cases hx0 : x.2=0
  · simpa only [← hx0,deriv_const] using ha
  · exact (mul_eq_zero.mp hx).resolve_left hx0

theorem factor_unique {g h : E × ℝ → ℝ} {a : E}
    (hg : AnalyticAt ℝ g (a,0)) (hh : AnalyticAt ℝ h (a,0))
    (he : ∀ᶠ x in 𝓝 (a,(0:ℝ)),x.2*g x=x.2*h x) :
    g =ᶠ[𝓝 (a,(0:ℝ))] h := by
  have hz : ∀ᶠ x in 𝓝 (a,(0:ℝ)),x.2*(g x-h x)=0 := by
    filter_upwards [he] with x hx
    rw [mul_sub,hx,sub_self]
  exact (factor_zero (hg.sub hh) hz).mono fun _ h => sub_eq_zero.mp h

def swapScalars (x : (E × ℝ) × ℝ) : (E × ℝ) × ℝ := ((x.1.1,x.2),x.1.2)

theorem swapScalars_analytic (a : E) :
    AnalyticAt ℝ (swapScalars (E := E)) ((a,0),0) := by
  have h1 : AnalyticAt ℝ (fun x : (E × ℝ) × ℝ => x.1) ((a,0),0) := analyticAt_fst
  have h11 : AnalyticAt ℝ (fun x : (E × ℝ) × ℝ => x.1.1) ((a,0),0) :=
    analyticAt_fst.comp (f := fun x : (E × ℝ) × ℝ => x.1) h1
  have h12 : AnalyticAt ℝ (fun x : (E × ℝ) × ℝ => x.1.2) ((a,0),0) :=
    analyticAt_snd.comp (f := fun x : (E × ℝ) × ℝ => x.1) h1
  exact (h11.prod analyticAt_snd).prod h12

theorem swapScalars_tendsto (a : E) :
    Tendsto (swapScalars (E := E)) (𝓝 ((a,0),0)) (𝓝 ((a,0),0)) :=
  (swapScalars_analytic a).continuousAt.tendsto

/-- If an analytic function vanishes on both coordinate hyperplanes, it has
an analytic factor after division by their product, with arbitrary Banach parameters. -/
theorem exists_analytic_two_factor {f : (E × ℝ) × ℝ → ℝ} {a : E}
    (hf : AnalyticAt ℝ f ((a,0),0))
    (hu : ∀ᶠ x : E × ℝ in 𝓝 (a,0),f ((x.1,0),x.2)=0)
    (hv : ∀ᶠ x : E × ℝ in 𝓝 (a,0),f (x,0)=0) :
    ∃ g : (E × ℝ) × ℝ → ℝ, AnalyticAt ℝ g ((a,0),0) ∧
      ∀ᶠ x in 𝓝 ((a,0),(0:ℝ)),f x=x.1.2*x.2*g x := by
  obtain ⟨q,hq,he⟩ := exists_analytic_factor hf hv
  let axis : E × ℝ → (E × ℝ) × ℝ := fun x => ((x.1,0),x.2)
  have ha : AnalyticAt ℝ axis (a,0) :=
    (analyticAt_fst.prod analyticAt_const).prod analyticAt_snd
  have hq0 : AnalyticAt ℝ (fun x : E × ℝ => q (axis x)) (a,0) := hq.comp (f := axis) ha
  have hz : ∀ᶠ x in 𝓝 (a,(0:ℝ)),x.2*q (axis x)=0 := by
    filter_upwards [ha.continuousAt.tendsto.eventually he,hu] with x hx hu
    exact hx.symm.trans hu
  have hzero := factor_zero hq0 hz
  have hqs : AnalyticAt ℝ (fun x => q (swapScalars x)) ((a,0),0) :=
    hq.comp (f := swapScalars) (swapScalars_analytic a)
  obtain ⟨g,hg,heg⟩ := exists_analytic_factor hqs hzero
  refine ⟨fun x => g (swapScalars x),hg.comp (f := swapScalars) (swapScalars_analytic a),?_⟩
  filter_upwards [he,(swapScalars_tendsto a).eventually heg] with x hx hgx
  change q x=x.1.2*g (swapScalars x) at hgx
  rw [hx,hgx]
  ring

#print axioms factor_unique
#print axioms exists_analytic_two_factor
end BecknerOnofri.AnalyticParameterDivision
