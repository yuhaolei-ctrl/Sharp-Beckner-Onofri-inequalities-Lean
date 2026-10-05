import BecknerOnofri.Friedrichs.FormNormIdentity
import BecknerOnofri.Friedrichs.AngularCutoffApproximation

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace BecknerOnofri.Friedrichs.SpatialForm

lemma continuous_memLp {h : ℝ → ℝ} (hc : Continuous h) : MemLp h 2 intervalMeasure :=
  (memLp_two_iff_integrable_sq hc.aestronglyMeasurable).mpr
    ((hc.pow 2).integrableOn_Icc.mono_set Ioo_subset_Icc_self)

def lift (m : ℕ) (h : ℝ → ℝ) (h0 : MemLp h 2 intervalMeasure)
    (h1 : MemLp (deriv h) 2 intervalMeasure)
    (hV : MemLp (fun t => potentialFactor m t*h t) 2 intervalMeasure) : EnergySpace :=
  (h0.toLp h,(h1.toLp (deriv h),hV.toLp (fun t => potentialFactor m t*h t)))

lemma lift_mem_core (m : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    (hs : HasCompactSupport h) (ht : tsupport h ⊆ Ioo 0 Real.pi)
    (h0 : MemLp h 2 intervalMeasure) (h1 : MemLp (deriv h) 2 intervalMeasure)
    (hV : MemLp (fun t => potentialFactor m t*h t) 2 intervalMeasure) :
    lift m h h0 h1 hV ∈ core m :=
  ⟨h,hh,hs,ht,h0.coeFn_toLp,h1.coeFn_toLp,hV.coeFn_toLp⟩

lemma integral_sq_sub {h g : ℝ → ℝ} (hh : MemLp h 2 intervalMeasure)
    (hg : MemLp g 2 intervalMeasure) :
    (∫ t,(h t-g t)^2 ∂intervalMeasure)=‖hh.toLp h-hg.toLp g‖^2 := by
  have he := integral_sq_toLp (hh.sub hg)
  rw [MemLp.toLp_sub hh hg] at he
  exact he

lemma formNorm_sub_identity (m : ℕ) {h g : ℝ → ℝ}
    (hh : Differentiable ℝ h) (hg : Differentiable ℝ g)
    (h0 : MemLp h 2 intervalMeasure) (g0 : MemLp g 2 intervalMeasure)
    (h1 : MemLp (deriv h) 2 intervalMeasure) (g1 : MemLp (deriv g) 2 intervalMeasure)
    (hV : MemLp (fun t => potentialFactor m t*h t) 2 intervalMeasure)
    (gV : MemLp (fun t => potentialFactor m t*g t) 2 intervalMeasure) :
    spatialFormNormSq m (h-g)=
      ‖(lift m h h0 h1 hV).1-(lift m g g0 g1 gV).1‖^2+
      ‖(lift m h h0 h1 hV).2.1-(lift m g g0 g1 gV).2.1‖^2+
      ‖(lift m h h0 h1 hV).2.2-(lift m g g0 g1 gV).2.2‖^2 := by
  have hd : deriv (h-g)=deriv h-deriv g := funext (fun t => deriv_sub (hh t) (hg t))
  have hv : (fun t => potentialFactor m t*(h-g) t)=
      (fun t => potentialFactor m t*h t)-(fun t => potentialFactor m t*g t) := by
    funext t
    simp only [Pi.sub_apply]
    ring
  have he := formNorm_identity m (h0.sub g0) (by rw [hd]; exact h1.sub g1)
    (by rw [hv]; exact hV.sub gV)
  simpa only [hd,hv,lift,MemLp.toLp_sub (h0) (g0),
    MemLp.toLp_sub (h1) (g1),MemLp.toLp_sub (hV) (gV)] using he

lemma tendsto_of_norm_sq {ι : Type*} {l : Filter ι} {E : Type*}
    [NormedAddCommGroup E] {v : ι → E} {w : E}
    (h : Tendsto (fun i => ‖v i-w‖^2) l (𝓝 (0:ℝ))) : Tendsto v l (𝓝 w) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp h
  simpa only [Function.comp_def,Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero] using hs

lemma energy_tendsto {ι : Type*} {l : Filter ι} {v : ι → EnergySpace} {w : EnergySpace}
    (ht : Tendsto (fun i => ‖(v i).1-w.1‖^2+‖(v i).2.1-w.2.1‖^2+
      ‖(v i).2.2-w.2.2‖^2) l (𝓝 (0:ℝ))) : Tendsto v l (𝓝 w) := by
  have h0 : Tendsto (fun i => ‖(v i).1-w.1‖^2) l (𝓝 (0:ℝ)) := by
    apply squeeze_zero (fun _ => sq_nonneg _) _ ht
    intro i
    nlinarith [sq_nonneg (‖(v i).2.1-w.2.1‖), sq_nonneg (‖(v i).2.2-w.2.2‖)]
  have h1 : Tendsto (fun i => ‖(v i).2.1-w.2.1‖^2) l (𝓝 (0:ℝ)) := by
    apply squeeze_zero (fun _ => sq_nonneg _) _ ht
    intro i
    nlinarith [sq_nonneg (‖(v i).1-w.1‖), sq_nonneg (‖(v i).2.2-w.2.2‖)]
  have h2 : Tendsto (fun i => ‖(v i).2.2-w.2.2‖^2) l (𝓝 (0:ℝ)) := by
    apply squeeze_zero (fun _ => sq_nonneg _) _ ht
    intro i
    nlinarith [sq_nonneg (‖(v i).1-w.1‖), sq_nonneg (‖(v i).2.1-w.2.1‖)]
  simpa only [← nhds_prod_eq] using
    (tendsto_of_norm_sq h0).prodMk ((tendsto_of_norm_sq h1).prodMk (tendsto_of_norm_sq h2))

#print axioms formNorm_sub_identity
end BecknerOnofri.Friedrichs.SpatialForm
