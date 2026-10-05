module

public import BecknerOnofri.Friedrichs.SpatialFormDefinitions
public import BecknerOnofri.Friedrichs.SmoothCutoffApproximation

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
namespace BecknerOnofri.Friedrichs.SpatialForm

lemma integral_sq_toLp {h : ℝ → ℝ} (hh : MemLp h 2 intervalMeasure) :
    (∫ t,(h t)^2 ∂intervalMeasure)=‖hh.toLp h‖^2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hh.coeFn_toLp] with t ht
  simp [ht,pow_two,real_inner_comm]

lemma potential_sq (m : ℕ) (h : ℝ → ℝ) (t : ℝ) :
    (potentialFactor m t*h t)^2=(m:ℝ)*((m:ℝ)-1)*(h t/Real.sin t)^2 := by
  simp only [potentialFactor,mul_pow,div_pow,Real.sq_sqrt (jacobi_coefficient_nonneg m)]
  ring

lemma potential_memLp {h : ℝ → ℝ} (hc : Continuous h) (m : ℕ)
    (hi : IntegrableOn (fun t => (h t/Real.sin t)^2) (Set.Ioo 0 Real.pi)) :
    MemLp (fun t => potentialFactor m t*h t) 2 intervalMeasure := by
  apply (memLp_two_iff_integrable_sq
    ((measurable_const.div Real.measurable_sin).mul hc.measurable).aestronglyMeasurable).mpr
  change Integrable (fun t => (potentialFactor m t*h t)^2) intervalMeasure
  simp_rw [potential_sq]
  exact hi.const_mul ((m:ℝ)*((m:ℝ)-1))

lemma formNorm_identity (m : ℕ) {h : ℝ → ℝ}
    (h0 : MemLp h 2 intervalMeasure) (h1 : MemLp (deriv h) 2 intervalMeasure)
    (hV : MemLp (fun t => potentialFactor m t*h t) 2 intervalMeasure) :
    spatialFormNormSq m h=‖h0.toLp h‖^2+‖h1.toLp (deriv h)‖^2+
      ‖hV.toLp (fun t => potentialFactor m t*h t)‖^2 := by
  have hi0 := (memLp_two_iff_integrable_sq h0.aestronglyMeasurable).mp h0
  have hi1 := (memLp_two_iff_integrable_sq h1.aestronglyMeasurable).mp h1
  have hiV := (memLp_two_iff_integrable_sq hV.aestronglyMeasurable).mp hV
  change (∫ t, h t^2+(deriv h t)^2+(m:ℝ)*((m:ℝ)-1)*(h t/Real.sin t)^2 ∂intervalMeasure)=_
  simp_rw [← potential_sq]
  have he := (integral_add (hi0.add hi1) hiV).trans
    (congrArg (fun z => z+∫ t,(potentialFactor m t*h t)^2 ∂intervalMeasure) (integral_add hi0 hi1))
  simpa only [Pi.add_apply,integral_sq_toLp h0,integral_sq_toLp h1,integral_sq_toLp hV] using he

#print axioms formNorm_identity
end BecknerOnofri.Friedrichs.SpatialForm
