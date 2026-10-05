import BecknerOnofri.Friedrichs.AngularFormDomain
import BecknerOnofri.Friedrichs.AngularWeakEquation

/-! Sine-weighted smooth profiles satisfy the spatial closed-form graph relation.
This theorem does not assume a spectral domain or define the spatial closure
using a Jacobi basis. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped ContDiff
namespace BecknerOnofri.Friedrichs.SpatialForm
open Legacy.BecknerOnofri.JacobiAngular

lemma inner_eq_integral_of_ae {u v : H} {f g : ℝ → ℝ}
    (hu : (u : ℝ → ℝ)=ᵐ[intervalMeasure] f)
    (hv : (v : ℝ → ℝ)=ᵐ[intervalMeasure] g) :
    inner ℝ u v=∫ t,f t*g t ∂intervalMeasure := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hu,hv] with t ht ht'
  simp [ht,ht',mul_comm]

lemma potential_product (m : ℕ) (f g : ℝ → ℝ) (t : ℝ) :
    (potentialFactor m t*f t)*(potentialFactor m t*g t)=
      ((m:ℝ)*((m:ℝ)-1)/(Real.sin t)^2)*f t*g t := by
  have hs := Real.sq_sqrt (jacobi_coefficient_nonneg m)
  dsimp [potentialFactor]
  calc
    _ = (Real.sqrt ((m:ℝ)*((m:ℝ)-1)))^2/(Real.sin t)^2*f t*g t := by ring
    _ = _ := by rw [hs]

def angularImageLp (m : ℕ) {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) : H :=
  (continuous_memLp (angularImage_continuous m hf)).toLp (angularImage m f)

theorem angular_operatorGraph {m : ℕ} (hm : 0<m) {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) :
    operatorGraph m (angularLift hm hf).1 (angularImageLp m hf) := by
  refine ⟨(angularLift hm hf).2.1,(angularLift hm hf).2.2,angular_mem_formClosure hm hf,?_⟩
  intro w hw
  obtain ⟨φ,hφ,hφc,hφs,hw0,hw1,hwV⟩ := hw
  have hend := compact_test_endpoints hφs
  have hu1 : ((angularLift hm hf).2.1 : ℝ → ℝ)=ᵐ[intervalMeasure] deriv (angular m f) :=
    (continuous_memLp (contDiff_infty_iff_deriv.mp (angular_smooth m hf)).2.continuous).coeFn_toLp
  have huV : ((angularLift hm hf).2.2 : ℝ → ℝ)=ᵐ[intervalMeasure]
      (fun t => potentialFactor m t*angular m f t) :=
    (potential_memLp (angular_smooth m hf).continuous m (angular_potential_integrable hm hf)).coeFn_toLp
  have hg : (angularImageLp m hf : ℝ → ℝ)=ᵐ[intervalMeasure] angularImage m f :=
    (continuous_memLp (angularImage_continuous m hf)).coeFn_toLp
  rw [inner_eq_integral_of_ae hu1 hw1,inner_eq_integral_of_ae huV hwV,
    inner_eq_integral_of_ae hg hw0]
  have hi1 : Integrable (fun t => deriv (angular m f) t*deriv φ t) intervalMeasure :=
    (((contDiff_infty_iff_deriv.mp (angular_smooth m hf)).2.continuous).mul
      (contDiff_infty_iff_deriv.mp hφ).2.continuous).integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hiV : Integrable (fun t => (potentialFactor m t*angular m f t)*
      (potentialFactor m t*φ t)) intervalMeasure := by
    have hi := L2.integrable_inner (𝕜 := ℝ) (angularLift hm hf).2.2 w.2.2
    apply hi.congr
    filter_upwards [huV,hwV] with t ht ht'
    simp [ht,ht',mul_comm]
  rw [← integral_add hi1 hiV]
  simp_rw [potential_product]
  exact angular_weak_conjugation m hf hφ hend.1 hend.2

#print axioms angular_operatorGraph
end BecknerOnofri.Friedrichs.SpatialForm
