import BecknerOnofri.HeatEnergyLimit

/-! The actual heat convolution contracts L1 distances between densities. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped Convolution Topology
namespace BecknerOnofri.HighDim.HeatApproximation
open Legacy.BecknerOnofri.HeatDensityApproximation

local instance (d : ℕ) : (torusMeasure d).IsAddRightInvariant := by
  unfold torusMeasure
  infer_instance

def l1distance {d : ℕ} (f g : Torus d → ℝ) : ℝ :=
  ∫ x, ‖f x-g x‖ ∂torusMeasure d

lemma l1distance_triangle {d : ℕ} {f g h : Torus d → ℝ}
    (hf : Integrable f (torusMeasure d)) (hg : Integrable g (torusMeasure d))
    (hh : Integrable h (torusMeasure d)) :
    l1distance f h ≤ l1distance f g + l1distance g h := by
  unfold l1distance
  have he := integral_add (hf.sub hg).norm (hg.sub hh).norm
  simp only [Pi.sub_apply] at he
  rw [← he]
  apply integral_mono (hf.sub hh).norm ((hf.sub hg).norm.add (hg.sub hh).norm)
  intro x
  exact norm_sub_le_norm_sub_add_norm_sub _ _ _

lemma l1distance_symm {d : ℕ} (f g : Torus d → ℝ) : l1distance f g = l1distance g f := by
  unfold l1distance
  simp only [norm_sub_rev]

theorem heat_l1_contraction {d : ℕ} (ρ η : Legacy.TorusEndpoint.ProbabilityDensity d)
    {t : ℝ} (ht : 0 < t) :
    l1distance (heatValue ρ t) (heatValue η t) ≤ l1distance ρ.value η.value := by
  let f : Torus d → ℝ := fun x => ‖ρ.value x-η.value x‖
  have hf : Integrable f (torusMeasure d) := (ρ.integrable.sub η.integrable).norm
  have hi := hf.integrable_convolution (ContinuousLinearMap.mul ℝ ℝ) (heatKernel_integrable ht)
  have hpoint (x : Torus d) : ‖heatValue ρ t x-heatValue η t x‖ ≤
      (f ⋆[ContinuousLinearMap.mul ℝ ℝ, torusMeasure d] heatKernel t) x := by
    change ‖(∫ y, ρ.value y*heatKernel t (x-y) ∂torusMeasure d)-
      (∫ y, η.value y*heatKernel t (x-y) ∂torusMeasure d)‖ ≤ _
    have hiρ : Integrable (fun y => ρ.value y*heatKernel t (x-y)) (torusMeasure d) :=
      heatValue_integrand_integrable ρ ht x
    have hiη : Integrable (fun y => η.value y*heatKernel t (x-y)) (torusMeasure d) :=
      heatValue_integrand_integrable η ht x
    rw [← integral_sub hiρ hiη]
    convert! norm_integral_le_integral_norm
      (fun y => ρ.value y*heatKernel t (x-y)-η.value y*heatKernel t (x-y)) using 1
    apply integral_congr_ae
    filter_upwards with y
    simp only [← sub_mul, norm_mul, Real.norm_of_nonneg (heatKernel_pos ht (x-y)).le, f,
      ContinuousLinearMap.mul_apply']
  have hiρ : Integrable (heatValue ρ t) (torusMeasure d) := heatValue_integrable ρ ht
  have hiη : Integrable (heatValue η t) (torusMeasure d) := heatValue_integrable η ht
  have h := integral_mono (hiρ.sub hiη).norm
    hi hpoint
  have hk : Integrable (heatKernel (d := d) t) (torusMeasure d) := heatKernel_integrable ht
  have hm : (∫ x, heatKernel (d := d) t x ∂torusMeasure d) = 1 := heatKernel_mass ht
  rw [integral_convolution (ContinuousLinearMap.mul ℝ ℝ) hf hk, hm] at h
  simpa only [ContinuousLinearMap.mul_apply', mul_one, l1distance, f, Pi.sub_apply] using! h

#print axioms heat_l1_contraction
end BecknerOnofri.HighDim.HeatApproximation
