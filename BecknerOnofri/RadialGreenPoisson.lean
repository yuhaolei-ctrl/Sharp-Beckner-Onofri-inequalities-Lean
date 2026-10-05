import BecknerOnofri.RadialGreenHeat
import BecknerOnofri.RadialGreenE1
import BecknerOnofri.RadialPoissonImages

/-! Poisson summation and absolutely justified time integration for the
actual twelve-dimensional heat representative. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped BigOperators Topology
namespace BecknerOnofri.HighDim.RadialGreenPoisson
open Legacy.BecknerOnofri Legacy.TorusEndpoint
open GreenHeatPointwise TorusLogIntegrability RadialGreenHeat ShiftedGaussianBound

def imageRadius (x : Fin 12 → ℝ) (k : Frequency 12) : ℝ := ∑ i,((k i:ℝ)+x i)^2

def imageTerm (x : Fin 12 → ℝ) (k : Frequency 12) (t : ℝ) : ℝ :=
  Real.exp (-(Real.pi^2*imageRadius x k)/t)/t

theorem imageRadius_pos (x : Fin 12 → ℝ) (hx : ∀ i,|x i|≤1/2) (hx0 : x≠0)
    (k : Frequency 12) : 0 < imageRadius x k := by
  by_cases hk : k=0
  · subst k
    simpa only [imageRadius,coordinateRadiusSq,Pi.zero_apply,Int.cast_zero,zero_add] using coordinateRadiusSq_pos hx0
  · obtain ⟨i,hi⟩ := Function.ne_iff.mp hk
    have hi0 : k i≠0 := hi
    have hn : (1:ℝ)≤|(k i:ℝ)| := by exact_mod_cast Int.one_le_abs hi0
    have hne : (k i:ℝ)+x i≠0 := by
      intro he
      have he' : (k i:ℝ)= -x i := by linarith
      rw [he',abs_neg] at hn
      linarith [hx i]
    exact Finset.sum_pos' (fun _ _ => sq_nonneg _) ⟨i,Finset.mem_univ _,sq_pos_of_ne_zero hne⟩

theorem shiftedGaussian_eq_image (x : Fin 12 → ℝ) {t : ℝ} (ht : 0<t)
    (k : Frequency 12) : shiftedGaussian (t/Real.pi) x (-k)=t*imageTerm x k t := by
  have he : shiftedRadiusSq x (-k)=imageRadius x k := by
    unfold shiftedRadiusSq imageRadius
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.neg_apply,Int.cast_neg]
    ring
  unfold shiftedGaussian imageTerm
  rw [he,mul_div_cancel₀ _ ht.ne']
  congr 1
  field_simp

theorem imageTerm_summable (x : Fin 12 → ℝ) {t : ℝ} (ht : 0<t) :
    Summable (fun k => imageTerm x k t) := by
  have hs := ((Equiv.neg (Frequency 12)).summable_iff.mpr
    (summable_shiftedGaussian (div_pos ht Real.pi_pos) x)).div_const t
  apply hs.congr
  intro k
  change shiftedGaussian (t/Real.pi) x (-k)/t=imageTerm x k t
  rw [shiftedGaussian_eq_image x ht,mul_div_cancel_left₀ _ ht.ne']

theorem imageTerm_nonneg (x : Fin 12 → ℝ) (k : Frequency 12) {t : ℝ} (ht : 0≤t) :
    0 ≤ imageTerm x k t := div_nonneg (Real.exp_pos _).le ht

theorem weighted_heat_eq_images (x : Fin 12 → ℝ) {t : ℝ} (ht : 0<t) :
    t^5*(∏ i,RadialThetaTail.theta t (x i))=Real.pi^6*∑' k,imageTerm x k t := by
  have hp := heatKernel_eq_theta_product (div_pos ht Real.pi_pos) x
  rw [mul_div_cancel₀ t Real.pi_pos.ne'] at hp
  have hp2 : HeatDensityApproximation.heatKernel (t/Real.pi) (quotientPoint x)=
      (t/Real.pi)^(-((12:ℝ))/2)*(∑' k,shiftedGaussian (t/Real.pi) x k) :=
    heatKernel_eq_shiftedGaussian (div_pos ht Real.pi_pos) x
  rw [← hp,hp2]
  have hg : (∑' k,shiftedGaussian (t/Real.pi) x k)=t*∑' k,imageTerm x k t := by
    rw [← (Equiv.neg (Frequency 12)).tsum_eq (fun k=>shiftedGaussian (t/Real.pi) x k)]
    simp only [Equiv.neg_apply,shiftedGaussian_eq_image x ht,tsum_mul_left]
  rw [hg]
  rw [show -(12:ℝ)/2= -(6:ℝ) by norm_num,
    Real.rpow_neg (div_pos ht Real.pi_pos).le,
    show (6:ℝ)=((6:ℕ):ℝ) by norm_num,Real.rpow_natCast]
  field_simp
  <;> ring

theorem imageTerm_measurable (x : Fin 12 → ℝ) (k : Frequency 12) :
    Measurable (imageTerm x k) :=
  (Real.measurable_exp.comp (measurable_const.div measurable_id)).div measurable_id

theorem imageTerm_integral (x : Fin 12 → ℝ) (hx : ∀ i,|x i|≤1/2) (hx0 : x≠0)
    (k : Frequency 12) :
    (∫ t in Ioo (0:ℝ) 1,imageTerm x k t)=RadialE1.E1 (Real.pi^2*imageRadius x k) :=
  RadialGreenE1.reciprocal_integral (mul_pos (sq_pos_of_pos Real.pi_pos) (imageRadius_pos x hx hx0 k))

theorem integrable_small_power : IntegrableOn (fun t : ℝ => t^5) (Ioo (0:ℝ) 1) :=
  ((continuous_id.pow 5).integrableOn_Icc).mono_set Ioo_subset_Icc_self

theorem integrable_imageSum (x : Fin 12 → ℝ) (hx : ∀ i,|x i|≤1/2) (hx0 : x≠0) :
    IntegrableOn (fun t => ∑' k,imageTerm x k t) (Ioo (0:ℝ) 1) := by
  have hi := (((sourceMellin_integrable x hx hx0).mono_set (fun _ ht=>ht.1)).add
    integrable_small_power).div_const (Real.pi^6)
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  have he : sourceMellin x t+t^5=t^5*(∏ i,RadialThetaTail.theta t (x i)) := by
    unfold sourceMellin
    ring
  dsimp only [Pi.add_apply]
  rw [he,weighted_heat_eq_images x ht.1,mul_div_cancel_left₀ _ (pow_ne_zero _ Real.pi_pos.ne')]

/-- The entire positive Poisson image sum is integrated by a genuine dominated
convergence argument. This proves summability of all E1 images as well. -/
theorem hasSum_imageIntegrals (x : Fin 12 → ℝ) (hx : ∀ i,|x i|≤1/2) (hx0 : x≠0) :
    HasSum (fun k => RadialE1.E1 (Real.pi^2*imageRadius x k))
      (∫ t in Ioo (0:ℝ) 1,∑' k,imageTerm x k t) := by
  have hh := hasSum_integral_of_dominated_convergence (fun k t=>imageTerm x k t)
    (fun k=>(imageTerm_measurable x k).aestronglyMeasurable)
    (fun k=>by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      rw [Real.norm_eq_abs,abs_of_nonneg (imageTerm_nonneg x k ht.1.le)])
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      exact imageTerm_summable x ht.1)
    (integrable_imageSum x hx hx0)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      exact (imageTerm_summable x ht.1).hasSum)
  simpa only [imageTerm_integral x hx hx0] using hh

/-- The exact large-time heat part used by the source. -/
def heatPart (x : Fin 12 → ℝ) : ℝ := (1/120:ℝ)*∫t in Ioi 1,sourceMellin x t

theorem sourceMellin_split (x : Fin 12 → ℝ) (hx : ∀ i,|x i|≤1/2) (hx0 : x≠0) :
    (∫t in Ioi 0,sourceMellin x t)=
      (∫t in Ioo (0:ℝ) 1,sourceMellin x t)+(∫t in Ioi 1,sourceMellin x t) := by
  have hh := intervalIntegral.integral_Ioi_sub_Ioi (sourceMellin_integrable x hx hx0) (by norm_num : (0:ℝ)≤1)
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),integral_Ioc_eq_integral_Ioo] at hh
  linarith

theorem integral_small_power : (∫t in Ioo (0:ℝ) 1,t^5)=(1/6:ℝ) := by
  rw [← integral_Ioc_eq_integral_Ioo,← intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)]
  norm_num [integral_pow]

/-- Exact source Poisson decomposition with its genuine -1/Γ(7) constant. -/
theorem green_poisson (x : Fin 12 → ℝ) (hx : ∀ i,|x i|≤1/2) (hx0 : x≠0) :
    green x=(Real.pi^6/120)*(∑' k,RadialE1.E1 (Real.pi^2*imageRadius x k))-
      1/720+heatPart x := by
  have he : (∫t in Ioo (0:ℝ) 1,sourceMellin x t)=
      Real.pi^6*(∑' k,RadialE1.E1 (Real.pi^2*imageRadius x k))-1/6 := by
    have hi : (∫t in Ioo (0:ℝ) 1,sourceMellin x t)=
        ∫t in Ioo (0:ℝ) 1,(Real.pi^6*(∑'k,imageTerm x k t)-t^5) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      rw [← weighted_heat_eq_images x ht.1,sourceMellin]
      ring
    rw [hi,integral_sub ((integrable_imageSum x hx hx0).const_mul _) integrable_small_power,
      integral_const_mul,← (hasSum_imageIntegrals x hx hx0).tsum_eq,integral_small_power]
  rw [green_eq_sourceMellin,sourceMellin_split x hx hx0,he,heatPart]
  ring

#print axioms hasSum_imageIntegrals
#print axioms green_poisson
end BecknerOnofri.HighDim.RadialGreenPoisson
