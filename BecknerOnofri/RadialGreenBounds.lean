module

public import BecknerOnofri.RadialGreenPoisson
public import BecknerOnofri.RadialPoissonBound

@[expose] public section

/-! Actual Haar-a.e. radial domination and the complete diagonal E1/image
bound for the normalized Green kernel. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter Classical
open scoped BigOperators Topology
namespace BecknerOnofri.HighDim.RadialGreenHeat
open Legacy.BecknerOnofri Legacy.TorusEndpoint
open GreenHeatPointwise TorusLogIntegrability SpatialThetaDiagonal RadialGreenPoisson

theorem radialGreen_measurable (d : ℕ) : Measurable (radialGreen d) := by
  have ha : Continuous (radialAngle d) :=
    (Real.continuous_arcsin.comp (Real.continuous_sqrt.comp (continuous_id.div_const _))).div_const _
  have hq : Continuous (fun S => quotientPoint (fun _ : Fin d => radialAngle d S)) := by
    apply continuous_pi
    intro i
    exact (AddCircle.continuous_mk' (1:ℝ)).comp ha
  exact measurable_const.mul ((measurable_heatGreen d).comp hq.measurable)

/-- A.e. domination of the original Fourier-constructed normalized Green
kernel by the exact radial profile, in the actual Haar measure. -/
theorem kernel_le_radialGreen_ae {d : ℕ} (hd : 0<d) :
    ∀ᵐ x ∂torusMeasure d,GreenRoughEnergy.kernel d x≤radialGreen d (ArcsineProductBins.radialSum x) := by
  have hh : ∀ᵐ x ∂torusMeasure d,endpointSigma d*heatGreen x≤
      radialGreen d (ArcsineProductBins.radialSum x) := by
    apply ae_of_cell_except_zero hd
      (measurableSet_le (measurable_const.mul (measurable_heatGreen d))
        ((radialGreen_measurable d).comp (ArcsineProductBins.radialSum_continuous d).measurable))
    intro x hx hx0
    have he : ArcsineProductBins.radialSum (quotientPoint x)=sineSquareSum x :=
      ArcsineProductBins.radialSum_coe x
    dsimp only [Pi.mul_apply,Function.comp_apply]
    rw [he]
    exact green_le_radialGreen hd x (centeredCell_coordinates hx) hx0
  filter_upwards [hh,kernel_eq_heatGreen_ae hd] with x hx he
  exact he.trans_le hx

theorem diagonal_image_sum_split {y : ℝ} (hy : 0<y) (hy' : y≤1/2) :
    (∑' k : Frequency 12,RadialE1.E1 (Real.pi^2*imageRadius (fun _ => y) k))=
      RadialE1.E1 (Real.pi^2*12*y^2)+
      ∑' k : RadialPoissonImages.NonzeroImage 12,RadialE1.E1 (Real.pi^2*RadialPoissonImages.radius y k.val) := by
  have hx : ∀ i : Fin 12,|(fun _ : Fin 12=>y) i|≤1/2 := by intro i; rwa [abs_of_pos hy]
  have hx0 : (fun _ : Fin 12=>y)≠0 := by
    intro he
    have hz : y=0 := congrFun he 0
    exact hy.ne' hz
  have hh := (hasSum_imageIntegrals (fun _ => y) hx hx0).summable.sum_add_tsum_compl
    (s := ({0} : Finset (Frequency 12)))
  simp only [Finset.sum_singleton] at hh
  rw [← hh]
  congr 1
  · simp only [imageRadius,Pi.zero_apply,Int.cast_zero,zero_add,Finset.sum_const,
      Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    congr 1
    ring
  · have hset : ((↑({0} : Finset (Frequency 12)) : Set (Frequency 12))ᶜ)={k | k≠0} := by
      ext k
      simp
    rw [hset]
    rfl

/-- Complete actual radial upper bound: one singular E1 term, every nonzero
Poisson image bounded by J12, the exact mean subtraction, and the heat tail. -/
theorem diagonal_green_le_E1_images_heat {y : ℝ} (hy : 0<y) (hy' : y≤1/2) :
    green (fun _ : Fin 12 => y)≤
      (Real.pi^6/120)*RadialE1.E1 (Real.pi^2*12*y^2)+RadialPoissonImages.J12-
        1/720+heatPart (fun _ => y) := by
  have hx : ∀ i : Fin 12,|(fun _ : Fin 12=>y) i|≤1/2 := by intro i; rwa [abs_of_pos hy]
  have hx0 : (fun _ : Fin 12=>y)≠0 := by
    intro he
    exact hy.ne' (congrFun he 0)
  have hg : Real.Gamma 6=120 := by
    convert Real.Gamma_nat_eq_factorial 5 using 1 <;> norm_num
  have hb := RadialPoissonImages.diagonal_nonzero_images_le_J12 hy.le hy'
  rw [hg] at hb
  rw [green_poisson _ hx hx0,diagonal_image_sum_split hy hy',mul_add]
  linarith

theorem radialGreen_le_E1_images_heat {S : ℝ} (hS : S∈Ioc (0:ℝ) 12) :
    radialGreen 12 S≤
      (Real.pi^6/120)*RadialE1.E1 (Real.pi^2*12*(radialAngle 12 S)^2)+RadialPoissonImages.J12-
        1/720+heatPart (fun _ => radialAngle 12 S) := by
  have hy := radialAngle_mem (by norm_num : 0<12) ⟨hS.1.le,hS.2⟩
  have hy0 : 0<radialAngle 12 S := by
    apply lt_of_le_of_ne hy.1
    intro he
    apply diagonal_nonzero (by norm_num : 0<12) hS
    funext i
    exact he.symm
  exact diagonal_green_le_E1_images_heat hy0 hy.2

#print axioms kernel_le_radialGreen_ae
#print axioms radialGreen_le_E1_images_heat
end BecknerOnofri.HighDim.RadialGreenHeat
