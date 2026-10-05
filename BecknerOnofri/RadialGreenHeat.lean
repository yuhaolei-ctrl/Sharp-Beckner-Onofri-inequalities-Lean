module

public import BecknerOnofri.SpatialThetaComparison
public import BecknerOnofri.ArcsineProductBins
public import BecknerOnofri.SubcriticalGap
public import Legacy.BecknerOnofri.GreenExponentialIntegrability

@[expose] public section

/-! The actual normalized Green kernel, its heat representative, and the
spatial-theta radial comparison. The Fourier kernel is identified almost
everywhere; all pointwise integrals below are used away from the singularity. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped BigOperators Topology
namespace BecknerOnofri.HighDim.RadialGreenHeat
open Legacy.BecknerOnofri Legacy.TorusEndpoint
open GreenHeatPointwise TorusLogIntegrability SpatialThetaDiagonal

/-- A pointwise representative of the actual normalized Fourier Green kernel. -/
def green {d : ℕ} (x : Fin d → ℝ) : ℝ := endpointSigma d*heatGreen (quotientPoint x)

def radialGreen (d : ℕ) (S : ℝ) : ℝ := green (fun _ : Fin d => radialAngle d S)

theorem kernel_eq_heatGreen_ae {d : ℕ} (hd : 0<d) :
    GreenRoughEnergy.kernel d =ᵐ[torusMeasure d] (fun x => endpointSigma d*heatGreen x) := by
  filter_upwards [GreenExponentialIntegrability.heatGreen_eq_realGreen_ae hd] with x hx
  exact congrArg (fun a => endpointSigma d*a) hx.symm

theorem kernel_eq_green_on_cell_ae {d : ℕ} (hd : 0<d) :
    (fun x => GreenRoughEnergy.kernel d (quotientPoint x)) =ᵐ[volume.restrict (centeredCell d)] green :=
  (quotientPoint_measurePreserving d).quasiMeasurePreserving.ae_eq_comp (kernel_eq_heatGreen_ae hd)

theorem heatKernel_eq_theta_product {d : ℕ} {t : ℝ} (ht : 0<t) (x : Fin d → ℝ) :
    HeatDensityApproximation.heatKernel t (quotientPoint x)=
      ∏ i,RadialThetaTail.theta (Real.pi*t) (x i) := by
  unfold HeatDensityApproximation.heatKernel
  rw [TorusHeatPositivity.torusTheta_eq_ofReal_product ht,Complex.ofReal_re]
  apply Finset.prod_congr rfl
  intro i _
  unfold RadialThetaTail.theta CircleHeat.realHeat
  rw [mul_div_cancel_left₀ t Real.pi_pos.ne']
  rfl

theorem sineSquareSum_pos {d : ℕ} {x : Fin d → ℝ}
    (hx : ∀ i,|x i|≤1/2) (hx0 : x≠0) : 0<sineSquareSum x := by
  obtain ⟨i,hi⟩ := Function.ne_iff.mp hx0
  apply Finset.sum_pos' (fun _ _ => sq_nonneg _)
  refine ⟨i,Finset.mem_univ _,sq_pos_of_ne_zero ?_⟩
  intro hs
  have hmem : Real.pi*x i∈Icc (-(Real.pi/2)) (Real.pi/2) := by
    have hab := (abs_le.mp (hx i))
    constructor <;> nlinarith [Real.pi_pos]
  have hzmem : (0:ℝ)∈Icc (-(Real.pi/2)) (Real.pi/2) := by
    constructor <;> linarith [Real.pi_pos]
  have he := Real.strictMonoOn_sin.injOn hmem hzmem (hs.trans Real.sin_zero.symm)
  exact hi ((mul_eq_zero.mp he).resolve_left Real.pi_pos.ne')

theorem diagonal_nonzero {d : ℕ} (hd : 0<d) {S : ℝ} (hS : S∈Ioc (0:ℝ) d) :
    (fun _ : Fin d => radialAngle d S)≠0 := by
  intro he
  have hy : radialAngle d S=0 := congrFun he ⟨0,hd⟩
  have hs := sineSquare_radialAngle hd ⟨hS.1.le,hS.2⟩
  rw [hy] at hs
  simp only [mul_zero,Real.sin_zero,zero_pow (by norm_num : (2:ℕ)≠0)] at hs
  have hp : 0<S/(d:ℝ) := div_pos hS.1 (Nat.cast_pos.mpr hd)
  linarith

theorem integrable_diagonal {d : ℕ} (hd : 0<d) {S : ℝ} (hS : S∈Ioc (0:ℝ) d) :
    IntegrableOn (heatMellin (quotientPoint (fun _ : Fin d => radialAngle d S))) (Ioi 0) := by
  apply integrable_heatMellin hd _ _ (diagonal_nonzero hd hS)
  intro i
  have hh := radialAngle_mem hd ⟨hS.1.le,hS.2⟩
  rw [abs_of_nonneg hh.1]
  exact hh.2

/-- Integration of the proved theta-product comparison, with integrability
at both spatial points established independently of the comparison. -/
theorem green_le_radialGreen {d : ℕ} (hd : 0<d) (x : Fin d → ℝ)
    (hx : ∀ i,|x i|≤1/2) (hx0 : x≠0) : green x≤radialGreen d (sineSquareSum x) := by
  have hS : sineSquareSum x∈Ioc (0:ℝ) d := ⟨sineSquareSum_pos hx hx0,(sineSquareSum_mem x).2⟩
  apply mul_le_mul_of_nonneg_left _ (endpointSigma_pos hd).le
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ)≤1/2)
  apply integral_mono_ae (integrable_heatMellin hd x hx hx0) (integrable_diagonal hd hS)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  unfold heatMellin
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_pos_of_pos ht _).le
  apply sub_le_sub_right
  change HeatDensityApproximation.heatKernel t (quotientPoint x) ≤
    HeatDensityApproximation.heatKernel t (quotientPoint (fun _ : Fin d => radialAngle d (sineSquareSum x)))
  rw [heatKernel_eq_theta_product ht x,
    heatKernel_eq_theta_product ht (fun _ : Fin d => radialAngle d (sineSquareSum x))]
  simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,radialTheta] using
    theta_product_le_diagonal hd (mul_pos Real.pi_pos ht) x

/-- The exact diagonal Green profile decreases at every positive squared-sine
radius. The excluded endpoint is precisely the logarithmic singularity. -/
theorem radialGreen_antitone {d : ℕ} (hd : 0<d) :
    AntitoneOn (radialGreen d) (Ioc (0:ℝ) d) := by
  intro S hS T hT hST
  apply mul_le_mul_of_nonneg_left _ (endpointSigma_pos hd).le
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ)≤1/2)
  apply integral_mono_ae (integrable_diagonal hd hT) (integrable_diagonal hd hS)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  unfold heatMellin
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_pos_of_pos ht _).le
  apply sub_le_sub_right
  simp only [heatKernel_eq_theta_product ht]
  simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,radialTheta] using
    radialTheta_antitone hd (mul_pos Real.pi_pos ht) ⟨hS.1.le,hS.2⟩ ⟨hT.1.le,hT.2⟩ hST

/-- The paper's twelve-dimensional Mellin integrand with its exp(-t n²)
time convention. -/
def sourceMellin (x : Fin 12 → ℝ) (t : ℝ) : ℝ :=
  t^5*((∏ i,RadialThetaTail.theta t (x i))-1)

theorem sourceMellin_scale (x : Fin 12 → ℝ) {t : ℝ} (ht : 0<t) :
    sourceMellin x (Real.pi*t)=Real.pi^5*heatMellin (quotientPoint x) t := by
  rw [sourceMellin,← heatKernel_eq_theta_product ht]
  unfold heatMellin
  rw [show (((12:ℕ):ℝ)/2-1)=((5:ℕ):ℝ) by norm_num,Real.rpow_natCast,mul_pow]
  ring

theorem sourceMellin_integrable (x : Fin 12 → ℝ) (hx : ∀ i,|x i|≤1/2) (hx0 : x≠0) :
    IntegrableOn (sourceMellin x) (Ioi 0) := by
  have hi : IntegrableOn (fun t => sourceMellin x (Real.pi*t)) (Ioi 0) := by
    apply ((integrable_heatMellin (by norm_num) x hx hx0).const_mul (Real.pi^5)).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (sourceMellin_scale x ht).symm
  simpa only [mul_zero] using (integrableOn_Ioi_comp_mul_left_iff (sourceMellin x) 0 Real.pi_pos).mp hi

/-- Exact normalization of the actual d12 Green representative in the source's
time variable. The identity itself holds even where the Bochner integral is
undefined; the preceding theorem supplies genuine integrability off zero. -/
theorem green_eq_sourceMellin (x : Fin 12 → ℝ) :
    green x=(1/120:ℝ)*∫ t in Ioi 0,sourceMellin x t := by
  have hi : (∫ t in Ioi 0,sourceMellin x (Real.pi*t))=
      Real.pi^5*(∫ t in Ioi 0,heatMellin (quotientPoint x) t) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact sourceMellin_scale x ht
  rw [integral_comp_mul_left_Ioi _ 0 Real.pi_pos,mul_zero,smul_eq_mul] at hi
  have hs : endpointSigma 12=Real.pi^6/60 := spectralThreshold_twelve
  unfold green heatGreen
  rw [hs]
  have hh := congrArg (fun a : ℝ => Real.pi*a) hi
  rw [mul_inv_cancel_left₀ Real.pi_pos.ne'] at hh
  rw [hh]
  ring

#print axioms green_le_radialGreen
#print axioms radialGreen_antitone
#print axioms green_eq_sourceMellin
end BecknerOnofri.HighDim.RadialGreenHeat
