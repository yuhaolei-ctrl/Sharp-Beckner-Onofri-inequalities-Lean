import BecknerOnofri.SelectedNumericalModel
import BecknerOnofri.GreenContinuous
import BecknerOnofri.Arithmetic
import BecknerOnofri.SubcriticalGap
import Legacy.BecknerOnofri.GreenExponentialIntegrability
import Legacy.BecknerOnofri.SubcriticalEulerEnergy

/-! Actual entropy/convolution initialization for the dimension-twelve
certificate. No density norm or numerical iteration is an input. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
namespace BecknerOnofri.HighDim.InitialNormBound
open ContinuousGibbs GinibreCovariance
open Legacy.BecknerOnofri

local instance (d : ℕ) : (torusMeasure d).IsAddLeftInvariant := by
  unfold torusMeasure
  infer_instance
local instance : (AddCircle.haarAddCircle (T := 1)).IsNegInvariant := by
  have he : AddCircle.haarAddCircle (T := 1) = (volume : Measure UnitAddCircle) := by
    simpa using (AddCircle.volume_eq_smul_haarAddCircle (T := 1)).symm
  rw [he]
  infer_instance
local instance (d : ℕ) : (torusMeasure d).IsNegInvariant := by
  unfold torusMeasure
  infer_instance

def density {d : ℕ} (q : Space d) : Legacy.TorusEndpoint.ProbabilityDensity d where
  value := normalized q
  nonneg := Filter.Eventually.of_forall (fun x => (normalized_pos q x).le)
  integrable := ContinuousGibbs.integrable d (normalized q)
  mass := mean_normalized q

theorem density_memLp {d : ℕ} (q : Space d) :
    MemLp (density q).value 2 (torusMeasure d) :=
  (normalized q).continuous.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem log_density {d : ℕ} (q : Space d) (x : Torus d) :
    Real.log (normalized q x)=q x-Real.log (partition q) := by
  change Real.log ((partition q)⁻¹*exponential q x)=_
  rw [exponential_apply,Real.log_mul (inv_ne_zero (partition_pos q).ne') (Real.exp_pos _).ne',
    Real.log_inv,Real.log_exp]
  ring

theorem density_entropy {d : ℕ} (q : Space d) :
    Legacy.TorusEndpoint.densityEntropy (density q).value =
      mean d (q*normalized q)-Real.log (partition q) := by
  change (∫ x, normalized q x*Real.log (normalized q x) ∂torusMeasure d)=_
  simp_rw [log_density, mul_sub]
  have hi : Integrable (fun x => normalized q x*q x) (torusMeasure d) :=
    ContinuousGibbs.integrable d (normalized q*q)
  rw [integral_sub hi ((ContinuousGibbs.integrable d (normalized q)).mul_const _),
    integral_mul_const,show (∫ x, normalized q x ∂torusMeasure d)=1 from mean_normalized q,one_mul]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => mul_comm _ _)

theorem green_eq_potential {d : ℕ} (q : Space d) (x : Torus d) :
    greenContinuous d (normalized q) x=GreenRoughEnergy.potential (density q) x := by
  change (∫ y, GreenRoughEnergy.kernel d y*normalized q (x-y) ∂torusMeasure d)=
    ∫ y, GreenRoughEnergy.kernel d (x-y)*normalized q y ∂torusMeasure d
  simpa only [sub_sub_cancel] using
    (integral_sub_left_eq_self
      (fun y => GreenRoughEnergy.kernel d y*normalized q (x-y)) (torusMeasure d) x).symm

/-- The actual translated-kernel entropy inequality and Gibbs identity imply
the source's pointwise logarithmic density bound. The pairing hypothesis is
discharged from the actual Euler energy identity for maximizers below. -/
theorem log_density_le {d : ℕ} (q : Space d)
    (hconv : q=greenContinuous d (normalized q))
    (hpair : mean d (q*normalized q)≤2*Real.log (partition q))
    (hexp : Integrable (fun x => Real.exp ((7/10:ℝ)*GreenRoughEnergy.kernel d x)) (torusMeasure d))
    (x : Torus d) :
    Real.log (normalized q x)≤(5/2:ℝ)*Real.log (GreenRoughEnergy.partition d (7/10)) := by
  let L := Real.log (GreenRoughEnergy.partition d (7/10))
  let J := mean d (q*normalized q)
  have hp (y : Torus d) : (7/10:ℝ)*q y≤
      J-Real.log (partition q)+L := by
    have hh := GreenRoughEnergy.potential_entropy_bound (density q) (density_memLp q) (7/10) hexp y
    rw [density_entropy q,← green_eq_potential q y,← hconv] at hh
    exact hh
  have hJ : (7/10:ℝ)*J≤J-Real.log (partition q)+L := by
    have hh := integral_mono
      ((ContinuousGibbs.integrable d (q*normalized q)).const_mul (7/10:ℝ))
      ((ContinuousGibbs.integrable d (normalized q)).const_mul (J-Real.log (partition q)+L))
      (fun y => by
        have hy := mul_le_mul_of_nonneg_right (hp y) (normalized_pos q y).le
        simpa only [ContinuousMap.mul_apply,mul_assoc] using hy)
    rw [integral_const_mul,integral_const_mul,
      show (∫ y, normalized q y ∂torusMeasure d)=1 from mean_normalized q,mul_one] at hh
    exact hh
  have hE : J≤5*L := by dsimp [J] at *; linarith
  rw [log_density]
  have hh := hp x
  dsimp [J,L] at *
  linarith

/-- Genuine L-infinity to L2 conversion, using mass one and the actual square
integral defining `gibbsL2Norm`. -/
theorem gibbsL2Norm_le_exp {d : ℕ} (q : Space d)
    (hconv : q=greenContinuous d (normalized q))
    (hpair : mean d (q*normalized q)≤2*Real.log (partition q))
    (hexp : Integrable (fun x => Real.exp ((7/10:ℝ)*GreenRoughEnergy.kernel d x)) (torusMeasure d)) :
    gibbsL2Norm q≤Real.exp ((5/4:ℝ)*Real.log (GreenRoughEnergy.partition d (7/10))) := by
  let L := Real.log (GreenRoughEnergy.partition d (7/10))
  have hp (x : Torus d) : normalized q x≤Real.exp ((5/2:ℝ)*L) := by
    rw [← Real.exp_log (normalized_pos q x)]
    exact Real.exp_le_exp.mpr (log_density_le q hconv hpair hexp x)
  have hsq : (∫ x, (normalized q x)^2 ∂torusMeasure d)≤Real.exp ((5/2:ℝ)*L) := by
    have hh := integral_mono (ContinuousGibbs.integrable d ((normalized q)^2))
      ((ContinuousGibbs.integrable d (normalized q)).const_mul (Real.exp ((5/2:ℝ)*L)))
      (fun x => by
        have hx := mul_le_mul_of_nonneg_right (hp x) (normalized_pos q x).le
        simpa only [ContinuousMap.pow_apply,pow_two,ContinuousMap.mul_apply] using hx)
    rw [integral_const_mul,
      show (∫ x, normalized q x ∂torusMeasure d)=1 from mean_normalized q,mul_one] at hh
    exact hh
  calc
    gibbsL2Norm q=Real.sqrt (∫ x, (normalized q x)^2 ∂torusMeasure d) := by
      simp only [gibbsL2Norm,normalized_apply]
    _ ≤ Real.sqrt (Real.exp ((5/2:ℝ)*L)) := Real.sqrt_le_sqrt hsq
    _ = _ := by rw [← Real.exp_half]; congr 1; dsimp [L]; ring

theorem alpha_admissible : (7/10:ℝ)<endpointConstant 12 := by
  apply (lt_div_iff₀ (Legacy.TorusEndpoint.endpointSigma_pos (by norm_num))).mpr
  change (7/10:ℝ)*spectralThreshold 12<(12:ℝ)
  rw [spectralThreshold_twelve]
  have hp : Real.pi^6<(3.15:ℝ)^6 := by gcongr; exact Real.pi_lt_d2
  norm_num at hp
  nlinarith

theorem kernel_exp_integrable :
    Integrable (fun x => Real.exp ((7/10:ℝ)*GreenRoughEnergy.kernel 12 x)) (torusMeasure 12) :=
  GreenExponentialIntegrability.kernel_exp_integrable (by norm_num) (by norm_num) alpha_admissible

theorem kernel_partition_pos : 0<GreenRoughEnergy.partition 12 (7/10) :=
  GreenExponentialIntegrability.kernel_partition_pos (by norm_num) (by norm_num) alpha_admissible

theorem partition_power_lt_initial_norm {P : ℝ} (hP : 0<P) (hP' : P<24000) :
    Real.exp ((5/4:ℝ)*Real.log P)<300000 := by
  have hfour : (Real.exp ((5/4:ℝ)*Real.log P))^4=P^5 := by
    rw [← Real.exp_nat_mul]
    have he : (4:ℝ)*((5/4:ℝ)*Real.log P)=5*Real.log P := by ring
    norm_num only [Nat.cast_ofNat]
    rw [he,show (5:ℝ)=((5:ℕ):ℝ) by norm_num,Real.exp_nat_mul,Real.exp_log hP]
  have hpow : P^5<(24000:ℝ)^5 := by gcongr
  have hfinal : (Real.exp ((5/4:ℝ)*Real.log P))^4<(300000:ℝ)^4 := by
    rw [hfour]
    exact hpow.trans Arithmetic.partition_to_initial_norm_real
  exact (pow_lt_pow_iff_left₀ (Real.exp_pos _).le (by norm_num : (0:ℝ)≤300000)
    (by norm_num : (4:ℕ)≠0)).mp hfinal

open Legacy.BecknerOnofri.TorusSobolev Legacy.BecknerOnofri.SubcriticalAttainment
open Legacy.BecknerOnofri.SubcriticalEuler Legacy.BecknerOnofri.SmoothFourier

/-- Euler pairing for the actual selected endpoint maximizer, derived from
its full variational property and the continuous representative. -/
theorem selected_pairing {u : TorusL2 12} (hu : SelectedNumericalModel.Selected u) :
    mean 12 (SelectedNumericalModel.potential u*normalized (SelectedNumericalModel.potential u))=
      criticalEnergy u := by
  calc
    _ = ∫ x, gibbsValue u x*(u x).re ∂torusMeasure 12 := by
      apply integral_congr_ae
      filter_upwards [WienerFourier.representative_ae_eq u
        (SelectedNumericalModel.fourier_norm_summable hu),
        smoothGibbsValue_ae_eq u (SelectedNumericalModel.fourier_norm_summable hu)] with x hx hg
      simp only [ContinuousMap.mul_apply,SelectedNumericalModel.potential_apply hu,
        SelectedNumericalModel.potential_normalized hu,hx,hg,mul_comm]
    _ = _ := by
      convert! maximizer_pairing SelectedNumericalModel.rough hu.1 hu.2.1 using 1 <;> norm_num

theorem selected_pairing_le_log {u : TorusL2 12} (hu : SelectedNumericalModel.Selected u) :
    mean 12 (SelectedNumericalModel.potential u*normalized (SelectedNumericalModel.potential u))≤
      2*Real.log (ContinuousGibbs.partition (SelectedNumericalModel.potential u)) := by
  have hf : 0≤functional (1/2) u := by
    simpa using hu.2.1 0 (admissible_zero 12)
  rw [selected_pairing hu,SelectedNumericalModel.potential_partition hu]
  unfold functional at hf
  linarith

/-- Source Lemma cs:norm for the actual selected optimizer and its actual
Gibbs density, with kernel exponential integrability proved above. -/
theorem selected_norm_le_partition_power {u : TorusL2 12}
    (hu : SelectedNumericalModel.Selected u) :
    gibbsL2Norm (SelectedNumericalModel.potential u)≤
      (GreenRoughEnergy.partition 12 (7/10))^(5/4:ℝ) := by
  rw [Real.rpow_def_of_pos kernel_partition_pos]
  simpa only [mul_comm] using gibbsL2Norm_le_exp (SelectedNumericalModel.potential u)
    (SelectedNumericalModel.potential_green hu) (selected_pairing_le_log hu) kernel_exp_integrable

/-- The analytic initialization of the numerical trajectory: only the actual
kernel partition bound remains a numerical premise. -/
theorem selected_initial_norm {u : TorusL2 12}
    (hu : SelectedNumericalModel.Selected u)
    (hZ : GreenRoughEnergy.partition 12 (7/10)<24000) :
    gibbsL2Norm (SelectedNumericalModel.potential u)<300000 := by
  exact (gibbsL2Norm_le_exp (SelectedNumericalModel.potential u)
    (SelectedNumericalModel.potential_green hu) (selected_pairing_le_log hu) kernel_exp_integrable).trans_lt
      (partition_power_lt_initial_norm kernel_partition_pos hZ)

#print axioms gibbsL2Norm_le_exp
#print axioms kernel_exp_integrable
#print axioms partition_power_lt_initial_norm
#print axioms selected_pairing
#print axioms selected_norm_le_partition_power
#print axioms selected_initial_norm
end BecknerOnofri.HighDim.InitialNormBound
