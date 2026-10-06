module

public import BecknerOnofri.GreenHilbertContinuous
public import BecknerOnofri.ContinuousOptimizers

@[expose] public section

/-! Continuous representatives and the actual sup-norm bound for H^d on
T^d. This bridges the manuscript's H11 neighborhood to the C-space IFT. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped ENNReal
namespace BecknerOnofri.HighDim.FullSobolevEmbedding
open ContinuousGibbs ContinuousFirstShell

lemma radius_pow_le_scale {d : ℕ} (k : Frequency d) :
    frequencyLength k^d ≤ sobolevScale (d:ℝ) k := by
  have hr : 0 ≤ frequencyLength k := Real.sqrt_nonneg _
  apply (sq_le_sq₀ (pow_nonneg hr _) (sobolevScale_pos _ _).le).mp
  rw [sobolevScale_sq,Real.rpow_natCast,← pow_mul, Nat.mul_comm d 2,pow_mul]
  apply pow_le_pow_left₀ (sq_nonneg _)
  have hr' : frequencyLength k ≤ 2*Real.pi*frequencyLength k := by
    calc
      _ = 1*frequencyLength k := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith [Real.pi_gt_three]) hr
  exact (pow_le_pow_left₀ hr hr' 2).trans (by linarith)

def majorant (d : ℕ) : FourierL2 d := lp.single 2 0 1 + greenFourierVector d

lemma inv_scale_bound {d : ℕ} (hd : 0 < d) (k : Frequency d) :
    ‖(((sobolevScale (d:ℝ) k)⁻¹:ℝ):ℂ)‖ ≤ ‖majorant d k‖ := by
  simp only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (sobolevScale_pos _ _))]
  unfold majorant
  rw [lp.coeFn_add,Pi.add_apply,lp.single_apply,greenFourierVector_apply hd]
  by_cases hk : k=0
  · subst k
    simp [sobolevScale,frequencyLength]
  · simp only [hk,if_false,Pi.single_eq_of_ne hk,zero_add,Complex.norm_real,Real.norm_eq_abs]
    have hp : 0 < frequencyLength k^d := lt_of_lt_of_le zero_lt_one
      (GreenCritical.nonzero_eigenvalue_ge_one (⟨k,hk⟩ : NonzeroFrequency d))
    rw [abs_of_pos (div_pos zero_lt_one hp),one_div]
    exact inv_anti₀ hp (radius_pow_le_scale k)

def inverseScaleLp {d : ℕ} (hd : 0 < d) : FourierL2 d :=
  ⟨fun k => (((sobolevScale (d:ℝ) k)⁻¹:ℝ):ℂ),
    (lp.memℓp (majorant d)).mono' (inv_scale_bound hd)⟩

lemma fourier_summable {d : ℕ} (hd : 0 < d) (u : Torus d → ℝ)
    (hu : InSobolev (d:ℝ) u) : Summable (fun k => ‖fourierCoeff u k‖) := by
  have hs := lp.summable_mul (by simpa using Real.HolderConjugate.two_two)
    (inverseScaleLp hd) (encodeSobolev u hu)
  apply hs.congr
  intro k
  rw [← norm_mul]
  change ‖(((sobolevScale (d:ℝ) k)⁻¹:ℝ):ℂ)*scaledFourier (d:ℝ) u k‖ = _
  have he := congrFun (unscale_encodeSobolev u hu) k
  exact congrArg norm he

lemma fourier_sum_bound {d : ℕ} (hd : 0 < d) (u : Torus d → ℝ)
    (hu : InSobolev (d:ℝ) u) :
    (∑' k, ‖fourierCoeff u k‖) ≤ ‖inverseScaleLp hd‖*sobolevNorm (d:ℝ) u := by
  have h := lp.tsum_mul_le_mul_norm' (by simpa using Real.HolderConjugate.two_two)
    (inverseScaleLp hd) (encodeSobolev u hu)
  rw [encodeSobolev_norm] at h
  convert! h using 1
  apply tsum_congr
  intro k
  rw [← norm_mul]
  exact (congrArg norm (congrFun (unscale_encodeSobolev u hu) k)).symm

lemma continuous_norm_bound {d : ℕ} (hd : 0 < d) (u : Space d)
    (hu : InSobolev (d:ℝ) u) : ‖u‖ ≤ ‖inverseScaleLp hd‖*sobolevNorm (d:ℝ) u := by
  have hs : Summable (fun k => ‖coefficient k u‖) :=
    (fourier_summable hd u hu).congr (fun k => by rw [coefficient_eq_fourierCoeff])
  have h := OnsetContinuous.norm_le_wiener u hs
  have he : OnsetWienerBounds.radialSize 0 (fun k => coefficient k u) = ∑' k, ‖fourierCoeff u k‖ := by
    simp [OnsetWienerBounds.radialSize,Legacy.BecknerOnofri.RadialWiener.radialWeight,
      coefficient_eq_fourierCoeff]
  rw [he] at h
  exact h.trans (fourier_sum_bound hd u hu)

#print axioms fourier_summable
#print axioms continuous_norm_bound
end BecknerOnofri.HighDim.FullSobolevEmbedding
