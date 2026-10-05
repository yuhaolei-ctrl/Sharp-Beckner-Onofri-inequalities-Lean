import BecknerOnofri.LatticeSobolevSummability
import BecknerOnofri.FullSobolevEmbedding

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped ENNReal
namespace BecknerOnofri.HighDim.SobolevEmbedding
open ContinuousGibbs ContinuousFirstShell

def inverseScaleLp {d : ℕ} (hd : 0<d) {s : ℝ} (hs : (d:ℝ)/2<s) : FourierL2 d := by
  have hd' : (0:ℝ)<d := by exact_mod_cast hd
  have hp : (1/2:ℝ)<s/d := (lt_div_iff₀ hd').mpr (by linarith)
  have hsum : Summable (fun k : Frequency d => (sobolevScale s k)⁻¹^2) :=
    Summable.of_nonneg_of_le (fun k => sq_nonneg _) (inverse_scale_square_le_product hd hs)
      (summable_productWeight d hp)
  exact ⟨fun k => (((sobolevScale s k)⁻¹:ℝ):ℂ),
    (memℓp_gen_iff (by norm_num : (0:ℝ)<(2:ℝ≥0∞).toReal)).mpr (by
      simpa only [ENNReal.toReal_ofNat,Real.rpow_two,Complex.norm_real,Real.norm_eq_abs,sq_abs] using hsum)⟩

lemma fourier_summable {d : ℕ} (hd : 0 < d) {s : ℝ} (hs : (d:ℝ)/2<s) (u : Torus d → ℝ)
    (hu : InSobolev s u) : Summable (fun k => ‖fourierCoeff u k‖) := by
  have hsum := lp.summable_mul (by simpa using Real.HolderConjugate.two_two)
    (inverseScaleLp hd hs) (encodeSobolev u hu)
  apply hsum.congr
  intro k
  rw [← norm_mul]
  change ‖(((sobolevScale s k)⁻¹:ℝ):ℂ)*scaledFourier s u k‖ = _
  have he := congrFun (unscale_encodeSobolev u hu) k
  exact congrArg norm he

lemma fourier_sum_bound {d : ℕ} (hd : 0 < d) {s : ℝ} (hs : (d:ℝ)/2<s) (u : Torus d → ℝ)
    (hu : InSobolev s u) :
    (∑' k, ‖fourierCoeff u k‖) ≤ ‖inverseScaleLp hd hs‖*sobolevNorm s u := by
  have h := lp.tsum_mul_le_mul_norm' (by simpa using Real.HolderConjugate.two_two)
    (inverseScaleLp hd hs) (encodeSobolev u hu)
  rw [encodeSobolev_norm] at h
  convert! h using 1
  apply tsum_congr
  intro k
  rw [← norm_mul]
  exact (congrArg norm (congrFun (unscale_encodeSobolev u hu) k)).symm

lemma continuous_norm_bound {d : ℕ} (hd : 0 < d) {s : ℝ} (hs : (d:ℝ)/2<s) (u : Space d)
    (hu : InSobolev s u) : ‖u‖ ≤ ‖inverseScaleLp hd hs‖*sobolevNorm s u := by
  have hsum : Summable (fun k => ‖coefficient k u‖) :=
    (fourier_summable hd hs u hu).congr (fun k => by rw [coefficient_eq_fourierCoeff])
  have h := OnsetContinuous.norm_le_wiener u hsum
  have he : OnsetWienerBounds.radialSize 0 (fun k => coefficient k u) = ∑' k, ‖fourierCoeff u k‖ := by
    simp [OnsetWienerBounds.radialSize,Legacy.BecknerOnofri.RadialWiener.radialWeight,
      coefficient_eq_fourierCoeff]
  rw [he] at h
  exact h.trans (fourier_sum_bound hd hs u hu)

lemma exists_continuous_representative {d : ℕ} (hd : 0<d) {s : ℝ} (hs : (d:ℝ)/2<s)
    (u : Torus d → ℝ) (hu : InSobolev s u) : ∃ v : Space d,
      (v : Torus d → ℝ) =ᵐ[torusMeasure d] u ∧ InSobolev s v ∧
      ‖v‖≤‖inverseScaleLp hd hs‖*sobolevNorm s u := by
  let U := Bridge.potentialLp u hu.1
  have hsum : Summable (fun k => ‖Legacy.BecknerOnofri.TorusSobolev.fourierIsometry d U k‖) := by
    simpa only [U,Bridge.potentialLp_fourier] using fourier_summable hd hs u hu
  let v := ContinuousOptimizers.realRepresentative U hsum
  have he : (v : Torus d → ℝ) =ᵐ[torusMeasure d] u := by
    filter_upwards [ContinuousOptimizers.realRepresentative_ae U hsum,Bridge.potentialLp_ae u hu.1]
      with x hx hu'
    exact hx.trans (congrArg Complex.re hu')
  have hv : InSobolev s v := (OnsetRaw.inSobolev_congr_ae he).mpr hu
  refine ⟨v,he,hv,?_⟩
  simpa only [OnsetRaw.sobolevNorm_congr_ae he] using continuous_norm_bound hd hs v hv

#print axioms exists_continuous_representative
end BecknerOnofri.HighDim.SobolevEmbedding
