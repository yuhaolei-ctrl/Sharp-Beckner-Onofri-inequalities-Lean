module

public import BecknerOnofri.LocalElevenCore.WeightedCubicExponentialTail
public import BecknerOnofri.LocalElevenCore.GraphWienerBounds

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
namespace BecknerOnofri.HighDim.LocalEleven.WienerAlgebraBounds
open ContinuousGibbs ContinuousFirstShell GraphRegularity GraphWienerBounds
open WeightedCubicExponentialTail WeightedExponentialRemainder
open Legacy.TorusEndpoint Legacy.BecknerOnofri.WienerFourier Legacy.BecknerOnofri.RadialWiener
open Legacy.BecknerOnofri.WeightedWiener BecknerOnofri.OnsetWienerBounds

lemma coefficient_product {d : ℕ} (u v : Space d)
    (hu : Summable (fun k => ‖coefficient k u‖))
    (hv : Summable (fun k => ‖coefficient k v‖)) (k : Frequency d) :
    coefficient k (u*v)=convolution (fun k => coefficient k u) (fun k => coefficient k v) k := by
  have he : absoluteFourierSeries (convolution (fun k => coefficient k u) (fun k => coefficient k v))=
      fun x => (u x:ℂ)*(v x:ℂ) := by
    funext x
    rw [convolution_series _ _ hu hv,series_eq u hu,series_eq v hv]
  rw [← absoluteFourierSeries_coefficient _ (convolution_norm_summable _ _ hu hv),he,
    coefficient_integral]
  simp only [UnitAddTorus.mFourierCoeff,smul_eq_mul,ContinuousMap.mul_apply,Complex.ofReal_mul]
  rfl

lemma radial_mul {d : ℕ} (m : ℕ) (u v : Space d) (hu : Radial m u) (hv : Radial m v) :
    Radial m (u*v) := by
  have hu0 := summable_norm (radialWeight_isWeight m) hu
  have hv0 := summable_norm (radialWeight_isWeight m) hv
  simpa only [Radial,RadialSummable,coefficient_product u v hu0 hv0] using
    Legacy.BecknerOnofri.WeightedWiener.convolution_summable (radialWeight_isWeight m) _ _ hu hv

lemma wienerSize_mul_le {d : ℕ} (m : ℕ) (u v : Space d) (hu : Radial m u) (hv : Radial m v) :
    wienerSize m (u*v)≤wienerSize m u*wienerSize m v := by
  have hu0 := summable_norm (radialWeight_isWeight m) hu
  have hv0 := summable_norm (radialWeight_isWeight m) hv
  have ha (k : Frequency d) : 0≤radialWeight m k*‖coefficient k u‖ :=
    mul_nonneg ((radialWeight_isWeight m).nonneg k) (norm_nonneg _)
  have hb (k : Frequency d) : 0≤radialWeight m k*‖coefficient k v‖ :=
    mul_nonneg ((radialWeight_isWeight m).nonneg k) (norm_nonneg _)
  apply hasSum_le _ (radial_mul m u v hu hv).hasSum (fourierConvolution_hasSum _ _ hu hv ha hb)
  intro k
  simpa only [coefficient_product u v hu0 hv0] using
    convolution_le (radialWeight_isWeight m) _ _ hu hv k

lemma wienerSize_smul {d : ℕ} (m : ℕ) (c : ℝ) (u : Space d) :
    wienerSize m (c • u)=‖c‖*wienerSize m u := by
  unfold wienerSize radialSize
  simp only [map_smul,norm_smul]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro k
  ring

lemma wienerSize_neg {d : ℕ} (m : ℕ) (u : Space d) : wienerSize m (-u)=wienerSize m u := by
  simp only [wienerSize,radialSize,map_neg,norm_neg]

lemma radial_sub {d : ℕ} (m : ℕ) (u v : Space d) (hu : Radial m u) (hv : Radial m v) :
    Radial m (u-v) := by
  have hn : Radial m (-v) := by simpa only [neg_one_smul] using radial_smul m (-1) v hv
  simpa only [sub_eq_add_neg] using radial_add m u (-v) hu hn

lemma wienerSize_sub_le {d : ℕ} (m : ℕ) (u v : Space d) (hu : Radial m u) (hv : Radial m v) :
    wienerSize m (u-v)≤wienerSize m u+wienerSize m v := by
  have hn : Radial m (-v) := by simpa only [neg_one_smul] using radial_smul m (-1) v hv
  simpa only [sub_eq_add_neg,wienerSize_neg] using wienerSize_add_le m u (-v) hu hn

lemma radial_one {d : ℕ} (m : ℕ) : Radial m (1 : Space d) := (radial_unit_hasSum m).summable

lemma wienerSize_one {d : ℕ} (m : ℕ) : wienerSize m (1 : Space d)=1 :=
  (radial_unit_hasSum m).tsum_eq

lemma center_eq {d : ℕ} (u : Space d) : center d u=u-mean d u • (1 : Space d) := by
  ext x
  simp [center_apply]

lemma radial_center {d : ℕ} (m : ℕ) (u : Space d) (hu : Radial m u) : Radial m (center d u) := by
  rw [center_eq]
  exact radial_sub m u _ hu (radial_smul m _ _ (radial_one m))

lemma wienerSize_center_le {d : ℕ} (m : ℕ) (u : Space d) (hu : Radial m u) :
    wienerSize m (center d u)≤2*wienerSize m u := by
  rw [center_eq]
  have h := wienerSize_sub_le m u (mean d u • (1 : Space d)) hu
    (radial_smul m (mean d u) (1 : Space d) (radial_one m))
  rw [wienerSize_smul,wienerSize_one,mul_one,Real.norm_eq_abs] at h
  have hm := mean_le_radialSize m u hu
  change |mean d u|≤wienerSize m u at hm
  linarith

#print axioms wienerSize_center_le
#print axioms wienerSize_mul_le
end BecknerOnofri.HighDim.LocalEleven.WienerAlgebraBounds
