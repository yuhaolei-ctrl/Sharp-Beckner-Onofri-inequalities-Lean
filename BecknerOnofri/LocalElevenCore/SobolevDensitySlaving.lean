module

public import BecknerOnofri.LocalElevenCore.WeightedSlavingError

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter Asymptotics
open scoped Topology
namespace BecknerOnofri.HighDim.LocalEleven.QuadraticSlaving
open ContinuousGibbs ContinuousFirstShell ContinuousComplement
open GraphRegularity GraphWienerBounds WienerAlgebraBounds
open BecknerOnofri.OnsetWienerBounds

lemma density_error_identity {d : ℕ} (hd : 11≤d) :
    ∀ᶠ z in 𝓝 (0 : Coordinates d),
      normalized (slicePotential hd z) -
        (1+assembly d z+(quadraticCorrection hd z : Space d)+quadraticTerm (assembly d z)) =
      (inverseGreen hd (nonlinearRemainder (slicePotential hd z)-quadraticTerm (assembly d z))).val+
        (nonlinearRemainder (slicePotential hd z)-quadraticTerm (assembly d z)) := by
  filter_upwards [slaving_error_identity hd] with z hz
  rw [← hz]
  have hcenter : center d (slicePotential hd z)=slicePotential hd z := by
    ext x
    simp only [center_apply,mean_slicePotential,sub_zero]
  simp only [nonlinearRemainder,hcenter]
  change _=(sliceCorrection hd z : Space d)-(quadraticCorrection hd z : Space d)+_
  have he : slicePotential hd z=assembly d z+(sliceCorrection hd z : Space d) := rfl
  rw [he]
  abel

/-- The second Taylor expansion in the manuscript's complement calculation,
with the actual normalized density and the same quadratic complementary term. -/
theorem normalized_density_quadratic_expansion_all_sobolev {d : ℕ} (hd : 11≤d) (s : ℝ) :
    (fun z => sobolevNorm s (normalized (slicePotential hd z)-
      (1+assembly d z+(quadraticCorrection hd z : Space d)+quadraticTerm (assembly d z)) : Space d))
      =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖^3) := by
  obtain ⟨m,hm⟩ := exists_nat_ge s
  have hb : (fun z => sobolevNorm s (normalized (slicePotential hd z)-
      (1+assembly d z+(quadraticCorrection hd z : Space d)+quadraticTerm (assembly d z)) : Space d))
      =O[𝓝 (0 : Coordinates d)] (fun z =>
        wienerSize m (nonlinearRemainder (slicePotential hd z)-quadraticTerm (assembly d z))) := by
    apply IsBigO.of_bound (2*(1+2*Real.pi)^m)
    filter_upwards [density_error_identity hd,nonlinear_error_radial hd m] with z hz hr
    rw [Real.norm_of_nonneg (show 0≤sobolevNorm s (normalized (slicePotential hd z)-
      (1+assembly d z+(quadraticCorrection hd z : Space d)+quadraticTerm (assembly d z)) : Space d) from Real.sqrt_nonneg _),
      Real.norm_of_nonneg (radialSize_nonneg _ _),hz]
    have hi := inverseGreen_radial hd m _ hr
    have hs := GraphAllSobolevBounds.sobolevNorm_le_wiener hm _ (radial_add m _ _ hi hr)
    have ha := wienerSize_add_le m _ _ hi hr
    have hg := inverseGreen_wienerSize_le hd m _ hr
    have hh := mul_le_mul_of_nonneg_left (ha.trans (add_le_add hg (le_refl _)))
      (by positivity : 0≤(1+2*Real.pi)^m)
    exact hs.trans (by convert hh using 1 <;> ring)
  exact hb.trans (nonlinear_error_wiener_cubic hd m)

lemma slaving_error_inSobolev {d : ℕ} (hd : 11≤d) (s : ℝ) :
    ∀ᶠ z in 𝓝 (0 : Coordinates d),
      InSobolev s ((sliceCorrection hd z-quadraticCorrection hd z).val : Space d) := by
  obtain ⟨m,hm⟩ := exists_nat_ge s
  filter_upwards [slaving_error_identity hd,nonlinear_error_radial hd m] with z hz hr
  rw [hz]
  exact GraphAllSobolevBounds.inSobolev_of_wiener hm _ (inverseGreen_radial hd m _ hr)

lemma density_error_inSobolev {d : ℕ} (hd : 11≤d) (s : ℝ) :
    ∀ᶠ z in 𝓝 (0 : Coordinates d),
      InSobolev s (normalized (slicePotential hd z)-
        (1+assembly d z+(quadraticCorrection hd z : Space d)+quadraticTerm (assembly d z)) : Space d) := by
  obtain ⟨m,hm⟩ := exists_nat_ge s
  filter_upwards [density_error_identity hd,nonlinear_error_radial hd m] with z hz hr
  rw [hz]
  exact GraphAllSobolevBounds.inSobolev_of_wiener hm _
    (radial_add m _ _ (inverseGreen_radial hd m _ hr) hr)

lemma quadraticCorrection_inSobolev {d : ℕ} (hd : 11≤d) (s : ℝ) (z : Coordinates d) :
    InSobolev s (quadraticCorrection hd z : Space d) := by
  obtain ⟨m,hm⟩ := exists_nat_ge s
  exact GraphAllSobolevBounds.inSobolev_of_wiener hm _
    (inverseGreen_radial hd m _
      (WeightedGibbsCubicRemainder.radial_quadratic m _ (radial_assembly m z) (mean_assembly z)))

#print axioms normalized_density_quadratic_expansion_all_sobolev
end BecknerOnofri.HighDim.LocalEleven.QuadraticSlaving
