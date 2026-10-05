import BecknerOnofri.SubspectralResolvent
import BecknerOnofri.ComplementSobolev

/-! Exact Hs norm bound for the same Fourier inverse used by the local IFT.
In particular s=11 gives the bound displayed in the manuscript. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped ENNReal
namespace BecknerOnofri.HighDim.SubspectralResolvent
open ContinuousGibbs ContinuousFirstShell

lemma scaled_inverse {d : ℕ} (hd : 0 < d) {μ s : ℝ} (hμ : 0 ≤ μ) (hμ1 : μ < 1)
    (u : Space d) (hu : InSobolev s u) (k : Frequency d) :
    scaledFourier s (inverse hμ hμ1 u) k = inverseLp hμ hμ1 (encodeSobolev u hu) k := by
  unfold scaledFourier
  rw [← coefficient_eq_fourierCoeff, inverse_fourier hd]
  change (sobolevScale s k : ℂ) * ((((symbol μ k)⁻¹:ℝ):ℂ) * coefficient k u) = _
  change _ = (((symbol μ k)⁻¹:ℝ):ℂ) * ((sobolevScale s k:ℂ)*fourierCoeff u k)
  rw [← coefficient_eq_fourierCoeff]
  ring

lemma inverse_sobolev {d : ℕ} (hd : 0 < d) {μ s : ℝ} (hμ : 0 ≤ μ) (hμ1 : μ < 1)
    (u : Space d) (hu : InSobolev s u) : InSobolev s (inverse hμ hμ1 u) := by
  refine ⟨(inverse hμ hμ1 u).continuous.memLp_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _), ?_⟩
  have hs := (lp.memℓp (inverseLp hμ hμ1 (encodeSobolev u hu))).summable
    (by norm_num : (0:ℝ)<(2:ℝ≥0∞).toReal)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hs
  apply hs.congr
  intro k
  rw [← scaled_inverse hd hμ hμ1 u hu k, scaledFourier_norm_sq]

lemma inverse_sobolevNorm_bound {d : ℕ} (hd : 0 < d) {μ s : ℝ}
    (hμ : 0 ≤ μ) (hμ1 : μ < 1) (u : Space d) (hu : InSobolev s u) :
    sobolevNorm s (inverse hμ hμ1 u) ≤ (1-μ)⁻¹*sobolevNorm s u := by
  have henc : encodeSobolev (inverse hμ hμ1 u) (inverse_sobolev hd hμ hμ1 u hu) =
      inverseLp hμ hμ1 (encodeSobolev u hu) := by
    apply lp.ext
    funext k
    exact scaled_inverse hd hμ hμ1 u hu k
  rw [← encodeSobolev_norm _ (inverse_sobolev hd hμ hμ1 u hu), henc,
    ← encodeSobolev_norm u hu]
  exact inverseLp_bound hμ hμ1 _

#print axioms inverse_sobolevNorm_bound
end BecknerOnofri.HighDim.SubspectralResolvent
