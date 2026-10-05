import BecknerOnofri.GeneralEuler.Regularity
import BecknerOnofri.SmoothTorusSobolev
import BecknerOnofri.OptimizerEulerPaper

/-! Raw smoothness and the Fourier Euler equation imply the internal analytic
interface. No maximality or decay assumption is added. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
namespace BecknerOnofri.HighDim.GeneralEulerBridge
open ContinuousGibbs ContinuousFirstShell
open Legacy.BecknerOnofri.TorusSobolev Legacy.BecknerOnofri.SubcriticalEuler

theorem regularity_data {d : ℕ} (hd : 0 < d) {β : ℝ} (hβ : 0 < β)
    (u : ContinuousGibbs.Space d) (hs : SmoothOnTorus u)
    (he : ∀ k : NonzeroFrequency d,
      (frequencyLength k.val^d : ℂ)*fourierCoeff u k.val =
        (β/spectralThreshold d : ℝ)*fourierCoeff (normalizedGibbs u) k.val) :
    BecknerOnofri.GeneralEuler.Regularity.Data (spectralThreshold d/(2*β)) (toL2 d u) := by
  have hf (k : Frequency d) : fourierIsometry d (toL2 d u) k=fourierCoeff u k :=
    coefficient_eq_fourierCoeff k u
  have hg (k : Frequency d) : Legacy.TorusEndpoint.densityFourier (gibbsValue (toL2 d u)) k =
      fourierCoeff (normalizedGibbs u) k := by
    exact fourierCoeff_congr_ae (OptimizerDuality.gibbsValue_toL2_ae u) k
  refine ⟨?_,?_⟩
  · intro m
    simpa only [Legacy.BecknerOnofri.RadialWiener.RadialSummable,
      Legacy.BecknerOnofri.RadialWiener.radialWeight,hf,← Bridge.frequencyLength_eq] using SmoothTorus.smooth_fourier_moments hs m
  · intro k hk
    rw [hf,hg]
    have hh := he ⟨k,hk⟩
    have hp : 0 < frequencyLength k^d := lt_of_lt_of_le zero_lt_one
      (GreenCritical.nonzero_eigenvalue_ge_one ⟨k,hk⟩)
    have hfactor : 1/(2*(spectralThreshold d/(2*β)))=β/spectralThreshold d := by
      field_simp [(spectralThreshold_pos hd).ne',hβ.ne']
      <;> ring
    change fourierCoeff u k =
      ((1/(2*(spectralThreshold d/(2*β)))*(frequencyLength k^d)⁻¹ : ℝ) : ℂ) * _
    rw [hfactor]
    have hc : (↑(frequencyLength k^d) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hp.ne'
    apply mul_left_cancel₀ hc
    rw [show ((frequencyLength k^d:ℝ):ℂ)*fourierCoeff u k =
      (β/spectralThreshold d : ℝ)*fourierCoeff (normalizedGibbs u) k by
        simpa only [Complex.ofReal_pow] using hh]
    have hpc : (↑(frequencyLength k) : ℂ)^d ≠ 0 := by
      simpa only [Complex.ofReal_pow] using hc
    push_cast
    field_simp [hpc]

#print axioms regularity_data
end BecknerOnofri.HighDim.GeneralEulerBridge
