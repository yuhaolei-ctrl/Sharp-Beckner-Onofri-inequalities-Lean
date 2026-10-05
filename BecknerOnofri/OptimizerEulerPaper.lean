import BecknerOnofri.RawOptimizerCorrespondence
import BecknerOnofri.EulerEquation

/-! Smooth positive density representatives, the Fourier Euler equation, and
Kirkwood--Monroe at every actual global extremizer. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
namespace BecknerOnofri.HighDim.OptimizerDuality
open ContinuousGibbs ContinuousFirstShell ContinuousOptimizers

theorem normalizedGibbs_smooth {d : ℕ} (u : Torus d → ℝ) (hu : SmoothOnTorus u) :
    SmoothOnTorus (normalizedGibbs u) := by
  change ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
    (fun x : Fin d → ℝ => Real.exp (u (fun j => (x j : UnitAddCircle))) /
      (∫ y,Real.exp (u y) ∂torusMeasure d))
  exact hu.exp.div_const _

theorem raw_optimizer_euler {d : ℕ} (hd : 0 < d) {β : ℝ} (hβ : 0 < β)
    (u : Torus d → ℝ) (hu : InCriticalSobolev u) (hm : MeanZero u)
    (hmax : ∀ v : Torus d → ℝ, InCriticalSobolev v → dualFunctional β v ≤ dualFunctional β u) :
    ∀ k : NonzeroFrequency d,
      (frequencyLength k.val^d : ℂ)*fourierCoeff u k.val =
        (β/spectralThreshold d : ℝ)*fourierCoeff (normalizedGibbs u) k.val := by
  obtain ⟨v,he,hv,hvm,_,_,hvmax⟩ := continuous_optimizer_of_raw hd hβ u hu hm hmax
  have hβσ : β/spectralThreshold d*spectralThreshold d=β :=
    div_mul_cancel₀ β (spectralThreshold_pos hd).ne'
  have hf := continuous_optimizer_full hd (div_pos hβ (spectralThreshold_pos hd)) v hv hvm
    (by simpa only [hβσ] using hvmax)
  have hs := ((ReducedEquation.full_zero_iff_stationary hd _ v).mp hf).2
  intro k
  rw [fourierCoeff_congr_ae he,fourierCoeff_congr_ae (Gap.gibbs_congr he)]
  simpa only [Complex.ofReal_pow] using hs k

/-- Regularity is a conclusion on every finite-entropy extremizer, including
any attained critical endpoint. -/
theorem minimizer_smooth_positive_kirkwood {d : ℕ} (hd : 0 < d) {β : ℝ} (hβ : 0 < β)
    (ρ : ProbabilityDensity d) (hρ : IsGlobalMinimizer β ρ) :
    (∃ q : Torus d → ℝ, ρ.value =ᵐ[torusMeasure d] q ∧ SmoothOnTorus q ∧ ∀ x, 0 < q x) ∧
    ρ.value =ᵐ[torusMeasure d] normalizedGibbs (Gap.densityPotential β ρ.value) ∧
    (∀ k : NonzeroFrequency d,
      (frequencyLength k.val^d : ℂ)*fourierCoeff (Gap.densityPotential β ρ.value) k.val =
        (β/spectralThreshold d : ℝ)*fourierCoeff ρ.value k.val) := by
  obtain ⟨u,hu,hm,hus,_,hmax,hg⟩ := continuous_optimizer_of_minimizer hd hβ ρ hρ
  have hp := (minimizer_iff_prescribed_optimizer hd hβ ρ hρ.1).mp hρ
  have hr := Gap.densityPotential_regular hd hβ ρ hρ.1
  refine ⟨⟨normalizedGibbs u,hg,normalizedGibbs_smooth u hus,?_⟩,hp.2,?_⟩
  · intro x
    rw [← normalized_apply]
    exact normalized_pos u x
  · intro k
    have he := raw_optimizer_euler hd hβ (Gap.densityPotential β ρ.value) hr.1 hr.2 hp.1 k
    rw [← fourierCoeff_congr_ae hp.2] at he
    exact he

#print axioms raw_optimizer_euler
#print axioms minimizer_smooth_positive_kirkwood
end BecknerOnofri.HighDim.OptimizerDuality
