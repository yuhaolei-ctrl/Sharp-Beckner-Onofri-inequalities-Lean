module

public import BecknerOnofri.LocalElevenContinuousInverse
public import BecknerOnofri.QuarticSignsEleven
public import BecknerOnofri.ComplementHessian
public import BecknerOnofri.LocalElevenCore.RawComplementGap

@[expose] public section

/-! Uniform strict negativity of the physical Hessian on the full raw
critical-Sobolev complement, for small continuous potentials. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory
open scoped Topology
namespace BecknerOnofri.HighDim.LocalEleven.ComplementHessian

open BecknerOnofri.HighDim.ComplementHessian hiding normalized_le_two_near_zero secondVariation_complement_bound secondVariation_complement_uniform weighted_square_bound weighted_square_integrable
open BecknerOnofri.HighDim.RawComplementGap hiding normalizedEnergy_gap normalizedEnergy_nonneg raw_fourier_square_hasSum raw_normalizedEnergy_hasSum
open ContinuousGibbs RawComplementGap

theorem normalized_le_two_near_zero (d : ℕ) :
    ∀ᶠ (u : Space d) in 𝓝 0, ∀ x, normalizedGibbs u x ≤ 2 := by
  have hc := (normalized_analytic (0 : Space d)).continuousAt
  filter_upwards [hc.eventually (Metric.ball_mem_nhds (normalized (0 : Space d))
    (by norm_num : (0:ℝ)<1))] with u hu
  simp only [Metric.mem_ball, dist_eq_norm, normalized_zero] at hu
  intro x
  have hx := (normalized u - 1).norm_coe_le_norm x
  simp only [ContinuousMap.sub_apply, ContinuousMap.one_apply, normalized_apply, Real.norm_eq_abs] at hx
  have hle := le_abs_self (normalizedGibbs u x - 1)
  linarith

theorem weighted_square_integrable {d : ℕ} (u : Space d) (h : Torus d → ℝ)
    (hh : MemLp h 2 (torusMeasure d)) :
    Integrable (fun x => normalizedGibbs u x * (h x)^2) (torusMeasure d) := by
  have hs : Integrable (fun x => (h x)^2) (torusMeasure d) := by
    convert! hh.integrable_mul hh using 1
    funext x
    exact pow_two (h x)
  have hp := hs.bdd_mul (normalized u).continuous.aestronglyMeasurable
    (Eventually.of_forall (fun x => (normalized u).norm_coe_le_norm x))
  simpa only [normalized_apply] using hp

theorem weighted_square_bound {d : ℕ} (u : Space d) (h : Torus d → ℝ)
    (hh : MemLp h 2 (torusMeasure d)) (hu : ∀ x, normalizedGibbs u x ≤ 2) :
    (∫ x, normalizedGibbs u x*(h x)^2 ∂torusMeasure d) ≤
      2*(∫ x, (h x)^2 ∂torusMeasure d) := by
  rw [← integral_const_mul]
  have hs : Integrable (fun x => (h x)^2) (torusMeasure d) := by
    convert! hh.integrable_mul hh using 1
    funext x
    exact pow_two (h x)
  apply integral_mono (weighted_square_integrable u h hh)
    (hs.const_mul 2)
  intro x
  exact mul_le_mul_of_nonneg_right (hu x) (sq_nonneg _)

/-- A fixed negative energy bound, valid for every raw critical-Sobolev
variation with no constant or first-shell mode. -/
theorem secondVariation_complement_bound {d : ℕ} (hd : 11 ≤ d) {μ : ℝ}
    (hμ : 0 < μ) (hμ2 : μ ≤ 2) (u : Space d) (hu : ∀ x, normalizedGibbs u x ≤ 2)
    (h : Torus d → ℝ) (hh : InCriticalSobolev h)
    (hc : ComplementSupported (fourierCoeff h)) :
    secondVariation (μ*spectralThreshold d) u h ≤ -(7/16:ℝ)*normalizedPotentialEnergy h := by
  have hw := weighted_square_bound u h hh.1 hu
  have hg := normalizedEnergy_gap hd h hh hc
  have hE := normalizedEnergy_nonneg (by omega : 0 < d) h hh
  have hdiv : normalizedPotentialEnergy h / 2 ≤ normalizedPotentialEnergy h / μ :=
    div_le_div_of_nonneg_left hE hμ hμ2
  have hσ : spectralThreshold d ≠ 0 := by
    exact (Legacy.TorusEndpoint.endpointSigma_pos (by omega : 0 < d)).ne'
  have he : spectralThreshold d / (μ*spectralThreshold d) = 1/μ := by field_simp
  unfold secondVariation
  rw [he]
  have hs := sq_nonneg (∫ x, normalizedGibbs u x*h x ∂torusMeasure d)
  nlinarith [show 1/μ*normalizedPotentialEnergy h = normalizedPotentialEnergy h/μ by ring]

theorem secondVariation_complement_uniform {d : ℕ} (hd : 11 ≤ d) :
    ∀ᶠ (u : Space d) in 𝓝 0, ∀ μ : ℝ, 0 < μ → μ ≤ 2 →
      ∀ h : Torus d → ℝ, InCriticalSobolev h → ComplementSupported (fourierCoeff h) →
        secondVariation (μ*spectralThreshold d) u h ≤ -(7/16:ℝ)*normalizedPotentialEnergy h := by
  filter_upwards [normalized_le_two_near_zero d] with u hu
  exact fun μ hμ hμ2 h hh hc => secondVariation_complement_bound hd hμ hμ2 u hu h hh hc

#print axioms secondVariation_complement_uniform
end BecknerOnofri.HighDim.LocalEleven.ComplementHessian
