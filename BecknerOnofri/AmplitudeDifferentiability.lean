module

public import BecknerOnofri.DiagonalAmplitude
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv

@[expose] public section

/-! The chosen inverse amplitude is differentiable at every nearby positive
parameter. Local uniqueness identifies it with the genuine analytic inverse. -/
noncomputable section
open Filter Set
open scoped Topology
namespace BecknerOnofri.HighDim.DiagonalScalarBranch

lemma amplitude_hasDerivAt_of_regular {d : ℕ} (hd : 12 ≤ d) {μ : ℝ}
    (hμ : 1 < μ) (hupper : μ < upperParameter hd)
    (ha : AnalyticAt ℝ (parameter hd) (amplitude hd μ))
    (hne : deriv (parameter hd) (amplitude hd μ) ≠ 0) :
    HasDerivAt (amplitude hd) (deriv (parameter hd) (amplitude hd μ))⁻¹ μ := by
  have hspec := amplitude_spec hd ⟨hμ.le,hupper.le⟩
  have hlo := amplitude_pos hd hμ hupper.le
  have hhi : amplitude hd μ < amplitudeRadius hd := by
    apply lt_of_le_of_ne hspec.1.2
    intro he
    have hx : μ = upperParameter hd := by
      rw [← hspec.2,he]
      rfl
    exact hupper.ne hx
  have hleft : ∀ᶠ t in 𝓝 (amplitude hd μ), amplitude hd (parameter hd t) = t := by
    have hp : ∀ᶠ t in 𝓝 (amplitude hd μ), parameter hd t ∈ Ioo 1 (upperParameter hd) := by
      apply ha.continuousAt.preimage_mem_nhds
      rw [hspec.2]
      exact Ioo_mem_nhds hμ hupper
    filter_upwards [Ioo_mem_nhds hlo hhi,hp] with t ht hp
    exact (amplitude_unique hd ⟨hp.1.le,hp.2.le⟩ ⟨ht.1.le,ht.2.le⟩ rfl).symm
  have h := ha.hasStrictDerivAt.to_local_left_inverse hne hleft
  rw [hspec.2] at h
  exact h.hasDerivAt

lemma amplitude_hasDerivAt {d : ℕ} (hd : 12 ≤ d) :
    ∀ᶠ μ in 𝓝[>] (1:ℝ),
      HasDerivAt (amplitude hd) (deriv (parameter hd) (amplitude hd μ))⁻¹ μ := by
  filter_upwards [self_mem_nhdsWithin,
    (gt_mem_nhds (upperParameter_gt_one hd)).filter_mono nhdsWithin_le_nhds,
    (amplitude_tendsto hd).eventually (parameter_analytic hd).eventually_analyticAt,
    (amplitude_tendsto hd).eventually (parameter_derivative_pos hd)] with μ hμ hupper ha hpos
  exact amplitude_hasDerivAt_of_regular hd hμ hupper ha
    (hpos (amplitude_pos hd hμ hupper.le)).ne'

#print axioms amplitude_hasDerivAt
end BecknerOnofri.HighDim.DiagonalScalarBranch
