module

public import BecknerOnofri.SmoothConditionalGamma
public import BecknerOnofri.SelectedChannelEntropy

@[expose] public section

/-! Nonstationary shape-density data for the standalone global entropy estimate.
No optimizer, Euler equation or extremality premise is part of this data. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped ContDiff BigOperators
namespace BecknerOnofri.HighDim.ShapeEntropy
open ConditionalEntropy EntropyShearer Legacy.BecknerOnofri

structure Data (ρ : ProbabilityDensity 12) where
  smooth : SmoothOnTorus ρ.value
  symmetric : ∀ (π : Equiv.Perm (Fin 12)) (x : Torus 12),
    ρ.value (ContinuousSymmetry.pointPermutation π x)=ρ.value x
  mixture : GenericCosineRepresentation.HasPositiveCosineMixture ρ.value
  profile : (Fin 12 → ℝ) → ℝ
  continuous_profile : ContinuousOn profile (cosineCube 12)
  convex_profile : ∀ v ∈ cosineCube 12, ∀ i : Fin 12,
    ConvexOn ℝ (Icc (-1 : ℝ) 1) (fun t => profile (Function.update v i t))
  monotone_profile : ∀ v ∈ cosineCube 12, ∀ i : Fin 12,
    MonotoneOn (fun t => profile (Function.update v i t)) (Icc (-1 : ℝ) 1)
  representation : ∀ x,ρ.value x=Real.exp (profile (cosineVector x))

variable {ρ : ProbabilityDensity 12} (D : Data ρ)
include D

lemma continuous_density : Continuous ρ.value := UniformFourier.smooth_continuous D.smooth
lemma positive_density : PositiveBounded ρ.value :=
  positiveBounded_of_continuous_pos (continuous_density D)
    (fun x => by rw [D.representation]; exact Real.exp_pos _)
lemma exchangeable : Spin.Exchangeable (Spin.channelLaw ρ) :=
  Spin.channelLaw_exchangeable ρ D.symmetric
lemma feasible : Spin.Feasible (Spin.countLaw (Spin.channelLaw ρ)) :=
  Spin.channel_count_feasible ρ D.mixture

lemma conditional_mean_range (i : Fin 12) (x : Torus 12) :
    conditionalCosineMoment ρ.value i 1 x∈Ico (0 : ℝ) 1 := by
  obtain ⟨F,hc,hcv,hm,hr⟩ := conditional_log_profile D.profile D.continuous_profile
    D.convex_profile D.monotone_profile ρ.value D.representation i x
  have h := conditional_profile_stats (positive_density D) i x F hc hcv hm hr
  exact ⟨h.1,h.2.1⟩

lemma conditional_gamma_finite (ψ : ℝ → ℝ)
    (hψ : ∀ t∈Ico (0 : ℝ) 1,ψ t≤CircleScalar.gamma t)
    (i : Fin 12) (x : Torus 12) (s : Finset ℕ) :
    2*Spin.binaryCost (conditionalCosineMoment ρ.value i 1 x)+
      ψ (conditionalCosineMoment ρ.value i 1 x)+
      (21/1000)*(conditionalCosineMoment ρ.value i 2 x)^2+
      (27/40)*(∑ n∈s,(conditionalCosineMoment ρ.value i (n+3) x)^2/(n+3 : ℝ))≤
      conditionalEntropy ρ.value i x := by
  obtain ⟨F,hc,hcv,hm,hr⟩ := conditional_log_profile D.profile D.continuous_profile
    D.convex_profile D.monotone_profile ρ.value D.representation i x
  obtain ⟨h0,h1,hs⟩ := conditional_profile_stats (positive_density D) i x F hc hcv hm hr
  have hm := hψ _ ⟨h0,h1⟩
  have hsum := Summable.sum_le_tsum s (fun n _ => by positivity) hs
  have h := smooth_conditional_gamma D.profile D.continuous_profile D.convex_profile
    D.monotone_profile ρ.value D.representation D.smooth i x
  linarith

lemma spin_entropy : Spin.relativeEntropy (Spin.countLaw (Spin.channelLaw ρ)) Spin.reference≤
    ∑ i : Fin 12,∫ x,ρ.value x*Spin.binaryCost (conditionalCosineMoment ρ.value i 1 x) ∂torusMeasure 12 :=
  Spin.count_entropy_le_conditional ρ (positive_density D) (exchangeable D)

#print axioms conditional_gamma_finite
end BecknerOnofri.HighDim.ShapeEntropy
