import BecknerOnofri.LocalElevenCore.ActiveAmplitudeFactor

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter
open scoped Topology
namespace BecknerOnofri.HighDim.LocalEleven.ActiveAmplitudeFactor
open ContinuousFirstShell AmplitudeLinearization RescaledReducedEquation ReducedEquation ContinuousSymmetry

theorem real_residual {d : ℕ} (hd : 11≤d) :
    ∀ᶠ x : ℝ × Amplitudes d in 𝓝 (1,0),∀ i,(reduced hd (realEmbedding d x) i).im=0 := by
  filter_upwards [(realEmbedding_tendsto d).eventually (reduced_reflection hd)] with x hx i
  have he : conjugateCoordinates (realCoordinates d x.2)=realCoordinates d x.2 := by
    ext j
    simp only [conjugateCoordinates_apply,realCoordinates_apply,Complex.conj_ofReal]
  simp only [realEmbedding_apply,he] at hx
  have hh := congrArg Complex.im (congrFun hx i)
  simp only [conjugateCoordinates_apply,Complex.conj_im] at hh
  change (reduced hd (x.1,realCoordinates d x.2) i).im=0
  linarith

/-- The actual reduced critical equation factors coordinatewise, including all
coordinate hyperplanes, so every active coordinate must solve its analytic factor. -/
theorem reduced_zero_iff_coordinate_factors {d : ℕ} (hd : 11≤d) :
    ∀ᶠ x : ℝ × Amplitudes d in 𝓝 (1,0),
      reduced hd (realEmbedding d x)=0 ↔ ∀ i,x.2 i=0 ∨ factor hd i x=0 := by
  have hf : ∀ᶠ x : ℝ × Amplitudes d in 𝓝 (1,0),∀ i,
      scalar hd i x=x.2 i*factor hd i x :=
    Filter.eventually_all.mpr (fun i => scalar_eq_coordinate_mul_factor hd i)
  filter_upwards [hf,real_residual hd] with x hf hr
  constructor
  · intro hz i
    have h : scalar hd i x=0 := congrArg Complex.re (congrFun hz i)
    rw [hf i] at h
    exact mul_eq_zero.mp h
  · intro h
    ext i
    apply Complex.ext
    · change scalar hd i x=0
      rw [hf i]
      exact mul_eq_zero.mpr (h i)
    · exact hr i

#print axioms reduced_zero_iff_coordinate_factors
end BecknerOnofri.HighDim.LocalEleven.ActiveAmplitudeFactor
