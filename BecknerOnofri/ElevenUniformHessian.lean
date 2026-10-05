module

public import BecknerOnofri.UniformEntropyHessian
public import BecknerOnofri.UniformFourierHessian
public import BecknerOnofri.ElevenTransitionZeroSet

@[expose] public section

/-! The second derivative in the trusted definition is computed by actual
entropy differentiation and the exact quadratic Fourier identity. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped Topology
namespace BecknerOnofri.HighDim.Eleven
open ContinuousGibbs

lemma uniformHessian_eq (β : ℝ) (h : Space 11) :
    uniformHessian β h = (∫ x, (h x)^2 ∂torusMeasure 11) -
      β/spectralThreshold 11*UniformFourier.energy h := by
  let E := UniformFourier.energy h
  let c := β/(2*spectralThreshold 11)
  have hf (t : ℝ) : rawFreeEnergy β (fun x => 1+t*h x) =
      (∫ x, (1+t*h x)*Real.log (1+t*h x) ∂torusMeasure 11)-c*(t^2*E) := by
    change _ - β/(2*spectralThreshold 11)*UniformFourier.energy (fun x => 1+t*h x) = _
    rw [UniformFourier.perturbation_energy]
  have hd (t : ℝ) (ht : |t| < 1/(2*(‖h‖+1))) :
      HasDerivAt (fun t => rawFreeEnergy β (fun x => 1+t*h x))
        ((∫ x, (Real.log (1+t*h x)+1)*h x ∂torusMeasure 11)-c*(2*t*E)) t := by
    simp_rw [hf]
    convert! (UniformEntropy.entropy_hasDerivAt h ht).sub
      ((((hasDerivAt_id t).pow 2).mul_const E).const_mul c) using 1 <;> simp_all only [id_eq, one_mul, pow_one] <;> ring
  have he : deriv (fun t => rawFreeEnergy β (fun x => 1+t*h x)) =ᶠ[𝓝 0]
      (fun t => (∫ x, (Real.log (1+t*h x)+1)*h x ∂torusMeasure 11)-c*(2*t*E)) := by
    filter_upwards [(isOpen_lt continuous_abs continuous_const).mem_nhds
      (by change |(0:ℝ)| < 1/(2*(‖h‖+1)); simp only [abs_zero]; positivity)] with t ht
    exact (hd t ht).deriv
  unfold uniformHessian
  rw [he.deriv_eq]
  have H := (UniformEntropy.entropy_second_hasDerivAt h).sub
    ((((hasDerivAt_id (0:ℝ)).const_mul 2).mul_const E).const_mul c)
  have H' : HasDerivAt
      (fun t => (∫ x, (Real.log (1+t*h x)+1)*h x ∂torusMeasure 11)-c*(2*t*E))
      ((∫ x, (h x)^2 ∂torusMeasure 11)-c*(2*E)) 0 := by
    convert! H using 1 <;> first | rfl | ring
  rw [H'.deriv]
  dsimp [c, E]
  ring

theorem uniform_hessian :
    0 < 1-globalTransition/spectralThreshold 11 ∧
    ∀ h : Torus 11 → ℝ, SmoothOnTorus h → MeanZero h →
      (1-globalTransition/spectralThreshold 11)*(∫ x, (h x)^2 ∂torusMeasure 11) ≤
        uniformHessian globalTransition h := by
  refine ⟨transition_spectral_gap, fun h hs _hm => ?_⟩
  let H : Space 11 := ⟨h, UniformFourier.smooth_continuous hs⟩
  change _ ≤ uniformHessian globalTransition H
  rw [uniformHessian_eq]
  have hb := mul_le_mul_of_nonneg_left (UniformFourier.energy_le_square H)
    (div_nonneg transition_pos.le (spectralThreshold_pos (d := 11) (by norm_num)).le)
  change globalTransition/spectralThreshold 11*UniformFourier.energy H ≤
    globalTransition/spectralThreshold 11*(∫ x, (h x)^2 ∂torusMeasure 11) at hb
  dsimp only [H, ContinuousMap.coe_mk] at *
  linarith

#print axioms uniformHessian_eq
#print axioms uniform_hessian
end BecknerOnofri.HighDim.Eleven
