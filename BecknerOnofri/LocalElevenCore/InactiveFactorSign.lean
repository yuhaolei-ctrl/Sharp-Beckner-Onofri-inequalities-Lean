import BecknerOnofri.LocalElevenCore.ActiveFactorNonzero
import BecknerOnofri.LocalElevenCore.ActiveAmplitudeEquations

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter
open scoped Topology
namespace BecknerOnofri.HighDim.LocalEleven.ActiveAmplitudeFactor
open AmplitudeLinearization RescaledReducedEquation ReducedEquation

/-- At a real reduced critical point with an active coordinate, each inactive
coordinate has a strictly negative Euler factor, hence a positive energy direction. -/
theorem inactive_factor_negative {d : ℕ} (hd : 11≤d) (i j : Fin d) (hij : i≠j) :
    ∀ᶠ x : Input d in 𝓝 (1,0), reduced hd (realEmbedding d x)=0 → x.2 i≠0 → x.2 j=0 →
      factor hd j x<0 := by
  obtain ⟨H,hH,hH0,he⟩ := exists_nonzero_squared_difference_factor hd i j hij
  filter_upwards [he,scalar_eq_coordinate_mul_factor hd i] with x he hi
  intro hz hai haj
  have hs : scalar hd i x=0 := by simp only [scalar,hz,Pi.zero_apply,Complex.zero_re]
  rw [hs] at hi
  have hfi : factor hd i x=0 := (mul_eq_zero.mp hi.symm).resolve_left hai
  have hh := he.2
  rw [hfi,haj,zero_pow (by norm_num : 2≠0),sub_zero,zero_sub] at hh
  have hp := mul_pos (sq_pos_of_ne_zero hai) he.1
  linarith

#print axioms inactive_factor_negative
end BecknerOnofri.HighDim.LocalEleven.ActiveAmplitudeFactor
