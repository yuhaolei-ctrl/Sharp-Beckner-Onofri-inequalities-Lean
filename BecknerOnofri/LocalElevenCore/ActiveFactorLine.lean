import BecknerOnofri.LocalElevenCore.ActiveFactorDifference

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter Asymptotics
open scoped Topology
namespace BecknerOnofri.HighDim.LocalEleven.ActiveAmplitudeFactor
open ContinuousFirstShell AmplitudeLinearization RescaledReducedEquation ReducedEquation ReducedCubicExpansion

def twoLine {d : ℕ} (i j : Fin d) : ℝ →L[ℝ] Amplitudes d :=
  ContinuousLinearMap.pi (fun k => if k=i then ContinuousLinearMap.id ℝ ℝ
    else if k=j then (2:ℝ) • ContinuousLinearMap.id ℝ ℝ else 0)

@[simp] theorem twoLine_apply {d : ℕ} (i j : Fin d) (t : ℝ) (k : Fin d) :
    twoLine i j t k=if k=i then t else if k=j then 2*t else 0 := by
  simp only [twoLine,ContinuousLinearMap.pi_apply]
  split_ifs <;> simp

theorem cubic_two_coordinates {d : ℕ} (hd : 11≤d) (i j : Fin d) (z : Coordinates d)
    (t : ℝ) (hi : z i=(t:ℂ)) (hj : z j=((2*t:ℝ):ℂ)) :
    (cubicModel hd z i).re-(cubicModel hd z j).re/2 =
      -3*(quarticB d-2*quarticA d)*t^3 := by
  simp only [cubicModel_apply,hi,hj,Complex.norm_real,Real.norm_eq_abs,sq_abs,
    Complex.neg_re,Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    Complex.mul_im,zero_mul,mul_zero,sub_zero,add_zero]
  ring

theorem scalar_two_line_cubic {d : ℕ} (hd : 11≤d) (i j : Fin d) (hij : i≠j) :
    (fun t : ℝ => scalar hd i (1,twoLine i j t)-scalar hd j (1,twoLine i j t)/2 -
      (-3*(quarticB d-2*quarticA d))*t^3)
      =O[𝓝 0] (fun t => ‖t‖^5) := by
  let Z : ℝ →L[ℝ] Coordinates d := (realCoordinates d).comp (twoLine i j)
  have ht : Tendsto Z (𝓝 (0:ℝ)) (𝓝 0) := by
    simpa only [map_zero] using Z.continuous.tendsto (0:ℝ)
  have hb : (fun t => reduced hd (1,Z t)-cubicModel hd (Z t))
      =O[𝓝 (0:ℝ)] (fun t => ‖t‖^5) :=
    ((reduced_cubic_expansion_fifth hd).comp_tendsto ht).trans
      ((Z.isBigO_comp (fun t => t) (𝓝 0)).norm_left.norm_right.pow 5)
  let ev : Coordinates d →L[ℝ] ℝ :=
    Complex.reCLM.comp (ContinuousLinearMap.proj i) -
      (1/2:ℝ) • (Complex.reCLM.comp (ContinuousLinearMap.proj j))
  have h := (ev.isBigO_comp _ _).trans hb
  apply h.congr_left
  intro t
  have hi : Z t i=(t:ℂ) := by simp [Z,hij]
  have hj : Z t j=((2*t:ℝ):ℂ) := by simp [Z,hij.symm]
  have hc := cubic_two_coordinates hd i j (Z t) t hi hj
  change ((reduced hd (1,Z t) i).re-(cubicModel hd (Z t) i).re) -
    (1/2)*((reduced hd (1,Z t) j).re-(cubicModel hd (Z t) j).re) = _
  change _ = (reduced hd (1,Z t) i).re-(reduced hd (1,Z t) j).re/2 -
    (-3*(quarticB d-2*quarticA d))*t^3
  linarith

#print axioms scalar_two_line_cubic
end BecknerOnofri.HighDim.LocalEleven.ActiveAmplitudeFactor
