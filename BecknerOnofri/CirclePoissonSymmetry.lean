module

public import BecknerOnofri.CircleTorusFlow

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
namespace BecknerOnofri.HighDim.CirclePoisson

local instance : (AddCircle.haarAddCircle (T:=1)).IsNegInvariant := by
  have he : AddCircle.haarAddCircle (T:=1)=(volume : Measure UnitAddCircle) := by
    simpa using (AddCircle.volume_eq_smul_haarAddCircle (T:=1)).symm
  rw [he]
  infer_instance

theorem kernel_even (q : ℝ) (x : UnitAddCircle) : kernel q (-x)=kernel q x := by
  unfold kernel
  have h : (fourier 1 (-x)).re=(fourier 1 x).re := by
    simp only [fourier_apply,zsmul_neg,AddCircle.toCircle_neg]
    simp
  rw [h]

theorem smoothing_even (q : ℝ) (p : UnitAddCircle → ℝ) (he : ∀ x,p (-x)=p x)
    (x : UnitAddCircle) : smoothing q p (-x)=smoothing q p x := by
  unfold smoothing
  rw [← integral_neg_eq_self (fun y => kernel q y*p (-x-y)) AddCircle.haarAddCircle]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro y
  change kernel q (-y)*p (-x-(-y))=kernel q y*p (x-y)
  rw [kernel_even,show -x-(-y)=-(x-y) by abel,he]

theorem torus_flow_even (p : Torus 1 → ℝ) (he : ∀ x,p (-x)=p x)
    (s : ℝ) (x : Torus 1) : torusFlow s p (-x)=torusFlow s p x := by
  by_cases hs : s=0
  · simp only [torusFlow,if_pos hs,he]
  · simp only [torusFlow,if_neg hs,Pi.neg_apply]
    apply smoothing_even
    intro z
    exact he (fun _ => z)

theorem torus_flow_mass (s : ℝ) (hs : 0<s) (p : Torus 1 → ℝ) (hp : Continuous p) :
    (∫ x,torusFlow s p x ∂torusMeasure 1)=∫ x,p x ∂torusMeasure 1 := by
  have h := torus_flow_coefficient s hs p hp 0
  simp only [Pi.zero_apply,Int.cast_zero,abs_zero,neg_zero,zero_mul,Real.exp_zero,
    Complex.ofReal_one,one_mul,UnitAddTorus.mFourierCoeff,UnitAddTorus.mFourier_zero,
    ContinuousMap.one_apply,one_smul,integral_complex_ofReal] at h
  exact Complex.ofReal_injective h

#print axioms torus_flow_even
#print axioms torus_flow_mass
end BecknerOnofri.HighDim.CirclePoisson
