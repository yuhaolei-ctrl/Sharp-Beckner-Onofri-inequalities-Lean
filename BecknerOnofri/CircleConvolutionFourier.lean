module

public import BecknerOnofri.CirclePoissonProbability
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

noncomputable section
open MeasureTheory
namespace BecknerOnofri.HighDim.CirclePoisson

theorem fourier_point_add (n : ℤ) (x y : UnitAddCircle) :
    fourier n (x+y)=fourier n x*fourier n y := by
  simp only [fourier_apply,zsmul_add,AddCircle.toCircle_add,Circle.coe_mul]

theorem convolution_coefficient (f g : UnitAddCircle → ℂ)
    (hf : Continuous f) (hg : Continuous g) (n : ℤ) :
    _root_.fourierCoeff (fun x => ∫ y,f y*g (x-y) ∂AddCircle.haarAddCircle) n=
      _root_.fourierCoeff f n*_root_.fourierCoeff g n := by
  have hshift (y : UnitAddCircle) :
      (∫ x,fourier (-n) x*g (x-y) ∂AddCircle.haarAddCircle)=
        fourier (-n) y*_root_.fourierCoeff g n := by
    rw [← integral_add_right_eq_self (fun x : UnitAddCircle => fourier (-n) x*g (x-y)) y]
    simp only [add_sub_cancel_right,fourier_point_add]
    unfold _root_.fourierCoeff
    rw [← integral_const_mul]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro x
    simp only [smul_eq_mul]
    ring
  have hcont : Continuous (Function.uncurry (fun x y : UnitAddCircle =>
      fourier (-n) x*(f y*g (x-y)))) := by
    exact ((fourier _).continuous.comp continuous_fst).mul
      ((hf.comp continuous_snd).mul (hg.comp (continuous_fst.sub continuous_snd)))
  unfold _root_.fourierCoeff
  simp only [smul_eq_mul]
  simp_rw [← integral_const_mul]
  rw [integral_integral_swap_of_hasCompactSupport hcont (HasCompactSupport.of_compactSpace _)]
  have hinner (y : UnitAddCircle) :
      (∫ x,fourier (-n) x*(f y*g (x-y)) ∂AddCircle.haarAddCircle)=
        f y*(fourier (-n) y*_root_.fourierCoeff g n) := by
    rw [← hshift,← integral_const_mul]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro x
    ring
  simp_rw [hinner]
  rw [integral_const_mul,← integral_mul_const]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro y
  change f y*(fourier (-n) y*_root_.fourierCoeff g n)=
    fourier (-n) y*f y*_root_.fourierCoeff g n
  ring

#print axioms convolution_coefficient
end BecknerOnofri.HighDim.CirclePoisson
