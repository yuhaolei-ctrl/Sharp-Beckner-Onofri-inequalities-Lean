module

public import BecknerOnofri.CircleConvolutionFourier
public import BecknerOnofri.CirclePoissonFourier

@[expose] public section

/-! Fourier action and mass preservation of the actual Haar Poisson convolution. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
namespace BecknerOnofri.HighDim.CirclePoisson

theorem smoothing_coefficient (q : ℝ) (hq : 0≤q) (hq1 : q<1)
    (p : UnitAddCircle → ℝ) (hp : Continuous p) (n : ℤ) :
    _root_.fourierCoeff (fun x => (smoothing q p x:ℂ)) n=
      ((q^n.natAbs:ℝ):ℂ)*_root_.fourierCoeff (fun x => (p x:ℂ)) n := by
  have he : (fun x => (smoothing q p x:ℂ))=
      (fun x => ∫ y,(kernel q y:ℂ)*(p (x-y):ℂ) ∂AddCircle.haarAddCircle) := by
    funext x
    unfold smoothing
    rw [← integral_complex_ofReal]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro y
    exact Complex.ofReal_mul _ _
  have h := convolution_coefficient (fun x => (kernel q x:ℂ)) (fun x => (p x:ℂ)) (Complex.continuous_ofReal.comp (kernel_continuous q hq hq1))
    (Complex.continuous_ofReal.comp hp) n
  rw [he,h,kernel_coefficient q hq hq1]

theorem smoothing_mass (q : ℝ) (hq : 0≤q) (hq1 : q<1)
    (p : UnitAddCircle → ℝ) (hp : Continuous p) :
    (∫ x,smoothing q p x ∂AddCircle.haarAddCircle)=∫ x,p x ∂AddCircle.haarAddCircle := by
  have h := smoothing_coefficient q hq hq1 p hp 0
  simp only [_root_.fourierCoeff,neg_zero,fourier_zero,one_smul,
    Int.natAbs_zero,pow_zero,Complex.ofReal_one,one_mul,integral_complex_ofReal] at h
  exact Complex.ofReal_injective h

theorem smoothing_continuous (q : ℝ) (hq : 0≤q) (hq1 : q<1)
    (p : UnitAddCircle → ℝ) (hp : Continuous p) : Continuous (smoothing q p) := by
  have hcont : Continuous (Function.uncurry (fun x y : UnitAddCircle => kernel q y*p (x-y))) :=
    ((kernel_continuous q hq hq1).comp continuous_snd).mul
      (hp.comp (continuous_fst.sub continuous_snd))
  have h := continuous_parametric_integral_of_continuous
    (μ:=AddCircle.haarAddCircle) hcont isCompact_univ
  unfold smoothing
  simpa only [Measure.restrict_univ] using h

theorem flow_coefficient (s : ℝ) (hs : 0<s)
    (p : UnitAddCircle → ℝ) (hp : Continuous p) (n : ℤ) :
    _root_.fourierCoeff (fun x => (smoothing (Real.exp (-s)) p x:ℂ)) n=
      (Real.exp (-((n.natAbs:ℝ)*s)):ℂ)*_root_.fourierCoeff (fun x => (p x:ℂ)) n := by
  rw [smoothing_coefficient _ (Real.exp_pos _).le (by rw [Real.exp_lt_one_iff]; linarith) p hp n]
  have he : Real.exp (-s)^n.natAbs=Real.exp (-((n.natAbs:ℝ)*s)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [he]

#print axioms smoothing_coefficient
#print axioms flow_coefficient
end BecknerOnofri.HighDim.CirclePoisson
