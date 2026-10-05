import BecknerOnofri.CircleFisherHalf

/-! Construct the actual canonical exponential factor and prove the pointwise
Fisher identity from Fourier differentiation. No Fisher identity is assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open MeasureTheory
open scoped ComplexConjugate
namespace BecknerOnofri.HighDim.CircleFisher
open Legacy.TorusEndpoint Legacy.BecknerOnofri.WienerFourier CircleOuter
open Legacy.BecknerOnofri.WeightedWiener

theorem logarithm_fisher_factor (g : Torus 1 → ℝ)
    (hg : Continuous g) (he : ∀ x,g (-x)=g x)
    (hw : Summable (fun k => linearWeight k*
      ‖UnitAddTorus.mFourierCoeff (fun x => (g x:ℂ)) k‖)) :
    ∃ f : C(Torus 1,ℂ),
      (∀ x,Complex.normSq (f x)=Real.exp (g x)) ∧
      Summable (fun k => linearWeight k*‖UnitAddTorus.mFourierCoeff f k‖) ∧
      (∀ k,conj (UnitAddTorus.mFourierCoeff f k)=UnitAddTorus.mFourierCoeff f k) ∧
      (∀ k,k (0:Fin 1)<0 → UnitAddTorus.mFourierCoeff f k=0) ∧
      ∀ x,Real.exp (g x)*lambda g x=
        2*(conj (f x)*signedSeries (UnitAddTorus.mFourierCoeff f) x).re := by
  let l : Frequency 1 → ℝ := fun k => (UnitAddTorus.mFourierCoeff (fun x => (g x:ℂ)) k).re
  have hl (k : Frequency 1) : (l k:ℂ)=UnitAddTorus.mFourierCoeff (fun x => (g x:ℂ)) k := by
    apply Complex.conj_eq_iff_re.mp
    rw [← real_coefficient_neg,even_coefficient_neg g he]
  have hs := summable_norm linearWeight_isWeight hw
  have hls : Summable (fun k => ‖l k‖) := by
    simpa only [← hl,Complex.norm_real] using hs
  have hle (k : Frequency 1) : l (-k)=l k := by
    dsimp only [l]
    rw [even_coefficient_neg g he]
  have hlw : Summable (fun k => linearWeight k*‖(l k:ℂ)‖) := by
    simpa only [hl] using hw
  have hlmoment : Summable (fun k => ‖|(k (0:Fin 1):ℝ)| * l k‖) := by
    simpa only [norm_mul,Real.norm_eq_abs,abs_abs,Complex.norm_real] using
      first_moment_summable (fun k => (l k:ℂ)) hlw
  have hrec (x : Torus 1) : absoluteFourierSeries (fun k => (l k:ℂ)) x=(g x:ℂ) := by
    let G : C(Torus 1,ℂ) := ⟨fun x => (g x:ℂ),Complex.continuous_ofReal.comp hg⟩
    have hsum := UnitAddTorus.hasSum_mFourier_series_apply_of_summable (f:=G) hs.of_norm x
    simpa only [absoluteFourierSeries,hl,smul_eq_mul] using
      (show (∑' k,UnitAddTorus.mFourierCoeff (fun x => (g x:ℂ)) k • UnitAddTorus.mFourier k x)=(g x:ℂ) from hsum.tsum_eq)
  let a := halfSpectrum (0:Fin 1) l
  have ha : Summable (fun k => ‖a k‖) := halfSpectrum_summable 0 l hls
  have haw : Summable (fun k => linearWeight k*‖a k‖) := by
    apply Summable.of_nonneg_of_le (fun k => mul_nonneg (linearWeight_isWeight.nonneg k) (norm_nonneg _)) _ hlw
    intro k
    rw [Complex.norm_real]
    exact mul_le_mul_of_nonneg_left (halfSpectrum_norm_le 0 l k) (linearWeight_isWeight.nonneg k)
  let f : C(Torus 1,ℂ) := ⟨fun x => Complex.exp (absoluteFourierSeries a x),
    Complex.continuous_exp.comp (absoluteFourierSeries_continuous a ha)⟩
  have hfp (x : Torus 1) : Complex.normSq (f x)=Real.exp (g x) := by
    change Complex.normSq (Complex.exp (absoluteFourierSeries (halfSpectrum 0 l) x))=_
    rw [exponential_boundary_square 0 l hls hle,hrec,Complex.ofReal_re]
  have hfw : Summable (fun k => linearWeight k*‖UnitAddTorus.mFourierCoeff f k‖) :=
    Legacy.BecknerOnofri.WeightedWiener.exponential_fourier_summable linearWeight_isWeight a haw
  have hfs := summable_norm linearWeight_isWeight hfw
  have hbrec (x : Torus 1) : absoluteFourierSeries (UnitAddTorus.mFourierCoeff f) x=
      Complex.exp (absoluteFourierSeries a x) := by
    have h := UnitAddTorus.hasSum_mFourier_series_apply_of_summable (f:=f) hfs.of_norm x
    change absoluteFourierSeries (UnitAddTorus.mFourierCoeff f) x=f x
    simpa only [absoluteFourierSeries,smul_eq_mul] using h.tsum_eq
  refine ⟨f,hfp,hfw,?_,?_,?_⟩
  · intro k
    change conj (UnitAddTorus.mFourierCoeff (fun x => Complex.exp (absoluteFourierSeries a x)) k)=
      UnitAddTorus.mFourierCoeff (fun x => Complex.exp (absoluteFourierSeries a x)) k
    rw [exponential_coefficient a ha]
    exact exponential_real a (halfSpectrum_real 0 l) k
  · intro k hk
    exact exponential_fourier_nonnegative_support 0 a ha (halfSpectrum_negative 0 l) k hk
  · intro x
    have hlam : lambda g x=2*(signedSeries a x).re := by
      have h := half_signed_real_part l hlmoment hle x
      simpa only [lambda,absoluteFourierSeries,Complex.ofReal_mul,hl] using h.symm
    have hd := exponential_signed_series a (UnitAddTorus.mFourierCoeff f) haw hfw hbrec x
    calc
      Real.exp (g x)*lambda g x=Complex.normSq (f x)*(2*(signedSeries a x).re) := by rw [hfp,hlam]
      _ = 2*(conj (f x)*(f x*signedSeries a x)).re := normSq_log_derivative _ _
      _ = _ := by rw [hd]; rfl

#print axioms logarithm_fisher_factor
end BecknerOnofri.HighDim.CircleFisher
