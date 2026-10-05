import BecknerOnofri.CircleOuterBoundary
import Legacy.BecknerOnofri.WeightedWiener
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! Reconstruction from the actual Fourier coefficients of a continuous even
logarithm. Absolute summability is an explicit regularity premise here; it will
be discharged for the smooth densities in the entropy-remainder theorem. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open MeasureTheory
open scoped ComplexConjugate
namespace BecknerOnofri.HighDim.CircleOuter
open Legacy.TorusEndpoint Legacy.BecknerOnofri.WienerFourier

local instance : (AddCircle.haarAddCircle (T:=1)).IsNegInvariant := by
  have he : AddCircle.haarAddCircle (T:=1)=(volume : Measure UnitAddCircle) := by
    simpa using (AddCircle.volume_eq_smul_haarAddCircle (T:=1)).symm
  rw [he]
  infer_instance
local instance (d : ℕ) : (torusMeasure d).IsNegInvariant := by
  unfold torusMeasure
  infer_instance

theorem real_coefficient_neg {d : ℕ} (g : Torus d → ℝ) (k : Frequency d) :
    UnitAddTorus.mFourierCoeff (fun x => (g x:ℂ)) (-k)=
      conj (UnitAddTorus.mFourierCoeff (fun x => (g x:ℂ)) k) := by
  unfold UnitAddTorus.mFourierCoeff
  rw [← integral_conj]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  simp only [neg_neg,smul_eq_mul,map_mul,Complex.conj_ofReal,UnitAddTorus.mFourier_neg]
  simp

theorem even_coefficient_neg {d : ℕ} (g : Torus d → ℝ) (he : ∀ x,g (-x)=g x)
    (k : Frequency d) :
    UnitAddTorus.mFourierCoeff (fun x => (g x:ℂ)) (-k)=
      UnitAddTorus.mFourierCoeff (fun x => (g x:ℂ)) k := by
  change (∫ x,UnitAddTorus.mFourier (-(-k)) x*(g x:ℂ) ∂torusMeasure d)=
    ∫ x,UnitAddTorus.mFourier (-k) x*(g x:ℂ) ∂torusMeasure d
  rw [← integral_neg_eq_self (fun x => UnitAddTorus.mFourier (-(-k)) x*(g x:ℂ)) (torusMeasure d)]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  change UnitAddTorus.mFourier (-(-k)) (-x)*(g (-x):ℂ)=UnitAddTorus.mFourier (-k) x*(g x:ℂ)
  rw [he,neg_neg]
  congr 1
  simp only [UnitAddTorus.mFourier,ContinuousMap.coe_mk,Pi.neg_apply,fourier_apply,
    zsmul_neg,neg_zsmul]

theorem logarithm_outer_exists {d : ℕ} (i : Fin d) (g : Torus d → ℝ)
    (hg : Continuous g) (he : ∀ x,g (-x)=g x)
    (hs : Summable (fun k => ‖UnitAddTorus.mFourierCoeff (fun x => (g x:ℂ)) k‖)) :
    ∃ f : C(Torus d,ℂ),
      (∀ x,Complex.normSq (f x)=Real.exp (g x)) ∧
      Summable (fun k => ‖UnitAddTorus.mFourierCoeff f k‖) ∧
      (∀ k,conj (UnitAddTorus.mFourierCoeff f k)=UnitAddTorus.mFourierCoeff f k) ∧
      (∀ k,k i<0 → UnitAddTorus.mFourierCoeff f k=0) ∧
      ∀ w : Frequency d → ℝ,Legacy.BecknerOnofri.WeightedWiener.IsWeight w →
        Summable (fun k => w k*‖UnitAddTorus.mFourierCoeff (fun x => (g x:ℂ)) k‖) →
        Summable (fun k => w k*‖UnitAddTorus.mFourierCoeff f k‖) := by
  let l : Frequency d → ℝ := fun k => (UnitAddTorus.mFourierCoeff (fun x => (g x:ℂ)) k).re
  have hl (k : Frequency d) : (l k:ℂ)=UnitAddTorus.mFourierCoeff (fun x => (g x:ℂ)) k := by
    apply Complex.conj_eq_iff_re.mp
    rw [← real_coefficient_neg,even_coefficient_neg g he]
  have hls : Summable (fun k => ‖l k‖) := by
    simpa only [← hl,Complex.norm_real] using hs
  have hle (k : Frequency d) : l (-k)=l k := by
    dsimp only [l]
    rw [even_coefficient_neg g he]
  have hrec (x : Torus d) : absoluteFourierSeries (fun k => (l k:ℂ)) x=(g x:ℂ) := by
    let G : C(Torus d,ℂ) := ⟨fun x => (g x:ℂ),Complex.continuous_ofReal.comp hg⟩
    have hsum := UnitAddTorus.hasSum_mFourier_series_apply_of_summable (f:=G) hs.of_norm x
    simpa only [absoluteFourierSeries,hl,smul_eq_mul] using (show (∑' k,UnitAddTorus.mFourierCoeff (fun x => (g x:ℂ)) k • UnitAddTorus.mFourier k x)=(g x:ℂ) from hsum.tsum_eq)
  let a := halfSpectrum i l
  have ha : Summable (fun k => ‖a k‖) := halfSpectrum_summable i l hls
  let f : C(Torus d,ℂ) := ⟨fun x => Complex.exp (absoluteFourierSeries a x),
    Complex.continuous_exp.comp (absoluteFourierSeries_continuous a ha)⟩
  refine ⟨f,?_,?_,?_,?_,?_⟩
  · intro x
    change Complex.normSq (Complex.exp (absoluteFourierSeries (halfSpectrum i l) x))=_
    rw [exponential_boundary_square i l hls hle,hrec,Complex.ofReal_re]
  · exact exponential_fourier_summable a ha
  · intro k
    change conj (UnitAddTorus.mFourierCoeff (fun x => Complex.exp (absoluteFourierSeries a x)) k)=_
    change conj (UnitAddTorus.mFourierCoeff (fun x => Complex.exp (absoluteFourierSeries a x)) k)=
      UnitAddTorus.mFourierCoeff (fun x => Complex.exp (absoluteFourierSeries a x)) k
    rw [exponential_coefficient a ha]
    exact exponential_real a (halfSpectrum_real i l) k
  · intro k hk
    exact exponential_fourier_nonnegative_support i a ha (halfSpectrum_negative i l) k hk

  · intro w hw hweight
    have haw : Summable (fun k => w k*‖a k‖) := by
      apply Summable.of_nonneg_of_le (fun k => mul_nonneg (hw.nonneg k) (norm_nonneg _)) _ hweight
      intro k
      have hnorm : ‖a k‖≤‖UnitAddTorus.mFourierCoeff (fun x => (g x:ℂ)) k‖ := by
        rw [← hl,Complex.norm_real]
        exact halfSpectrum_norm_le i l k
      exact mul_le_mul_of_nonneg_left hnorm (hw.nonneg k)
    exact Legacy.BecknerOnofri.WeightedWiener.exponential_fourier_summable hw a haw

#print axioms logarithm_outer_exists
end BecknerOnofri.HighDim.CircleOuter
