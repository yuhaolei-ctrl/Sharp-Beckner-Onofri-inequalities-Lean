module

public import BecknerOnofri.CircleDeficitDefinitions
public import BecknerOnofri.CircleTorusRegularity
public import BecknerOnofri.CircleDensityParseval

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
namespace BecknerOnofri.HighDim.CirclePoisson

theorem integral_torus_circle (f : Torus 1 → ℝ) :
    (∫ x,f x ∂torusMeasure 1)=∫ z : UnitAddCircle,f (fun _ => z) ∂AddCircle.haarAddCircle := by
  have h := (measurePreserving_funUnique AddCircle.haarAddCircle (Fin 1)).symm
    (MeasurableEquiv.funUnique (Fin 1) UnitAddCircle)
  exact (h.integral_comp' f).symm

theorem moment_eq_cosine_integral (p : Torus 1 → ℝ) (hp : Continuous p) (n : ℕ) :
    moment p n=∫ z : UnitAddCircle,p (fun _ => z)*(fourier (n:ℤ) z).re ∂AddCircle.haarAddCircle := by
  unfold moment
  rw [CircleRegularity.torus_coefficient_circle]
  unfold _root_.fourierCoeff
  simp only [smul_eq_mul]
  have hc : Continuous (fun z : UnitAddCircle => fourier (-(n:ℤ)) z*(p (fun _ => z):ℂ)) :=
    (map_continuous (fourier (-(n:ℤ)))).mul
      (Complex.continuous_ofReal.comp (hp.comp (continuous_pi (fun _ => continuous_id))))
  have hi := hc.integrable_of_hasCompactSupport (μ:=AddCircle.haarAddCircle) (HasCompactSupport.of_compactSpace _)
  have h := integral_re hi
  change (∫ z : UnitAddCircle,(fourier (-(n:ℤ)) z*(p (fun _ => z):ℂ)).re ∂AddCircle.haarAddCircle)=
    (∫ z : UnitAddCircle,fourier (-(n:ℤ)) z*(p (fun _ => z):ℂ) ∂AddCircle.haarAddCircle).re at h
  rw [← h]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  simp only [fourier_neg,Complex.mul_re,Complex.conj_re,Complex.ofReal_re,
    Complex.ofReal_im,mul_zero,zero_mul,sub_zero,mul_comm]

#print axioms moment_eq_cosine_integral
end BecknerOnofri.HighDim.CirclePoisson
