module

public import BecknerOnofri.CircleTorusDerivative

@[expose] public section

/-! Continuity, actual Fourier coefficients and self-adjointness of the
circle |n| multiplier on functions with an absolutely summable first moment. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped ComplexConjugate
namespace BecknerOnofri.HighDim.CircleFisher
open Legacy.TorusEndpoint CircleOuter

theorem lambda_coeff_summable (g : Torus 1 → ℝ)
    (hw : Summable (fun k => linearWeight k*‖UnitAddTorus.mFourierCoeff (fun x => (g x:ℂ)) k‖)) :
    Summable (fun k => ‖((|(k (0:Fin 1):ℝ)|:ℝ):ℂ)*UnitAddTorus.mFourierCoeff (fun x => (g x:ℂ)) k‖) := by
  simpa only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_abs] using
    first_moment_summable (UnitAddTorus.mFourierCoeff (fun x => (g x:ℂ))) hw

theorem lambda_continuous (g : Torus 1 → ℝ)
    (hw : Summable (fun k => linearWeight k*‖UnitAddTorus.mFourierCoeff (fun x => (g x:ℂ)) k‖)) :
    Continuous (lambda g) := by
  exact Complex.continuous_re.comp
    (absoluteFourierSeries_continuous _ (lambda_coeff_summable g hw))

theorem lambda_series (g : Torus 1 → ℝ) (x : Torus 1) :
    (lambda g x:ℂ)=absoluteFourierSeries
      (fun k => ((|(k (0:Fin 1):ℝ)|:ℝ):ℂ)*UnitAddTorus.mFourierCoeff (fun y => (g y:ℂ)) k) x := by
  apply Complex.conj_eq_iff_re.mp
  change conj (absoluteFourierSeries
    (fun k => ((|(k (0:Fin 1):ℝ)|:ℝ):ℂ)*UnitAddTorus.mFourierCoeff (fun y => (g y:ℂ)) k) x)=_
  rw [series_conjugate]
  apply congrArg (fun a => absoluteFourierSeries a x)
  funext k
  simp only [Pi.neg_apply,Int.cast_neg,abs_neg,map_mul,Complex.conj_ofReal,
    real_coefficient_neg,Complex.conj_conj]

theorem lambda_coefficient (g : Torus 1 → ℝ)
    (hw : Summable (fun k => linearWeight k*‖UnitAddTorus.mFourierCoeff (fun x => (g x:ℂ)) k‖))
    (k : Frequency 1) :
    UnitAddTorus.mFourierCoeff (fun x => (lambda g x:ℂ)) k=
      ((|(k (0:Fin 1):ℝ)|:ℝ):ℂ)*UnitAddTorus.mFourierCoeff (fun x => (g x:ℂ)) k := by
  simp_rw [lambda_series]
  exact absoluteFourierSeries_coefficient _ (lambda_coeff_summable g hw) k

theorem lambda_self_adjoint (p g : Torus 1 → ℝ) (hp : Continuous p) (hg : Continuous g)
    (hpw : Summable (fun k => linearWeight k*‖UnitAddTorus.mFourierCoeff (fun x => (p x:ℂ)) k‖))
    (hgw : Summable (fun k => linearWeight k*‖UnitAddTorus.mFourierCoeff (fun x => (g x:ℂ)) k‖)) :
    (∫ x,p x*lambda g x ∂torusMeasure 1)=∫ x,lambda p x*g x ∂torusMeasure 1 := by
  let P : C(Torus 1,ℂ) := ⟨fun x => (p x:ℂ),Complex.continuous_ofReal.comp hp⟩
  let G : C(Torus 1,ℂ) := ⟨fun x => (g x:ℂ),Complex.continuous_ofReal.comp hg⟩
  let LP : C(Torus 1,ℂ) := ⟨fun x => (lambda p x:ℂ),Complex.continuous_ofReal.comp (lambda_continuous p hpw)⟩
  let LG : C(Torus 1,ℂ) := ⟨fun x => (lambda g x:ℂ),Complex.continuous_ofReal.comp (lambda_continuous g hgw)⟩
  have h1 := boundary_parseval_inner P LG
  have h2 := boundary_parseval_inner LP G
  have hc1 (k : Frequency 1) : UnitAddTorus.mFourierCoeff LG k=
      ((|(k (0:Fin 1):ℝ)|:ℝ):ℂ)*UnitAddTorus.mFourierCoeff G k := lambda_coefficient g hgw k
  have hc2 (k : Frequency 1) : UnitAddTorus.mFourierCoeff LP k=
      ((|(k (0:Fin 1):ℝ)|:ℝ):ℂ)*UnitAddTorus.mFourierCoeff P k := lambda_coefficient p hpw k
  simp only [hc1] at h1
  simp only [hc2,map_mul,Complex.conj_ofReal] at h2
  have hterms : (fun k => conj (UnitAddTorus.mFourierCoeff P k)*
      (((|(k (0:Fin 1):ℝ)|:ℝ):ℂ)*UnitAddTorus.mFourierCoeff G k))=
      (fun k => ((|(k (0:Fin 1):ℝ)|:ℝ):ℂ)*conj (UnitAddTorus.mFourierCoeff P k)*UnitAddTorus.mFourierCoeff G k) := by
    funext k; ring
  rw [hterms] at h1
  have h := h1.unique h2
  have hi1 : (∫ x,conj (P x)*LG x ∂torusMeasure 1)=((∫ x,p x*lambda g x ∂torusMeasure 1:ℝ):ℂ) := by
    simp only [P,LG,ContinuousMap.coe_mk,Complex.conj_ofReal,← Complex.ofReal_mul,integral_complex_ofReal]
  have hi2 : (∫ x,conj (LP x)*G x ∂torusMeasure 1)=((∫ x,lambda p x*g x ∂torusMeasure 1:ℝ):ℂ) := by
    simp only [LP,G,ContinuousMap.coe_mk,Complex.conj_ofReal,← Complex.ofReal_mul,integral_complex_ofReal]
  rw [hi1,hi2] at h
  exact Complex.ofReal_injective h

#print axioms lambda_self_adjoint
end BecknerOnofri.HighDim.CircleFisher
