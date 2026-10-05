import BecknerOnofri.CircleTorusDerivative

/-! Parseval identifies the actual signed-derivative boundary pairing with
weighted Hardy coefficient energy. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped ComplexConjugate
namespace BecknerOnofri.HighDim.CircleFisher
open Legacy.TorusEndpoint CircleOuter

theorem signed_pairing (f : C(Torus 1,ℂ)) (u : CircleHardy.Space)
    (hw : Summable (fun k => linearWeight k*‖UnitAddTorus.mFourierCoeff f k‖))
    (hu : ∀ n : ℕ,(u n:ℂ)=UnitAddTorus.mFourierCoeff f (fun _ => (n:ℤ)))
    (hn : ∀ k,k (0:Fin 1)<0 → UnitAddTorus.mFourierCoeff f k=0) :
    (∫ x,(conj (f x)*signedSeries (UnitAddTorus.mFourierCoeff f) x).re ∂torusMeasure 1)=
      ∑' n : ℕ,(n:ℝ)*(u n)^2 := by
  let a := UnitAddTorus.mFourierCoeff f
  have hs := signed_coefficients_summable a hw
  let D : C(Torus 1,ℂ) := ⟨signedSeries a,
    absoluteFourierSeries_continuous (fun k => (k (0:Fin 1):ℂ)*a k) hs⟩
  have hD (k : Frequency 1) : UnitAddTorus.mFourierCoeff D k=(k (0:Fin 1):ℂ)*a k :=
    absoluteFourierSeries_coefficient _ hs k
  have h := boundary_parseval_inner f D
  simp only [hD] at h
  let c : ℤ → ℂ := fun z => a (fun _ => z)
  have hZ : HasSum (fun z : ℤ => conj (c z)*((z:ℂ)*c z))
      (∫ x,conj (f x)*D x ∂torusMeasure 1) :=
    ((Equiv.funUnique (Fin 1) ℤ).symm.hasSum_iff).mpr h
  have hN := hZ.nat_add_neg_add_one
  have hz (n : ℕ) : c (-(n+1:ℤ))=0 := hn (fun _ => -(n+1:ℤ)) (by omega)
  have hterm (n : ℕ) : conj (c (n:ℤ))*((n:ℂ)*c (n:ℤ))+
      conj (c (-(n+1:ℤ)))*((-(n+1:ℤ):ℂ)*c (-(n+1:ℤ)))=((n:ℝ)*(u n)^2:ℝ) := by
    rw [hz,map_zero,zero_mul,add_zero]
    have hc : c (n:ℤ)=(u n:ℂ) := (hu n).symm
    rw [hc,Complex.conj_ofReal]
    push_cast
    ring
  have hN' : HasSum (fun n : ℕ => (((n:ℝ)*(u n)^2:ℝ):ℂ))
      (∫ x,conj (f x)*D x ∂torusMeasure 1) := by
    apply HasSum.congr_fun hN
    intro n
    simpa only [Int.cast_natCast,Int.cast_neg] using (hterm n).symm
  have hi : Integrable (fun x => conj (f x)*D x) (torusMeasure 1) :=
    ((continuous_star.comp f.continuous).mul D.continuous).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hr := (Complex.reCLM.hasSum hN').tsum_eq
  simp only [Complex.reCLM_apply,Complex.ofReal_re] at hr
  have hir := integral_re hi
  change (∫ x,(conj (f x)*D x).re ∂torusMeasure 1)=(∫ x,conj (f x)*D x ∂torusMeasure 1).re at hir
  exact hir.trans hr.symm

#print axioms signed_pairing
end BecknerOnofri.HighDim.CircleFisher
