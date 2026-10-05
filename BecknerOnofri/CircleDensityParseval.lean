module

public import BecknerOnofri.CircleOuterParseval

@[expose] public section

/-! Parseval for an actual even circle probability density, with its zero mode removed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped ComplexConjugate
namespace BecknerOnofri.HighDim.CircleOuter

theorem density_parseval (p : Torus 1 → ℝ) (hp : Continuous p)
    (he : ∀ x,p (-x)=p x) (hm : (∫ x,p x ∂torusMeasure 1)=1) :
    Summable (fun n : ℕ =>
      (UnitAddTorus.mFourierCoeff (fun x => (p x:ℂ)) (fun _ => (n+1:ℤ))).re^2) ∧
    (∫ x,(p x)^2 ∂torusMeasure 1)-1=
      2*∑' n : ℕ,(UnitAddTorus.mFourierCoeff (fun x => (p x:ℂ)) (fun _ => (n+1:ℤ))).re^2 := by
  let f : C(Torus 1,ℂ) := ⟨fun x => (p x:ℂ),Complex.continuous_ofReal.comp hp⟩
  let c : ℤ → ℂ := fun n => UnitAddTorus.mFourierCoeff f (fun _ => n)
  have hc (n : ℤ) : ((c n).re:ℂ)=c n := by
    apply Complex.conj_eq_iff_re.mp
    exact (real_coefficient_neg p (fun _ => n)).symm.trans (even_coefficient_neg p he (fun _ => n))
  have hsq (n : ℤ) : ‖c n‖^2=(c n).re^2 := by
    conv_lhs => rw [← hc n]
    rw [Complex.norm_real,Real.norm_eq_abs,sq_abs]
  have hfull := boundary_parseval f
  have hZ : HasSum (fun n : ℤ => (c n).re^2) (∫ x,(p x)^2 ∂torusMeasure 1) := by
    have h := ((Equiv.funUnique (Fin 1) ℤ).symm.hasSum_iff).mpr hfull
    change HasSum (fun n : ℤ => ‖c n‖^2) _ at h
    simpa only [hsq,f,ContinuousMap.coe_mk,Complex.normSq_ofReal,pow_two] using h
  have hN : Summable (fun n : ℕ => (c (n:ℤ)).re^2) :=
    hZ.summable.comp_injective (fun a b h => by exact_mod_cast h)
  have hS : Summable (fun n : ℕ => (c (n+1:ℤ)).re^2) := by
    simpa only [Nat.cast_add,Nat.cast_one] using (summable_nat_add_iff 1).mpr hN
  have hneg (n : ℕ) : c (-(n+1:ℤ))=c (n+1:ℤ) := by
    exact even_coefficient_neg p he (fun _ => (n+1:ℤ))
  have hz : c 0=1 := by
    change UnitAddTorus.mFourierCoeff (fun x => (p x:ℂ)) (0:Frequency 1)=1
    simp only [UnitAddTorus.mFourierCoeff,neg_zero,UnitAddTorus.mFourier_zero,
      ContinuousMap.one_apply,one_smul,integral_complex_ofReal]
    exact congrArg Complex.ofReal hm
  have h := tsum_nat_add_neg_add_one hZ.summable
  simp only [hneg,hZ.tsum_eq] at h
  rw [hN.tsum_add hS] at h
  have h0 := hN.tsum_eq_zero_add
  simp only [Nat.cast_zero,hz,Complex.one_re,one_pow,Nat.cast_add,Nat.cast_one] at h0
  refine ⟨hS,?_⟩
  change (∫ x,(p x)^2 ∂torusMeasure 1)-1=2*∑' n : ℕ,(c (n+1:ℤ)).re^2
  linarith

#print axioms density_parseval
end BecknerOnofri.HighDim.CircleOuter
