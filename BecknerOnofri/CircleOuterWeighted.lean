module

public import BecknerOnofri.CircleOuterMoments

@[expose] public section

/-! The first weighted Wiener moment supplies the finite coefficient energy
required by the Hardy dissipation bound. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped ComplexConjugate ENNReal
namespace BecknerOnofri.HighDim.CircleOuter
open Legacy.TorusEndpoint Legacy.BecknerOnofri.WeightedWiener

theorem linearWeight_isWeight : IsWeight linearWeight where
  one_le k := by unfold linearWeight; linarith [abs_nonneg (k (0:Fin 1):ℝ)]
  zero := by simp [linearWeight]
  submul k l := by
    have h := abs_add_le (k (0:Fin 1):ℝ) (l (0:Fin 1):ℝ)
    have hp := mul_nonneg (abs_nonneg (k (0:Fin 1):ℝ)) (abs_nonneg (l (0:Fin 1):ℝ))
    simp only [linearWeight,Pi.add_apply,Int.cast_add]
    nlinarith

theorem hardy_weighted_energy (f : C(Torus 1,ℂ)) (u : CircleHardy.Space) (hu : ‖u‖=1)
    (hc : ∀ n : ℕ,(u n:ℂ)=UnitAddTorus.mFourierCoeff f (fun _ => (n:ℤ)))
    (hw : Summable (fun k => linearWeight k*‖UnitAddTorus.mFourierCoeff f k‖)) :
    Summable (fun n : ℕ => (n:ℝ)*(u n)^2) := by
  have hinj : Function.Injective (fun n : ℕ => (fun _ : Fin 1 => (n:ℤ))) := by
    intro a b h
    have he := congrFun h (0:Fin 1)
    change (a:ℤ)=(b:ℤ) at he
    exact_mod_cast he
  have hs := hw.comp_injective hinj
  apply Summable.of_nonneg_of_le (fun n => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)) _ hs
  intro n
  change (n:ℝ)*(u n)^2≤linearWeight (fun _ => (n:ℤ))*‖UnitAddTorus.mFourierCoeff f (fun _ => (n:ℤ))‖
  rw [← hc,Complex.norm_real,Real.norm_eq_abs]
  have hnu : |u n|≤1 := by
    have h := lp.norm_apply_le_norm (by norm_num : (2:ℝ≥0∞)≠0) u n
    simpa only [Real.norm_eq_abs,hu] using h
  have hsq : (u n)^2≤|u n| := by nlinarith [sq_abs (u n),abs_nonneg (u n)]
  have hn : (0:ℝ)≤n := Nat.cast_nonneg _
  simp only [linearWeight,Int.cast_natCast,abs_of_nonneg hn]
  nlinarith [mul_le_mul_of_nonneg_left hsq hn,abs_nonneg (u n)]

#print axioms hardy_weighted_energy
end BecknerOnofri.HighDim.CircleOuter
