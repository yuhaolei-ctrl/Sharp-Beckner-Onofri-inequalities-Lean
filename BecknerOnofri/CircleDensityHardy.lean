module

public import BecknerOnofri.CircleDensityParseval
public import BecknerOnofri.CircleSmoothOuter
public import BecknerOnofri.CircleHardyEnergy

@[expose] public section

/-! Apply the Hardy shift estimate to actual density Fourier coefficients.
The remaining Fisher identity must identify the coefficient energy with the
integral of p Λ log p; that identity is not an assumption or conclusion here. -/
noncomputable section
open MeasureTheory
namespace BecknerOnofri.HighDim.CircleOuter

theorem smooth_density_hardy_bound (p : Torus 1 → ℝ)
    (hp : Continuous p) (hpos : ∀ x,0<p x) (he : ∀ x,p (-x)=p x)
    (hm : (∫ x,p x ∂torusMeasure 1)=1)
    (hsmooth : ContDiff ℝ 3 (fun x : ℝ => p (fun _ => (x:UnitAddCircle)))) :
    let r : ℕ → ℝ := fun n =>
      (UnitAddTorus.mFourierCoeff (fun x => (p x:ℂ)) (fun _ => (n:ℤ))).re
    ∃ u : CircleHardy.Space, ‖u‖=1 ∧
      Summable (fun n : ℕ => (n:ℝ)*(u n)^2) ∧
      (∀ n : ℕ,CircleHardy.moment u n=r n) ∧
      (r 1)^2<1 ∧
      2/(1-(r 1)^2)*(∑' n : ℕ,(r (n+2)-r 1*r (n+1))^2) ≤
        2*(∑' m : ℕ,(m:ℝ)*(u m)^2)-((∫ x,(p x)^2 ∂torusMeasure 1)-1) := by
  dsimp only
  obtain ⟨f,u,hfp,hu,hE,hfs,huc,hfn,hac⟩ :=
    smooth_probability_outer_representation p hp hpos he hm hsmooth
  have ht := CircleHardy.first_moment_sq_lt_one u hu
  have hb := CircleHardy.fisher_lower_bound u hu hE
  simp_rw [hac] at ht hb
  have hP := (density_parseval p hp he hm).2
  refine ⟨u,hu,hE,hac,ht,?_⟩
  simp only [Nat.cast_add,Nat.cast_one,Nat.cast_ofNat] at hb ⊢
  rw [hP]
  nlinarith [hb]

#print axioms smooth_density_hardy_bound
end BecknerOnofri.HighDim.CircleOuter
