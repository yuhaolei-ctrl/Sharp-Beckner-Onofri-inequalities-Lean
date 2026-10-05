module

public import BecknerOnofri.CircleFisherDensity
public import BecknerOnofri.CircleDensityParseval
public import BecknerOnofri.CircleHardyEnergy

@[expose] public section

/-! The manuscript's genuine Fisher dissipation lower bound for a smooth
positive even circle density. Both integrals and all moments are the actual
Haar/Fourier quantities. -/
noncomputable section
open MeasureTheory
namespace BecknerOnofri.HighDim.CircleFisher
open CircleOuter

theorem smooth_fisher_lower_bound (p : Torus 1 → ℝ)
    (hp : Continuous p) (hpos : ∀ x,0<p x) (he : ∀ x,p (-x)=p x)
    (hm : (∫ x,p x ∂torusMeasure 1)=1)
    (hsmooth : ContDiff ℝ 3 (fun x : ℝ => p (fun _ => (x:UnitAddCircle)))) :
    let r : ℕ → ℝ := fun n =>
      (UnitAddTorus.mFourierCoeff (fun x => (p x:ℂ)) (fun _ => (n:ℤ))).re
    (r 1)^2<1 ∧
      2/(1-(r 1)^2)*(∑' n : ℕ,(r (n+2)-r 1*r (n+1))^2) ≤
        (∫ x,p x*lambda (fun y => Real.log (p y)) x ∂torusMeasure 1)-
          ((∫ x,(p x)^2 ∂torusMeasure 1)-1) := by
  dsimp only
  obtain ⟨u,hu,hE,hac,hF⟩ := smooth_density_fisher_representation p hp hpos he hm hsmooth
  have ht := CircleHardy.first_moment_sq_lt_one u hu
  have hb := CircleHardy.fisher_lower_bound u hu hE
  simp_rw [hac] at ht hb
  have hP := (density_parseval p hp he hm).2
  refine ⟨ht,?_⟩
  simp only [Nat.cast_add,Nat.cast_one,Nat.cast_ofNat] at hb ⊢
  rw [hF,hP]
  nlinarith [hb]

#print axioms smooth_fisher_lower_bound
end BecknerOnofri.HighDim.CircleFisher
