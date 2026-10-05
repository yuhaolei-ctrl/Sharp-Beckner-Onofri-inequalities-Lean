import BecknerOnofri.CirclePoissonEntropyFisher
import BecknerOnofri.CirclePoissonEnergyDerivative

/-! Differential form of the actual circle entropy remainder along the Poisson
flow, with actual density moments and without an assumed dissipation estimate. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open MeasureTheory
namespace BecknerOnofri.HighDim.CirclePoisson
open CircleOuter CircleFisher

theorem torus_flow_real_coefficient (s : ℝ) (hs : 0<s) (p : Torus 1 → ℝ)
    (hp : Continuous p) (n : ℕ) :
    (UnitAddTorus.mFourierCoeff (fun x => (torusFlow s p x:ℂ)) (fun _ => (n:ℤ))).re=
      Real.exp (-(n:ℝ)*s)*(UnitAddTorus.mFourierCoeff (fun x => (p x:ℂ)) (fun _ => (n:ℤ))).re := by
  rw [torus_flow_coefficient s hs p hp]
  simp only [Int.cast_natCast,abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) n),
    Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]

theorem smooth_deficit_dissipation (p : Torus 1 → ℝ) (hp : Continuous p)
    (hpos : ∀ x,0<p x) (he : ∀ x,p (-x)=p x) (hm : (∫ x,p x ∂torusMeasure 1)=1)
    (hsmooth : ContDiff ℝ 3 (fun x : ℝ => p (fun _ => (x:UnitAddCircle))))
    (s : ℝ) (hs : 0<s) :
    let r : ℕ → ℝ := fun n =>
      (UnitAddTorus.mFourierCoeff (fun x => (p x:ℂ)) (fun _ => (n:ℤ))).re
    let R : ℕ → ℝ := fun n => Real.exp (-(n:ℝ)*s)*r n
    let D : ℝ → ℝ := fun t =>
      (∫ x,torusFlow t p x*Real.log (torusFlow t p x) ∂torusMeasure 1)-
        ∑' n : ℕ,Real.exp (-2*(n+1:ℝ)*t)*(r (n+1))^2/(n+1:ℝ)
    HasDerivAt D
      (-(∫ x,torusFlow s p x*lambda (fun y => Real.log (torusFlow s p y)) x ∂torusMeasure 1)+
        ((∫ x,(torusFlow s p x)^2 ∂torusMeasure 1)-1)) s ∧
    (R 1)^2<1 ∧
      2/(1-(R 1)^2)*(∑' n : ℕ,(R (n+2)-R 1*R (n+1))^2) ≤ -deriv D s := by
  dsimp only
  let r : ℕ → ℝ := fun n =>
    (UnitAddTorus.mFourierCoeff (fun x => (p x:ℂ)) (fun _ => (n:ℤ))).re
  have hw := CircleRegularity.torus_weighted_summable (fun x => (p x:ℂ)) (Complex.ofRealCLM.contDiff.comp hsmooth)
  have hr : Summable (fun n : ℕ => (r (n+1))^2) := by
    simpa only [r,Nat.cast_add,Nat.cast_one] using (density_parseval p hp he hm).1
  have hd := (entropy_fisher_hasDerivAt p hp hpos hw s hs).sub (fourier_energy_hasDerivAt r hr s hs)
  have hP := (density_parseval _ (torus_flow_continuous s hs p hp)
    (torus_flow_even p he s) ((torus_flow_mass s hs p hp).trans hm)).2
  have hsq (n : ℕ) : (Real.exp (-(n+1:ℝ)*s))^2=Real.exp (-2*(n+1:ℝ)*s) := by
    rw [pow_two,← Real.exp_add]
    congr 1
    ring
  have hnorm : (∫ x,(torusFlow s p x)^2 ∂torusMeasure 1)-1=
      2*∑' n : ℕ,Real.exp (-2*(n+1:ℝ)*s)*(r (n+1))^2 := by
    rw [hP]
    congr 1
    apply tsum_congr
    intro n
    rw [show (n+1:ℤ)=((n+1:ℕ):ℤ) by norm_cast,torus_flow_real_coefficient s hs p hp,mul_pow]
    simpa only [Nat.cast_add,Nat.cast_one,hsq,r]
  have hdeq : -(∫ x,torusFlow s p x*lambda (fun y => Real.log (torusFlow s p y)) x ∂torusMeasure 1)-
      (-2*∑' n : ℕ,Real.exp (-2*(n+1:ℝ)*s)*(r (n+1))^2)=
      -(∫ x,torusFlow s p x*lambda (fun y => Real.log (torusFlow s p y)) x ∂torusMeasure 1)+
        ((∫ x,(torusFlow s p x)^2 ∂torusMeasure 1)-1) := by rw [hnorm]; ring
  rw [hdeq] at hd
  refine ⟨hd,?_⟩
  have hb := flow_fisher_lower_bound p hp hpos he hm hw s hs
  dsimp only at hb
  simp_rw [torus_flow_real_coefficient s hs p hp] at hb
  refine ⟨hb.1,?_⟩
  have hdd := hd.deriv
  change deriv (fun t => (∫ x,torusFlow t p x*Real.log (torusFlow t p x) ∂torusMeasure 1)-
    ∑' n : ℕ,Real.exp (-2*(n+1:ℝ)*t)*(r (n+1))^2/(n+1:ℝ)) s=_ at hdd
  dsimp only [r] at hdd
  rw [hdd]
  linarith [hb.2]

#print axioms smooth_deficit_dissipation
end BecknerOnofri.HighDim.CirclePoisson
