module

public import BecknerOnofri.CircleRemainder
public import BecknerOnofri.CircleGammaEntropyReduction
public import BecknerOnofri.CircleComparisonOn
public import BecknerOnofri.CircleMomentTransport

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open MeasureTheory Set
namespace BecknerOnofri.HighDim.CirclePoisson
open CircleScalar CircleOuter

theorem energy_series_summable (r : ℕ → ℝ)
    (hr : Summable (fun n : ℕ => (r (n+1))^2)) :
    Summable (fun n : ℕ => (r (n+1))^2/(n+1:ℝ)) := by
  apply Summable.of_nonneg_of_le (fun n => by positivity) _ hr
  intro n
  exact div_le_self (sq_nonneg _) (by linarith [Nat.cast_nonneg (α:=ℝ) n])

theorem energy_series_split (r : ℕ → ℝ)
    (hr : Summable (fun n : ℕ => (r (n+1))^2)) :
    (∑' n : ℕ,(r (n+1))^2/(n+1:ℝ))=(r 1)^2+(r 2)^2/2+
      ∑' n : ℕ,(r (n+3))^2/(n+3:ℝ) := by
  have h := (energy_series_summable r hr).sum_add_tsum_nat_add 2
  norm_num [Finset.sum_range_succ,Nat.cast_add,add_assoc] at h
  simpa only [add_assoc] using h.symm

theorem gamma_of_comparisons (p : Torus 1 → ℝ) (hp : Continuous p)
    (hpos : ∀ x,0<p x) (he : ∀ x,p (-x)=p x) (hm : (∫ x,p x ∂torusMeasure 1)=1)
    (hsmooth : ContDiff ℝ 3 (fun x : ℝ => p (fun _ => (x:UnitAddCircle))))
    (ht : 0≤moment p 1)
    (hI : rate (moment p 1)≤∫ x,p x*Real.log (p x) ∂torusMeasure 1)
    (ha : besselMoment 2 (parameter (moment p 1))≤moment p 2)
    (hb : |moment p 3-besselMoment 3 (parameter (moment p 1))|≤
      6*(moment p 2-besselMoment 2 (parameter (moment p 1)))) :
    2*Spin.binaryCost (moment p 1)+gamma (moment p 1)+(21/1000)*(moment p 2)^2+
      (27/40)*(∑' n : ℕ,(moment p (n+3))^2/(n+3:ℝ)) ≤
        ∫ x,p x*Real.log (p x) ∂torusMeasure 1 := by
  have hsq : (moment p 1)^2<1 := (CircleFisher.smooth_fisher_lower_bound p hp hpos he hm hsmooth).1
  have ht1 : moment p 1<1 := by nlinarith
  obtain ⟨hS,hRem⟩ := smooth_circle_remainder p hp hpos he hm hsmooth
  let A : ℕ → ℝ := fun n => weight (n+1) (moment p 1)*
    (moment p (n+2)-moment p 1*moment p (n+1))^2
  have hnonneg (n : ℕ) : 0≤A n := by
    apply mul_nonneg _ (sq_nonneg _)
    unfold weight
    exact tsum_nonneg (fun j => by positivity)
  have hfirst := hS.sum_le_tsum ({0,1}:Finset ℕ) (fun n _ => hnonneg n)
  have hfirst' : weight 1 (moment p 1)*(moment p 2-(moment p 1)^2)^2+
      weight 2 (moment p 1)*(moment p 3-moment p 1*moment p 2)^2≤∑' n,A n := by
    simpa [A,pow_two] using hfirst

  have hr : Summable (fun n : ℕ => (moment p (n+1))^2) := by
    simpa only [moment,Nat.cast_add,Nat.cast_one] using (density_parseval p hp he hm).1
  have hsplit := energy_series_split (moment p) hr
  apply gamma_entropy_reduction (moment p 1) (moment p 2) (moment p 3)
    (∫ x,p x*Real.log (p x) ∂torusMeasure 1)
    (∑' n : ℕ,(moment p (n+3))^2/(n+3:ℝ)) ht ht1 hI _ ha hb
  change _≤(∫ x,p x*Real.log (p x) ∂torusMeasure 1)-(∑' n : ℕ,(moment p (n+1))^2/(n+1:ℝ)) at hRem
  rw [hsplit] at hRem
  linarith

#print axioms gamma_of_comparisons
end BecknerOnofri.HighDim.CirclePoisson
