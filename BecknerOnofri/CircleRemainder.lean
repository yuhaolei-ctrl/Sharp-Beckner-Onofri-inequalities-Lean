import BecknerOnofri.CircleDeficitIntegral
import BecknerOnofri.CircleRemainderSeries

/-! The quantitative circle entropy remainder, obtained by integrating the
actual Poisson dissipation. Finite nonnegative sums followed by their monotone
limit justify the infinite remainder without assuming its summability. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open MeasureTheory Set Filter
namespace BecknerOnofri.HighDim.CirclePoisson
open CircleOuter

theorem remainder_finite_dissipation (p : Torus 1 → ℝ) (hp : Continuous p)
    (hpos : ∀ x,0<p x) (he : ∀ x,p (-x)=p x) (hm : (∫ x,p x ∂torusMeasure 1)=1)
    (hsmooth : ContDiff ℝ 3 (fun x : ℝ => p (fun _ => (x:UnitAddCircle))))
    (s : ℝ) (hs : 0<s) (S : Finset ℕ) :
    (∑ n ∈ S,remainderKernel (n+1) (moment p 1) s*(moment p (n+2)-moment p 1*moment p (n+1))^2)≤
      -deriv (deficit p) s := by
  let r := moment p
  let R : ℕ → ℝ := fun n => Real.exp (-(n:ℝ)*s)*r n
  have hc (n : ℕ) : moment (torusFlow s p) n=R n := torus_flow_real_coefficient s hs p hp n
  have hr : Summable (fun n : ℕ => (R (n+1))^2) := by
    have h := (density_parseval _ (torus_flow_continuous s hs p hp)
      (torus_flow_even p he s) ((torus_flow_mass s hs p hp).trans hm)).1
    have h' : Summable (fun n : ℕ => (moment (torusFlow s p) (n+1))^2) := by
      simpa only [moment,Nat.cast_add,Nat.cast_one] using h
    simpa only [hc] using h'
  have hsum := adjacent_square_summable R hr
  have hd := smooth_deficit_dissipation p hp hpos he hm hsmooth s hs
  have hR : (R 1)^2<1 := hd.2.1
  have hbound : 2/(1-(R 1)^2)*(∑' n : ℕ,(R (n+2)-R 1*R (n+1))^2)≤-deriv (deficit p) s := hd.2.2
  have hc0 : 0≤2/(1-(R 1)^2) := div_nonneg (by norm_num) (sub_nonneg.mpr hR.le)
  have hterm (n : ℕ) : remainderKernel (n+1) (r 1) s*(r (n+2)-r 1*r (n+1))^2=
      2/(1-(R 1)^2)*(R (n+2)-R 1*R (n+1))^2 := by
    simpa only [R,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,neg_one_mul] using remainder_kernel_scaled r n s
  calc
    _ = 2/(1-(R 1)^2)*∑ n ∈ S,(R (n+2)-R 1*R (n+1))^2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun n _ => hterm n)
    _ ≤ 2/(1-(R 1)^2)*∑' n : ℕ,(R (n+2)-R 1*R (n+1))^2 :=
      mul_le_mul_of_nonneg_left (hsum.sum_le_tsum S (fun n _ => sq_nonneg _)) hc0
    _ ≤ _ := hbound

theorem smooth_circle_remainder (p : Torus 1 → ℝ) (hp : Continuous p)
    (hpos : ∀ x,0<p x) (he : ∀ x,p (-x)=p x) (hm : (∫ x,p x ∂torusMeasure 1)=1)
    (hsmooth : ContDiff ℝ 3 (fun x : ℝ => p (fun _ => (x:UnitAddCircle)))) :
    Summable (fun n : ℕ => CircleScalar.weight (n+1) (moment p 1)*
      (moment p (n+2)-moment p 1*moment p (n+1))^2) ∧
    (∑' n : ℕ,CircleScalar.weight (n+1) (moment p 1)*
      (moment p (n+2)-moment p 1*moment p (n+1))^2) ≤
      (∫ x,p x*Real.log (p x) ∂torusMeasure 1)-∑' n : ℕ,(moment p (n+1))^2/(n+1:ℝ) := by
  have ht2 : (moment p 1)^2<1 := (CircleFisher.smooth_fisher_lower_bound p hp hpos he hm hsmooth).1
  obtain ⟨hDI,hDval⟩ := smooth_deficit_integral p hp hpos he hm hsmooth
  let F : ℕ → ℝ → ℝ := fun n s => remainderKernel (n+1) (moment p 1) s*
    (moment p (n+2)-moment p 1*moment p (n+1))^2
  let A : ℕ → ℝ := fun n => CircleScalar.weight (n+1) (moment p 1)*
    (moment p (n+2)-moment p 1*moment p (n+1))^2
  have hi (n : ℕ) : IntegrableOn (F n) (Ioi (0:ℝ)) :=
    (remainder_kernel_integrable (n+1) (moment p 1) ht2).mul_const _
  have hI (n : ℕ) : (∫ s in Ioi (0:ℝ),F n s)=A n := by
    dsimp only [F,A]
    rw [integral_mul_const,remainder_kernel_integral_of_sq_lt (n+1) _ ht2]
  have hfinite (S : Finset ℕ) : ∑ n ∈ S,A n≤deficit p 0 := by
    have hmono : (∫ s in Ioi (0:ℝ),∑ n ∈ S,F n s)≤
        ∫ s in Ioi (0:ℝ),-deriv (deficit p) s := by
      apply integral_mono_ae (integrable_finsetSum S (fun n _ => hi n)) hDI
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      exact remainder_finite_dissipation p hp hpos he hm hsmooth s hs S
    rw [integral_finsetSum S (fun n _ => hi n)] at hmono
    simp only [hI,hDval] at hmono
    exact hmono
  have hA : 0≤A := by
    intro n
    dsimp [A]
    apply mul_nonneg _ (sq_nonneg _)
    rw [← remainder_kernel_integral_of_sq_lt (n+1) _ ht2]
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact remainder_kernel_nonneg (n+1) _ s ht2 hs.le
  refine ⟨summable_of_sum_le hA hfinite,?_⟩
  have h := Real.tsum_le_of_sum_le hA hfinite
  simpa only [A,deficit,torusFlow,ite_true,mul_zero,Real.exp_zero,one_mul] using h

#print axioms smooth_circle_remainder
end BecknerOnofri.HighDim.CirclePoisson
