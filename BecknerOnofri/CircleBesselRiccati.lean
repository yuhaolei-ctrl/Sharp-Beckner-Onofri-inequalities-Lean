module

public import BecknerOnofri.CircleBesselSeries

@[expose] public section

/-! The source's Bessel recurrence and Riccati equation, proved from the
actual convergent factorial series rather than assumed special-function rules. -/
noncomputable section
namespace BecknerOnofri.HighDim.CircleScalar

theorem bessel_recurrence_term (h : ℝ) (j : ℕ) :
    h*besselOrderTerm h 0 (j+1)=h*besselOrderTerm h 2 j+besselOrderTerm h 1 (j+1) := by
  have he : j+1+1=j+2 := by omega
  simp only [besselOrderTerm,Nat.add_zero,he]
  rw [show j+2=(j+1)+1 by omega]
  simp only [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one,pow_add,pow_one]
  field_simp
  <;> ring

theorem bessel_recurrence (h : ℝ) : h*bessel 0 h=h*bessel 2 h+bessel 1 h := by
  have h0 := (besselOrderTerm_summable h 0).sum_add_tsum_nat_add 1
  have h1 := (besselOrderTerm_summable h 1).sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one] at h0 h1
  have hz : besselOrderTerm h 0 0=1 := by norm_num [besselOrderTerm]
  have ho : besselOrderTerm h 1 0=h := by norm_num [besselOrderTerm]
  rw [hz] at h0
  rw [ho] at h1
  have he : h*(∑' j : ℕ,besselOrderTerm h 0 (j+1))=
      h*(∑' j : ℕ,besselOrderTerm h 2 j)+(∑' j : ℕ,besselOrderTerm h 1 (j+1)) := by
    rw [← tsum_mul_left,← tsum_mul_left,← Summable.tsum_add
      ((besselOrderTerm_summable h 2).mul_left h)
      ((summable_nat_add_iff 1).mpr (besselOrderTerm_summable h 1))]
    exact tsum_congr (bessel_recurrence_term h)
  simp only [bessel_series_eq]
  rw [← h0,← h1,mul_add,mul_one,he]
  ring

theorem besselMoment_recurrence (h : ℝ) : h*(1-besselMoment 2 h)=besselMoment 1 h := by
  have hp : bessel 0 h≠0 := by rw [bessel_zero_eq]; exact (besselI0Two_pos h).ne'
  have he := bessel_recurrence h
  unfold besselMoment
  field_simp [hp]
  linarith

theorem besselMoment_first_riccati (h : ℝ) (hh : h≠0) :
    deriv (besselMoment 1) h+besselMoment 1 h/h+2*(besselMoment 1 h)^2=2 := by
  have hd := (besselMoment_derivative 1 (by decide) h).deriv
  have hz : besselMoment 0 h=1 := by
    rw [besselMoment_eq]
    exact GibbsTrialLower.besselRatio_zero h
  norm_num only [Nat.sub_self,Nat.reduceAdd] at hd
  rw [hz] at hd
  have he := besselMoment_recurrence h
  rw [hd]
  field_simp [hh]
  nlinarith

#print axioms bessel_recurrence
#print axioms besselMoment_first_riccati
end BecknerOnofri.HighDim.CircleScalar
