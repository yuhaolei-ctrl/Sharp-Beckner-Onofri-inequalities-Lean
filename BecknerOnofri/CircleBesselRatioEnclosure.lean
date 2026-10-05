import BecknerOnofri.CircleBesselEnclosure
import BecknerOnofri.CircleBesselInverse

/-! Certified ratios and inverse-mean brackets from actual convergent series. -/
noncomputable section
namespace BecknerOnofri.HighDim.CircleScalar

theorem besselPartial_zero_pos (N : ℕ) (h : ℝ) (hh : 0≤h) (hN : 1≤N) :
    0<besselPartial 0 N h := by
  have he : besselTerm 0 h 0=1 := by norm_num [besselTerm]
  have hb := Finset.single_le_sum (s:=Finset.range N) (f:=besselTerm 0 h)
    (fun i _ => by unfold besselTerm; positivity) (Finset.mem_range.mpr (by omega : 0<N))
  rw [he] at hb
  exact lt_of_lt_of_le (by norm_num : (0:ℝ)<1) hb

theorem besselMoment_finite_enclosure (n N : ℕ) (h q : ℝ) (hh : 0≤h)
    (hN : 1≤N) (hq : 0≤q) (hq1 : q<1) (hbound : h^2≤q*(N+1:ℝ)^2) :
    besselPartial n N h/(besselPartial 0 N h+besselTerm 0 h N/(1-q))≤besselMoment n h ∧
    besselMoment n h≤(besselPartial n N h+besselTerm n h N/(1-q))/besselPartial 0 N h := by
  have hn : 0≤(n:ℝ) := Nat.cast_nonneg _
  have hbase : h^2≤q*(N+1:ℝ)*(N+0+1:ℝ) := by nlinarith
  have hgen : h^2≤q*(N+1:ℝ)*(N+n+1:ℝ) := by
    nlinarith [mul_nonneg (mul_nonneg hq (by positivity : 0≤(N+1:ℝ))) hn]
  obtain ⟨h0l,h0u⟩ := bessel_finite_enclosure 0 N h q hh hq hq1 (by simpa using hbase)
  obtain ⟨hnl,hnu⟩ := bessel_finite_enclosure n N h q hh hq hq1 hgen
  have hp := besselPartial_zero_pos N h hh hN
  have hb0 := hp.trans_le h0l
  have hu0 := hb0.trans_le h0u
  have hpn : 0≤besselPartial n N h := by
    unfold besselPartial
    exact Finset.sum_nonneg (fun j _ => by unfold besselTerm; positivity)
  have hbn := hpn.trans hnl
  unfold besselMoment
  constructor
  · calc
      _ ≤bessel n h/(besselPartial 0 N h+besselTerm 0 h N/(1-q)) :=
        div_le_div_of_nonneg_right hnl hu0.le
      _ ≤bessel n h/bessel 0 h := div_le_div_of_nonneg_left hbn hb0 h0u
  · calc
      _ ≤bessel n h/besselPartial 0 N h := div_le_div_of_nonneg_left hbn hp h0l
      _ ≤_ := div_le_div_of_nonneg_right hnu hp.le

theorem parameter_bracket (t l u : ℝ) (ht : 0≤t) (ht1 : t<1)
    (hl : besselMoment 1 l≤t) (hu : t≤besselMoment 1 u) :
    l≤parameter t ∧ parameter t≤u := by
  have he := (parameter_mean ht ht1).1
  constructor
  · apply besselMoment_first_strictMono.le_iff_le.mp
    rwa [he]
  · apply besselMoment_first_strictMono.le_iff_le.mp
    rwa [he]

#print axioms besselMoment_finite_enclosure
#print axioms parameter_bracket
end BecknerOnofri.HighDim.CircleScalar
