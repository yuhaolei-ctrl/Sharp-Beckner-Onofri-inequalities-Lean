module

public import BecknerOnofri.CircleBesselEnclosureDefinitions
public import BecknerOnofri.CircleBesselSeries

@[expose] public section

/-! Sound factorial-series enclosures, at any nonnegative real parameter.
All omitted terms are bounded analytically by a convergent geometric series. -/
noncomputable section
open scoped BigOperators
namespace BecknerOnofri.HighDim.CircleScalar

theorem besselTerm_eq (n j : ℕ) (h : ℝ) : besselTerm n h j=besselOrderTerm h n j := by
  unfold besselTerm besselOrderTerm
  rw [show 2*j+n=(j+n)+j by omega,pow_add]
  congr 1
  ring

theorem besselTerm_summable (n : ℕ) (h : ℝ) : Summable (besselTerm n h) := by
  have he : besselTerm n h=besselOrderTerm h n := funext (fun j => besselTerm_eq n j h)
  rw [he]
  exact besselOrderTerm_summable h n

theorem besselTerm_step (n j : ℕ) (h : ℝ) :
    besselTerm n h (j+1)*((j+1:ℕ):ℝ)*((j+n+1:ℕ):ℝ)=h^2*besselTerm n h j := by
  unfold besselTerm
  rw [show j+1+n=(j+n)+1 by omega,show 2*(j+1)+n=(2*j+n)+2 by omega]
  simp only [Nat.factorial_succ,Nat.cast_mul,pow_add]
  field_simp
  <;> ring

theorem besselTerm_step_le (n N j : ℕ) (h q : ℝ) (hh : 0≤h) (hq : 0≤q)
    (hjq : N≤j) (hbound : h^2≤q*(N+1:ℝ)*(N+n+1:ℝ)) :
    besselTerm n h (j+1)≤q*besselTerm n h j := by
  have hterm : 0≤besselTerm n h j := by unfold besselTerm; positivity
  have hN : (N:ℝ)≤j := by exact_mod_cast hjq
  have hn : 0≤(n:ℝ) := Nat.cast_nonneg _
  have hden : (N+1:ℝ)*(N+n+1:ℝ)≤(j+1:ℝ)*(j+n+1:ℝ) := by
    apply mul_le_mul <;> linarith
  have hb : h^2≤q*((j+1:ℝ)*(j+n+1:ℝ)) := by
    nlinarith [mul_le_mul_of_nonneg_left hden hq]
  have hs := besselTerm_step n j h
  push_cast at hs
  apply le_of_mul_le_mul_right _ (by positivity : 0<(j+1:ℝ)*(j+n+1:ℝ))
  calc
    besselTerm n h (j+1)*((j+1:ℝ)*(j+n+1:ℝ))=h^2*besselTerm n h j := by nlinarith [hs]
    _ ≤(q*((j+1:ℝ)*(j+n+1:ℝ)))*besselTerm n h j := mul_le_mul_of_nonneg_right hb hterm
    _ =_ := by ring

theorem bessel_finite_enclosure (n N : ℕ) (h q : ℝ) (hh : 0≤h) (hq : 0≤q)
    (hq1 : q<1) (hbound : h^2≤q*(N+1:ℝ)*(N+n+1:ℝ)) :
    besselPartial n N h≤bessel n h ∧
      bessel n h≤besselPartial n N h+besselTerm n h N/(1-q) := by
  have hb (j : ℕ) : besselTerm n h (j+N)≤besselTerm n h N*q^j := by
    induction j with
    | zero => simp
    | succ j ih =>
      have hs := besselTerm_step_le n N (j+N) h q hh hq (by omega) hbound
      calc
        besselTerm n h (j+1+N)≤q*besselTerm n h (j+N) := by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hs
        _ ≤q*(besselTerm n h N*q^j) := mul_le_mul_of_nonneg_left ih hq
        _ =_ := by rw [pow_succ]; ring
  have hs := besselTerm_summable n h
  have hshift := (summable_nat_add_iff N).mpr hs
  have hgeom := (summable_geometric_of_lt_one hq hq1).mul_left (besselTerm n h N)
  have htail := Summable.tsum_le_tsum hb hshift hgeom
  rw [tsum_mul_left,tsum_geometric_of_lt_one hq hq1] at htail
  have hsplit := hs.sum_add_tsum_nat_add N
  change besselPartial n N h+(∑' j : ℕ,besselTerm n h (j+N))=bessel n h at hsplit
  have hnon : 0≤∑' j : ℕ,besselTerm n h (j+N) := by
    apply tsum_nonneg
    intro j
    unfold besselTerm
    positivity
  simp only [div_eq_mul_inv]
  constructor <;> linarith

#print axioms bessel_finite_enclosure
end BecknerOnofri.HighDim.CircleScalar
