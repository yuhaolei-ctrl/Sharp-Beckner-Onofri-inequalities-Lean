module

public import BecknerOnofri.CircleBesselEnclosure
public import BecknerOnofri.EntropyExpCertificate

@[expose] public section

/-! Directed fixed-precision evaluation of the positive Bessel series. The
state encloses both the next term and the partial sum; the analytic geometric
tail is then added. This supplies the inverse-mean and gamma certificates. -/
namespace BecknerOnofri.HighDim.ScalarCertificate
open scoped BigOperators
open CircleScalar EntropyTail.ExpCertificate

structure BesselState where
  termLower : ℚ
  termUpper : ℚ
  sumLower : ℚ
  sumUpper : ℚ

def besselInitial (P : ℕ) (h : ℚ) (n : ℕ) : BesselState :=
  ⟨roundDown P (h^n/n.factorial), roundUp P (h^n/n.factorial),0,0⟩

def besselStep (P : ℕ) (h : ℚ) (n j : ℕ) (c : BesselState) : BesselState :=
  let q := h^2/((j+1 : ℚ)*(j+n+1 : ℚ))
  ⟨roundDown P (q*c.termLower),roundUp P (q*c.termUpper),
   c.sumLower+c.termLower,c.sumUpper+c.termUpper⟩

def besselRounded (P : ℕ) (h : ℚ) (n : ℕ) : ℕ → BesselState
  | 0 => besselInitial P h n
  | j+1 => besselStep P h n j (besselRounded P h n j)

def BesselState.Sound (c : BesselState) (h : ℝ) (n j : ℕ) : Prop :=
  (c.termLower : ℝ)≤besselTerm n h j ∧ besselTerm n h j≤(c.termUpper : ℝ) ∧
  (c.sumLower : ℝ)≤besselPartial n j h ∧ besselPartial n j h≤(c.sumUpper : ℝ)

theorem besselTerm_succ_eq (n j : ℕ) (h : ℝ) :
    besselTerm n h (j+1)=(h^2/((j+1 : ℝ)*(j+n+1 : ℝ)))*besselTerm n h j := by
  have hs := besselTerm_step n j h
  push_cast at hs
  have hd : (j+1 : ℝ)*(j+n+1 : ℝ)≠0 := by positivity
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff hd).mpr
  convert hs using 1 <;> ring

theorem besselInitial_sound (P : ℕ) (hP : 0<P) (h : ℚ) (n : ℕ) :
    (besselInitial P h n).Sound (h : ℝ) n 0 := by
  have hl := (Rat.cast_le (K := ℝ)).mpr (roundDown_le P hP (h^n/n.factorial))
  have hu := (Rat.cast_le (K := ℝ)).mpr (le_roundUp P hP (h^n/n.factorial))
  simp only [Rat.cast_div,Rat.cast_pow,Rat.cast_natCast] at hl hu
  simpa [BesselState.Sound,besselInitial,besselTerm,besselPartial] using
    (show ((roundDown P (h^n/n.factorial) : ℚ) : ℝ)≤(h : ℝ)^n/n.factorial ∧
      (h : ℝ)^n/n.factorial≤((roundUp P (h^n/n.factorial) : ℚ) : ℝ) ∧
      (0 : ℝ)≤0 ∧ (0 : ℝ)≤0 from ⟨hl,hu,le_rfl,le_rfl⟩)

theorem besselStep_sound (P : ℕ) (hP : 0<P) (h : ℚ) (n j : ℕ) (c : BesselState)
    (hc : c.Sound (h : ℝ) n j) : (besselStep P h n j c).Sound (h : ℝ) n (j+1) := by
  let q : ℚ := h^2/((j+1 : ℚ)*(j+n+1 : ℚ))
  have hq : (0 : ℝ)≤(q : ℝ) := by dsimp [q]; positivity
  have hl := (Rat.cast_le (K := ℝ)).mpr (roundDown_le P hP (q*c.termLower))
  have hu := (Rat.cast_le (K := ℝ)).mpr (le_roundUp P hP (q*c.termUpper))
  simp only [Rat.cast_mul] at hl hu
  have ht : besselTerm n (h : ℝ) (j+1)=(q : ℝ)*besselTerm n (h : ℝ) j := by
    rw [besselTerm_succ_eq]
    simp [q]
  have hs : besselPartial n (j+1) (h : ℝ)=besselPartial n j (h : ℝ)+besselTerm n (h : ℝ) j := by
    exact Finset.sum_range_succ (besselTerm n (h : ℝ)) j
  refine ⟨?_,?_,?_,?_⟩
  · rw [ht]
    exact hl.trans (mul_le_mul_of_nonneg_left hc.1 hq)
  · rw [ht]
    exact (mul_le_mul_of_nonneg_left hc.2.1 hq).trans hu
  · rw [hs]
    change ((c.sumLower+c.termLower : ℚ) : ℝ)≤_
    rw [Rat.cast_add]
    exact add_le_add hc.2.2.1 hc.1
  · rw [hs]
    change _≤((c.sumUpper+c.termUpper : ℚ) : ℝ)
    rw [Rat.cast_add]
    exact add_le_add hc.2.2.2 hc.2.1

theorem besselRounded_sound (P : ℕ) (hP : 0<P) (h : ℚ) (n N : ℕ) :
    (besselRounded P h n N).Sound (h : ℝ) n N := by
  induction N with
  | zero => exact besselInitial_sound P hP h n
  | succ N ih => exact besselStep_sound P hP h n N _ ih

theorem besselRounded_enclosure (P : ℕ) (hP : 0<P) (h : ℚ) (n N : ℕ)
    (hh : 0≤h) (hbound : h^2≤(1/2 : ℚ)*(N+1)^2) :
    ((besselRounded P h n N).sumLower : ℝ)≤bessel n (h : ℝ) ∧
      bessel n (h : ℝ)≤((besselRounded P h n N).sumUpper+2*(besselRounded P h n N).termUpper : ℚ) := by
  have hs := besselRounded_sound P hP h n N
  have hn : (0 : ℝ)≤n := Nat.cast_nonneg n
  have hb : (h : ℝ)^2≤(1/2 : ℝ)*(N+1)*(N+n+1) := by
    have hb' := (Rat.cast_le (K := ℝ)).mpr hbound
    push_cast at hb'
    nlinarith [mul_nonneg (show (0 : ℝ)≤N+1 by positivity) hn]
  have he := bessel_finite_enclosure n N (h : ℝ) (1/2) (by exact_mod_cast hh)
    (by norm_num) (by norm_num) hb
  constructor
  · exact hs.2.2.1.trans he.1
  · push_cast
    norm_num at he
    linarith [hs.2.1,hs.2.2.2,he.2]

#print axioms besselRounded_enclosure
end BecknerOnofri.HighDim.ScalarCertificate
