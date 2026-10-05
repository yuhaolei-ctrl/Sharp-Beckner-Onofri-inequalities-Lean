import BecknerOnofri.CircleWeightDefinitions
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

/-! Positive-series bounds for the circle remainder weights. The remainder
is controlled analytically for every truncation order, not by a sampled sum. -/
noncomputable section
open scoped BigOperators
namespace BecknerOnofri.HighDim.CircleScalar

theorem weight_summable (n : ℕ) {t : ℝ} (ht : 0≤t) (ht1 : t<1) :
    Summable (fun j : ℕ => t^(2*j)/(n+j+1:ℝ)) := by
  have ht2 : t^2<1 := by nlinarith
  apply Summable.of_nonneg_of_le (fun j => by positivity) (fun j => ?_)
    (summable_geometric_of_lt_one (sq_nonneg t) ht2)
  rw [pow_mul]
  exact div_le_self (pow_nonneg (sq_nonneg t) j) (by
    have hn := Nat.cast_nonneg (α:=ℝ) n
    have hj := Nat.cast_nonneg (α:=ℝ) j
    linarith)

theorem weight_initial_lower (n : ℕ) {t : ℝ} (ht : 0≤t) (ht1 : t<1) :
    1/(n+1:ℝ)≤weight n t := by
  have h := (weight_summable n ht ht1).le_tsum 0 (fun j _ => by positivity)
  simpa [weight] using h

theorem weight_mono (n : ℕ) {a b : ℝ} (ha : 0≤a) (hab : a≤b) (hb : b<1) :
    weight n a≤weight n b := by
  apply Summable.tsum_le_tsum (fun j => ?_)
    (weight_summable n ha (hab.trans_lt hb)) (weight_summable n (ha.trans hab) hb)
  exact div_le_div_of_nonneg_right (pow_le_pow_left₀ ha hab _) (by positivity)

theorem weight_finite_enclosure (n N : ℕ) {t : ℝ} (ht : 0≤t) (ht1 : t<1) :
    (∑ j ∈ Finset.range N, t^(2*j)/(n+j+1:ℝ))≤weight n t ∧
    weight n t≤(∑ j ∈ Finset.range N,t^(2*j)/(n+j+1:ℝ))+
      t^(2*N)/((n+N+1:ℝ)*(1-t^2)) := by
  have hs := weight_summable n ht ht1
  have ht2 : t^2<1 := by nlinarith
  have hshift : Summable (fun j : ℕ => t^(2*(j+N))/(n+(j+N)+1:ℝ)) := by
    simpa only [Nat.cast_add] using (summable_nat_add_iff N).mpr hs
  have hb (j : ℕ) : t^(2*(j+N))/(n+(j+N)+1:ℝ)≤
      (t^(2*N)/(n+N+1:ℝ))*(t^2)^j := by
    calc
      t^(2*(j+N))/(n+(j+N)+1:ℝ)≤t^(2*(j+N))/(n+N+1:ℝ) :=
        div_le_div_of_nonneg_left (pow_nonneg ht _) (by positivity) (by push_cast; linarith)
      _ =_ := by rw [Nat.mul_add,pow_add,pow_mul]; ring
  have hgeom := (summable_geometric_of_lt_one (sq_nonneg t) ht2).mul_left (t^(2*N)/(n+N+1:ℝ))
  have htail := Summable.tsum_le_tsum hb hshift hgeom
  rw [tsum_mul_left,tsum_geometric_of_lt_one (sq_nonneg t) ht2] at htail
  have he : (t^(2*N)/(n+N+1:ℝ))*(1-t^2)⁻¹=
      t^(2*N)/((n+N+1:ℝ)*(1-t^2)) := by
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  rw [he] at htail
  have hsplit := hs.sum_add_tsum_nat_add N
  have hnon : 0≤∑' j : ℕ,t^(2*(j+N))/(n+(j+N)+1:ℝ) := tsum_nonneg (fun j => by positivity)
  change _=weight n t at hsplit
  simp only [Nat.cast_add] at hsplit
  constructor <;> linarith

#print axioms weight_finite_enclosure
#print axioms weight_initial_lower
#print axioms weight_mono
end BecknerOnofri.HighDim.CircleScalar
