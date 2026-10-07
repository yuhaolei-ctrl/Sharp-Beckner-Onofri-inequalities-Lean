module

public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Data.List.GetD

@[expose] public section

/-!
# Truncated convolution of coefficient lists

Coefficients below `Q` of a power `(∑ c X^e)^k` of a polynomial with natural coefficients,
computed by structural recursion on lists. The functions here reduce efficiently in the Lean
kernel and are used by `decide +kernel` certificates; `powBase_spec` identifies their values
with the coefficients of the polynomial power.
-/

namespace BecknerOnofri.TruncatedConvolution

open Polynomial

/-- Add the list `l`, shifted by `e`, to `acc`, discarding entries beyond `acc.length`. -/
def shiftAdd (e : ℕ) (acc l : List ℕ) : List ℕ :=
  List.zipWith (· + ·) acc (List.replicate e 0 ++ l ++ List.replicate acc.length 0)

/-- Multiply the truncated coefficient list `a` by `∑ c X^e` over `base`. -/
def mulBase (Q : ℕ) (base : List (ℕ × ℕ)) (a : List ℕ) : List ℕ :=
  base.foldl (fun acc ec => shiftAdd ec.1 acc (a.map (ec.2 * ·))) (List.replicate Q 0)

/-- The coefficients of `(∑ c X^e)^k` below `Q`. -/
def powBase (Q : ℕ) (base : List (ℕ × ℕ)) : ℕ → List ℕ
  | 0 => (List.range Q).map fun q => if q = 0 then 1 else 0
  | k + 1 => mulBase Q base (powBase Q base k)

/-- The polynomial `∑ c X^e` over a list of terms. -/
noncomputable def termPolynomial (base : List (ℕ × ℕ)) : ℕ[X] :=
  (base.map fun ec => monomial ec.1 ec.2).sum

lemma length_shiftAdd (e : ℕ) (acc l : List ℕ) : (shiftAdd e acc l).length = acc.length := by
  simp [shiftAdd]
  omega

lemma getD_shifted (e : ℕ) (l : List ℕ) (m q : ℕ) :
    (List.replicate e 0 ++ l ++ List.replicate m 0).getD q 0 =
      if e ≤ q then l.getD (q - e) 0 else 0 := by
  split_ifs with he
  · by_cases hl : q < e + l.length
    · rw [List.getD_append _ _ _ _ (by simpa using hl),
        List.getD_append_right _ _ _ _ (by simpa using he), List.length_replicate]
    · rw [List.getD_append_right _ _ _ _ (by simp; omega),
        List.getD_eq_default l 0 (by omega)]
      by_cases hm : q - (List.replicate e 0 ++ l).length < m
      · exact List.getD_replicate 0 hm
      · exact List.getD_eq_default _ _ (by simp at hm ⊢; omega)
  · rw [List.getD_append _ _ _ _ (by simp; omega), List.getD_append _ _ _ _ (by simp; omega),
      List.getD_replicate 0 (by omega)]

lemma getD_shiftAdd (e : ℕ) (acc l : List ℕ) {q : ℕ} (hq : q < acc.length) :
    (shiftAdd e acc l).getD q 0 =
      acc.getD q 0 + if e ≤ q then l.getD (q - e) 0 else 0 := by
  rw [List.getD_eq_getElem _ _ (by rw [length_shiftAdd]; exact hq), List.getD_eq_getElem _ _ hq]
  simp only [shiftAdd, List.getElem_zipWith]
  congr 1
  rw [← getD_shifted e l acc.length q, List.getD_eq_getElem]

lemma foldl_shiftAdd (Q : ℕ) (a : List ℕ) (base : List (ℕ × ℕ)) (acc : List ℕ)
    (hacc : acc.length = Q) :
    (base.foldl (fun acc ec => shiftAdd ec.1 acc (a.map (ec.2 * ·))) acc).length = Q ∧
    ∀ q < Q, (base.foldl (fun acc ec => shiftAdd ec.1 acc (a.map (ec.2 * ·))) acc).getD q 0 =
      acc.getD q 0 + (base.map fun ec => if ec.1 ≤ q then ec.2 * a.getD (q - ec.1) 0 else 0).sum := by
  induction base generalizing acc with
  | nil => simpa using hacc
  | cons ec base ih =>
    obtain ⟨h1, h2⟩ := ih (shiftAdd ec.1 acc (a.map (ec.2 * ·)))
      (by rw [length_shiftAdd, hacc])
    refine ⟨h1, fun q hq => ?_⟩
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    rw [h2 q hq, getD_shiftAdd _ _ _ (by omega), add_assoc]
    congr 2
    split_ifs
    · simpa using List.getD_map a 0 (n := q - ec.1) (ec.2 * ·)
    · rfl

lemma coeff_termPolynomial_mul (base : List (ℕ × ℕ)) (P : ℕ[X]) (q : ℕ) :
    (termPolynomial base * P).coeff q =
      (base.map fun ec => if ec.1 ≤ q then ec.2 * P.coeff (q - ec.1) else 0).sum := by
  induction base with
  | nil => simp [termPolynomial]
  | cons ec base ih =>
    simp only [termPolynomial, List.map_cons, List.sum_cons, add_mul, coeff_add] at ih ⊢
    rw [ih, ← C_mul_X_pow_eq_monomial, mul_assoc, coeff_C_mul, coeff_X_pow_mul']
    split_ifs <;> simp

/-- Terms of exponent at least `Q` do not affect the coefficients below `Q`. -/
lemma sum_filter_small (base : List (ℕ × ℕ)) (Q : ℕ) (f : ℕ × ℕ → ℕ)
    (hf : ∀ ec, Q ≤ ec.1 → f ec = 0) :
    ((base.filter fun ec => ec.1 < Q).map f).sum = (base.map f).sum := by
  induction base with
  | nil => rfl
  | cons ec base ih =>
    by_cases h : ec.1 < Q
    · simp [h, ih]
    · simp [h, ih, hf ec (by omega)]

theorem powBase_spec (Q : ℕ) (base : List (ℕ × ℕ)) (k : ℕ) :
    (powBase Q (base.filter fun ec => ec.1 < Q) k).length = Q ∧
    ∀ q < Q, (powBase Q (base.filter fun ec => ec.1 < Q) k).getD q 0 =
      (termPolynomial base ^ k).coeff q := by
  induction k with
  | zero =>
    refine ⟨by simp [powBase], fun q hq => ?_⟩
    rw [List.getD_eq_getElem _ _ (by simpa [powBase] using hq)]
    simp [powBase, coeff_one]
  | succ k ih =>
    obtain ⟨hl, hc⟩ := ih
    obtain ⟨h1, h2⟩ := foldl_shiftAdd Q (powBase Q (base.filter fun ec => ec.1 < Q) k)
      (base.filter fun ec => ec.1 < Q) (List.replicate Q 0) (by simp)
    refine ⟨h1, fun q hq => ?_⟩
    simp only [powBase, mulBase]
    rw [h2 q hq, pow_succ', coeff_termPolynomial_mul]
    rw [List.getD_replicate 0 hq, zero_add]
    rw [sum_filter_small base Q _ (fun ec h => by split_ifs <;> omega)]
    congr 1
    apply List.map_congr_left
    intro ec _
    split_ifs with he
    · rw [hc _ (by omega)]
    · rfl

end BecknerOnofri.TruncatedConvolution
