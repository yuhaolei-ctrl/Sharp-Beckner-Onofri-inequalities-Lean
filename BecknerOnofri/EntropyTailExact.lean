module

public import BecknerOnofri.EntropyTailTwo

@[expose] public section

/-!
# The scalar tail for indices `3 ≤ n ≤ 50`

Lemma 5.13 of the manuscript verifies `T_n < R_n` for `2 ≤ n ≤ 50` from the shell
polynomial
`(∑_{|j| ≤ n} C(2n, n+|j|) z^{j²})^{12} = ∑_q p_q z^q`, since
`b^{12} (T_n + C_n) = ∑_{q ≥ 1} p_q q^{-6}` with `b = C(2n, n)`.

Here the coefficients `p_q` with `q < Q` are computed exactly by truncated convolution
in the kernel. The remaining coefficients are bounded by charging their total mass
`(∑_j C(2n, n+|j|))^{12} - ∑_{q<Q} p_q` the weight `Q^{-6}`. This gives an upper bound
for `G_{12,n}`, so it suffices for `T_n < R_n`.
-/

namespace BecknerOnofri.HighDim.EntropyTail.ExactTail

open Polynomial Finset

/-! ### Truncated convolution on coefficient lists -/

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

/-- The terms `(j², w_j C(2n, n+j))`, `0 ≤ j ≤ r`, of the shell polynomial of radius `r`
with index `n`, where `w_0 = 1` and `w_j = 2` for `j ≥ 1`. -/
def shellTerms (n r : ℕ) : List (ℕ × ℕ) :=
  (List.range (r + 1)).map fun j => (j ^ 2, (if j = 0 then 1 else 2) * (2 * n).choose (n + j))

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

/-! ### The inverse sixth moment of a polynomial with natural coefficients -/

/-- `∑_q p_q q^{-6}` for `P = ∑_q p_q X^q`, with the convention `0^{-6} = 0`. -/
noncomputable def inverseSixthNat (P : ℕ[X]) : ℚ :=
  P.sum fun q c => (c : ℚ) / (q : ℚ) ^ 6

lemma inverseSixthNat_eq_range (P : ℕ[X]) {N : ℕ} (hN : P.natDegree < N) :
    inverseSixthNat P = ∑ q ∈ range N, (P.coeff q : ℚ) / (q : ℚ) ^ 6 :=
  P.sum_over_range' (fun q => by simp) N hN

lemma eval_one_eq_range (P : ℕ[X]) {N : ℕ} (hN : P.natDegree < N) :
    P.eval 1 = ∑ q ∈ range N, P.coeff q := by
  rw [eval_eq_sum_range' hN]
  simp

/-- Lower bound by the coefficients below `Q`. -/
theorem lower_le_inverseSixthNat (P : ℕ[X]) (Q : ℕ) :
    ∑ q ∈ range Q, (P.coeff q : ℚ) / (q : ℚ) ^ 6 ≤ inverseSixthNat P := by
  rw [inverseSixthNat_eq_range P (N := max P.natDegree Q + 1) (by omega)]
  exact sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr (by omega))
    (fun _ _ _ => by positivity)

/-- Upper bound: coefficients beyond `Q` carry the weight `Q^{-6}`. -/
theorem inverseSixthNat_le_upper (P : ℕ[X]) {Q : ℕ} (hQ : 0 < Q) :
    inverseSixthNat P ≤ ∑ q ∈ range Q, (P.coeff q : ℚ) / (q : ℚ) ^ 6 +
      (((P.eval 1 : ℕ) : ℚ) - ∑ q ∈ range Q, (P.coeff q : ℚ)) / (Q : ℚ) ^ 6 := by
  set N := max (P.natDegree + 1) Q
  have hN : P.natDegree < N := by omega
  have hQN : Q ≤ N := le_max_right _ _
  rw [inverseSixthNat_eq_range P hN, eval_one_eq_range P hN]
  rw [← sum_range_add_sum_Ico _ hQN, Nat.cast_sum, ← sum_range_add_sum_Ico _ hQN]
  simp only [add_sub_cancel_left, add_le_add_iff_left, sum_div]
  apply sum_le_sum
  intro q hq
  have hq' := (mem_Ico.mp hq).1
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast hq') 6


/-! ### Lists and finite sums -/

/-- `∑_{i < |l|} l_i (q+i)^{-6}`, evaluated by the kernel in one pass. -/
def inverseSixthFrom : ℕ → List ℕ → ℚ
  | _, [] => 0
  | q, a :: l => (a : ℚ) / (q : ℚ) ^ 6 + inverseSixthFrom (q + 1) l

/-- `∑_{q < |l|} l_q q^{-6}`. -/
def listInverseSixth (l : List ℕ) : ℚ := inverseSixthFrom 0 l

lemma list_sum_range {M : Type*} [AddCommMonoid M] (f : ℕ → M) (N : ℕ) :
    ((List.range N).map f).sum = ∑ i ∈ range N, f i := by
  induction N with
  | zero => simp
  | succ N ih => rw [List.range_succ, List.map_append, List.sum_append, ih, sum_range_succ]; simp

lemma list_sum_eq_getD (l : List ℕ) : l.sum = ∑ q ∈ range l.length, l.getD q 0 := by
  induction l with
  | nil => simp
  | cons a l ih => rw [List.sum_cons, ih, List.length_cons, sum_range_succ']; simp [add_comm]

/-! ### The shell polynomial -/

/-- The shell polynomial `∑_{|j| ≤ r} C(2n, n+|j|) X^{j²}`. -/
noncomputable def shellPolynomial (n r : ℕ) : ℕ[X] := termPolynomial (shellTerms n r)

lemma shellPolynomial_eq (n r : ℕ) : shellPolynomial n r =
    ∑ j ∈ Icc (-(r : ℤ)) r, monomial (j.natAbs ^ 2) ((2 * n).choose (n + j.natAbs)) := by
  unfold shellPolynomial termPolynomial shellTerms
  rw [List.map_map, list_sum_range]
  induction r with
  | zero => simp
  | succ r ih =>
    have hs : Icc (-((r + 1 : ℕ) : ℤ)) ((r + 1 : ℕ) : ℤ) =
        insert (-((r + 1 : ℕ) : ℤ)) (insert ((r + 1 : ℕ) : ℤ) (Icc (-(r : ℤ)) r)) := by
      ext j
      simp only [mem_Icc, mem_insert]
      omega
    rw [sum_range_succ, ih, hs, sum_insert (by simp; omega), sum_insert (by simp)]
    simp only [Function.comp, Nat.succ_ne_zero, ite_false, Int.natAbs_neg, Int.natAbs_natCast,
      two_mul, map_add]
    abel

lemma prod_monomial_nat {ι : Type*} (s : Finset ι) (m : ι → ℕ) (a : ι → ℕ) :
    (∏ i ∈ s, monomial (m i) (a i)) = monomial (∑ i ∈ s, m i) (∏ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp [hi, ih, monomial_mul_monomial]

lemma shellPolynomial_pow (n r : ℕ) : shellPolynomial n r ^ 12 =
    ∑ k ∈ RectangleLattice.box (fun _ : Fin 12 => r),
      monomial (latticeSquare k) (∏ i : Fin 12, (2 * n).choose (n + (k i).natAbs)) := by
  rw [shellPolynomial_eq, RectangleLattice.box, sum_pow']
  apply sum_congr rfl
  intro k _
  exact prod_monomial_nat univ _ _

lemma inverseSixthNat_add (P R : ℕ[X]) :
    inverseSixthNat (P + R) = inverseSixthNat P + inverseSixthNat R :=
  sum_add_index _ _ _ (fun _ => by simp) (fun _ _ _ => by push_cast; ring)

lemma inverseSixthNat_monomial (e c : ℕ) :
    inverseSixthNat (monomial e c) = (c : ℚ) / (e : ℚ) ^ 6 :=
  sum_monomial_index _ _ (by simp)

lemma inverseSixthNat_sum {ι : Type*} (s : Finset ι) (P : ι → ℕ[X]) :
    inverseSixthNat (∑ i ∈ s, P i) = ∑ i ∈ s, inverseSixthNat (P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [inverseSixthNat]
  | insert i s hi ih => rw [sum_insert hi, sum_insert hi, inverseSixthNat_add, ih]

lemma inverseSixthNat_shell (n r : ℕ) : inverseSixthNat (shellPolynomial n r ^ 12) =
    ∑ k ∈ RectangleLattice.box (fun _ : Fin 12 => r),
      ((∏ i : Fin 12, (2 * n).choose (n + (k i).natAbs) : ℕ) : ℚ) / (latticeSquare k : ℚ) ^ 6 := by
  rw [shellPolynomial_pow, inverseSixthNat_sum]
  simp only [inverseSixthNat_monomial]

lemma shellPolynomial_eval_one (n r : ℕ) :
    (shellPolynomial n r).eval 1 = ((shellTerms n r).map Prod.snd).sum := by
  unfold shellPolynomial termPolynomial
  induction shellTerms n r with
  | nil => simp
  | cons ec l ih => simp [ih]

/-! ### The real scalar tail as a difference of two shell sums -/

lemma weight_cast (n : ℕ) (k : Frequency 12) :
    (frequencyLength k ^ 12)⁻¹ * (∏ i : Fin 12, scalarCoefficient n (k i).natAbs) =
      ((((∏ i : Fin 12, (2 * n).choose (n + (k i).natAbs) : ℕ) : ℚ) /
        (latticeSquare k : ℚ) ^ 6 / ((2 * n).choose n : ℚ) ^ 12 : ℚ) : ℝ) := by
  have hp : frequencyLength k ^ 12 = (latticeSquare k : ℝ) ^ 6 := by
    have h := frequencyLength_pow_eq k
    norm_num only [Nat.cast_ofNat, show (12 : ℝ) / 2 = 6 by norm_num, Real.rpow_ofNat] at h
    exact h
  rw [hp]
  simp only [scalarCoefficient, prod_div_distrib, prod_const, card_univ, Fintype.card_fin]
  push_cast
  ring

/-- The summand `|k|^{-12} ∏ a_n(k_i)` of `G_{12,n}`. -/
noncomputable def term (n : ℕ) (k : Frequency 12) : ℝ :=
  (frequencyLength k ^ 12)⁻¹ * ∏ i : Fin 12, scalarCoefficient n (k i).natAbs

theorem sum_box_term (n r : ℕ) : (∑ k ∈ RectangleLattice.box (fun _ : Fin 12 => r), term n k) =
    ((inverseSixthNat (shellPolynomial n r ^ 12) / ((2 * n).choose n : ℚ) ^ 12 : ℚ) : ℝ) := by
  rw [inverseSixthNat_shell, sum_div, Rat.cast_sum]
  exact Finset.sum_congr rfl (fun k _ => weight_cast n k)

theorem box_one_subset {n : ℕ} (hn : 1 ≤ n) : RectangleLattice.box (fun _ : Fin 12 => 1) ⊆
    RectangleLattice.box (fun _ : Fin 12 => n) := by
  intro k hk
  rw [RandomRectangles.mem_box_natAbs] at hk ⊢
  exact fun i => (hk i).trans hn

theorem scalarTail_eq_sdiff {n : ℕ} : scalarTail n =
    ∑ k ∈ (RectangleLattice.box (fun _ : Fin 12 => n)) \
      (RectangleLattice.box (fun _ : Fin 12 => 1)), term n k := by
  classical
  have hfilter : (RectangleLattice.box (fun _ : Fin 12 => n)) \
      (RectangleLattice.box (fun _ : Fin 12 => 1)) =
      (RectangleLattice.box (fun _ : Fin 12 => n)).filter outsideCube := by
    ext k
    simp only [Finset.mem_sdiff, Finset.mem_filter, outsideCube_iff_not_mem]
  rw [scalarTail_eq_finite_sum, hfilter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro k _
  dsimp only [scalarTailWeight, term]
  split_ifs <;> simp

/-- `b^{12} T_n` as a difference of two inverse sixth moments of shell polynomials. -/
theorem scalarTail_eq_shell {n : ℕ} (hn : 1 ≤ n) : scalarTail n =
    (((inverseSixthNat (shellPolynomial n n ^ 12) - inverseSixthNat (shellPolynomial n 1 ^ 12)) /
      ((2 * n).choose n : ℚ) ^ 12 : ℚ) : ℝ) := by
  have h := Finset.sum_sdiff (f := term n) (box_one_subset hn)
  rw [← scalarTail_eq_sdiff, sum_box_term, sum_box_term] at h
  rw [sub_div, Rat.cast_sub]
  linarith

/-! ### The cube contribution -/

/-- `C_n = ∑_{r=1}^{12} C(12,r) (2 a_n(1))^r r^{-6}`; the `r = 0` term vanishes. -/
noncomputable def cubeSum (n : ℕ) : ℝ :=
  ∑ r ∈ range 13, ((12 : ℕ).choose r : ℝ) * (2 * scalarCoefficient n 1) ^ r / (r : ℝ) ^ 6

lemma shellPolynomial_one (n : ℕ) : shellPolynomial n 1 =
    monomial 0 ((2 * n).choose n) + monomial 1 (2 * (2 * n).choose (n + 1)) := by
  simp [shellPolynomial, termPolynomial, shellTerms, List.range_succ]

theorem sum_box_one (n : ℕ) :
    (∑ k ∈ RectangleLattice.box (fun _ : Fin 12 => 1), term n k) = cubeSum n := by
  have hb : (0 : ℚ) < (2 * n).choose n := by exact_mod_cast Nat.choose_pos (by omega)
  rw [sum_box_term, shellPolynomial_one, add_comm, add_pow, inverseSixthNat_sum]
  simp only [monomial_pow, monomial_mul_monomial, ← C_eq_natCast, ← monomial_zero_left,
    zero_mul, add_zero, one_mul, inverseSixthNat_monomial, sum_div, Rat.cast_sum, cubeSum]
  apply sum_congr rfl
  intro r hr
  have hr' := mem_range.mp hr
  simp only [scalarCoefficient]
  push_cast
  rw [mul_pow, mul_pow, div_pow]
  field_simp
  have hB : ((2 * n).choose n : ℝ) ^ (12 - r) ≠ 0 :=
    pow_ne_zero _ (by exact_mod_cast (Nat.choose_pos (by omega : n ≤ 2 * n)).ne')
  have h12 : ((2 * n).choose n : ℝ) ^ 12 = ((2 * n).choose n : ℝ) ^ (12 - r) *
      ((2 * n).choose n : ℝ) ^ r := by rw [← pow_add]; congr 1; omega
  calc
    _ = ((2 * n).choose (n + 1) : ℝ) ^ r * ((12 : ℕ).choose r : ℝ) /
        ((r : ℝ) ^ 6 * ((2 * n).choose n : ℝ) ^ r) *
        (((2 * n).choose n : ℝ) ^ (12 - r) / ((2 * n).choose n : ℝ) ^ (12 - r)) := by
      rw [h12]; ring
    _ = _ := by rw [div_self hB, mul_one]

theorem cubeSum_lower {n : ℕ} :
    ∑ r ∈ range 13, ((12 : ℕ).choose r : ℝ) * 2 ^ r / (r : ℝ) ^ 6 -
      (∑ r ∈ range 13, ((12 : ℕ).choose r : ℝ) * 2 ^ r * r / (r : ℝ) ^ 6) / ((n : ℝ) + 1) ≤
      cubeSum n := by
  have ha : scalarCoefficient n 1 = 1 - 1 / ((n : ℝ) + 1) := by
    rw [scalarCoefficient_eq, first_coefficient]
    field_simp
    ring
  rw [sum_div, ← sum_sub_distrib, cubeSum]
  apply sum_le_sum
  intro r _
  have hb := one_add_mul_le_pow (a := -(1 / ((n : ℝ) + 1)))
    (by have : 0 < 1 / ((n : ℝ) + 1) := by positivity
        have : 1 / ((n : ℝ) + 1) ≤ 1 := by
          rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
        linarith) r
  rw [ha, mul_pow]
  have hc : (0 : ℝ) ≤ ((12 : ℕ).choose r : ℝ) * 2 ^ r / (r : ℝ) ^ 6 := by positivity
  calc
    _ = ((12 : ℕ).choose r : ℝ) * 2 ^ r / (r : ℝ) ^ 6 * (1 + r * -(1 / ((n : ℝ) + 1))) := by ring
    _ ≤ ((12 : ℕ).choose r : ℝ) * 2 ^ r / (r : ℝ) ^ 6 * (1 + -(1 / ((n : ℝ) + 1))) ^ r :=
      mul_le_mul_of_nonneg_left hb hc
    _ = _ := by ring

/-! ### The kernel computation -/

/-- Truncation radius used for index `n`. -/
def radius (n : ℕ) : ℕ := 3 * n + 10

/-- Upper bound for `b^{12} G_{12,n} = ∑_{q ≥ 1} p_q q^{-6}`. -/
def fullUpper (n : ℕ) : ℚ :=
  let p := powBase (radius n) ((shellTerms n n).filter fun ec => ec.1 < radius n) 12
  listInverseSixth p +
    ((((shellTerms n n).map Prod.snd).sum ^ 12 : ℕ) - (p.sum : ℚ)) / (radius n : ℚ) ^ 6

/-- Exact value of `b^{12} C_n`, the cube contribution (all its exponents are below `13`). -/
def cubeLower (n : ℕ) : ℚ :=
  listInverseSixth (powBase 13 ((shellTerms n 1).filter fun ec => ec.1 < 13) 12)

/-- The rational value of `R_n`. -/
def budgetRat (n : ℕ) : ℚ :=
  12 * ((21 / 500) * Legacy.D10.binomialCoeff n 2 + (67 / 100) *
    (harmonic n - 2 * Legacy.D10.binomialCoeff n 1 - Legacy.D10.binomialCoeff n 2))

/-- The finite check for one index. -/
def check (n : ℕ) : Bool :=
  decide (fullUpper n - cubeLower n < budgetRat n * ((2 * n).choose n : ℚ) ^ 12)

lemma inverseSixthFrom_eq (l : List ℕ) (q : ℕ) :
    inverseSixthFrom q l = ∑ i ∈ range l.length, (l.getD i 0 : ℚ) / ((q + i : ℕ) : ℚ) ^ 6 := by
  induction l generalizing q with
  | nil => simp [inverseSixthFrom]
  | cons a l ih =>
    rw [inverseSixthFrom, ih, List.length_cons, sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, add_zero]
    rw [add_comm]
    congr 1
    exact sum_congr rfl (fun i _ => by congr 3; omega)

lemma listInverseSixth_eq (Q : ℕ) (l : List ℕ) (P : ℕ[X]) (hl : l.length = Q)
    (hc : ∀ q < Q, l.getD q 0 = P.coeff q) :
    listInverseSixth l = ∑ q ∈ range Q, (P.coeff q : ℚ) / (q : ℚ) ^ 6 := by
  unfold listInverseSixth
  rw [inverseSixthFrom_eq, hl]
  exact sum_congr rfl (fun q hq => by rw [hc q (mem_range.mp hq), zero_add])

lemma list_sum_eq (Q : ℕ) (l : List ℕ) (P : ℕ[X]) (hl : l.length = Q)
    (hc : ∀ q < Q, l.getD q 0 = P.coeff q) :
    (l.sum : ℚ) = ∑ q ∈ range Q, (P.coeff q : ℚ) := by
  rw [list_sum_eq_getD, hl, Nat.cast_sum]
  exact sum_congr rfl (fun q hq => by rw [hc q (mem_range.mp hq)])

theorem fullUpper_spec (n : ℕ) :
    inverseSixthNat (shellPolynomial n n ^ 12) ≤ fullUpper n := by
  obtain ⟨hl, hc⟩ := powBase_spec (radius n) (shellTerms n n) 12
  have h := inverseSixthNat_le_upper (shellPolynomial n n ^ 12) (Q := radius n) (by unfold radius; omega)
  unfold fullUpper
  simp only
  rw [listInverseSixth_eq _ _ _ hl hc, list_sum_eq _ _ _ hl hc, ← shellPolynomial_eval_one]
  simpa [eval_pow, shellPolynomial] using h

theorem cubeLower_spec (n : ℕ) :
    cubeLower n ≤ inverseSixthNat (shellPolynomial n 1 ^ 12) := by
  obtain ⟨hl, hc⟩ := powBase_spec 13 (shellTerms n 1) 12
  unfold cubeLower
  rw [listInverseSixth_eq _ _ _ hl hc]
  exact lower_le_inverseSixthNat _ 13

theorem budgetRat_cast (n : ℕ) : (budgetRat n : ℝ) = scalarBudget n := by
  rw [scalarBudget_eq, tailBudget]
  simp [budgetRat, Legacy.D10.binomialCoeffReal]

theorem scalarTail_lt_of_check {n : ℕ} (hn : 1 ≤ n) (h : check n = true) :
    scalarTail n < scalarBudget n := by
  have hc := of_decide_eq_true h
  have hb : (0 : ℚ) < ((2 * n).choose n : ℚ) ^ 12 := by
    have := Nat.choose_pos (n := 2 * n) (k := n) (by omega)
    positivity
  rw [scalarTail_eq_shell hn, ← budgetRat_cast]
  apply Rat.cast_lt.mpr
  rw [div_lt_iff₀ hb]
  linarith [fullUpper_spec n, cubeLower_spec n]

/-! ### The finite range `3 ≤ n ≤ 50` -/



theorem check_3 : check 3 = true := by decide +kernel
theorem check_4 : check 4 = true := by decide +kernel
theorem check_5 : check 5 = true := by decide +kernel
theorem check_6 : check 6 = true := by decide +kernel
theorem check_7 : check 7 = true := by decide +kernel
theorem check_8 : check 8 = true := by decide +kernel
theorem check_9 : check 9 = true := by decide +kernel
theorem check_10 : check 10 = true := by decide +kernel
theorem check_11 : check 11 = true := by decide +kernel
theorem check_12 : check 12 = true := by decide +kernel
theorem check_13 : check 13 = true := by decide +kernel
theorem check_14 : check 14 = true := by decide +kernel
theorem check_15 : check 15 = true := by decide +kernel
theorem check_16 : check 16 = true := by decide +kernel
theorem check_17 : check 17 = true := by decide +kernel
theorem check_18 : check 18 = true := by decide +kernel
theorem check_19 : check 19 = true := by decide +kernel
theorem check_20 : check 20 = true := by decide +kernel
theorem check_21 : check 21 = true := by decide +kernel
theorem check_22 : check 22 = true := by decide +kernel
theorem check_23 : check 23 = true := by decide +kernel
theorem check_24 : check 24 = true := by decide +kernel
theorem check_25 : check 25 = true := by decide +kernel
theorem check_26 : check 26 = true := by decide +kernel
theorem check_27 : check 27 = true := by decide +kernel
theorem check_28 : check 28 = true := by decide +kernel
theorem check_29 : check 29 = true := by decide +kernel
theorem check_30 : check 30 = true := by decide +kernel
theorem check_31 : check 31 = true := by decide +kernel
theorem check_32 : check 32 = true := by decide +kernel
theorem check_33 : check 33 = true := by decide +kernel
theorem check_34 : check 34 = true := by decide +kernel
theorem check_35 : check 35 = true := by decide +kernel
theorem check_36 : check 36 = true := by decide +kernel
theorem check_37 : check 37 = true := by decide +kernel
theorem check_38 : check 38 = true := by decide +kernel
theorem check_39 : check 39 = true := by decide +kernel
theorem check_40 : check 40 = true := by decide +kernel
theorem check_41 : check 41 = true := by decide +kernel
theorem check_42 : check 42 = true := by decide +kernel
theorem check_43 : check 43 = true := by decide +kernel
theorem check_44 : check 44 = true := by decide +kernel
theorem check_45 : check 45 = true := by decide +kernel
theorem check_46 : check 46 = true := by decide +kernel
theorem check_47 : check 47 = true := by decide +kernel
theorem check_48 : check 48 = true := by decide +kernel
theorem check_49 : check 49 = true := by decide +kernel
theorem check_50 : check 50 = true := by decide +kernel

theorem check_mid {n : ℕ} (h3 : 3 ≤ n) (h50 : n ≤ 50) : check n = true := by
  interval_cases n
  · exact check_3
  · exact check_4
  · exact check_5
  · exact check_6
  · exact check_7
  · exact check_8
  · exact check_9
  · exact check_10
  · exact check_11
  · exact check_12
  · exact check_13
  · exact check_14
  · exact check_15
  · exact check_16
  · exact check_17
  · exact check_18
  · exact check_19
  · exact check_20
  · exact check_21
  · exact check_22
  · exact check_23
  · exact check_24
  · exact check_25
  · exact check_26
  · exact check_27
  · exact check_28
  · exact check_29
  · exact check_30
  · exact check_31
  · exact check_32
  · exact check_33
  · exact check_34
  · exact check_35
  · exact check_36
  · exact check_37
  · exact check_38
  · exact check_39
  · exact check_40
  · exact check_41
  · exact check_42
  · exact check_43
  · exact check_44
  · exact check_45
  · exact check_46
  · exact check_47
  · exact check_48
  · exact check_49
  · exact check_50

/-- Lemma 5.13 for `3 ≤ n ≤ 50`, by exact shell sums. -/
theorem scalarTail_lt_budget_mid {n : ℕ} (h3 : 3 ≤ n) (h50 : n ≤ 50) :
    scalarTail n < scalarBudget n :=
  scalarTail_lt_of_check (by omega) (check_mid h3 h50)

end BecknerOnofri.HighDim.EntropyTail.ExactTail
