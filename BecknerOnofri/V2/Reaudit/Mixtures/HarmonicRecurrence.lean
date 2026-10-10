module

public import BecknerOnofri.V2.ThetaTail.Defs
public import Legacy.D10.BinomialReal

@[expose] public section

/-! # The harmonic identity `eq:harmonic-identity` by the printed recurrence (S043)

The manuscript proves `H_n = 2 ∑_{j≥1} a_n(j)/j` in four displayed steps:

* `eq:harmonic-coefficient-recurrence`: `n² (a_n(j) - a_{n-1}(j)) = j² a_n(j)` for `n ≥ 1`;
* `eq:harmonic-binomial-telescope`: `j C(2n, n+j) = n [C(2n-1, n+j-1) - C(2n-1, n+j)]`;
* upon summation `∑_{j≥1} j a_n(j) = n/2` (first-moment telescope);
* `eq:harmonic-sum-increment`: `2 ∑_{j≥1} (a_n(j) - a_{n-1}(j))/j = (2/n²) ∑_{j≥1} j a_n(j) = 1/n`;

and both sides of the identity vanish at `n = 0`.  Each step is a theorem below, for the manuscript's
`a_n(j) = C(2n, n+|j|)/C(2n, n)` (`ThetaTail.aCoef`) and `H_n` (`ThetaTail.Hn`).  The recurrence
is the repository's `Legacy.D10.binomialCoeff_row_step` (cast to `ℝ`); the telescope
`eq:harmonic-binomial-telescope` is proved here from Pascal's rule, and the first moment is
obtained from it by summation, exactly as printed. -/

noncomputable section
open Finset
open scoped BigOperators

namespace BecknerOnofri.V2.Reaudit.Mixtures
open BecknerOnofri.V2.ThetaTail (aCoef Hn)

theorem aCoef_nonneg' (n : ℕ) (j : ℤ) : 0 ≤ aCoef n j := by
  unfold aCoef; positivity

theorem aCoef_eq_binomialCoeff (n : ℕ) (j : ℤ) :
    aCoef n j = ((Legacy.D10.binomialCoeff n j.natAbs : ℚ) : ℝ) := by
  unfold aCoef Legacy.D10.binomialCoeff
  push_cast
  rfl

theorem aCoef_eq_zero_of_lt (n : ℕ) (j : ℤ) (h : n < j.natAbs) : aCoef n j = 0 := by
  rw [aCoef_eq_binomialCoeff, Legacy.D10.binomialCoeff_eq_zero h]; simp

@[simp] theorem aCoef_zero (n : ℕ) : aCoef n 0 = 1 := by
  rw [aCoef_eq_binomialCoeff]; simp

/-- `eq:harmonic-coefficient-recurrence`. -/
theorem harmonic_coefficient_recurrence (n : ℕ) (hn : 1 ≤ n) (j : ℤ) :
    (n : ℝ) ^ 2 * (aCoef n j - aCoef (n - 1) j) = (j : ℝ) ^ 2 * aCoef n j := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have h := Legacy.D10.binomialCoeff_row_step m j.natAbs
  have hR := congrArg (fun x : ℚ => (x : ℝ)) h
  simp only [Rat.cast_mul, Rat.cast_pow, Rat.cast_add, Rat.cast_one, Rat.cast_sub,
    Rat.cast_natCast] at hR
  rw [Nat.add_sub_cancel, aCoef_eq_binomialCoeff, aCoef_eq_binomialCoeff]
  have hj : ((j.natAbs : ℕ) : ℝ) ^ 2 = (j : ℝ) ^ 2 := by
    rw [Nat.cast_natAbs, Int.cast_abs, sq_abs]
  push_cast
  rw [← hj]
  linarith [hR]

/-- `eq:harmonic-binomial-telescope`:
`j C(2n, n+j) = n [C(2n-1, n+j-1) - C(2n-1, n+j)]`, for `n, j ≥ 1`. -/
theorem harmonic_binomial_telescope (n j : ℕ) (hn : 1 ≤ n) (hj : 1 ≤ j) :
    (j : ℤ) * ((2 * n).choose (n + j) : ℤ) =
      n * (((2 * n - 1).choose (n + j - 1) : ℤ) - ((2 * n - 1).choose (n + j) : ℤ)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have e1 : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
  have e2 : m + 1 + (i + 1) - 1 = m + i + 1 := by omega
  rw [e1, e2, show 2 * (m + 1) = (2 * m + 1) + 1 by omega,
    show m + 1 + (i + 1) = (m + i + 1) + 1 by omega]
  have hP := Nat.add_one_mul_choose_eq (2 * m + 1) (m + i + 1)
  -- hP : (2m+2) * C(2m+1, m+i+1) = C(2m+2, m+i+2) * (m+i+2)
  by_cases hle : i ≤ m
  · have hR := Nat.choose_succ_right_eq (2 * m + 1) (m + i + 1)
    -- hR : C(2m+1, m+i+2) * (m+i+2) = C(2m+1, m+i+1) * (2m+1 - (m+i+1))
    have hsub : 2 * m + 1 - (m + i + 1) = m - i := by omega
    rw [hsub] at hR
    have hP' : (((2 * m + 1 + 1) : ℕ) : ℤ) * ((2 * m + 1).choose (m + i + 1) : ℤ) =
        (((2 * m + 1 + 1).choose (m + i + 1 + 1) : ℕ) : ℤ) * (((m + i + 1 + 1) : ℕ) : ℤ) := by
      exact_mod_cast hP
    have hR' : (((2 * m + 1).choose (m + i + 1 + 1) : ℕ) : ℤ) * (((m + i + 1 + 1) : ℕ) : ℤ) =
        ((2 * m + 1).choose (m + i + 1) : ℤ) * ((m - i : ℕ) : ℤ) := by
      exact_mod_cast hR
    have hpos : (0 : ℤ) < (((m + i + 1 + 1) : ℕ) : ℤ) := by positivity
    apply mul_right_cancel₀ hpos.ne'
    have hmi : ((m - i : ℕ) : ℤ) = (m : ℤ) - i := by omega
    push_cast at hP' hR' hmi ⊢
    rw [hmi] at hR'
    linear_combination (-((i : ℤ) + 1)) * hP' + ((m : ℤ) + 1) * hR'
  · -- all binomial coefficients vanish
    have h1 : (2 * m + 1 + 1).choose (m + i + 1 + 1) = 0 :=
      Nat.choose_eq_zero_of_lt (by omega)
    have h2 : (2 * m + 1).choose (m + i + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    have h3 : (2 * m + 1).choose (m + i + 1 + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    simp [h1, h2, h3]

theorem aCoef_natCast (n m : ℕ) :
    aCoef n (m : ℤ) = ((2 * n).choose (n + m) : ℝ) / ((2 * n).choose n : ℝ) := by
  simp [aCoef]

theorem aCoef_succ_cast (n j : ℕ) :
    aCoef n ((j : ℤ) + 1) = ((2 * n).choose (n + (j + 1)) : ℝ) / ((2 * n).choose n : ℝ) := by
  have : ((j : ℤ) + 1) = ((j + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [this, aCoef_natCast]

theorem centralBinom_pos (n : ℕ) : (0 : ℝ) < ((2 * n).choose n : ℝ) := by
  exact_mod_cast Nat.choose_pos (by omega)

/-- the first-moment telescope in `ℤ`: `∑_{j=1}^{n} j C(2n, n+j) = n C(2n-1, n)`. -/
theorem first_moment_binomial (m : ℕ) :
    ∑ j ∈ range (m + 1), ((j : ℤ) + 1) * ((2 * (m + 1)).choose (m + 1 + (j + 1)) : ℤ) =
      ((m : ℤ) + 1) * ((2 * m + 1).choose (m + 1) : ℤ) := by
  have h : ∀ j ∈ range (m + 1), ((j : ℤ) + 1) * ((2 * (m + 1)).choose (m + 1 + (j + 1)) : ℤ) =
      ((m : ℤ) + 1) * (((2 * m + 1).choose (m + 1 + j) : ℤ) -
        ((2 * m + 1).choose (m + 1 + (j + 1)) : ℤ)) := by
    intro j _
    have := harmonic_binomial_telescope (m + 1) (j + 1) (by omega) (by omega)
    have e1 : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
    have e2 : m + 1 + (j + 1) - 1 = m + 1 + j := by omega
    rw [e1, e2] at this
    push_cast at this ⊢
    exact this
  rw [Finset.sum_congr rfl h, ← Finset.mul_sum]
  congr 1
  have := Finset.sum_range_sub' (fun i : ℕ => ((2 * m + 1).choose (m + 1 + i) : ℤ)) (m + 1)
  rw [this]
  have h0 : (2 * m + 1).choose (m + 1 + (m + 1)) = 0 := Nat.choose_eq_zero_of_lt (by omega)
  simp [h0]

/-- `2 C(2n-1, n) = C(2n, n)`. -/
theorem two_mul_choose_half (m : ℕ) :
    2 * (2 * m + 1).choose (m + 1) = (2 * (m + 1)).choose (m + 1) := by
  have h1 := Nat.choose_symm_half m
  have h2 : (2 * m + 1 + 1).choose (m + 1) = (2 * m + 1).choose m + (2 * m + 1).choose (m + 1) :=
    Nat.choose_succ_succ' (2 * m + 1) m
  rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, h2, ← h1]
  ring

/-- the first moment `∑_{j≥1} j a_n(j) = n/2` (finite sum, as `a_n(j) = 0` for `j > n`). -/
theorem harmonic_first_moment (n : ℕ) :
    ∑ j ∈ range n, ((j : ℝ) + 1) * aCoef n ((j : ℤ) + 1) = (n : ℝ) / 2 := by
  rcases n with _ | m
  · simp
  · have hc := centralBinom_pos (m + 1)
    have hI := first_moment_binomial m
    have hR : (∑ j ∈ range (m + 1), ((j : ℝ) + 1) * ((2 * (m + 1)).choose (m + 1 + (j + 1)) : ℝ)) =
        ((m : ℝ) + 1) * ((2 * m + 1).choose (m + 1) : ℝ) := by exact_mod_cast hI
    have h2 : (2 : ℝ) * ((2 * m + 1).choose (m + 1) : ℝ) = ((2 * (m + 1)).choose (m + 1) : ℝ) := by
      exact_mod_cast two_mul_choose_half m
    simp_rw [aCoef_succ_cast, mul_div_assoc']
    rw [← Finset.sum_div, hR, div_eq_div_iff hc.ne' (by norm_num)]
    push_cast
    nlinarith [h2]

theorem aCoef_succ_eq_zero (n j : ℕ) (h : n ≤ j) : aCoef n ((j : ℤ) + 1) = 0 := by
  apply aCoef_eq_zero_of_lt
  have : ((j : ℤ) + 1).natAbs = j + 1 := by omega
  omega

/-- `eq:harmonic-sum-increment`: `2 ∑_{j≥1} (a_n(j) - a_{n-1}(j))/j = (2/n²) ∑_{j≥1} j a_n(j) = 1/n`
(finite sums over `j = 1, …, n`; `a_{n-1}(n) = 0`). -/
theorem harmonic_sum_increment (m : ℕ) :
    2 * ∑ j ∈ range (m + 1),
        (aCoef (m + 1) ((j : ℤ) + 1) - aCoef m ((j : ℤ) + 1)) / ((j : ℝ) + 1) =
      (2 / ((m : ℝ) + 1) ^ 2) * ∑ j ∈ range (m + 1), ((j : ℝ) + 1) * aCoef (m + 1) ((j : ℤ) + 1) ∧
    (2 / ((m : ℝ) + 1) ^ 2) * ∑ j ∈ range (m + 1), ((j : ℝ) + 1) * aCoef (m + 1) ((j : ℤ) + 1) =
      1 / ((m : ℝ) + 1) := by
  have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  constructor
  · rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have hr := harmonic_coefficient_recurrence (m + 1) (by omega) ((j : ℤ) + 1)
    simp only [Nat.add_sub_cancel] at hr
    push_cast at hr
    have hj : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    field_simp
    nlinarith [hr]
  · have h1 := harmonic_first_moment (m + 1)
    have h2 : ∑ j ∈ range (m + 1), ((j : ℝ) + 1) * aCoef (m + 1) ((j : ℤ) + 1) =
        ((m : ℝ) + 1) / 2 := by exact_mod_cast h1
    rw [h2]
    field_simp

theorem summable_aCoef_div (n : ℕ) :
    Summable (fun j : ℕ => aCoef n ((j : ℤ) + 1) / ((j : ℝ) + 1)) := by
  apply summable_of_ne_finset_zero (s := range n)
  intro j hj
  rw [aCoef_succ_eq_zero n j (by simpa using hj), zero_div]

theorem tsum_aCoef_div_eq_sum (n : ℕ) :
    ∑' j : ℕ, aCoef n ((j : ℤ) + 1) / ((j : ℝ) + 1) =
      ∑ j ∈ range n, aCoef n ((j : ℤ) + 1) / ((j : ℝ) + 1) := by
  apply tsum_eq_sum
  intro j hj
  rw [aCoef_succ_eq_zero n j (by simpa using hj), zero_div]

/-- `eq:harmonic-identity` (finite form): `H_n = 2 ∑_{j=1}^{n} a_n(j)/j`, by induction on `n` from
`eq:harmonic-sum-increment`; both sides vanish at `n = 0`. -/
theorem harmonic_identity_finite (n : ℕ) :
    Hn n = 2 * ∑ j ∈ range n, aCoef n ((j : ℤ) + 1) / ((j : ℝ) + 1) := by
  induction n with
  | zero => simp [Hn]
  | succ m ih =>
    have hinc := (harmonic_sum_increment m).1.trans (harmonic_sum_increment m).2
    have hsplit : ∑ j ∈ range (m + 1), aCoef m ((j : ℤ) + 1) / ((j : ℝ) + 1) =
        ∑ j ∈ range m, aCoef m ((j : ℤ) + 1) / ((j : ℝ) + 1) := by
      rw [Finset.sum_range_succ, aCoef_succ_eq_zero m m le_rfl, zero_div, add_zero]
    have hsub : ∑ j ∈ range (m + 1),
        (aCoef (m + 1) ((j : ℤ) + 1) - aCoef m ((j : ℤ) + 1)) / ((j : ℝ) + 1) =
        ∑ j ∈ range (m + 1), aCoef (m + 1) ((j : ℤ) + 1) / ((j : ℝ) + 1) -
          ∑ j ∈ range (m + 1), aCoef m ((j : ℤ) + 1) / ((j : ℝ) + 1) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    rw [hsub, hsplit] at hinc
    have hH : Hn (m + 1) = Hn m + 1 / ((m : ℝ) + 1) := by
      unfold Hn; rw [Finset.sum_Icc_succ_top (by omega)]; push_cast; ring
    rw [hH, ih]
    linarith

/-- `eq:harmonic-identity`: `H_n = 2 ∑_{j≥1} a_n(j)/j` (same type as `Mixture.harmonic_identity`). -/
theorem harmonic_identity_printed (n : ℕ) :
    Hn n = 2 * ∑' j : ℕ, aCoef n ((j : ℤ) + 1) / ((j : ℝ) + 1) := by
  rw [tsum_aCoef_div_eq_sum]
  exact harmonic_identity_finite n

/-- `eq:section5-scalar-positive-budget` (same type as `Mixture.Rn_eq_positive`). -/
theorem Rn_eq_positive_printed (n : ℕ) :
    BecknerOnofri.V2.ThetaTail.Rn n = 3 / 5 * aCoef n 2 + 16 / 5 * aCoef n 3 +
      81 / 5 * ∑' j : ℕ, aCoef n ((j : ℤ) + 4) / ((j : ℝ) + 4) := by
  have hs := (summable_aCoef_div n).sum_add_tsum_nat_add 3
  have e1 : ∑' j : ℕ, aCoef n (((j + 3 : ℕ) : ℤ) + 1) / (((j + 3 : ℕ) : ℝ) + 1) =
      ∑' j : ℕ, aCoef n ((j : ℤ) + 4) / ((j : ℝ) + 4) := by
    refine tsum_congr (fun j => ?_)
    push_cast
    ring_nf
  have hH := harmonic_identity_printed n
  rw [← hs, e1] at hH
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hH
  norm_num at hH
  unfold BecknerOnofri.V2.ThetaTail.Rn
  have h1 : aCoef n 1 = aCoef n ((0 : ℕ) + 1) := by norm_num
  linarith [hH]

#print axioms harmonic_coefficient_recurrence
#print axioms harmonic_binomial_telescope
#print axioms harmonic_first_moment
#print axioms harmonic_sum_increment
#print axioms harmonic_identity_printed
#print axioms Rn_eq_positive_printed

end BecknerOnofri.V2.Reaudit.Mixtures
