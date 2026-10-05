import Legacy.BecknerOnofri.MixedExponentialDerivatives

/-! The explicit Bell remainder is an actual multivariate polynomial with natural coefficients. -/
noncomputable section
open scoped BigOperators
namespace Legacy.BecknerOnofri.MixedExponentialDerivatives
open FiniteDifferences

/-- Variables are ordered nonempty direction blocks; only lower-order blocks occur in remainders. -/
def monomialPolynomial {d : ℕ} : Monomial d → MvPolynomial (Block d) ℕ
  | [] => 1
  | b :: bs => MvPolynomial.X b * monomialPolynomial bs

def termsPolynomial {d : ℕ} : Terms d → MvPolynomial (Block d) ℕ
  | [] => 0
  | q :: qs => monomialPolynomial q + termsPolynomial qs

def remainderPolynomial {d : ℕ} (is : List (Fin d)) : MvPolynomial (Block d) ℕ :=
  termsPolynomial (remainderTerms is)

theorem monomialPolynomial_eval {d : ℕ} (u : Space d → ℝ) (bs : Monomial d) (x : Space d) :
    MvPolynomial.eval₂ (Nat.castRingHom ℝ) (fun b => mixedPartial b u x) (monomialPolynomial bs) =
      evalMonomial u bs x := by
  induction bs with
  | nil => simp [monomialPolynomial, evalMonomial]
  | cons b bs ih => simp [monomialPolynomial, evalMonomial, ih]

theorem termsPolynomial_eval {d : ℕ} (u : Space d → ℝ) (ps : Terms d) (x : Space d) :
    MvPolynomial.eval₂ (Nat.castRingHom ℝ) (fun b => mixedPartial b u x) (termsPolynomial ps) =
      evalTerms u ps x := by
  induction ps with
  | nil => simp [termsPolynomial, evalTerms]
  | cons p ps ih => simp [termsPolynomial, evalTerms, monomialPolynomial_eval, ih]

theorem remainderPolynomial_eval {d : ℕ} (u : Space d → ℝ) (is : List (Fin d)) (x : Space d) :
    MvPolynomial.eval₂ (Nat.castRingHom ℝ) (fun b => mixedPartial b u x) (remainderPolynomial is) =
      evalTerms u (remainderTerms is) x :=
  termsPolynomial_eval u _ x

theorem remainderPolynomial_coefficient_nonneg {d : ℕ} (is : List (Fin d))
    (a : Block d →₀ ℕ) : 0 ≤ (((remainderPolynomial is).coeff a : ℕ) : ℝ) :=
  Nat.cast_nonneg _

theorem monomialPolynomial_vars {d : ℕ} (bs : Monomial d) {b : Block d}
    (hb : b ∈ (monomialPolynomial bs).vars) : b ∈ bs := by
  induction bs with
  | nil => simpa [monomialPolynomial] using hb
  | cons a bs ih =>
    have h := MvPolynomial.vars_mul (MvPolynomial.X a) (monomialPolynomial bs) hb
    simp only [MvPolynomial.vars_X, Finset.mem_union, Finset.mem_singleton] at h
    rcases h with rfl | h
    · simp
    · exact List.mem_cons_of_mem _ (ih h)

theorem termsPolynomial_vars {d : ℕ} (ps : Terms d) {b : Block d}
    (hb : b ∈ (termsPolynomial ps).vars) : ∃ q ∈ ps, b ∈ q := by
  induction ps with
  | nil => simpa [termsPolynomial] using hb
  | cons p ps ih =>
    have h := MvPolynomial.vars_add_subset (monomialPolynomial p) (termsPolynomial ps) hb
    simp only [Finset.mem_union] at h
    rcases h with h | h
    · exact ⟨p, by simp, monomialPolynomial_vars p h⟩
    · obtain ⟨q, hq, hb⟩ := ih h
      exact ⟨q, by simp [hq], hb⟩

/-- Every variable occurring in the actual Bell polynomial has strictly lower positive order. -/
theorem remainderPolynomial_vars_lower_order {d : ℕ} (is : List (Fin d)) {b : Block d}
    (hb : b ∈ (remainderPolynomial is).vars) : 0 < b.length ∧ b.length < is.length := by
  obtain ⟨q, hq, hb⟩ := termsPolynomial_vars (remainderTerms is) hb
  exact remainderTerms_admissible is q hq b hb

/-- The non-leading part of the genuine derivative is exp(u) times an actual
natural-coefficient polynomial evaluated on the genuine derivative family. -/
theorem remainder_eq_polynomial {d : ℕ} (u : Space d → ℝ) (is : List (Fin d)) (x : Space d) :
    remainder u is x = Real.exp (u x) *
      MvPolynomial.eval₂ (Nat.castRingHom ℝ) (fun b => mixedPartial b u x) (remainderPolynomial is) := by
  rw [remainderPolynomial_eval]
  rfl

#print axioms remainderPolynomial_eval
#print axioms remainder_eq_polynomial
#print axioms remainderPolynomial_vars_lower_order
end Legacy.BecknerOnofri.MixedExponentialDerivatives
