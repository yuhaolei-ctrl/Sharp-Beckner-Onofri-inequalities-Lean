module

public import Legacy.BecknerOnofri.FiniteDifferenceDefs

@[expose] public section

/-! Explicit finite Bell monomials, with direction order retained and nonnegative coefficients. -/
noncomputable section
namespace Legacy.BecknerOnofri.MixedExponentialDerivatives

abbrev Block (d : ℕ) := List (Fin d)
abbrev Monomial (d : ℕ) := List (Block d)
abbrev Terms (d : ℕ) := List (Monomial d)

/-- Leibniz differentiation appends the new direction to exactly one factor. -/
def differentiateMonomial {d : ℕ} (i : Fin d) : Monomial d → Terms d
  | [] => []
  | b :: bs => ((b ++ [i]) :: bs) :: (differentiateMonomial i bs).map (fun q => b :: q)

/-- Differentiating exp(u) times a monomial either adds a one-direction factor
or differentiates one existing factor. Repeated terms encode positive integer coefficients. -/
def stepTerms {d : ℕ} (i : Fin d) (ps : Terms d) : Terms d :=
  ps.flatMap (fun bs => ([i] :: bs) :: differentiateMonomial i bs)

/-- Reverse-list recursion represents differentiation in the original left-to-right order. -/
def remainderTermsRev {d : ℕ} : List (Fin d) → Terms d
  | [] => []
  | i :: is => if is = [] then [] else [[i], is.reverse] :: stepTerms i (remainderTermsRev is)

def remainderTerms {d : ℕ} (is : List (Fin d)) : Terms d := remainderTermsRev is.reverse

@[simp] theorem remainderTerms_nil {d : ℕ} : remainderTerms ([] : List (Fin d)) = [] := rfl
@[simp] theorem remainderTerms_single {d : ℕ} (i : Fin d) : remainderTerms [i] = [] := by
  simp [remainderTerms, remainderTermsRev]

theorem remainderTerms_snoc {d : ℕ} (is : List (Fin d)) (i : Fin d) (his : is ≠ []) :
    remainderTerms (is ++ [i]) = [[i], is] :: stepTerms i (remainderTerms is) := by
  have hr : is.reverse ≠ [] := by simpa using his
  simp [remainderTerms, remainderTermsRev, hr]

/-- Every factor uses at least one and fewer than n actual coordinate derivatives. -/
def Admissible {d : ℕ} (n : ℕ) (bs : Monomial d) : Prop :=
  ∀ b ∈ bs, 0 < b.length ∧ b.length < n

theorem admissible_mono {d n m : ℕ} {bs : Monomial d} (h : Admissible n bs) (hn : n ≤ m) :
    Admissible m bs := fun b hb => ⟨(h b hb).1, (h b hb).2.trans_le hn⟩

theorem differentiateMonomial_admissible {d : ℕ} (i : Fin d) {n : ℕ} {bs : Monomial d}
    (hbs : Admissible n bs) :
    ∀ q ∈ differentiateMonomial i bs, Admissible (n+1) q := by
  induction bs with
  | nil => simp [differentiateMonomial]
  | cons b bs ih =>
    have hb := hbs b (by simp)
    have ht : Admissible n bs := fun q hq => hbs q (by simp [hq])
    intro q hq
    simp only [differentiateMonomial, List.mem_cons, List.mem_map] at hq
    rcases hq with rfl | ⟨r, hr, rfl⟩
    · intro a ha
      simp only [List.mem_cons] at ha
      rcases ha with rfl | ha
      · simp only [List.length_append, List.length_singleton]
        omega
      · exact (admissible_mono ht (Nat.le_succ n)) a ha
    · intro a ha
      simp only [List.mem_cons] at ha
      rcases ha with rfl | ha
      · exact ⟨hb.1, hb.2.trans (Nat.lt_succ_self n)⟩
      · exact ih ht r hr a ha

theorem stepTerms_admissible {d n : ℕ} (i : Fin d) (hn : 0 < n) {ps : Terms d}
    (hps : ∀ q ∈ ps, Admissible n q) :
    ∀ q ∈ stepTerms i ps, Admissible (n+1) q := by
  intro q hq
  obtain ⟨bs, hbs, hq⟩ := List.mem_flatMap.mp hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · intro a ha
    simp only [List.mem_cons] at ha
    rcases ha with rfl | ha
    · simp only [List.length_singleton]
      omega
    · exact admissible_mono (hps bs hbs) (Nat.le_succ n) a ha
  · exact differentiateMonomial_admissible i (hps bs hbs) q hq

/-- The Bell remainder contains only strictly lower-order nonempty derivative factors. -/
theorem remainderTerms_admissible {d : ℕ} (is : List (Fin d)) :
    ∀ q ∈ remainderTerms is, Admissible is.length q := by
  induction is using List.reverseRecOn with
  | nil => simp
  | append_singleton is i ih =>
    by_cases his : is = []
    · subst is
      simp
    · rw [remainderTerms_snoc is i his]
      intro q hq
      simp only [List.mem_cons] at hq
      rcases hq with rfl | hq
      · have hn : 0 < is.length := List.length_pos_of_ne_nil his
        intro a ha
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl <;> simp only [List.length_append, List.length_singleton] <;> omega
      · simpa only [List.length_append, List.length_singleton] using
          stepTerms_admissible i (List.length_pos_of_ne_nil his) ih q hq

end Legacy.BecknerOnofri.MixedExponentialDerivatives
