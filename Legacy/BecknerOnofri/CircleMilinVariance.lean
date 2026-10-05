import Legacy.BecknerOnofri.CircleMilinCoefficientCap

noncomputable section
open scoped BigOperators
namespace Legacy.BecknerOnofri.CircleMilin

private theorem reciprocal_prod_cancel (a : ℕ → ℂ) (xs : List ℕ)
    (hp : ∀ j ∈ xs, 0 < j) :
    (((xs.map (fun j : ℕ => (j : ℝ)⁻¹)).prod : ℝ) : ℂ) * wordValue a xs = (xs.map a).prod := by
  induction xs with
  | nil => simp [wordValue]
  | cons j xs ih =>
    have hj : (j : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (hp j (by simp)))
    have hi := ih (fun k hk => hp k (by simp [hk]))
    simp only [List.map_cons,List.prod_cons,Complex.ofReal_mul,Complex.ofReal_inv,
      Complex.ofReal_natCast,wordValue] at *
    calc
      _ = (j : ℂ)⁻¹ * (j : ℂ) * a j *
        (((xs.map (fun j : ℕ => (j : ℝ)⁻¹)).prod : ℝ) : ℂ) *
        (xs.map (fun j : ℕ => (j : ℂ) * a j)).prod := by ring
      _ = _ := by rw [inv_mul_cancel₀ hj]; simpa [mul_assoc] using congrArg (a j * ·) hi

private theorem weighted_prod_norm (a : ℕ → ℂ) (xs : List ℕ)
    (hp : ∀ j ∈ xs, 0 < j) :
    (xs.map (fun j : ℕ => (j : ℝ)*‖a j‖^2)).prod =
      (xs.map (fun j : ℕ => (j : ℝ)⁻¹)).prod * ‖wordValue a xs‖^2 := by
  induction xs with
  | nil => simp [wordValue]
  | cons j xs ih =>
    have hj : (j : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (hp j (by simp)))
    have hi := ih (fun k hk => hp k (by simp [hk]))
    simp only [List.map_cons,List.prod_cons,wordValue] at *
    rw [hi,norm_mul,norm_mul,Complex.norm_natCast]
    field_simp

/-- The precise scalar/complex factors used in coefficient Cauchy--Schwarz. -/
theorem complexWord_eq (a : ℕ → ℂ) {n : ℕ} {xs : List ℕ} (hx : xs ∈ words n) :
    complexWord a xs = (qWord xs : ℂ) * wordValue a xs := by
  unfold complexWord qWord
  rw [Complex.ofReal_mul,Complex.ofReal_inv,Complex.ofReal_natCast,mul_assoc,
    reciprocal_prod_cancel a xs ((mem_words_iff _ _).mp hx).1]

theorem pWord_eq (a : ℕ → ℂ) {n : ℕ} {xs : List ℕ} (hx : xs ∈ words n) :
    pWord a xs = qWord xs * ‖wordValue a xs‖^2 := by
  unfold pWord qWord
  rw [weighted_prod_norm a xs ((mem_words_iff _ _).mp hx).1]
  ring

private theorem weighted_variance {ι : Type*} (s : Finset ι) (q : ι → ℝ) (v : ι → ℂ) :
    let b := ∑ i ∈ s, (q i : ℂ) * v i
    (∑ i ∈ s, q i*‖v i-b‖^2) =
      (∑ i ∈ s, q i*‖v i‖^2)-2*‖b‖^2+(∑ i ∈ s,q i)*‖b‖^2 := by
  dsimp
  let b := ∑ i ∈ s, (q i : ℂ) * v i
  have hbre : b.re = ∑ i ∈ s,q i*(v i).re := by simp [b,Complex.mul_re]
  have hbim : b.im = ∑ i ∈ s,q i*(v i).im := by simp [b,Complex.mul_im]
  change (∑ i ∈ s,q i*‖v i-b‖^2) = _-2*‖b‖^2+_*‖b‖^2
  calc
    _ = ∑ i ∈ s, (q i*‖v i‖^2 - 2*b.re*(q i*(v i).re) -
        2*b.im*(q i*(v i).im) + q i*‖b‖^2) := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [Complex.sq_norm,Complex.normSq_apply,Complex.sub_re,Complex.sub_im]
      ring
    _ = _ := by
      rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.sum_sub_distrib,
        ← Finset.mul_sum,← Finset.mul_sum,← Finset.sum_mul,← hbre,← hbim]
      simp only [Complex.sq_norm,Complex.normSq_apply]
      ring

/-- The full squared-distance deficit is retained. Its nonnegativity gives
Milin's coefficient bound; zero deficit forces every word to have one value. -/
theorem variance_le_gap (a : ℕ → ℂ) (n : ℕ) :
    (∑ xs ∈ words n,qWord xs*‖wordValue a xs-bCoeff a n‖^2) ≤
      pCoeff a n-‖bCoeff a n‖^2 := by
  have hb : bCoeff a n = ∑ xs ∈ words n,(qWord xs : ℂ)*wordValue a xs := by
    unfold bCoeff
    apply Finset.sum_congr rfl
    exact fun xs hx => complexWord_eq a hx
  have hp : pCoeff a n = ∑ xs ∈ words n,qWord xs*‖wordValue a xs‖^2 := by
    unfold pCoeff
    apply Finset.sum_congr rfl
    exact fun xs hx => pWord_eq a hx
  have hv := weighted_variance (words n) qWord (wordValue a)
  rw [← hb,← hp] at hv
  have hq := qCoeff_le_one n
  have hn := sq_nonneg ‖bCoeff a n‖
  change (∑ xs ∈ words n,qWord xs) ≤ 1 at hq
  nlinarith

theorem coefficient_sq_le (a : ℕ → ℂ) (n : ℕ) : ‖bCoeff a n‖^2 ≤ pCoeff a n := by
  have hv := variance_le_gap a n
  have hn : 0 ≤ ∑ xs ∈ words n,qWord xs*‖wordValue a xs-bCoeff a n‖^2 := by
    apply Finset.sum_nonneg
    intro xs hx
    exact mul_nonneg (qWord_pos hx).le (sq_nonneg _)
  linarith

theorem wordValue_eq_of_coefficient_equality (a : ℕ → ℂ) (n : ℕ)
    (he : pCoeff a n = ‖bCoeff a n‖^2) {xs : List ℕ} (hx : xs ∈ words n) :
    wordValue a xs = bCoeff a n := by
  have hv := variance_le_gap a n
  rw [he,sub_self] at hv
  have hn : ∀ ys ∈ words n,0 ≤ qWord ys*‖wordValue a ys-bCoeff a n‖^2 := by
    intro ys hy
    exact mul_nonneg (qWord_pos hy).le (sq_nonneg _)
  have heq : ∑ ys ∈ words n,qWord ys*‖wordValue a ys-bCoeff a n‖^2 = 0 :=
    le_antisymm hv (Finset.sum_nonneg hn)
  have ht := (Finset.sum_eq_zero_iff_of_nonneg hn).mp heq xs hx
  have hnz := (mul_eq_zero.mp ht).resolve_left (ne_of_gt (qWord_pos hx))
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hnz))

/-- Comparing the one-letter and all-ones words is the exact equality
recurrence; no Euler equation or equality classification is assumed. -/
theorem coefficient_equality_recurrence (a : ℕ → ℂ) {n : ℕ} (hn : 0 < n)
    (he : pCoeff a n = ‖bCoeff a n‖^2) : (n : ℂ)*a n = a 1^n := by
  have hs := wordValue_eq_of_coefficient_equality a n he (singleton_mem_words hn)
  have hr := wordValue_eq_of_coefficient_equality a n he (replicate_mem_words n)
  simpa [wordValue] using hs.trans hr.symm

end Legacy.BecknerOnofri.CircleMilin
