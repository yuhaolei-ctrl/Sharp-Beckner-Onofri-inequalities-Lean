module

public import BecknerOnofri.HighDimRectangles
public import Legacy.D10.BinomialCorrelated

@[expose] public section

/-!
Exact finite random-rectangle representation of normalized cosine-power Fourier
coefficients. The radius law is the difference of successive coefficients.
-/
noncomputable section
set_option autoImplicit false
open scoped BigOperators
open Finset

namespace BecknerOnofri.RandomRectangles
open RectangleLattice Legacy.D10

@[simp] theorem coeff_zero (n : ℕ) : binomialCoeffReal n 0 = 1 := by
  simp [binomialCoeffReal]

theorem coeff_nonneg (n j : ℕ) : 0 ≤ binomialCoeffReal n j := by
  unfold binomialCoeffReal
  exact_mod_cast binomialCoeff_nonneg n j

theorem coeff_eq_zero {n j : ℕ} (hj : n < j) : binomialCoeffReal n j = 0 := by
  simp [binomialCoeffReal, binomialCoeff_eq_zero hj]

theorem coeff_antitone (n : ℕ) : Antitone (binomialCoeffReal n) := by
  apply antitone_nat_of_succ_le
  intro j
  by_cases hj : j ≤ n
  · have hstep : ((n : ℝ) + j + 1) * binomialCoeffReal n (j + 1) =
        ((n : ℝ) - j) * binomialCoeffReal n j := by
      have h := congrArg (fun x : ℚ => (x : ℝ)) (binomialCoeff_step n j hj)
      simpa only [Rat.cast_mul, Rat.cast_add, Rat.cast_sub, Rat.cast_natCast,
        Rat.cast_one, binomialCoeffReal] using h
    have hj0 := coeff_nonneg n j
    have hj1 := coeff_nonneg n (j+1)
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    have hjpos : (0 : ℝ) ≤ j := Nat.cast_nonneg _
    nlinarith
  · rw [coeff_eq_zero (by omega : n < j), coeff_eq_zero (by omega : n < j+1)]

/-- Probability of radius r for the normalized cosine power of index n. -/
def radiusLaw (n r : ℕ) : ℝ := binomialCoeffReal n r - binomialCoeffReal n (r+1)

theorem radiusLaw_nonneg (n r : ℕ) : 0 ≤ radiusLaw n r :=
  sub_nonneg.mpr (coeff_antitone n (Nat.le_succ r))

theorem sum_radiusLaw (n : ℕ) : ∑ r ∈ range (n+1), radiusLaw n r = 1 := by
  unfold radiusLaw
  rw [sum_range_sub']
  simp [coeff_eq_zero (by omega : n < n+1)]

theorem filtered_telescope (b : ℕ → ℝ) (j n : ℕ) :
    (∑ r ∈ range n, if j ≤ r then b r - b (r+1) else 0) =
      if j < n then b j - b n else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih]
    by_cases hj : j < n
    · simp only [hj, if_true, show j ≤ n by omega, show j < n+1 by omega]
      ring
    · by_cases he : j = n
      · subst j
        simp
      · simp [hj, show ¬ j ≤ n by omega, show ¬ j < n+1 by omega]

/-- The survival function of the radius law is exactly the Fourier coefficient. -/
theorem radius_survival (n j : ℕ) :
    (∑ r ∈ range (n+1), if j ≤ r then radiusLaw n r else 0) =
      binomialCoeffReal n j := by
  unfold radiusLaw
  rw [filtered_telescope]
  by_cases hj : j < n+1
  · simp [hj, coeff_eq_zero (by omega : n < n+1)]
  · simp [hj, coeff_eq_zero (by omega : n < j)]

/-- Conditional independent radii; the latent component itself may be correlated. -/
def rectangleLaw {d : ℕ} (N R : Fin d → ℕ) : ℝ := ∏ i, radiusLaw (N i) (R i)

theorem rectangleLaw_nonneg {d : ℕ} (N R : Fin d → ℕ) : 0 ≤ rectangleLaw N R :=
  prod_nonneg (fun _ _ => radiusLaw_nonneg _ _)

theorem sum_rectangleLaw {d : ℕ} (N : Fin d → ℕ) :
    (∑ R ∈ latentBox N, rectangleLaw N R) = 1 := by
  unfold rectangleLaw latentBox
  rw [← prod_univ_sum]
  simp only [sum_radiusLaw, prod_const_one]

theorem mem_box_natAbs {d : ℕ} (R : Fin d → ℕ) (k : Lattice d) :
    k ∈ box R ↔ ∀ i, (k i).natAbs ≤ R i := by
  rw [mem_box]
  constructor
  · intro h i
    have hi := h i
    omega
  · intro h i
    have hi := h i
    omega

/-- Exact rectangle-survival identity for every integer Fourier vector. -/
theorem rectangle_survival {d : ℕ} (N : Fin d → ℕ) (k : Lattice d) :
    (∑ R ∈ latentBox N, if k ∈ box R then rectangleLaw N R else 0) =
      binomialProduct N (fun i => (k i).natAbs) := by
  have he (R : Fin d → ℕ) :
      (if k ∈ box R then rectangleLaw N R else 0) =
        ∏ i, if (k i).natAbs ≤ R i then radiusLaw (N i) (R i) else 0 := by
    classical
    simp only [mem_box_natAbs]
    by_cases h : ∀ i, (k i).natAbs ≤ R i
    · simp [h, rectangleLaw]
    · rw [if_neg h]
      obtain ⟨i, hi⟩ := not_forall.mp h
      exact (prod_eq_zero (mem_univ i) (if_neg hi)).symm
  simp_rw [he]
  unfold latentBox binomialProduct
  rw [← prod_univ_sum (fun i => range (N i+1))
    (fun i r => if (k i).natAbs ≤ r then radiusLaw (N i) r else 0)]
  simp only [radius_survival]


theorem rectangle_subset {d : ℕ} {N R : Fin d → ℕ} (hR : R ∈ latentBox N) :
    box R ⊆ box N := by
  intro k hk
  rw [mem_box_natAbs] at hk ⊢
  have hr : ∀ i, R i < N i + 1 := by
    simpa [latentBox, Fintype.mem_piFinset] using hR
  intro i
  exact (hk i).trans (by have h := hr i; omega)

/-- Every finite weighted component sum is the exact average over integer rectangles. -/
theorem sum_component_rectangles {d : ℕ} (N : Fin d → ℕ) (f : Lattice d → ℝ) :
    (∑ k ∈ box N, f k * binomialProduct N (fun i => (k i).natAbs)) =
      ∑ R ∈ latentBox N, rectangleLaw N R * (∑ k ∈ box R, f k) := by
  classical
  simp_rw [← rectangle_survival N, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro R hR
  have hsub := rectangle_subset hR
  have hfilter : (box N).filter (fun k => k ∈ box R) = box R := by
    ext k
    simp only [mem_filter, and_iff_right_iff_imp]
    exact fun hk => hsub hk
  calc
    _ = rectangleLaw N R * (∑ k ∈ box N, if k ∈ box R then f k else 0) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro k hk
      split_ifs <;> ring
    _ = _ := by rw [← sum_filter, hfilter, mul_sum]

def componentCoeff {d : ℕ} (N : Fin d → ℕ) (k : Lattice d) : ℝ :=
  binomialProduct N (fun i => (k i).natAbs)

theorem componentCoeff_nonneg {d : ℕ} (N : Fin d → ℕ) (k : Lattice d) :
    0 ≤ componentCoeff N k := by
  unfold componentCoeff binomialProduct
  exact prod_nonneg (fun i _ => coeff_nonneg _ _)

theorem componentCoeff_eq_zero {d : ℕ} {N : Fin d → ℕ} {k : Lattice d}
    (hk : k ∉ box N) : componentCoeff N k = 0 := by
  classical
  rw [mem_box_natAbs] at hk
  push Not at hk
  obtain ⟨i, hi⟩ := hk
  exact prod_eq_zero (mem_univ i) (coeff_eq_zero hi)

theorem summable_weighted_component {d : ℕ} (N : Fin d → ℕ) (f : Lattice d → ℝ) :
    Summable (fun k => f k * componentCoeff N k) := by
  apply summable_of_ne_finset_zero (s := box N)
  intro k hk
  rw [componentCoeff_eq_zero hk, mul_zero]

theorem tsum_component_rectangles {d : ℕ} (N : Fin d → ℕ) (f : Lattice d → ℝ) :
    (∑' k, f k * componentCoeff N k) =
      ∑ R ∈ latentBox N, rectangleLaw N R * (∑ k ∈ box R, f k) := by
  rw [tsum_eq_sum (s := box N) (fun k hk => by rw [componentCoeff_eq_zero hk, mul_zero])]
  exact sum_component_rectangles N f

/-- Unnormalized inverse-power Fourier energy of one component coefficient. -/
def componentEnergy {d : ℕ} (p : ℝ) (N : Fin d → ℕ) : ℝ :=
  ∑' k, weight p k * componentCoeff N k

/-- Its deleted-coordinate energy, in the original ambient lattice. -/
def componentDeletion {d : ℕ} (p : ℝ) (N : Fin d → ℕ) (i : Fin d) : ℝ :=
  ∑' k, (if k i = 0 then weight p k else 0) * componentCoeff N k

theorem componentEnergy_rectangles {d : ℕ} {p : ℝ} (hp : 0 < p) (N : Fin d → ℕ) :
    componentEnergy p N = ∑ R ∈ latentBox N, rectangleLaw N R * latticeSum p R := by
  rw [componentEnergy, tsum_component_rectangles]
  simp_rw [← latticeSum_eq_sum_box hp]

theorem componentDeletion_rectangles {d : ℕ} {p : ℝ} (hp : 0 < p)
    (N : Fin d → ℕ) (i : Fin d) :
    componentDeletion p N i = ∑ R ∈ latentBox N,
      rectangleLaw N R * latticeSum p (Function.update R i 0) := by
  rw [componentDeletion, tsum_component_rectangles]
  apply sum_congr rfl
  intro R hR
  congr 1
  rw [latticeSum_eq_sum_box hp, box_delete, sum_filter]

/-- Exact component energy transfer; positivity is used only to average the
proved rectangle inequality. -/
theorem component_comparison {d : ℕ} (hd : 13 ≤ d) (N : Fin d → ℕ) :
    componentEnergy (d : ℝ) N ≤ (1 / ((d : ℝ)-1)) *
      ∑ i : Fin d, componentDeletion ((d : ℝ)-1) N i := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hdm : (0 : ℝ) < (d : ℝ)-1 := by
    have : (13 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  rw [componentEnergy_rectangles hdpos]
  simp_rw [componentDeletion_rectangles hdm]
  rw [sum_comm]
  rw [mul_sum]
  apply sum_le_sum
  intro R hR
  calc
    _ ≤ rectangleLaw N R * ((1 / ((d : ℝ)-1)) *
        ∑ i : Fin d, latticeSum ((d : ℝ)-1) (Function.update R i 0)) :=
      mul_le_mul_of_nonneg_left (rectangle_comparison hd R) (rectangleLaw_nonneg N R)
    _ = _ := by rw [← mul_sum]; ring

#print axioms rectangle_survival
#print axioms component_comparison

end BecknerOnofri.RandomRectangles
