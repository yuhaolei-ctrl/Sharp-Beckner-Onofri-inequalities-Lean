module

public import Legacy.BecknerOnofri.FiniteDifferenceDefs
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

/-! Analytic finite-difference facts on the actual closed cube. -/
noncomputable section
open Finset Set Filter
open scoped BigOperators Topology
namespace Legacy.BecknerOnofri.FiniteDifferences

/-- A family of actual coordinate derivatives, including boundary derivatives within the cube. -/
structure IsCoordinateJet {d : ℕ} (D : List (Fin d) → Space d → ℝ) : Prop where
  continuous : ∀ a, ContinuousOn (D a) (closedCube d)
  derivative : ∀ a i x, x ∈ closedCube d →
    HasDerivWithinAt (fun t => D a (Function.update x i t))
      (D (a ++ [i]) x) (Icc (0 : ℝ) 1) (x i)

theorem update_add {d : ℕ} (x y : Space d) (i : Fin d) (t : ℝ) :
    Function.update x i t + y = Function.update (x+y) i (t+y i) := by
  ext k
  by_cases hk : k = i
  · subst k; simp
  · simp [Function.update_of_ne hk]

theorem rectangularDifference_hasDerivAt {d : ℕ} (a : Index d) (h : ℝ)
    (f g : Space d → ℝ) (x : Space d) (i : Fin d)
    (hd : ∀ j : DifferenceGrid a,
      HasDerivAt (fun t => f (Function.update (x + fun k => ((j k).val : ℝ)*h) i t))
        (g (x + fun k => ((j k).val : ℝ)*h)) (x i + ((j i).val : ℝ)*h)) :
    HasDerivAt (fun t => rectangularDifference a h f (Function.update x i t))
      (rectangularDifference a h g x) (x i) := by
  unfold rectangularDifference
  apply HasDerivAt.fun_sum
  intro j hj
  have hjd := (hd j).comp (x i) ((hasDerivAt_id (x i)).add_const (((j i).val : ℝ)*h))
  simp only [mul_one] at hjd
  simpa only [update_add, Function.comp_def, id_eq] using hjd.const_mul
    (∏ i : Fin d, (-1 : ℝ) ^ (a i - (j i).val) * ((a i).choose (j i).val : ℝ))

theorem rectangularDifference_continuousOn_coordinate {d : ℕ}
    (a : Index d) (h : ℝ) (f : Space d → ℝ) (x : Space d) (i : Fin d)
    {s : Set ℝ} (hf : ContinuousOn f (closedCube d))
    (hx : ∀ t ∈ s, ∀ j : DifferenceGrid a,
      Function.update x i t + (fun k => ((j k).val : ℝ)*h) ∈ closedCube d) :
    ContinuousOn (fun t => rectangularDifference a h f (Function.update x i t)) s := by
  unfold rectangularDifference
  apply continuousOn_finsetSum
  intro j hj
  apply continuousOn_const.mul
  apply hf.comp
  · fun_prop
  · intro t ht
    exact hx t ht j


def directionIndex {d : ℕ} : List (Fin d) → Index d
  | [] => 0
  | i :: is => directionIndex is + Finsupp.single i 1

@[simp] theorem directionIndex_nil {d : ℕ} : directionIndex ([] : List (Fin d)) = 0 := rfl
@[simp] theorem directionIndex_cons {d : ℕ} (i : Fin d) (is : List (Fin d)) :
    directionIndex (i :: is) = directionIndex is + Finsupp.single i 1 := rfl

@[simp] theorem degree_directionIndex {d : ℕ} (is : List (Fin d)) :
    degree (directionIndex is) = is.length := by
  induction is with
  | nil => simp [degree]
  | cons i is ih => simp [degree, Finset.sum_add_distrib] at ih ⊢; exact ih

theorem IsCoordinateJet.prepend {d : ℕ} {D : List (Fin d) → Space d → ℝ}
    (hD : IsCoordinateJet D) (i : Fin d) : IsCoordinateJet (fun is => D (i :: is)) := by
  constructor
  · intro is; exact hD.continuous (i :: is)
  · intro is j x hx; exact hD.derivative (i :: is) j x hx

/-- Every vertex of the difference rectangle lies in the closed unit cube. -/
def Fits {d : ℕ} (a : Index d) (h : ℝ) (x : Space d) : Prop :=
  (∀ k, 0 ≤ x k) ∧ ∀ k, x k + (a k : ℝ)*h ≤ 1

theorem Fits.mem_cube {d : ℕ} {a : Index d} {h : ℝ} {x : Space d}
    (hf : Fits a h x) (hh : 0 ≤ h) : x ∈ closedCube d := by
  refine ⟨hf.1, fun k => ?_⟩
  change x k ≤ (1 : ℝ)
  have hp : 0 ≤ (a k : ℝ)*h := mul_nonneg (Nat.cast_nonneg _) hh
  linarith [hf.2 k]

theorem Fits.shift_mem_cube {d : ℕ} {a : Index d} {h : ℝ} {x : Space d}
    (hf : Fits a h x) (hh : 0 ≤ h) (j : DifferenceGrid a) :
    x + (fun k => ((j k).val : ℝ)*h) ∈ closedCube d := by
  constructor <;> intro k
  · exact add_nonneg (hf.1 k) (mul_nonneg (Nat.cast_nonneg _) hh)
  · have hja : ((j k).val : ℝ) ≤ (a k : ℝ) := by exact_mod_cast Nat.le_of_lt_succ (j k).isLt
    change x k + ((j k).val : ℝ)*h ≤ 1
    have hm := mul_le_mul_of_nonneg_right hja hh
    linarith [hf.2 k]

theorem Fits.update {d : ℕ} {a : Index d} {h : ℝ} {x : Space d}
    (i : Fin d) (hf : Fits (a + Finsupp.single i 1) h x) {t : ℝ}
    (ht : t ∈ Icc (x i) (x i+h)) : Fits a h (Function.update x i t) := by
  constructor <;> intro k
  · by_cases hk : k = i
    · subst k; simpa using (hf.1 i).trans ht.1
    · simpa [Function.update_of_ne hk] using hf.1 k
  · by_cases hk : k = i
    · subst k
      have hb := hf.2 i
      simp only [Finsupp.add_apply, Finsupp.single_eq_same, Nat.cast_add, Nat.cast_one] at hb
      simp only [Function.update_self]
      linarith [ht.2]
    · have hb := hf.2 k
      simpa [Finsupp.single_eq_of_ne hk, Function.update_of_ne hk] using hb

theorem Fits.shift_coordinate_interior {d : ℕ} {a : Index d} {h : ℝ} {x : Space d}
    (i : Fin d) (hf : Fits (a + Finsupp.single i 1) h x) (hh : 0 ≤ h) {t : ℝ}
    (ht : t ∈ Ioo (x i) (x i+h)) (j : DifferenceGrid a) :
    0 < t + ((j i).val : ℝ)*h ∧ t + ((j i).val : ℝ)*h < 1 := by
  have hja : ((j i).val : ℝ) ≤ (a i : ℝ) := by exact_mod_cast Nat.le_of_lt_succ (j i).isLt
  have hmul := mul_le_mul_of_nonneg_right hja hh
  have hb := hf.2 i
  simp only [Finsupp.add_apply, Finsupp.single_eq_same, Nat.cast_add, Nat.cast_one] at hb
  constructor
  · have hn := mul_nonneg (Nat.cast_nonneg (j i).val) hh
    linarith [hf.1 i, ht.1]
  · linarith [ht.2]

theorem coordinate_mvt {d : ℕ} {D : List (Fin d) → Space d → ℝ}
    (hD : IsCoordinateJet D) (a : Index d) (i : Fin d) {h : ℝ} (hh : 0 < h)
    (x : Space d) (hx : Fits (a + Finsupp.single i 1) h x) :
    ∃ t ∈ Ioo (x i) (x i+h),
      rectangularDifference a h (D [i]) (Function.update x i t) =
        (rectangularDifference a h (D []) (translate x i h) -
          rectangularDifference a h (D []) x) / h := by
  have hcont := rectangularDifference_continuousOn_coordinate a h (D []) x i
    (hD.continuous []) (fun t ht j => (hx.update i ht).shift_mem_cube hh.le j)
  have hderiv : ∀ t ∈ Ioo (x i) (x i+h),
      HasDerivAt (fun u => rectangularDifference a h (D []) (Function.update x i u))
        (rectangularDifference a h (D [i]) (Function.update x i t)) t := by
    intro t ht
    have hd := rectangularDifference_hasDerivAt a h (D []) (D [i])
      (Function.update x i t) i (fun j => ?_)
    · simpa only [Function.update_self, Function.update_idem] using hd
    · have hj := hD.derivative [] i
        (Function.update x i t + fun k => ((j k).val : ℝ)*h)
        ((hx.update i (mem_Icc_of_Ioo ht)).shift_mem_cube hh.le j)
      have hi := hx.shift_coordinate_interior i hh.le ht j
      simp only [List.nil_append, Pi.add_apply, Function.update_self] at hj
      simpa only [Function.update_self] using hj.hasDerivAt (Icc_mem_nhds hi.1 hi.2)
  obtain ⟨t, ht, he⟩ := exists_hasDerivAt_eq_slope
    (fun u => rectangularDifference a h (D []) (Function.update x i u))
    (fun u => rectangularDifference a h (D [i]) (Function.update x i u))
    (by linarith : x i < x i+h) hcont hderiv
  refine ⟨t, ht, ?_⟩
  have hu : Function.update x i (x i+h) = translate x i h := by
    ext k
    by_cases hk : k = i
    · subst k; simp
    · simp [Function.update_of_ne hk, translate_apply_ne _ _ _ _ hk]
  simpa only [hu, Function.update_eq_self, add_sub_cancel_left] using he

/-- One fixed ordering of the coordinate directions of a multiindex. -/
def directions {d : ℕ} (a : Index d) : List (Fin d) := a.toMultiset.toList

theorem directionIndex_apply {d : ℕ} (is : List (Fin d)) (i : Fin d) :
    directionIndex is i = is.count i := by
  induction is with
  | nil => simp
  | cons j js ih =>
    by_cases hij : i = j
    · subst j; simp [ih]
    · simp [ih, hij, Ne.symm hij]

@[simp] theorem directionIndex_directions {d : ℕ} (a : Index d) :
    directionIndex (directions a) = a := by
  ext i
  rw [directionIndex_apply]
  unfold directions
  rw [← Multiset.coe_count, Multiset.coe_toList, Finsupp.count_toMultiset]

@[simp] theorem length_directions {d : ℕ} (a : Index d) :
    (directions a).length = degree a := by
  rw [← degree_directionIndex, directionIndex_directions]

#print axioms rectangularDifference_hasDerivAt
#print axioms coordinate_mvt
#print axioms directionIndex_directions

end Legacy.BecknerOnofri.FiniteDifferences
