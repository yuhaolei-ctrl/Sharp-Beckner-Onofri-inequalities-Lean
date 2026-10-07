module

public import Legacy.D10.FiniteScalarSemantics
public import BecknerOnofri.TruncatedConvolution

@[expose] public section

/-!
# The truncated shell polynomial as a kernel-computable list

`shellArray n r` lists the coefficients of `(∑_{k ≤ 8} w_k C(2n, n-k) z^{k²})^r` below
`z^65`. This file computes the same coefficients by the structural list convolution of
`BecknerOnofri.TruncatedConvolution`, which the Lean kernel evaluates quickly, and proves that
the two agree (`shellArray_eq_shellList`). The finite certificates of Sections 3 and 4 rewrite
with this identity before `decide +kernel`.
-/

namespace Legacy.D10.FiniteScalar

open Polynomial BecknerOnofri.TruncatedConvolution

/-- The terms `(k², w_k C(2n, n-k))`, `0 ≤ k ≤ 8`, of the truncated radial polynomial. -/
def shellBase (n : Nat) : List (Nat × Nat) :=
  (List.range 9).map fun k => (k * k, radialWeight n k)

/-- The coefficients of `z^q`, `q < 65`, in the `r`-th power of the truncated radial
polynomial. -/
def shellList (n r : Nat) : List Nat :=
  powBase 65 ((shellBase n).filter fun ec => ec.1 < 65) r

theorem termPolynomial_shellBase (n : Nat) :
    termPolynomial (shellBase n) = truncatedRadialPolynomial n := by
  simp only [termPolynomial, shellBase, truncatedRadialPolynomial,
    List.range_succ, List.range_zero, List.map_append, List.map_cons,
    List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, Finset.sum_range_succ,
    Finset.sum_range_zero, List.nil_append]
  simp only [radialRow_get _ (by norm_num : (0 : Nat) < 9), radialRow_get _ (by norm_num : 1 < 9),
    radialRow_get _ (by norm_num : 2 < 9), radialRow_get _ (by norm_num : 3 < 9),
    radialRow_get _ (by norm_num : 4 < 9), radialRow_get _ (by norm_num : 5 < 9),
    radialRow_get _ (by norm_num : 6 < 9), radialRow_get _ (by norm_num : 7 < 9),
    radialRow_get _ (by norm_num : 8 < 9), add_zero, zero_add, add_assoc]

theorem shellArray_size (n r : Nat) : (shellArray n r).size = 65 := by
  cases r with
  | zero => exact initialCoefficients_size
  | succ r => rw [shellArray_succ, convolutionStep_size]

theorem shellArray_eq_shellList (n r : Nat) : shellArray n r = (shellList n r).toArray := by
  obtain ⟨hl, hc⟩ := powBase_spec 65 (shellBase n) r
  apply Array.ext
  · simp only [shellArray_size, List.size_toArray, shellList, hl]
  · intro i h1 h2
    have hi : i < 65 := by rwa [shellArray_size] at h1
    have h := shellArray_coeff n r hi
    rw [getElem!_pos (shellArray n r) i h1] at h
    rw [h, List.getElem_toArray, ← termPolynomial_shellBase, ← hc i hi, List.getD_eq_getElem]
    rfl

end Legacy.D10.FiniteScalar
