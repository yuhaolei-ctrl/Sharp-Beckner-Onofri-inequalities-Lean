module

public import BecknerOnofri.ElevenShellArray
public import BecknerOnofri.TruncatedConvolution
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-!
# The lattice shell counts in dimension eleven

`stage11` lists the numbers of `k ∈ [-10, 10]^{11}` with `|k|² = q` for `q ≤ 100`. It is
computed by the structural list convolution of `BecknerOnofri.TruncatedConvolution`, which the
kernel evaluates directly, and `stage11_correct` identifies it with `shellArray 11`.
-/

namespace BecknerOnofri.HighDim.Eleven.Shell

open Polynomial BecknerOnofri.TruncatedConvolution

/-- The terms `(j², 1)`, `-10 ≤ j ≤ 10`, of the one-dimensional theta polynomial. -/
def thetaBase : List (ℕ × ℕ) := (List.finRange 21).map fun j => (coordinateRadius j, 1)

/-- The coefficients of `z^q`, `q ≤ 100`, of the eleventh power of the theta polynomial.
Irreducible for elaboration, so that tactics do not evaluate it; the kernel still does. -/
@[irreducible] def stage11 : Array ℕ := (powBase 101 (thetaBase.filter fun ec => ec.1 < 101) 11).toArray

lemma termPolynomial_thetaBase : termPolynomial thetaBase = thetaPolynomial := by
  simp only [termPolynomial, thetaBase, thetaPolynomial, List.map_map, Function.comp_def,
    monomial_one_right_eq_X_pow, Fin.sum_univ_def]

lemma shellArray_size (d : ℕ) : (shellArray d).size = 101 := by
  cases d with
  | zero => exact initialArray_size
  | succ d => exact convolution_size _

theorem stage11_eq :
    stage11 = (powBase 101 (thetaBase.filter fun ec => ec.1 < 101) 11).toArray := by
  unfold stage11; rfl

theorem stage11_correct : shellArray 11 = stage11 := by
  obtain ⟨hl, hc⟩ := powBase_spec 101 thetaBase 11
  rw [stage11_eq]
  apply Array.ext
  · simp only [shellArray_size, List.size_toArray, hl]
  · intro i h1 h2
    have hi : i < 101 := by rwa [shellArray_size] at h1
    have h := shellArray_coeff 11 hi
    rw [getElem!_pos (shellArray 11) i h1] at h
    rw [h, ← termPolynomial_thetaBase, ← hc i hi]
    simp only [List.getElem_toArray]
    exact List.getD_eq_getElem _ _ (by rw [hl]; exact hi)

end BecknerOnofri.HighDim.Eleven.Shell
