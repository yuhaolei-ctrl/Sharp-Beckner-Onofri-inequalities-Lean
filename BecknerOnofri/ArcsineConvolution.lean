module

public import BecknerOnofri.ArcsineProductBins
public import Mathlib.Algebra.Polynomial.BigOperators

@[expose] public section

/-! Exact convolution probabilities, as coefficients of a polynomial power.
This supplies the mathematical meaning of the finite 12-fold bin convolution. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped BigOperators
namespace BecknerOnofri.HighDim.ArcsineProductBins
open ArcsineCircle

def binPolynomial (N : ℕ) : Polynomial ℝ :=
  ∑ j : Fin N,Polynomial.monomial j.val (binMass N j.val)

def convolution (N d j : ℕ) : ℝ := ((binPolynomial N)^d).coeff j

def sumCell (N d j : ℕ) : Set (Torus d) :=
  ⋃ b : Fin d → Fin N, if indexSum b=j then cell b else ∅

theorem product_monomial {ι : Type*} (s : Finset ι) (n : ι → ℕ) (a : ι → ℝ) :
    (∏ i∈s,Polynomial.monomial (n i) (a i))=
      Polynomial.monomial (∑ i∈s,n i) (∏ i∈s,a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp [hi,ih,Polynomial.monomial_mul_monomial]

/-- Finite products of genuine bin masses expand the exact polynomial power. -/
theorem binPolynomial_power (N d : ℕ) :
    (binPolynomial N)^d=
      ∑ b : Fin d → Fin N,Polynomial.monomial (indexSum b) (cellMass b) := by
  classical
  rw [binPolynomial,Fintype.sum_pow]
  apply Finset.sum_congr rfl
  intro b _
  exact product_monomial Finset.univ (fun i => (b i).val) (fun i => binMass N (b i).val)

theorem convolution_eq_sum (N d j : ℕ) :
    convolution N d j=∑ b : Fin d → Fin N,if indexSum b=j then cellMass b else 0 := by
  simp only [convolution,binPolynomial_power,Polynomial.finsetSum_coeff,Polynomial.coeff_monomial]

theorem convolution_nonneg {N : ℕ} (hN : 0<N) (d j : ℕ) : 0≤convolution N d j := by
  rw [convolution_eq_sum]
  apply Finset.sum_nonneg
  intro b _
  split_ifs <;> first | exact cellMass_nonneg hN b | exact le_rfl

theorem sumCell_measurable (N d j : ℕ) : MeasurableSet (sumCell N d j) := by
  apply MeasurableSet.iUnion
  intro b
  split_ifs <;> first | exact cell_measurable b | exact MeasurableSet.empty

/-- Actual sum-bin probabilities equal the coefficients of the d-fold convolution. -/
theorem sumCell_measure {N : ℕ} (hN : 0<N) (d j : ℕ) :
    (torusMeasure d).real (sumCell N d j)=convolution N d j := by
  classical
  unfold sumCell
  rw [measureReal_iUnion_fintype]
  · rw [convolution_eq_sum]
    apply Finset.sum_congr rfl
    intro b _
    split_ifs <;> simp only [cell_measure hN,measureReal_empty]
  · intro a b hab
    dsimp only [Function.onFun]
    split_ifs <;> first | exact cells_disjoint hN hab | simp
  · intro b
    split_ifs <;> first | exact cell_measurable b | exact MeasurableSet.empty

/-- The executable convolution recurrence is the ordinary finite Cauchy product. -/
theorem convolution_succ (N d j : ℕ) :
    convolution N (d+1) j=
      ∑ ij∈Finset.antidiagonal j,convolution N d ij.1*convolution N 1 ij.2 := by
  simp only [convolution,pow_one]
  rw [pow_succ,Polynomial.coeff_mul]

theorem indexSum_le {N d : ℕ} (b : Fin d → Fin N) : indexSum b≤d*(N-1) := by
  calc
    _ ≤ ∑ _i : Fin d,(N-1) := Finset.sum_le_sum (fun i _ => Nat.le_sub_one_of_lt (b i).isLt)
    _ = _ := by simp

theorem convolution_zero_of_large {N d j : ℕ} (hj : d*(N-1)<j) :
    convolution N d j=0 := by
  rw [convolution_eq_sum]
  apply Finset.sum_eq_zero
  intro b _
  exact if_neg (ne_of_lt ((indexSum_le b).trans_lt hj))

/-- The source's 4096-bin, twelve-fold convolution has exactly this finite support bound. -/
theorem source_convolution_support {j : ℕ} (hj : 49141≤j) : convolution 4096 12 j=0 := by
  apply convolution_zero_of_large
  omega

/-- Grouping weighted cells by their integer index sum gives the finite convolution sum. -/
theorem sum_cell_weight_eq (N d : ℕ) (w : ℕ → ℝ) :
    (∑ b : Fin d → Fin N,cellMass b*w (indexSum b))=
      ∑ j∈Finset.range (d*(N-1)+1),convolution N d j*w j := by
  classical
  symm
  simp_rw [convolution_eq_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  simp only [ite_mul,zero_mul]
  have hb : indexSum b∈Finset.range (d*(N-1)+1) :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le (indexSum_le b))
  simp [hb]

#print axioms sumCell_measure
#print axioms convolution_succ
#print axioms source_convolution_support
end BecknerOnofri.HighDim.ArcsineProductBins
