module

public import BecknerOnofri.BinarySpinChannel
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

/-! The binomial coefficients in the thirteen-state matrix are the actual
joint spin moments on each count class, verified over the full finite space. -/
noncomputable section
set_option maxRecDepth 65536
set_option maxHeartbeats 0
open scoped BigOperators
namespace BecknerOnofri.HighDim.Spin

theorem jointSpin_cast (S : Finset (Fin 12)) (σ : Configuration) :
    (jointSpinQ S σ:ℝ)=jointSpin S σ := by
  simp [jointSpinQ,jointSpin]

/-- The coefficient of `x^j` in `(x - 1)^a (x + 1)^b`. -/
def mixedCoeff (a b j : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (j + 1), ((a.choose k : ℚ) * (-1) ^ (a - k)) * (b.choose (j - k) : ℚ)

/-- The finite check: the coefficients of `(x - 1)^{s+1} (x + 1)^{11-s}` are the entries of
`C(12, j) A_{s,j}`. -/
theorem mixedCoeff_eq_moment : ∀ s : Order, ∀ j : Count,
    mixedCoeff (s.val + 1) (11 - s.val) j.val = ((12 : ℕ).choose j.val : ℚ) * momentQ s j := by
  decide +kernel

open Polynomial in
/-- Generating function: `∑_σ x^{|σ|} ∏_{i ∉ σ} c_i = ∏_i (x + c_i)`, read at `x^j`. -/
theorem sum_countClass_eq_coeff (S : Finset (Fin 12)) (j : ℕ) :
    (∑ σ ∈ (Finset.univ : Finset (Fin 12)).powersetCard j, jointSpinQ S σ) =
      (∏ i : Fin 12, (X + C (if i ∈ S then (-1 : ℚ) else 1))).coeff j := by
  rw [Finset.prod_add (fun _ => (X : ℚ[X])), finsetSum_coeff]
  simp only [Finset.prod_const, ← map_prod, ← Finset.compl_eq_univ_sdiff]
  rw [Finset.powersetCard_eq_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [mul_comm, coeff_C_mul, coeff_X_pow]
  split_ifs with h1 h2 h2
  · rw [mul_one]; rfl
  · exact absurd h1.symm h2
  · exact absurd h2.symm h1
  · rw [mul_zero]

open Polynomial in
theorem prod_split (S : Finset (Fin 12)) :
    (∏ i : Fin 12, (X + C (if i ∈ S then (-1 : ℚ) else 1))) =
      (X + C (-1)) ^ S.card * (X + C 1) ^ (12 - S.card) := by
  have h : ∀ i : Fin 12, (X + C (if i ∈ S then (-1 : ℚ) else 1)) =
      if i ∈ S then X + C (-1) else X + C 1 := fun i => by split_ifs <;> rfl
  simp only [h, Finset.prod_ite, Finset.prod_const, Finset.filter_mem_eq_inter,
    Finset.univ_inter]
  congr 2
  rw [Finset.filter_not, Finset.card_univ_sdiff]
  simp

open Polynomial in
theorem coeff_mixed (a b j : ℕ) :
    ((X + C (-1 : ℚ)) ^ a * (X + C 1) ^ b).coeff j = mixedCoeff a b j := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, mixedCoeff]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [coeff_X_add_C_pow, coeff_X_add_C_pow]
  simp [one_pow, mul_comm]

theorem card_firstCoordinates (s : Order) : (firstCoordinates s).card = s.val + 1 := by
  revert s; decide

/-- The joint moments on each count class, by a generating function (no enumeration of
the `2¹²` configurations). -/
theorem count_joint_moment_rational : ∀ s : Order,∀ j : Count,
    (∑ σ ∈ countClass j,jointSpinQ (firstCoordinates s) σ)=
      ((12:ℕ).choose j.val:ℚ)*momentQ s j := by
  intro s j
  rw [countClass, sum_countClass_eq_coeff, prod_split, card_firstCoordinates,
    show 12 - (s.val + 1) = 11 - s.val by omega, coeff_mixed, mixedCoeff_eq_moment]

theorem count_joint_moment (s : Order) (j : Count) :
    (∑ σ ∈ countClass j,jointSpin (firstCoordinates s) σ)=
      ((12:ℕ).choose j.val:ℝ)*moment s j := by
  have h := congrArg (fun a : ℚ => (a:ℝ)) (count_joint_moment_rational s j)
  simpa only [Rat.cast_sum,jointSpin_cast,Rat.cast_mul,Rat.cast_natCast,moment] using h

theorem exchangeable_joint_moment {ν : Configuration → ℝ} (hν : Exchangeable ν) (s : Order) :
    (∑ σ : Configuration,ν σ*jointSpin (firstCoordinates s) σ)=
      ∑ j : Count,moment s j*countLaw ν j := by
  rw [sum_count_classes]
  apply Finset.sum_congr rfl
  intro j _
  calc
    _ = ∑ σ ∈ countClass j,
        (countLaw ν j/((12:ℕ).choose j.val:ℝ))*jointSpin (firstCoordinates s) σ := by
      apply Finset.sum_congr rfl
      intro σ hσ
      have hh := (countClass_mem j σ).mp hσ
      have he := law_eq_countLaw_div hν σ
      rw [he,hh,show σ.card=j.val from congrArg Fin.val hh]
    _ = _ := by
      rw [← Finset.mul_sum,count_joint_moment]
      field_simp [(countClass_pos j).ne']

/-- Exactly the weighted cube-spin energy used in equation (5.138). -/
theorem exchangeable_energy {ν : Configuration → ℝ} (hν : Exchangeable ν) :
    (∑ s : Order,weight s*(∑ σ : Configuration,ν σ*jointSpin (firstCoordinates s) σ)^2)=
      quadratic (countLaw ν) := by
  simp_rw [exchangeable_joint_moment hν]
  exact (quadratic_eq_sum _).symm

#print axioms exchangeable_energy
end BecknerOnofri.HighDim.Spin
