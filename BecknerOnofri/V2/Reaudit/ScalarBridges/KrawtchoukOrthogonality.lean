module

public import BecknerOnofri.SpinDefinitions
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.BigOperators.NatAntidiagonal
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Tactic
public import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities

@[expose] public section

/-! # Krawtchouk orthogonality for fair independent spins (U19, `d12-spin-eq:orthogonal`,
`d12-spin-eq:A2`) along the printed subset argument

Printed proof (Appendix A.3, "Behavior at zero"):  *For independent fair spins, the symmetric
products defining `A_s` satisfy `∑_j b_j A_{s,j} A_{r,j} = 1_{s=r}/C(12,s)` and
`∑_j b_j A_{s,j} = 0` (`s ≥ 1`).  Indeed, expand both averages over subsets of spins.  A product has
nonzero expectation only if the subsets are equal, since otherwise some centered spin occurs once.
Also `A_{1,j} = x_j`, `A_{2,j} = (12 x_j² - 1)/11`; the second identity follows by expanding the
square of the sum of the twelve spins.*

Model.  A configuration of 12 fair spins is the set `P ⊆ Fin 12` of positive spins; the spin at `i`
is `spin P i = ±1`; the count is `|P|`.  The expectation of a function of the configuration is
`fairE F = 2⁻¹² ∑_P F P`.  Independence is `fairE_prod`: the expectation of a product of one-spin
functions is the product of the one-spin expectations.  `A_s` is the average of the products
`∏_{i∈U} spin P i` over the `s`-subsets `U` (`symAvg`), and the explicit Krawtchouk formula
`momentQ` of the repository is recovered as `symAvg_eq_moment` (the count `ℓ` of negative spins in
the subset). -/

noncomputable section

namespace BecknerOnofri.V2.Reaudit.ScalarBridges

open Finset Polynomial
open scoped BigOperators

/-- Spin configuration: the set of positive spins among 12 spins. -/
abbrev Config := Finset (Fin 12)

/-- The spin `±1` at site `i`. -/
def spin (P : Config) (i : Fin 12) : ℝ := if i ∈ P then 1 else -1

/-- The spin product `∏_{i∈U} σ_i`. -/
def spinProd (U P : Config) : ℝ := ∏ i ∈ U, spin P i

/-- Expectation under 12 fair independent spins (uniform on the `2¹²` configurations). -/
def fairE (F : Config → ℝ) : ℝ := (∑ P ∈ (Finset.univ : Finset (Fin 12)).powerset, F P) / 2 ^ 12

/-- `A_s`: the average of the products of `s` spins over the `s`-subsets of spins
("symmetric products", sampled without replacement). -/
def symAvg (s : ℕ) (P : Config) : ℝ :=
  (∑ U ∈ powersetCard s (Finset.univ : Finset (Fin 12)), spinProd U P) / ((12 : ℕ).choose s : ℝ)

/-! ### Independence -/

theorem sum_powerset_prod_spin (h : Fin 12 → ℝ → ℝ) :
    ∑ P ∈ (Finset.univ : Finset (Fin 12)).powerset, ∏ i, h i (spin P i) =
      ∏ i, (h i 1 + h i (-1)) := by
  rw [Finset.prod_add (fun i => h i 1) (fun i => h i (-1)) Finset.univ]
  refine Finset.sum_congr rfl (fun P _ => ?_)
  have e : ∀ i, h i (spin P i) = if i ∈ P then h i 1 else h i (-1) := by
    intro i; unfold spin; split_ifs <;> rfl
  simp_rw [e]
  rw [Finset.prod_ite]
  congr 1
  · apply Finset.prod_congr _ (fun _ _ => rfl)
    ext i; simp
  · apply Finset.prod_congr _ (fun _ _ => rfl)
    ext i; simp

/-- **Independence of fair spins**: `E ∏_i h_i(σ_i) = ∏_i E h_i(σ_i)`, with
`E h_i(σ_i) = (h_i(1) + h_i(-1))/2`. -/
theorem fairE_prod (h : Fin 12 → ℝ → ℝ) :
    fairE (fun P => ∏ i, h i (spin P i)) = ∏ i, ((h i 1 + h i (-1)) / 2) := by
  unfold fairE
  rw [sum_powerset_prod_spin, Finset.prod_div_distrib]
  simp

theorem spinProd_eq_prod_univ (U P : Config) :
    spinProd U P = ∏ i, (if i ∈ U then spin P i else 1) := by
  unfold spinProd
  rw [Finset.prod_ite_mem]
  simp

theorem spin_sq (P : Config) (i : Fin 12) : spin P i * spin P i = 1 := by
  unfold spin; split_ifs <;> norm_num

/-- Expectation of a product of two spin products: nonzero only if the subsets are equal,
"since otherwise some centered spin occurs once". -/
theorem fairE_spinProd_mul (U V : Config) :
    fairE (fun P => spinProd U P * spinProd V P) = if U = V then 1 else 0 := by
  have key := fairE_prod (fun (i : Fin 12) (x : ℝ) =>
    (if i ∈ U then x else 1) * (if i ∈ V then x else 1))
  have e : fairE (fun P => spinProd U P * spinProd V P) =
      fairE (fun P => ∏ x : Fin 12, (if x ∈ U then spin P x else 1) *
        if x ∈ V then spin P x else 1) := by
    congr 1
    funext P
    rw [spinProd_eq_prod_univ, spinProd_eq_prod_univ, ← Finset.prod_mul_distrib]
  rw [e, key]
  have hf : ∀ i : Fin 12,
      (((if i ∈ U then (1 : ℝ) else 1) * (if i ∈ V then 1 else 1)) +
        ((if i ∈ U then (-1 : ℝ) else 1) * (if i ∈ V then -1 else 1))) / 2 =
        if (i ∈ U ↔ i ∈ V) then 1 else 0 := by
    intro i
    by_cases hU : i ∈ U <;> by_cases hV : i ∈ V <;> simp [hU, hV] <;> norm_num
  have e2 : (∏ i : Fin 12, (((if i ∈ U then (1 : ℝ) else 1) * (if i ∈ V then 1 else 1)) +
        ((if i ∈ U then (-1 : ℝ) else 1) * (if i ∈ V then -1 else 1))) / 2) =
        ∏ i : Fin 12, (if (i ∈ U ↔ i ∈ V) then (1 : ℝ) else 0) := Finset.prod_congr rfl (fun i _ => hf i)
  rw [e2, Finset.prod_boole]
  have : (∀ i : Fin 12, (i ∈ U ↔ i ∈ V)) ↔ U = V := by
    constructor
    · intro h; ext i; exact h i
    · intro h i; rw [h]
  simp only [Finset.mem_univ, true_implies, this]

/-- `E ∏_{i∈U} σ_i = 0` for `U ≠ ∅` (take `V = ∅`). -/
theorem fairE_spinProd (U : Config) : fairE (fun P => spinProd U P) = if U = ∅ then 1 else 0 := by
  have h := fairE_spinProd_mul U ∅
  simpa [spinProd] using h

/-! ### The Krawtchouk formula from the subset count -/

theorem coeff_one_sub_X_pow (m k : ℕ) :
    (((1 : ℝ[X]) - X) ^ m).coeff k = (-1) ^ k * (m.choose k : ℝ) := by
  have h : ((1 : ℝ[X]) - X) ^ m = C ((-1 : ℝ) ^ m) * (X + C (-1 : ℝ)) ^ m := by
    rw [map_pow, map_neg, map_one, ← mul_pow]
    congr 1
    ring
  rw [h, coeff_C_mul, coeff_X_add_C_pow]
  by_cases hk : k ≤ m
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
    rw [Nat.add_sub_cancel_left]
    have : ((-1 : ℝ) ^ d) * ((-1 : ℝ) ^ d) = 1 := by rw [← mul_pow]; norm_num
    calc (-1 : ℝ) ^ (k + d) * ((-1) ^ d * ((k + d).choose k : ℝ))
        = (-1) ^ k * (((-1) ^ d * (-1) ^ d) * ((k + d).choose k : ℝ)) := by ring
      _ = _ := by rw [this]; ring
  · have : m.choose k = 0 := Nat.choose_eq_zero_of_lt (by omega)
    simp [this]

theorem spinProd_sum_eq_coeff (s : ℕ) (P : Config) :
    ∑ U ∈ powersetCard s (Finset.univ : Finset (Fin 12)), spinProd U P =
      (∏ i : Fin 12, (C (spin P i) * X + 1 : ℝ[X])).coeff s := by
  have h1 : (∏ i : Fin 12, (C (spin P i) * X + 1 : ℝ[X])) =
      ∑ U ∈ (Finset.univ : Finset (Fin 12)).powerset, C (spinProd U P) * X ^ U.card := by
    rw [Finset.prod_add (fun i => C (spin P i) * X) (fun _ => (1 : ℝ[X])) Finset.univ]
    refine Finset.sum_congr rfl (fun U _ => ?_)
    rw [Finset.prod_const_one, mul_one, Finset.prod_mul_distrib, ← map_prod, Finset.prod_const]
    rfl
  rw [h1, finsetSum_coeff]
  simp_rw [coeff_C_mul_X_pow]
  rw [powersetCard_eq_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun U _ => ?_)
  by_cases h : U.card = s
  · simp [h]
  · simp [h, Ne.symm h]

theorem prod_poly_eq (P : Config) :
    (∏ i : Fin 12, (C (spin P i) * X + 1 : ℝ[X])) = (1 - X) ^ (12 - P.card) * (X + 1) ^ P.card := by
  have e : ∀ i : Fin 12, (C (spin P i) * X + 1 : ℝ[X]) = if i ∈ P then X + 1 else 1 - X := by
    intro i
    unfold spin
    split_ifs
    · simp
    · simp; ring
  simp_rw [e]
  have hc1 : (Finset.univ.filter fun i : Fin 12 => i ∈ P).card = P.card := by
    have : (Finset.univ.filter fun i : Fin 12 => i ∈ P) = P := by ext i; simp
    rw [this]
  have hc2 : (Finset.univ.filter fun i : Fin 12 => i ∉ P).card = 12 - P.card := by
    have : (Finset.univ.filter fun i : Fin 12 => i ∉ P) = Finset.univ \ P := by ext i; simp
    rw [this, Finset.card_sdiff_of_subset (Finset.subset_univ P)]
    simp
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const, hc1, hc2, mul_comm]

/-- The count of negative spins `ℓ` in the subset: explicit Krawtchouk formula,
`∑_{|U|=s} ∏_{i∈U} σ_i = ∑_ℓ (-1)^ℓ C(12-j,ℓ) C(j,s-ℓ)` with `j = |P|` positive spins. -/
theorem spinProd_sum_eq (s : ℕ) (P : Config) :
    ∑ U ∈ powersetCard s (Finset.univ : Finset (Fin 12)), spinProd U P =
      ∑ l ∈ range (s + 1), (-1 : ℝ) ^ l * ((12 - P.card).choose l : ℝ) * (P.card.choose (s - l) : ℝ) := by
  rw [spinProd_sum_eq_coeff, prod_poly_eq, coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => ((1 - X : ℝ[X]) ^ (12 - P.card)).coeff i *
      ((X + 1 : ℝ[X]) ^ P.card).coeff j) s]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [coeff_one_sub_X_pow, coeff_X_add_one_pow]

/-! ### Connection with the repository's `momentQ`-based `A_{s,j}` -/

open BecknerOnofri.HighDim.Spin in
/-- The count of a configuration, as an element of `Count = Fin 13`. -/
def cnt (P : Config) : Count :=
  ⟨P.card, Nat.lt_succ_of_le (by simpa using Finset.card_le_univ P)⟩

open BecknerOnofri.HighDim.Spin in
/-- `A_{s,j}` of the repository is the average of the products of `s` spins over the
`s`-subsets, as a function of the count: the explicit formula (with `ℓ` the number of negative
spins in the subset) equals the symmetric product average. -/
theorem symAvg_eq_moment (s : Order) (P : Config) :
    symAvg (s.val + 1) P = moment s (cnt P) := by
  unfold symAvg moment momentQ
  rw [spinProd_sum_eq]
  push_cast
  simp only [cnt]

/-! ### Expectation of a function of the count -/

open BecknerOnofri.HighDim.Spin in
theorem fairE_card (F : ℕ → ℝ) :
    fairE (fun P => F P.card) = ∑ j : Count, reference j * F j.val := by
  unfold fairE
  rw [Finset.sum_powerset_apply_card]
  simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hr : ∀ j : Count, reference j = ((12 : ℕ).choose j.val : ℝ) / 2 ^ 12 := by
    intro j; unfold reference referenceQ; push_cast; norm_num
  calc (∑ m ∈ range (12 + 1), ((12 : ℕ).choose m : ℝ) * F m) / 2 ^ 12
      = ∑ m ∈ range 13, ((12 : ℕ).choose m : ℝ) * F m / 2 ^ 12 := by rw [Finset.sum_div]
    _ = ∑ j : Fin 13, ((12 : ℕ).choose j.val : ℝ) * F j.val / 2 ^ 12 :=
        (Fin.sum_univ_eq_sum_range (fun m => ((12 : ℕ).choose m : ℝ) * F m / 2 ^ 12) 13).symm
    _ = ∑ j : Count, reference j * F j.val := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [hr j]; ring

open BecknerOnofri.HighDim.Spin in
/-- Expectation of a function of the count, over `Count = Fin 13`. -/
theorem fairE_cnt (F : Count → ℝ) : fairE (fun P => F (cnt P)) = ∑ j : Count, reference j * F j := by
  have h := fairE_card (fun m => if hm : m < 13 then F ⟨m, hm⟩ else 0)
  have e1 : (fun P : Config => (fun m : ℕ => if hm : m < 13 then F ⟨m, hm⟩ else 0) P.card) =
      fun P => F (cnt P) := by
    funext P
    have : P.card < 13 := Nat.lt_succ_of_le (by simpa using Finset.card_le_univ P)
    simp only [this, dif_pos]
    rfl
  rw [e1] at h
  rw [h]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp [j.isLt]

/-! ### Linearity of the expectation -/

theorem fairE_sum {ι : Type*} (S : Finset ι) (F : ι → Config → ℝ) :
    fairE (fun P => ∑ i ∈ S, F i P) = ∑ i ∈ S, fairE (F i) := by
  unfold fairE
  rw [Finset.sum_comm, Finset.sum_div]

theorem fairE_div (F : Config → ℝ) (c : ℝ) : fairE (fun P => F P / c) = fairE F / c := by
  unfold fairE
  rw [← Finset.sum_div, div_div, div_div, mul_comm]

/-- **Orthogonality of the symmetric products**, expectation form:
`E[A_s A_r] = 1_{s=r} / C(12,s)` for `s ≤ 12`. -/
theorem fairE_symAvg_mul (s r : ℕ) (hs : s ≤ 12) :
    fairE (fun P => symAvg s P * symAvg r P) = if s = r then 1 / ((12 : ℕ).choose s : ℝ) else 0 := by
  have hC : ((12 : ℕ).choose s : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hs).ne'
  have e : ∀ P : Config, symAvg s P * symAvg r P =
      (∑ U ∈ powersetCard s (Finset.univ : Finset (Fin 12)),
        ∑ V ∈ powersetCard r (Finset.univ : Finset (Fin 12)), spinProd U P * spinProd V P) /
        (((12 : ℕ).choose s : ℝ) * ((12 : ℕ).choose r : ℝ)) := by
    intro P
    unfold symAvg
    rw [div_mul_div_comm, Finset.sum_mul_sum]
  simp_rw [e]
  rw [fairE_div, fairE_sum]
  simp_rw [fairE_sum, fairE_spinProd_mul]
  have hcount : ∑ U ∈ powersetCard s (Finset.univ : Finset (Fin 12)),
      ∑ V ∈ powersetCard r (Finset.univ : Finset (Fin 12)), (if U = V then (1 : ℝ) else 0) =
      if s = r then ((12 : ℕ).choose s : ℝ) else 0 := by
    simp_rw [Finset.sum_ite_eq, mem_powersetCard]
    by_cases hsr : s = r
    · subst hsr
      rw [if_pos rfl]
      calc ∑ U ∈ powersetCard s (Finset.univ : Finset (Fin 12)),
            (if U ⊆ Finset.univ ∧ U.card = s then (1 : ℝ) else 0)
          = ∑ U ∈ powersetCard s (Finset.univ : Finset (Fin 12)), (1 : ℝ) :=
            Finset.sum_congr rfl (fun U hU => by rw [mem_powersetCard] at hU; simp [hU])
        _ = ((12 : ℕ).choose s : ℝ) := by simp [card_powersetCard]
    · rw [if_neg hsr]
      apply Finset.sum_eq_zero
      intro U hU
      rw [mem_powersetCard] at hU
      have : ¬ (U ⊆ Finset.univ ∧ U.card = r) := fun h => hsr (hU.2.symm.trans h.2)
      rw [if_neg this]
  rw [hcount]
  by_cases hsr : s = r
  · subst hsr
    simp only [if_true]
    field_simp
  · simp [hsr]

open BecknerOnofri.HighDim.Spin in
theorem cnt_surjective : Function.Surjective cnt := by
  intro j
  obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin 12)))
    (n := j.val) (by simpa using Nat.lt_succ_iff.mp j.isLt)
  exact ⟨t, Fin.ext (by simpa [cnt] using ht)⟩

/-- Sum of the spins: `∑_i σ_i = 2 |P| - 12`. -/
theorem sum_spin (P : Config) : ∑ i, spin P i = 2 * (P.card : ℝ) - 12 := by
  have : ∀ i, spin P i = 2 * (if i ∈ P then (1 : ℝ) else 0) - 1 := by
    intro i; unfold spin; split_ifs <;> norm_num
  simp_rw [this]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_boole]
  simp [Finset.filter_mem_eq_inter]

/-- `e_1`: the sum of the spins. -/
theorem sum_powersetCard_one (P : Config) :
    ∑ U ∈ powersetCard 1 (Finset.univ : Finset (Fin 12)), spinProd U P = ∑ i, spin P i := by
  rw [powersetCard_one, Finset.sum_map]
  simp [spinProd]

/-- Newton's identity `2 e_2 = e_1² - p_2` evaluated at the spins (`p_2 = ∑ σ_i² = 12`):
"expanding the square of the sum of the twelve spins". -/
theorem two_mul_sum_powersetCard_two (P : Config) :
    2 * ∑ U ∈ powersetCard 2 (Finset.univ : Finset (Fin 12)), spinProd U P =
      (∑ i, spin P i) ^ 2 - 12 := by
  have h := MvPolynomial.psum_eq_mul_esymm_sub_sum (σ := Fin 12) (R := ℝ) 2 (by norm_num)
  have h2 := congrArg (MvPolynomial.aeval (spin P)) h
  have e : ∀ n, MvPolynomial.aeval (spin P) (MvPolynomial.esymm (Fin 12) ℝ n) =
      ∑ U ∈ powersetCard n (Finset.univ : Finset (Fin 12)), spinProd U P := by
    intro n
    simp [MvPolynomial.esymm, spinProd, map_sum, map_prod]
  have hp : ∀ n, MvPolynomial.aeval (spin P) (MvPolynomial.psum (Fin 12) ℝ n) =
      ∑ i, (spin P i) ^ n := by
    intro n
    simp [MvPolynomial.psum]
  have hanti : (Finset.antidiagonal 2).filter (fun a : ℕ × ℕ => a.1 ∈ Set.Ioo 0 2) = {(1, 1)} := by
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_antidiagonal, Set.mem_Ioo, Finset.mem_singleton,
      Prod.mk.injEq]
    omega
  rw [hanti] at h2
  simp only [map_sub, map_mul, map_pow, map_neg, map_one, map_natCast, Finset.sum_singleton, e, hp] at h2
  have h12 : ∑ i : Fin 12, (spin P i) ^ 2 = 12 := by
    have : ∀ i, spin P i ^ 2 = 1 := fun i => by rw [sq]; exact spin_sq P i
    simp [this]
  rw [sum_powersetCard_one] at h2
  simp only [pow_one] at h2
  rw [h12] at h2
  push_cast at h2
  nlinarith [h2]

open BecknerOnofri.HighDim.Spin

theorem meanCoordinate_eq (j : Count) : meanCoordinate j = (2 * (j.val : ℝ) - 12) / 12 := by
  unfold meanCoordinate meanCoordinateQ
  push_cast
  ring

theorem symAvg_one (P : Config) : symAvg 1 P = meanCoordinate (cnt P) := by
  unfold symAvg
  rw [sum_powersetCard_one, sum_spin, meanCoordinate_eq]
  simp [cnt]

theorem symAvg_two (P : Config) :
    symAvg 2 P = (12 * meanCoordinate (cnt P) ^ 2 - 1) / 11 := by
  unfold symAvg
  have h := two_mul_sum_powersetCard_two P
  rw [sum_spin] at h
  rw [meanCoordinate_eq]
  simp only [cnt]
  have hc : ((12 : ℕ).choose 2 : ℝ) = 66 := by norm_num [Nat.choose]
  rw [hc]
  field_simp
  nlinarith [h]

/-- `A_{1,j} = x_j` (`d12-spin-eq:A2`, first identity), via the spin model. -/
theorem moment_one_spins (j : Count) : moment ⟨0, by decide⟩ j = meanCoordinate j := by
  obtain ⟨P, rfl⟩ := cnt_surjective j
  rw [← symAvg_eq_moment ⟨0, by decide⟩ P]
  exact symAvg_one P

/-- `A_{2,j} = (12 x_j² - 1)/11` (`d12-spin-eq:A2`), by expanding the square of the sum of
the twelve spins. -/
theorem moment_two_spins (j : Count) :
    moment ⟨1, by decide⟩ j = (12 * meanCoordinate j ^ 2 - 1) / 11 := by
  obtain ⟨P, rfl⟩ := cnt_surjective j
  rw [← symAvg_eq_moment ⟨1, by decide⟩ P]
  exact symAvg_two P

/-- `∑_j b_j A_{s,j} = 0` for `s ≥ 1` (`d12-spin-eq:orthogonal`, second relation). -/
theorem reference_moment_zero_spins (s : Order) :
    ∑ j : Count, reference j * moment s j = 0 := by
  rw [← fairE_cnt (fun j => moment s j)]
  have : (fun P : Config => moment s (cnt P)) = fun P => symAvg (s.val + 1) P := by
    funext P; rw [symAvg_eq_moment]
  rw [this]
  unfold symAvg
  rw [fairE_div, fairE_sum]
  apply div_eq_zero_iff.2 (Or.inl _)
  apply Finset.sum_eq_zero
  intro U hU
  rw [mem_powersetCard] at hU
  rw [fairE_spinProd, if_neg]
  intro h
  rw [h] at hU
  simp at hU

/-- `∑_j b_j A_{s,j} A_{r,j} = 1_{s=r}/C(12,s)` (`d12-spin-eq:orthogonal`), proved by expanding both
averages over subsets of fair independent spins. -/
theorem reference_moment_orthogonal_spins (s r : Order) :
    ∑ j : Count, reference j * (moment s j * moment r j) =
      if s = r then 1 / ((12 : ℕ).choose (s.val + 1) : ℝ) else 0 := by
  rw [← fairE_cnt (fun j => moment s j * moment r j)]
  have : (fun P : Config => moment s (cnt P) * moment r (cnt P)) =
      fun P => symAvg (s.val + 1) P * symAvg (r.val + 1) P := by
    funext P; rw [symAvg_eq_moment, symAvg_eq_moment]
  rw [this, fairE_symAvg_mul _ _ (by have := s.isLt; omega)]
  by_cases h : s = r
  · subst h; simp
  · have : s.val + 1 ≠ r.val + 1 := fun h' => h (Fin.ext (by omega))
    rw [if_neg h, if_neg this]


/-! ### Conditional expectation given the count

"`A_{s,j}` is the conditional expectation of `σ_1⋯σ_s` given that count": conditional on the count
`j`, the positive spins form a uniformly chosen `j`-subset; the average over these subsets of the
product of the spins in any fixed `s`-subset `U` is `A_{s,j}`. -/

theorem spinProd_eq_neg_one_pow (U P : Config) : spinProd U P = (-1 : ℝ) ^ (U \ P).card := by
  unfold spinProd spin
  rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]
  congr 2
  ext i; simp [Finset.mem_sdiff]

theorem gen_spinProd (U : Config) :
    (∑ P ∈ (Finset.univ : Finset (Fin 12)).powerset, C (spinProd U P) * X ^ P.card : ℝ[X]) =
      (X - 1) ^ U.card * (X + 1) ^ (12 - U.card) := by
  have h := Finset.prod_add (fun _ : Fin 12 => (X : ℝ[X]))
    (fun i => if i ∈ U then (-1 : ℝ[X]) else 1) Finset.univ
  have e1 : (∏ i : Fin 12, ((X : ℝ[X]) + if i ∈ U then (-1 : ℝ[X]) else 1)) =
      (X - 1) ^ U.card * (X + 1) ^ (12 - U.card) := by
    have e : ∀ i : Fin 12, ((X : ℝ[X]) + if i ∈ U then (-1 : ℝ[X]) else 1) =
        if i ∈ U then X - 1 else X + 1 := by
      intro i; split_ifs <;> ring
    simp_rw [e]
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
    have hc1 : (Finset.univ.filter fun i : Fin 12 => i ∈ U).card = U.card := by
      have : (Finset.univ.filter fun i : Fin 12 => i ∈ U) = U := by ext i; simp
      rw [this]
    have hc2 : (Finset.univ.filter fun i : Fin 12 => i ∉ U).card = 12 - U.card := by
      have : (Finset.univ.filter fun i : Fin 12 => i ∉ U) = Finset.univ \ U := by ext i; simp
      rw [this, Finset.card_sdiff_of_subset (Finset.subset_univ U)]
      simp
    rw [hc1, hc2]
  rw [← e1, h]
  refine Finset.sum_congr rfl (fun P _ => ?_)
  rw [Finset.prod_const, spinProd_eq_neg_one_pow]
  have : (∏ i ∈ Finset.univ \ P, (if i ∈ U then (-1 : ℝ[X]) else 1)) = C ((-1 : ℝ) ^ (U \ P).card) := by
    rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const, map_pow, map_neg, map_one]
    congr 2
    ext i; simp [Finset.mem_sdiff]; tauto
  rw [this, mul_comm]

theorem sum_powersetCard_spinProd_eq_coeff (U : Config) (j : ℕ) :
    ∑ P ∈ powersetCard j (Finset.univ : Finset (Fin 12)), spinProd U P =
      (((X - 1) ^ U.card * (X + 1) ^ (12 - U.card) : ℝ[X])).coeff j := by
  rw [← gen_spinProd, finsetSum_coeff]
  simp_rw [coeff_C_mul_X_pow]
  rw [powersetCard_eq_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun P _ => ?_)
  by_cases h : P.card = j
  · simp [h]
  · simp [h, Ne.symm h]

open BecknerOnofri.HighDim.Spin in
/-- **Conditional expectation given the count.**  For any `s`-subset `U` of the spins (for instance
`{1,…,s}`), the average of `∏_{i∈U} σ_i` over the `C(12,j)` configurations with `j` positive spins is
`A_{s,j}`. -/
theorem condExp_spinProd_eq_moment (s : Order) (j : Count) (U : Config) (hU : U.card = s.val + 1) :
    (∑ P ∈ powersetCard j.val (Finset.univ : Finset (Fin 12)), spinProd U P) /
        ((12 : ℕ).choose j.val : ℝ) = moment s j := by
  have hj : j.val ≤ 12 := Nat.lt_succ_iff.mp j.isLt
  have hs : s.val + 1 ≤ 12 := by have := s.isLt; omega
  have hCj : ((12 : ℕ).choose j.val : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hj).ne'
  have hCs : ((12 : ℕ).choose (s.val + 1) : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hs).ne'
  -- the inner sum depends on `U` only through `|U|`
  have hinv : ∀ U' ∈ powersetCard (s.val + 1) (Finset.univ : Finset (Fin 12)),
      ∑ P ∈ powersetCard j.val (Finset.univ : Finset (Fin 12)), spinProd U' P =
        ∑ P ∈ powersetCard j.val (Finset.univ : Finset (Fin 12)), spinProd U P := by
    intro U' hU'
    rw [mem_powersetCard] at hU'
    rw [sum_powersetCard_spinProd_eq_coeff, sum_powersetCard_spinProd_eq_coeff, hU'.2, hU]
  -- double counting
  have hsum1 : ∑ U' ∈ powersetCard (s.val + 1) (Finset.univ : Finset (Fin 12)),
      ∑ P ∈ powersetCard j.val (Finset.univ : Finset (Fin 12)), spinProd U' P =
      ((12 : ℕ).choose (s.val + 1) : ℝ) *
        ∑ P ∈ powersetCard j.val (Finset.univ : Finset (Fin 12)), spinProd U P := by
    rw [Finset.sum_congr rfl hinv, Finset.sum_const, card_powersetCard]
    simp
  have hsum2 : ∑ U' ∈ powersetCard (s.val + 1) (Finset.univ : Finset (Fin 12)),
      ∑ P ∈ powersetCard j.val (Finset.univ : Finset (Fin 12)), spinProd U' P =
      ((12 : ℕ).choose (s.val + 1) : ℝ) * (((12 : ℕ).choose j.val : ℝ) * moment s j) := by
    rw [Finset.sum_comm]
    have : ∀ P ∈ powersetCard j.val (Finset.univ : Finset (Fin 12)),
        ∑ U' ∈ powersetCard (s.val + 1) (Finset.univ : Finset (Fin 12)), spinProd U' P =
          ((12 : ℕ).choose (s.val + 1) : ℝ) * moment s j := by
      intro P hP
      rw [mem_powersetCard] at hP
      have hc : cnt P = j := Fin.ext (by simpa [cnt] using hP.2)
      have h := symAvg_eq_moment s P
      rw [hc] at h
      unfold symAvg at h
      rw [← h]
      field_simp
    rw [Finset.sum_congr rfl this, Finset.sum_const, card_powersetCard]
    simp
    ring
  have key : ∑ P ∈ powersetCard j.val (Finset.univ : Finset (Fin 12)), spinProd U P =
      ((12 : ℕ).choose j.val : ℝ) * moment s j := by
    have := hsum1.symm.trans hsum2
    have := mul_left_cancel₀ hCs this
    exact this
  rw [key]
  field_simp

end BecknerOnofri.V2.Reaudit.ScalarBridges
