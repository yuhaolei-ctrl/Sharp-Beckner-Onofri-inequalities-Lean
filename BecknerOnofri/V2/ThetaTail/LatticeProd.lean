module

public import BecknerOnofri.V2.ThetaTail.Defs
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Topology.Algebra.InfiniteSum.Ring
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Algebra.Order.Group.Indicator

@[expose] public section

/-! # Absolute convergence and the heat sum off the cube (Appendix A.1, Gaussian stage)

* `∑_{n∈ℤ} f(n)` product lemma on `ℤ^d`;
* `θ(e^{-s}) = ∑_n e^{-s n²}`;
* `∑_{k ∈ ℤ^{12}} e^{-s|k|²} = θ(e^{-s})^{12}` and the cube sum `(1 + 2e^{-s})^{12}`;
* `∑_{k∉cube} e^{-s|k|²} = θ(e^{-s})^{12} − (1+2e^{-s})^{12}`;
* summability of the series defining `G(η)` ("comparison with the product of twelve Gaussian
  series"). -/
noncomputable section
open Finset Filter Topology
namespace BecknerOnofri.V2.ThetaTail

lemma summable_gauss_nat {s : ℝ} (hs : 0 < s) : Summable (fun n : ℕ => Real.exp (-s * (n : ℝ) ^ 2)) := by
  have hg : Summable (fun n : ℕ => Real.exp (-s) ^ n) :=
    summable_geometric_of_lt_one (Real.exp_pos _).le (Real.exp_lt_one_iff.2 (by linarith))
  refine Summable.of_nonneg_of_le (fun n => (Real.exp_pos _).le) (fun n => ?_) hg
  rw [← Real.exp_nat_mul]
  apply Real.exp_le_exp.2
  have : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
    rcases Nat.eq_zero_or_pos n with h | h
    · simp [h]
    · have : (1 : ℝ) ≤ n := by exact_mod_cast h
      nlinarith
  nlinarith

lemma summable_gauss_int {s : ℝ} (hs : 0 < s) :
    Summable (fun n : ℤ => Real.exp (-s * (n : ℝ) ^ 2)) := by
  refine summable_int_iff_summable_nat_and_neg.2 ⟨?_, ?_⟩
  · simpa using summable_gauss_nat hs
  · simpa using summable_gauss_nat hs

lemma gauss_pos (s : ℝ) (n : ℤ) : 0 < Real.exp (-s * (n : ℝ) ^ 2) := Real.exp_pos _

theorem theta_exp (s : ℝ) : theta (Real.exp (-s)) = ∑' n : ℤ, Real.exp (-s * (n : ℝ) ^ 2) := by
  unfold theta
  refine tsum_congr fun k => ?_
  have h : k ^ 2 = ((k.natAbs ^ 2 : ℕ) : ℤ) := by
    rw [Nat.cast_pow, Int.natAbs_sq]
  have h2 : ((k.natAbs ^ 2 : ℕ) : ℝ) = (k : ℝ) ^ 2 := by
    have := congrArg (fun z : ℤ => (z : ℝ)) h
    simpa using this.symm
  rw [h, zpow_natCast, ← Real.exp_nat_mul, h2]
  congr 1
  ring

theorem hasSum_theta_exp {s : ℝ} (hs : 0 < s) :
    HasSum (fun n : ℤ => Real.exp (-s * (n : ℝ) ^ 2)) (theta (Real.exp (-s))) := by
  rw [theta_exp]; exact (summable_gauss_int hs).hasSum

/-- the product lemma on `ℤ^d` for nonnegative summable `f`. -/
theorem hasSum_pi_prod (f : ℤ → ℝ) (hf0 : ∀ n, 0 ≤ f n) {a : ℝ} (hf : HasSum f a) (d : ℕ) :
    HasSum (fun k : Fin d → ℤ => ∏ i, f (k i)) (a ^ d) := by
  induction d with
  | zero => simpa using hasSum_fintype (fun _ : Fin 0 → ℤ => (1 : ℝ))
  | succ d ih =>
    have hprod : Summable (fun x : ℤ × (Fin d → ℤ) => f x.1 * ∏ i, f (x.2 i)) := by
      refine Summable.mul_of_nonneg (f := f) (g := fun k : Fin d → ℤ => ∏ i, f (k i))
        hf.summable ih.summable (fun n => hf0 n) (fun k => ?_)
      exact Finset.prod_nonneg fun i _ => hf0 _
    have h := hf.mul ih hprod
    rw [pow_succ']
    rw [← (Fin.consEquiv (fun _ : Fin (d + 1) => ℤ)).hasSum_iff]
    convert h using 1
    ext x
    simp [Fin.prod_univ_succ, Fin.consEquiv]

lemma latticeNormSq_nonneg (k : Fin 12 → ℤ) : 0 ≤ latticeNormSq k :=
  Finset.sum_nonneg fun i _ => sq_nonneg _

lemma latticeNorm_pow_twelve (k : Fin 12 → ℤ) : latticeNorm k ^ 12 = latticeNormSq k ^ 6 := by
  unfold latticeNorm
  rw [show (12 : ℕ) = 2 * 6 by norm_num, pow_mul, Real.sq_sqrt (latticeNormSq_nonneg k)]

lemma mem_cube12_iff (k : Fin 12 → ℤ) : k ∈ cube12 ↔ ∀ i, k i = -1 ∨ k i = 0 ∨ k i = 1 := by
  simp [cube12, Set.mem_pi]

lemma latticeNormSq_ge_four {k : Fin 12 → ℤ} (hk : k ∉ cube12) : 4 ≤ latticeNormSq k := by
  rw [mem_cube12_iff] at hk
  simp only [not_forall, not_or] at hk
  obtain ⟨i, h1, h0, h2⟩ := hk
  have hsq : (4 : ℝ) ≤ ((k i : ℤ) : ℝ) ^ 2 := by
    have : (4 : ℤ) ≤ (k i) ^ 2 := by
      have hne : k i ≤ -2 ∨ 2 ≤ k i := by omega
      rcases hne with h | h <;> nlinarith
    exact_mod_cast this
  unfold latticeNormSq
  calc (4 : ℝ) ≤ ((k i : ℤ) : ℝ) ^ 2 := hsq
    _ ≤ _ := Finset.single_le_sum (f := fun j => ((k j : ℤ) : ℝ) ^ 2) (fun j _ => sq_nonneg _)
      (Finset.mem_univ i)

/-- `e^{-s|k|²}` is the product of the one-dimensional Gaussians -/
lemma exp_latticeNormSq (s : ℝ) (k : Fin 12 → ℤ) :
    Real.exp (-s * latticeNormSq k) = ∏ i, Real.exp (-s * ((k i : ℤ) : ℝ) ^ 2) := by
  unfold latticeNormSq
  rw [Finset.mul_sum, Real.exp_sum]

theorem hasSum_gauss_pi {s : ℝ} (hs : 0 < s) :
    HasSum (fun k : Fin 12 → ℤ => Real.exp (-s * latticeNormSq k)) (theta (Real.exp (-s)) ^ 12) := by
  have := hasSum_pi_prod _ (fun n => (Real.exp_pos _).le) (hasSum_theta_exp hs) 12
  convert this using 1
  ext k
  exact exp_latticeNormSq s k

/-- the one-dimensional cube factor -/
def cubeFactor (s : ℝ) (n : ℤ) : ℝ :=
  ({-1, 0, 1} : Set ℤ).indicator (fun n : ℤ => Real.exp (-s * (n : ℝ) ^ 2)) n

lemma hasSum_cubeFactor (s : ℝ) : HasSum (cubeFactor s) (1 + 2 * Real.exp (-s)) := by
  have h : HasSum (cubeFactor s) (∑ n ∈ ({-1, 0, 1} : Finset ℤ), cubeFactor s n) :=
    hasSum_sum_of_ne_finset_zero (fun n hn => by
      unfold cubeFactor
      apply Set.indicator_of_notMem
      simpa using hn)
  convert h using 1
  unfold cubeFactor
  simp [Finset.sum_insert]
  ring

lemma prod_cubeFactor (s : ℝ) (k : Fin 12 → ℤ) :
    ∏ i, cubeFactor s (k i) = cube12.indicator (fun k => Real.exp (-s * latticeNormSq k)) k := by
  by_cases hk : k ∈ cube12
  · rw [Set.indicator_of_mem hk, exp_latticeNormSq]
    refine Finset.prod_congr rfl fun i _ => ?_
    unfold cubeFactor
    apply Set.indicator_of_mem
    have := (Set.mem_pi.1 hk) i (Set.mem_univ i)
    exact this
  · rw [Set.indicator_of_notMem hk]
    rw [mem_cube12_iff] at hk
    simp only [not_forall, not_or] at hk
    obtain ⟨i, h1, h0, h2⟩ := hk
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    unfold cubeFactor
    apply Set.indicator_of_notMem
    simp [h1, h0, h2]

theorem hasSum_cube12 (s : ℝ) :
    HasSum (fun k : Fin 12 → ℤ => cube12.indicator (fun k => Real.exp (-s * latticeNormSq k)) k)
      ((1 + 2 * Real.exp (-s)) ^ 12) := by
  have := hasSum_pi_prod (cubeFactor s)
    (fun n => by
      unfold cubeFactor
      exact Set.indicator_nonneg (fun _ _ => (Real.exp_pos _).le) n)
    (hasSum_cubeFactor s) 12
  convert this using 1
  ext k
  exact (prod_cubeFactor s k).symm

/-- `∑_{k∉cube} e^{-s|k|²} = θ(e^{-s})^{12} − (1+2e^{-s})^{12}`. -/
theorem hasSum_heat_off_cube {s : ℝ} (hs : 0 < s) :
    HasSum (fun k : Fin 12 → ℤ =>
        (cube12ᶜ).indicator (fun k => Real.exp (-s * latticeNormSq k)) k)
      (theta (Real.exp (-s)) ^ 12 - (1 + 2 * Real.exp (-s)) ^ 12) := by
  have h := (hasSum_gauss_pi hs).sub (hasSum_cube12 s)
  convert h using 1
  ext k
  have := Set.indicator_self_add_compl cube12 (fun k : Fin 12 → ℤ => Real.exp (-s * latticeNormSq k))
  have := congrFun this k
  simp only [Pi.add_apply] at this
  linarith

lemma gaussSummand_le {η : ℝ} (k : Fin 12 → ℤ) :
    gaussSummand η k ≤ (cube12ᶜ).indicator (fun k => Real.exp (-η * latticeNormSq k)) k := by
  unfold gaussSummand
  by_cases hk : k ∈ cube12ᶜ
  · rw [Set.indicator_of_mem hk, Set.indicator_of_mem hk]
    have h4 := latticeNormSq_ge_four hk
    rw [latticeNorm_pow_twelve]
    have : (1 : ℝ) ≤ latticeNormSq k ^ 6 := one_le_pow₀ (by linarith)
    exact div_le_self (Real.exp_pos _).le this
  · rw [Set.indicator_of_notMem hk, Set.indicator_of_notMem hk]

lemma gaussSummand_nonneg (η : ℝ) (k : Fin 12 → ℤ) : 0 ≤ gaussSummand η k := by
  unfold gaussSummand
  exact Set.indicator_nonneg (fun k _ => div_nonneg (Real.exp_pos _).le
    (pow_nonneg (Real.sqrt_nonneg _) _)) k

/-- absolute convergence of the series defining `G(η)` -/
theorem summable_gaussSummand {η : ℝ} (hη : 0 < η) : Summable (gaussSummand η) :=
  Summable.of_nonneg_of_le (gaussSummand_nonneg η) gaussSummand_le
    (hasSum_heat_off_cube hη).summable

theorem G_nonneg (η : ℝ) : 0 ≤ G η := tsum_nonneg (gaussSummand_nonneg η)

end BecknerOnofri.V2.ThetaTail
