import BecknerOnofri.BranchDefinitions
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! The actual discrete spectral gap away from constants and the first shell,
with a bounded inverse of the linearized Fourier multiplier. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators
open Finset

namespace BecknerOnofri.HighDim

/-- The integer-valued squared Euclidean frequency length. -/
def latticeSquare {d : ℕ} (k : Frequency d) : ℕ := ∑ i, (k i).natAbs ^ 2

/-- The first nonzero eigenspace consists of exactly ± the coordinate modes. -/
def InFirstShell {d : ℕ} (k : Frequency d) : Prop :=
  ∃ i : Fin d, k = axisFrequency i ∨ k = -axisFrequency i

/-- Frequencies in the mean-zero orthogonal complement of the first shell. -/
def ComplementFrequency {d : ℕ} (k : Frequency d) : Prop := k ≠ 0 ∧ ¬ InFirstShell k

theorem latticeSquare_cast {d : ℕ} (k : Frequency d) :
    (latticeSquare k : ℝ) = ∑ i : Fin d, (k i : ℝ)^2 := by
  simp only [latticeSquare, Nat.cast_sum, Nat.cast_pow, Nat.cast_natAbs, Int.cast_abs, sq_abs]

theorem latticeSquare_eq_zero_iff {d : ℕ} (k : Frequency d) : latticeSquare k = 0 ↔ k = 0 := by
  constructor
  · intro hk
    funext i
    have hle := single_le_sum (fun j _ => Nat.zero_le ((k j).natAbs^2)) (mem_univ i)
    change (k i).natAbs^2 ≤ latticeSquare k at hle
    rw [hk] at hle
    have hz : (k i).natAbs = 0 := by nlinarith
    exact Int.natAbs_eq_zero.mp hz
  · rintro rfl
    simp [latticeSquare]

theorem latticeSquare_axis {d : ℕ} (i : Fin d) : latticeSquare (axisFrequency i) = 1 := by
  simp [latticeSquare, axisFrequency, apply_ite]

theorem latticeSquare_neg {d : ℕ} (k : Frequency d) : latticeSquare (-k) = latticeSquare k := by
  simp only [latticeSquare, Pi.neg_apply, Int.natAbs_neg]

theorem latticeSquare_eq_one_iff {d : ℕ} (k : Frequency d) :
    latticeSquare k = 1 ↔ InFirstShell k := by
  constructor
  · intro hk
    have hn : k ≠ 0 := by intro hz; rw [hz] at hk; simp [latticeSquare] at hk
    have hex : ∃ i, k i ≠ 0 := by contrapose! hn; exact funext hn
    obtain ⟨i, hi⟩ := hex
    have hi0 : 0 < (k i).natAbs := Int.natAbs_pos.mpr hi
    have hle := single_le_sum (fun j _ => Nat.zero_le ((k j).natAbs^2)) (mem_univ i)
    change (k i).natAbs^2 ≤ latticeSquare k at hle
    rw [hk] at hle
    have hisq : (k i).natAbs^2 = 1 := by nlinarith
    have hiabs : (k i).natAbs = 1 := by nlinarith
    have hsum : (∑ j ∈ univ.erase i, (k j).natAbs^2) = 0 := by
      have h := sum_erase_add (s := univ) (fun j => (k j).natAbs^2) (mem_univ i)
      change _ + (k i).natAbs^2 = latticeSquare k at h
      rw [hk, hisq] at h
      omega
    have hjzero (j : Fin d) (hj : j ≠ i) : k j = 0 := by
      have hjmem : j ∈ univ.erase i := mem_erase.mpr ⟨hj, mem_univ _⟩
      have hle := single_le_sum (fun l _ => Nat.zero_le ((k l).natAbs^2)) hjmem
      rw [hsum] at hle
      have hz : (k j).natAbs = 0 := by nlinarith
      exact Int.natAbs_eq_zero.mp hz
    refine ⟨i, ?_⟩
    have hisign : k i = 1 ∨ k i = -1 := by omega
    rcases hisign with hp | hm
    · left
      funext j
      by_cases hj : j = i
      · subst j
        simp [axisFrequency, hp]
      · simp [axisFrequency, hj, hjzero j hj]
    · right
      funext j
      by_cases hj : j = i
      · subst j
        simp [axisFrequency, hm]
      · simp [axisFrequency, hj, hjzero j hj]
  · rintro ⟨i, rfl | rfl⟩
    · exact latticeSquare_axis i
    · rw [latticeSquare_neg, latticeSquare_axis]

theorem complement_latticeSquare_ge_two {d : ℕ} {k : Frequency d}
    (hk : ComplementFrequency k) : 2 ≤ latticeSquare k := by
  have hzero := (latticeSquare_eq_zero_iff k).not.mpr hk.1
  have hone := (latticeSquare_eq_one_iff k).not.mpr hk.2
  omega

theorem frequencyLength_pow_eq {d : ℕ} (k : Frequency d) :
    frequencyLength k ^ d = (latticeSquare k : ℝ)^((d:ℝ)/2) := by
  unfold frequencyLength
  rw [← latticeSquare_cast, Real.sqrt_eq_rpow, ← Real.rpow_natCast,
    ← Real.rpow_mul (Nat.cast_nonneg _)]
  congr 1
  ring

/-- Exact first-complement eigenvalue √2^d = 2^(d/2). -/
theorem complement_eigenvalue_lower {d : ℕ} {k : Frequency d} (hk : ComplementFrequency k) :
    (2:ℝ)^((d:ℝ)/2) ≤ frequencyLength k ^ d := by
  rw [frequencyLength_pow_eq]
  exact Real.rpow_le_rpow (by norm_num)
    (by exact_mod_cast complement_latticeSquare_ge_two hk) (by positivity)

theorem complement_eigenvalue_ge_sixtyfour {d : ℕ} (hd : 12 ≤ d)
    {k : Frequency d} (hk : ComplementFrequency k) : 64 ≤ frequencyLength k ^ d := by
  have hexp : (6:ℝ) ≤ (d:ℝ)/2 := by
    have : (12:ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hexp
  norm_num at h
  exact h.trans (complement_eigenvalue_lower hk)

/-- Uniform complement coercivity in the useful neighborhood 0≤β/σ≤2. -/
theorem complement_linearized_gap {d : ℕ} (hd : 12 ≤ d) {μ : ℝ}
    (_hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2) {k : Frequency d} (hk : ComplementFrequency k) :
    (31/32:ℝ) ≤ 1 - μ / frequencyLength k ^ d := by
  have hEig := complement_eigenvalue_ge_sixtyfour hd hk
  have hEig0 : 0 < frequencyLength k ^ d := by linarith
  have hdiv : μ / frequencyLength k ^ d ≤ (1/32:ℝ) := by
    apply (div_le_iff₀ hEig0).mpr
    linarith
  linarith

/-- The Fourier inverse multiplier of I−μD⁻¹ on the complement. -/
def complementInverseMultiplier {d : ℕ} (μ : ℝ) (k : Frequency d) : ℝ := by
  classical
  exact if ComplementFrequency k then (1 - μ / frequencyLength k ^ d)⁻¹ else 0

theorem complementInverseMultiplier_nonneg {d : ℕ} (hd : 12 ≤ d) {μ : ℝ}
    (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2) (k : Frequency d) :
    0 ≤ complementInverseMultiplier μ k := by
  unfold complementInverseMultiplier
  split_ifs with hk
  · exact inv_nonneg.mpr (by linarith [complement_linearized_gap hd hμ0 hμ2 hk])
  · rfl

theorem complementInverseMultiplier_bound {d : ℕ} (hd : 12 ≤ d) {μ : ℝ}
    (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2) (k : Frequency d) :
    complementInverseMultiplier μ k ≤ (32/31:ℝ) := by
  unfold complementInverseMultiplier
  split_ifs with hk
  · have hg := complement_linearized_gap hd hμ0 hμ2 hk
    have hp : 0 < 1 - μ / frequencyLength k ^ d := by linarith
    apply (inv_le_comm₀ hp (by norm_num : (0:ℝ)<32/31)).mpr
    norm_num
    exact hg
  · norm_num


/-- Fourier coefficient sequences supported on the genuine spectral complement. -/
def ComplementSupported {d : ℕ} (a : Frequency d → ℂ) : Prop :=
  ∀ k, ¬ ComplementFrequency k → a k = 0

def complementLinearized {d : ℕ} (μ : ℝ) (a : Frequency d → ℂ) : Frequency d → ℂ :=
  fun k => ((1 - μ / frequencyLength k ^ d : ℝ) : ℂ) * a k

def complementInverse {d : ℕ} (μ : ℝ) (a : Frequency d → ℂ) : Frequency d → ℂ :=
  fun k => (complementInverseMultiplier μ k : ℂ) * a k

theorem complementInverse_supported {d : ℕ} (μ : ℝ) (a : Frequency d → ℂ) :
    ComplementSupported (complementInverse μ a) := by
  intro k hk
  simp [complementInverse, complementInverseMultiplier, hk]

theorem complementLinearized_supported {d : ℕ} (μ : ℝ) {a : Frequency d → ℂ}
    (ha : ComplementSupported a) : ComplementSupported (complementLinearized μ a) := by
  intro k hk
  simp [complementLinearized, ha k hk]

theorem complementInverse_left {d : ℕ} (hd : 12 ≤ d) {μ : ℝ}
    (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2) {a : Frequency d → ℂ} (ha : ComplementSupported a) :
    complementInverse μ (complementLinearized μ a) = a := by
  funext k
  by_cases hk : ComplementFrequency k
  · have hpos : 0 < 1 - μ / frequencyLength k ^ d := by
      linarith [complement_linearized_gap hd hμ0 hμ2 hk]
    have hne : ((1 - μ / frequencyLength k ^ d : ℝ):ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr hpos.ne'
    simp only [complementInverse, complementLinearized, complementInverseMultiplier,
      if_pos hk, Complex.ofReal_inv, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
  · simp [complementInverse, complementLinearized, ha k hk]

theorem complementInverse_right {d : ℕ} (hd : 12 ≤ d) {μ : ℝ}
    (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2) {a : Frequency d → ℂ} (ha : ComplementSupported a) :
    complementLinearized μ (complementInverse μ a) = a := by
  funext k
  by_cases hk : ComplementFrequency k
  · have hpos : 0 < 1 - μ / frequencyLength k ^ d := by
      linarith [complement_linearized_gap hd hμ0 hμ2 hk]
    have hne : ((1 - μ / frequencyLength k ^ d : ℝ):ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr hpos.ne'
    simp only [complementInverse, complementLinearized, complementInverseMultiplier,
      if_pos hk, Complex.ofReal_inv, ← mul_assoc, mul_inv_cancel₀ hne, one_mul]
  · simp [complementInverse, complementLinearized, ha k hk]

theorem complementInverse_norm_bound {d : ℕ} (hd : 12 ≤ d) {μ : ℝ}
    (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2) (a : Frequency d → ℂ) (k : Frequency d) :
    ‖complementInverse μ a k‖ ≤ (32/31:ℝ)*‖a k‖ := by
  simp only [complementInverse, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (complementInverseMultiplier_nonneg hd hμ0 hμ2 k)]
  exact mul_le_mul_of_nonneg_right (complementInverseMultiplier_bound hd hμ0 hμ2 k) (norm_nonneg _)

/-- Every weighted Fourier Hilbert norm obeys the same inverse bound. This
applies to all Sobolev weights, and proves preservation of their summability. -/
theorem complementInverse_weighted_bound {d : ℕ} (hd : 12 ≤ d) {μ : ℝ}
    (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2) (a : Frequency d → ℂ) (ω : Frequency d → ℝ)
    (hω : ∀ k, 0 ≤ ω k) (ha : Summable (fun k => ω k * ‖a k‖^2)) :
    Summable (fun k => ω k * ‖complementInverse μ a k‖^2) ∧
      (∑' k, ω k * ‖complementInverse μ a k‖^2) ≤
        (32/31:ℝ)^2 * ∑' k, ω k * ‖a k‖^2 := by
  have hnon (k : Frequency d) : 0 ≤ ω k * ‖complementInverse μ a k‖^2 :=
    mul_nonneg (hω k) (sq_nonneg _)
  have hbound (k : Frequency d) :
      ω k * ‖complementInverse μ a k‖^2 ≤ (32/31:ℝ)^2 * (ω k * ‖a k‖^2) := by
    have h := sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ (32/31:ℝ)*‖a k‖)
      |>.mpr (complementInverse_norm_bound hd hμ0 hμ2 a k)
    have hm := mul_le_mul_of_nonneg_left h (hω k)
    nlinarith
  have hs := (ha.mul_left ((32/31:ℝ)^2)).of_nonneg_of_le hnon hbound
  refine ⟨hs, ?_⟩
  calc
    _ ≤ ∑' k, (32/31:ℝ)^2 * (ω k * ‖a k‖^2) :=
      hs.tsum_le_tsum hbound (ha.mul_left _)
    _ = _ := tsum_mul_left

/-- The actual complement is a complex vector subspace of Fourier sequences. -/
def complementSpace (d : ℕ) : Submodule ℂ (Frequency d → ℂ) where
  carrier := {a | ComplementSupported a}
  zero_mem' := by intro k hk; rfl
  add_mem' := by intro a b ha hb k hk; simp [ha k hk, hb k hk]
  smul_mem' := by intro c a ha k hk; simp [ha k hk]

/-- Algebraic inverse of the exact linearization, with quantitative boundedness
in every weighted Sobolev norm supplied by `complementInverse_weighted_bound`. -/
def complementLinearEquiv {d : ℕ} (hd : 12 ≤ d) {μ : ℝ}
    (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2) : complementSpace d ≃ₗ[ℂ] complementSpace d where
  toFun a := ⟨complementLinearized μ a, complementLinearized_supported μ a.property⟩
  invFun a := ⟨complementInverse μ (a : Frequency d → ℂ),
    complementInverse_supported μ (a : Frequency d → ℂ)⟩
  left_inv a := by apply Subtype.ext; exact complementInverse_left hd hμ0 hμ2 a.property
  right_inv a := by apply Subtype.ext; exact complementInverse_right hd hμ0 hμ2 a.property
  map_add' a b := by
    apply Subtype.ext
    funext k
    simp [complementLinearized, mul_add]
  map_smul' c a := by
    apply Subtype.ext
    funext k
    simp [complementLinearized, mul_left_comm]

#print axioms complement_eigenvalue_lower
#print axioms complementLinearEquiv
#print axioms complementInverse_weighted_bound

end BecknerOnofri.HighDim
