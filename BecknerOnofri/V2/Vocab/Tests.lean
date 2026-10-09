module

public import BecknerOnofri.V2.Vocab.HomEntropyTorus
public import Mathlib.Probability.Distributions.Geometric
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.PSeries

@[expose] public section

/-! # Theorem-level tests for the homogeneous entropy (G01)

* the zero function, constants of every finite nonnegative mass, unit mass;
* an almost-everywhere-modified representative (a non-constant function with entropy `0`);
* a finite-mass function whose `f log f` has non-integrable positive part, hence entropy `⊤`
  (on the geometric probability space `(ℕ, 2^{-(n+1)})`, `f n = 2^{n+1}/(n+1)^2`).
Everything is proved; nothing is evaluated numerically. -/

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace BecknerOnofri.V2.Vocab.Tests
open BecknerOnofri.V2.Vocab BecknerOnofri.HighDim

section Generic
variable {α : Type*} [MeasurableSpace α] (μ : Measure α)

/-- The zero function: mass zero, entropy zero (on every measure). -/
theorem zero_function : homEntropy μ (fun _ => (0 : ℝ)) = 0 := homEntropy_zero

/-- Constants of every finite nonnegative mass `c` have entropy zero, and lie in the domain. -/
theorem constant_function [IsProbabilityMeasure μ] (c : ℝ) (hc : 0 ≤ c) :
    FiniteMassDomain μ (fun _ => c) ∧ ∫ _x, c ∂μ = c ∧ homEntropy μ (fun _ => c) = 0 :=
  ⟨FiniteMassDomain.const hc, integral_const_prob c, homEntropy_const hc⟩

/-- Unit mass: the entropy integrand is the classical `f log f - f + 1`. -/
theorem unit_mass {f : α → ℝ} (h : ∫ x, f x ∂μ = 1) :
    homEntropy μ f = ∫⁻ x, ENNReal.ofReal (f x * Real.log (f x) - f x + 1) ∂μ :=
  homEntropy_of_mass_one h

/-- Positive homogeneity (all `c ≥ 0`) and the normalized-density formula. -/
theorem homogeneity {f : α → ℝ} (c : ℝ) (hc : 0 ≤ c) :
    homEntropy μ (fun x => c * f x) = ENNReal.ofReal c * homEntropy μ f :=
  homEntropy_const_mul hc f

end Generic

section TorusTests
variable (d : ℕ)

/-- Unit mass on the torus: the uniform density has zero entropy, and `entropy = 0` agrees. -/
theorem uniform_density_entropy_zero : torusEntropy (uniformDensity d).value = 0 :=
  homEntropy_const zero_le_one

/-- The torus constant of mass `3`. -/
theorem torus_constant_three :
    ∫ _x : Torus d, (3 : ℝ) ∂torusMeasure d = 3 ∧ torusEntropy (fun _ : Torus d => (3 : ℝ)) = 0 :=
  ⟨integral_const_prob 3, homEntropy_const (by norm_num)⟩

/-- Unit-mass bridge to the existing real `entropy`. -/
theorem unit_mass_bridge_real (ρ : ProbabilityDensity d) (hρ : ρ.FiniteEntropy) :
    torusEntropy ρ.value = ENNReal.ofReal (entropy ρ) :=
  torusEntropy_density_eq_ofReal_entropy ρ hρ

/-- Unit-mass bridge to the existing `extendedEntropy`, with no finiteness hypothesis. -/
theorem unit_mass_bridge_extended (ρ : ProbabilityDensity d) :
    extendedEntropy ρ = (torusEntropy ρ.value : EReal) :=
  extendedEntropy_eq_torusEntropy ρ

end TorusTests

section AEModified
/-- The probability space `Bool` with the Dirac mass at `true`. -/
abbrev diracTrue : Measure Bool := Measure.dirac true

/-- `1` at `true`, `100` at `false`: a non-constant function equal a.e. to the constant `1`. -/
def modified : Bool → ℝ := fun b => if b then 1 else 100

theorem modified_not_constant : ¬ ∀ b c, modified b = modified c := by
  intro h
  have := h true false
  simp [modified] at this

theorem modified_ae_eq_one : modified =ᵐ[diracTrue] fun _ => (1 : ℝ) := by
  have : diracTrue {b | ¬ modified b = 1} = 0 := by
    rw [Measure.dirac_apply' _ (by measurability)]
    simp [modified]
  exact this

/-- An a.e.-modified representative of the constant `1` has entropy `0` and the same mass. -/
theorem modified_entropy_zero :
    FiniteMassDomain diracTrue modified ∧ ∫ b, modified b ∂diracTrue = 1 ∧
      homEntropy diracTrue modified = 0 := by
  have hdom : FiniteMassDomain diracTrue modified :=
    (FiniteMassDomain.const (μ := diracTrue) (zero_le_one' ℝ)).congr_ae modified_ae_eq_one.symm
  refine ⟨hdom, ?_, ?_⟩
  · rw [integral_congr_ae modified_ae_eq_one]
    exact integral_const_prob 1
  · rw [homEntropy_congr_ae modified_ae_eq_one]
    exact homEntropy_const zero_le_one

/-- The zero-entropy criterion: a function is a.e. constant (here, equal to its mass `1`). -/
theorem modified_ae_const :
    modified =ᵐ[diracTrue] fun _ => ∫ y, modified y ∂diracTrue :=
  (homEntropy_eq_zero_iff modified_entropy_zero.1).1 modified_entropy_zero.2.2

end AEModified

section InfiniteEntropy

/-- Success probability `1/2`: the geometric probability measure `μ{n} = 2^{-(n+1)}` on `ℕ`. -/
def pHalf : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩

lemma pHalf_ne : pHalf ≠ 0 := by
  intro h
  have := congrArg Subtype.val h
  simp [pHalf] at this

lemma pHalf_weight (n : ℕ) : (1 - (pHalf : ℝ)) ^ n * (pHalf : ℝ) = (1 / 2 : ℝ) ^ (n + 1) := by
  have : (1 - (pHalf : ℝ)) = 1 / 2 := by simp [pHalf]; norm_num
  rw [this, show (pHalf : ℝ) = 1 / 2 from rfl, pow_succ]

/-- The probability space `(ℕ, 2^{-(n+1)})`. -/
abbrev geomHalf : Measure ℕ := geometricMeasure pHalf

/-- `f n = 2^{n+1} / (n+1)^2`, so that `f n · μ{n} = 1/(n+1)^2`. -/
def heavy (n : ℕ) : ℝ := 2 ^ (n + 1) / ((n : ℝ) + 1) ^ 2

lemma heavy_pos (n : ℕ) : 0 < heavy n := by unfold heavy; positivity

lemma weight_mul_heavy (n : ℕ) : (1 - (pHalf : ℝ)) ^ n * (pHalf : ℝ) * heavy n = 1 / ((n : ℝ) + 1) ^ 2 := by
  rw [pHalf_weight]
  unfold heavy
  have h2 : (2 : ℝ) ^ (n + 1) ≠ 0 := by positivity
  have h1 : ((n : ℝ) + 1) ^ 2 ≠ 0 := by positivity
  rw [one_div, inv_pow]
  field_simp

lemma summable_inv_sq_succ : Summable fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2 := by
  have := (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 (by norm_num : 1 < 2))
  simpa using this

/-- `heavy` has finite mass (and is nonnegative): it lies in the domain. -/
theorem heavy_mem_domain : FiniteMassDomain geomHalf heavy := by
  refine ⟨Filter.Eventually.of_forall fun n => (heavy_pos n).le, ?_⟩
  rw [integrable_geometricMeasure_iff pHalf_ne]
  refine summable_inv_sq_succ.congr fun n => ?_
  rw [Real.norm_of_nonneg (heavy_pos n).le, weight_mul_heavy]

/-- Eventually `2 log (n+1) ≤ (log 2 / 2) (n + 1)`. -/
lemma eventually_two_log_le :
    ∀ᶠ n : ℕ in Filter.atTop, 2 * Real.log ((n : ℝ) + 1) ≤ Real.log 2 / 2 * ((n : ℝ) + 1) := by
  have hε : 0 < Real.log 2 / 4 := by have := Real.log_pos (by norm_num : (1 : ℝ) < 2); positivity
  have h := Real.isLittleO_log_id_atTop.def hε
  have h2 : ∀ᶠ n : ℕ in Filter.atTop, ‖Real.log ((n : ℝ) + 1)‖ ≤ Real.log 2 / 4 * ‖((n : ℝ) + 1)‖ := by
    have ht : Filter.Tendsto (fun n : ℕ => (n : ℝ) + 1) Filter.atTop Filter.atTop :=
      Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    exact ht.eventually h
  filter_upwards [h2] with n hn
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hpos] at hn
  have := le_abs_self (Real.log ((n : ℝ) + 1))
  nlinarith

/-- The positive part of `f log f` is not integrable: it dominates `(log 2 / 2) / (n+1)` eventually. -/
theorem heavy_mul_log_not_integrable :
    ¬ Integrable (fun n => heavy n * Real.log (heavy n)) geomHalf := by
  intro hint
  rw [integrable_geometricMeasure_iff pHalf_ne] at hint
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hharm : ¬ Summable fun n : ℕ => Real.log 2 / 2 * (1 / ((n : ℝ) + 1)) := by
    intro hs
    have hs' : Summable fun n : ℕ => 1 / ((n : ℝ) + 1) := by
      have := hs.mul_left (2 / Real.log 2)
      refine this.congr fun n => ?_
      field_simp
    have h2 : Summable fun n : ℕ => 1 / (n : ℝ) :=
      (summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ)) 1).1 (by simpa using hs')
    exact Real.not_summable_one_div_natCast h2
  apply hharm
  refine Summable.of_norm_bounded_eventually hint ?_
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [eventually_two_log_le] with n hn
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hlogf : Real.log (heavy n) = ((n : ℝ) + 1) * Real.log 2 - 2 * Real.log ((n : ℝ) + 1) := by
    unfold heavy
    rw [Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    push_cast
    ring
  have hlow : Real.log 2 / 2 * ((n : ℝ) + 1) ≤ Real.log (heavy n) := by
    rw [hlogf]; nlinarith
  have hw : (1 - (pHalf : ℝ)) ^ n * (pHalf : ℝ) * ‖heavy n * Real.log (heavy n)‖ =
      1 / ((n : ℝ) + 1) ^ 2 * |Real.log (heavy n)| := by
    rw [norm_mul, Real.norm_of_nonneg (heavy_pos n).le, ← mul_assoc, weight_mul_heavy]
    rfl
  rw [hw]
  have habs : Real.log 2 / 2 * ((n : ℝ) + 1) ≤ |Real.log (heavy n)| := hlow.trans (le_abs_self _)
  calc ‖Real.log 2 / 2 * (1 / ((n : ℝ) + 1))‖ = Real.log 2 / 2 * (1 / ((n : ℝ) + 1)) :=
        Real.norm_of_nonneg (by positivity)
    _ = 1 / ((n : ℝ) + 1) ^ 2 * (Real.log 2 / 2 * ((n : ℝ) + 1)) := by field_simp
    _ ≤ 1 / ((n : ℝ) + 1) ^ 2 * |Real.log (heavy n)| :=
        mul_le_mul_of_nonneg_left habs (by positivity)

/-- A finite-mass nonnegative function whose positive part of `f log f` is not integrable has
homogeneous entropy `⊤`; the negative part is integrable (no `∞ - ∞`). -/
theorem heavy_entropy_top :
    FiniteMassDomain geomHalf heavy ∧
      ∫⁻ n, ENNReal.ofReal (-(heavy n * Real.log (heavy n))) ∂geomHalf < ∞ ∧
      ¬ Integrable (fun n => heavy n * Real.log (heavy n)) geomHalf ∧
      homEntropy geomHalf heavy = ∞ := by
  refine ⟨heavy_mem_domain, heavy_mem_domain.lintegral_neg_mul_log_lt_top,
    heavy_mul_log_not_integrable, ?_⟩
  by_contra h
  exact heavy_mul_log_not_integrable ((integrable_mul_log_iff heavy_mem_domain).2 h)

end InfiniteEntropy

end BecknerOnofri.V2.Vocab.Tests
