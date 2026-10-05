module

public import BecknerOnofri.Definitions
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

/-! Actual Haar-density entropy nonnegativity and rigidity.
The scalar Young argument follows the supplied low-dimensional project's
`TorusEndpoint/EntropyVariational.lean`; the short integrated proof here
is specialized to the trusted definitions of this project.
-/

noncomputable section
open MeasureTheory

namespace BecknerOnofri.HighDim

theorem entropy_young (r u : ℝ) (hr : 0 ≤ r) :
    r * u ≤ r * Real.log r - r + Real.exp u := by
  by_cases hz : r = 0
  · simpa [hz] using Real.exp_nonneg u
  have hp : 0 < r := lt_of_le_of_ne hr (Ne.symm hz)
  have h := Real.add_one_le_exp (u - Real.log r)
  rw [Real.exp_sub, Real.exp_log hp] at h
  have hm := (le_div_iff₀ hp).mp h
  nlinarith

theorem entropy_young_eq_iff {r u : ℝ} (hr : 0 ≤ r) :
    r * u = r * Real.log r - r + Real.exp u ↔ r = Real.exp u := by
  constructor
  · intro he
    by_contra hne
    by_cases hz : r = 0
    · simp only [hz, zero_mul, sub_zero, zero_add] at he
      exact (Real.exp_pos u).ne he
    have hp : 0 < r := lt_of_le_of_ne hr (Ne.symm hz)
    have hdiff : u - Real.log r ≠ 0 := by
      intro h
      have hu := sub_eq_zero.mp h
      exact hne (by rw [hu, Real.exp_log hp])
    have h := Real.add_one_lt_exp hdiff
    rw [Real.exp_sub, Real.exp_log hp] at h
    have hm := (lt_div_iff₀ hp).mp h
    nlinarith
  · intro he
    rw [he, Real.log_exp]
    ring

theorem entropy_nonneg {d : ℕ} (ρ : ProbabilityDensity d) (hρ : ρ.FiniteEntropy) :
    0 ≤ entropy ρ := by
  have hpoint : (fun x => ρ.value x - 1) ≤ᵐ[torusMeasure d]
      (fun x => ρ.value x * Real.log (ρ.value x)) := by
    filter_upwards [ρ.nonneg] with x hx
    have h := entropy_young (ρ.value x) 0 hx
    simp only [mul_zero, Real.exp_zero] at h
    linarith
  have h := integral_mono_ae (ρ.integrable.sub (integrable_const 1)) hρ hpoint
  simpa [integral_sub ρ.integrable (integrable_const 1), ρ.mass, entropy] using h

theorem entropy_eq_zero_iff {d : ℕ} (ρ : ProbabilityDensity d) (hρ : ρ.FiniteEntropy) :
    entropy ρ = 0 ↔ ρ.value =ᵐ[torusMeasure d] (fun _ => 1) := by
  constructor
  · intro he
    have hpoint : (fun x => ρ.value x - 1) ≤ᵐ[torusMeasure d]
        (fun x => ρ.value x * Real.log (ρ.value x)) := by
      filter_upwards [ρ.nonneg] with x hx
      have h := entropy_young (ρ.value x) 0 hx
      simp only [mul_zero, Real.exp_zero] at h
      linarith
    have hi : (∫ x, ρ.value x - 1 ∂torusMeasure d) =
        ∫ x, ρ.value x * Real.log (ρ.value x) ∂torusMeasure d := by
      rw [integral_sub ρ.integrable (integrable_const 1), ρ.mass]
      simpa [entropy] using he.symm
    have hae := (integral_eq_iff_of_ae_le
      (ρ.integrable.sub (integrable_const 1)) hρ hpoint).mp hi
    filter_upwards [ρ.nonneg, hae] with x hx heq
    change ρ.value x - 1 = ρ.value x * Real.log (ρ.value x) at heq
    have heq' : ρ.value x * 0 =
        ρ.value x * Real.log (ρ.value x) - ρ.value x + Real.exp 0 := by
      rw [Real.exp_zero]
      linarith
    simpa using (entropy_young_eq_iff hx).mp heq'
  · intro he
    unfold entropy
    calc
      _ = ∫ _ : Torus d, (1 : ℝ) * Real.log 1 ∂torusMeasure d := by
        apply integral_congr_ae
        filter_upwards [he] with x hx
        rw [hx]
      _ = 0 := by simp

end BecknerOnofri.HighDim
