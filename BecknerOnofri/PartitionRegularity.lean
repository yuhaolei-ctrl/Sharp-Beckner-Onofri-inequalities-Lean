module

public import BecknerOnofri.LegacyBridge

@[expose] public section

/-! Finiteness and normalization of the actual extended log-partition.
All exponential integrability is proved from critical Sobolev membership. -/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace BecknerOnofri.HighDim

theorem exp_centered_integrable {d : ℕ} (hd : 0 < d)
    (u : Torus d → ℝ) (hu : InCriticalSobolev u) :
    Integrable (fun x => Real.exp (centered u x)) (torusMeasure d) := by
  simpa using critical_exp_integrable hd u hu (p := 1) zero_lt_one

theorem logPartition_eq_log_integral {d : ℕ} (hd : 0 < d)
    (u : Torus d → ℝ) (hu : InCriticalSobolev u) :
    logPartition u = (Real.log (∫ x, Real.exp (centered u x) ∂torusMeasure d) : EReal) := by
  have hi := exp_centered_integrable hd u hu
  unfold logPartition
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (fun x => (Real.exp_pos _).le)),
    ENNReal.log_ofReal_of_pos (integral_exp_pos hi)]

theorem centered_integral {d : ℕ} (u : Torus d → ℝ)
    (hu : Integrable u (torusMeasure d)) :
    (∫ x, centered u x ∂torusMeasure d) = 0 := by
  unfold centered
  rw [integral_sub hu (integrable_const _)]
  simp

theorem logPartition_nonneg {d : ℕ} (hd : 0 < d)
    (u : Torus d → ℝ) (hu : InCriticalSobolev u) : 0 ≤ logPartition u := by
  have hi := hu.1.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hc : Integrable (centered u) (torusMeasure d) := hi.sub (integrable_const _)
  have hmono := integral_mono (hc.add (integrable_const 1))
    (exp_centered_integrable hd u hu) (fun x => Real.add_one_le_exp (centered u x))
  change (∫ x, centered u x + 1 ∂torusMeasure d) ≤
    ∫ x, Real.exp (centered u x) ∂torusMeasure d at hmono
  rw [integral_add hc (integrable_const 1), centered_integral u hi] at hmono
  have hZ : 1 ≤ ∫ x, Real.exp (centered u x) ∂torusMeasure d := by simpa using hmono
  rw [logPartition_eq_log_integral hd u hu]
  exact_mod_cast Real.log_nonneg hZ

theorem logPartition_finite {d : ℕ} (hd : 0 < d)
    (u : Torus d → ℝ) (hu : InCriticalSobolev u) :
    logPartition u ≠ ⊥ ∧ logPartition u ≠ ⊤ := by
  rw [logPartition_eq_log_integral hd u hu]
  simp

#print axioms logPartition_eq_log_integral
#print axioms logPartition_nonneg

end BecknerOnofri.HighDim
