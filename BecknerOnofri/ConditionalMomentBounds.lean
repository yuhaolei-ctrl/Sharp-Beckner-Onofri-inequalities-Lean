module

public import BecknerOnofri.ConditionalExpectations

@[expose] public section

noncomputable section
open MeasureTheory Function

namespace BecknerOnofri.HighDim.ConditionalEntropy
open EntropyShearer

theorem section_integrable {d : ℕ} {f : Torus d → ℝ}
    (hf : BoundedMeasurable f) (i : Fin d) (x : Torus d) :
    Integrable (fun z => f (Function.update x i z)) AddCircle.haarAddCircle := by
  obtain ⟨hm, B, hB⟩ := hf
  have hu : Measurable (fun z : UnitAddCircle => Function.update x i z) := by fun_prop
  exact (integrable_const B).mono' (hm.comp hu).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun z => hB _))

theorem conditional_density_integrable {d : ℕ} {f : Torus d → ℝ}
    (hf : PositiveBounded f) (i : Fin d) (x : Torus d) :
    Integrable (conditionalDensity f i x) AddCircle.haarAddCircle :=
  (section_integrable (prefix_positive hf _).bounded i x).div_const _

theorem conditional_moment_abs_le_one {d : ℕ} {f : Torus d → ℝ}
    (hf : PositiveBounded f) (i : Fin d) (n : ℕ) (x : Torus d) :
    |conditionalCosineMoment f i n x| ≤ 1 := by
  have hbound (z : UnitAddCircle) :
      ‖conditionalDensity f i x z * (fourier (n : ℤ) z).re‖ ≤ conditionalDensity f i x z := by
    rw [norm_mul, Real.norm_eq_abs, abs_of_pos (conditional_density_positive hf i x z)]
    have hc : ‖(fourier (n : ℤ) z).re‖ ≤ 1 := by
      calc
        _ = |(fourier (n : ℤ) z).re| := Real.norm_eq_abs _
        _ ≤ ‖fourier (n : ℤ) z‖ := Complex.abs_re_le_norm _
        _ = 1 := by simp [fourier_apply]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hc
      (conditional_density_positive hf i x z).le
  have h := norm_integral_le_of_norm_le (conditional_density_integrable hf i x)
    (Filter.Eventually.of_forall hbound)
  rw [conditional_density_mass hf i x] at h
  exact h

#print axioms conditional_moment_abs_le_one

end BecknerOnofri.HighDim.ConditionalEntropy
