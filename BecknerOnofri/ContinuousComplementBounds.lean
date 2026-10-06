module

public import BecknerOnofri.ContinuousComplementInverse

@[expose] public section

/-! Explicit sup-norm bounds for the actual continuous-function complement inverse. -/
noncomputable section
set_option autoImplicit false
namespace BecknerOnofri.HighDim
open ContinuousGibbs ContinuousFirstShell
open Legacy.BecknerOnofri.TorusSobolev

theorem continuousComplementFourier_norm_le {d : ℕ} (f : complement d) :
    ‖continuousComplementFourier d f‖ ≤ ‖f‖ := by
  change ‖fourierIsometry d (toL2 d f.val)‖ ≤ ‖f.val‖
  rw [(fourierIsometry d).norm_map]
  simpa only [one_mul] using (toL2 d).le_of_opNorm_le (toL2_norm_le d) f.val

theorem greenLiftReal_norm_le {d : ℕ} (hd : 0 < d) (a : realLpComplement d) :
    ‖greenLiftReal hd a‖ ≤ ‖greenFourierVector d‖ * ‖a‖ := by
  refine (ContinuousMap.norm_le _ (by positivity)).mpr fun x => ?_
  exact (Complex.abs_re_le_norm _).trans (greenLiftComplexValue_bound d a.val.val x)

theorem continuousComplementInverse_norm_le {d : ℕ} (hd : 12 ≤ d) {μ : ℝ}
    (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2) (f : complement d) :
    ‖continuousComplementInverse hd hμ0 hμ2 f‖ ≤
      (1 + (64/31:ℝ) * ‖greenFourierVector d‖) * ‖f‖ := by
  change ‖continuousComplementInverseValue hd hμ0 hμ2 f‖ ≤ _
  rw [continuousComplementInverseValue_apply]
  calc
    _ ≤ ‖f.val‖ + ‖μ • greenLiftReal (by omega)
        (realComplementInverse hd hμ0 hμ2 (continuousComplementFourier d f))‖ := norm_add_le _ _
    _ ≤ ‖f‖ + 2 * (‖greenFourierVector d‖ * ((32/31:ℝ) * ‖f‖)) := by
      apply add_le_add le_rfl
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hμ0]
      apply mul_le_mul hμ2 _ (norm_nonneg _) (by norm_num)
      exact (greenLiftReal_norm_le _ _).trans (mul_le_mul_of_nonneg_left
        ((lpComplementInverse_norm_le hd hμ0 hμ2 (continuousComplementFourier d f).val).trans
          (mul_le_mul_of_nonneg_left (continuousComplementFourier_norm_le f) (by norm_num)))
        (norm_nonneg _))
    _ = _ := by ring

theorem continuousComplementGreen_norm_le {d : ℕ} (hd : 0 < d) (f : complement d) :
    ‖continuousComplementGreen hd f‖ ≤ greenKernelNorm d * ‖f‖ := by
  change ‖greenContinuous d f.val‖ ≤ greenKernelNorm d * ‖f.val‖
  exact (greenContinuous d).le_of_opNorm_le (greenContinuous_norm_le d) f.val

#print axioms continuousComplementInverse_norm_le
end BecknerOnofri.HighDim
