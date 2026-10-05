module

public import BecknerOnofri.SmoothTorusFourierDecay
public import BecknerOnofri.OnsetSobolev

@[expose] public section

/-! Raw smooth functions belong to the actual Fourier-defined Sobolev spaces,
including the critical domain. No summability assumption is added. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
namespace BecknerOnofri.SmoothTorus
open HighDim

theorem real_continuous {d : ℕ} {f : Torus d → ℝ} (hf : SmoothOnTorus f) :
    Continuous f := by
  simpa only [Function.comp_def,Complex.ofReal_re] using
    Complex.continuous_re.comp (smooth_continuous (of_real hf))

theorem smooth_mem_sobolev {d : ℕ} {f : Torus d → ℝ} (hf : SmoothOnTorus f) (s : ℝ) :
    InSobolev s f := by
  obtain ⟨m,hm⟩ := exists_nat_ge s
  obtain ⟨C,hC,hbound⟩ := rapid_coefficient_bound (of_real hf) 0
  have hc (k : Frequency d) : ‖fourierCoeff f k‖ ≤ C := by
    simpa only [pow_zero,one_mul,SmoothTorus.coefficient,HighDim.fourierCoeff] using hbound k
  refine ⟨(real_continuous hf).memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _),?_⟩
  apply ((smooth_fourier_moments hf (2*m)).mul_left ((1+2*Real.pi)^(2*m)*C)).of_nonneg_of_le
    (fun k => by unfold sobolevTerm; positivity)
  intro k
  have hr : 0 ≤ frequencyLength k := Real.sqrt_nonneg _
  have hw : (1+(2*Real.pi*frequencyLength k)^2)^s ≤
      (1+2*Real.pi)^(2*m)*(1+frequencyLength k)^(2*m) :=
    OnsetSobolev.physical_weight_le_radial hm k
  unfold sobolevTerm
  calc
    _ ≤ ((1+2*Real.pi)^(2*m)*(1+frequencyLength k)^(2*m))*‖fourierCoeff f k‖^2 :=
      mul_le_mul_of_nonneg_right hw (sq_nonneg _)
    _ ≤ ((1+2*Real.pi)^(2*m)*(1+frequencyLength k)^(2*m))*(C*‖fourierCoeff f k‖) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith [hc k,norm_nonneg (fourierCoeff f k)]
    _ = _ := by ring

theorem smooth_mem_critical {d : ℕ} {f : Torus d → ℝ} (hf : SmoothOnTorus f) :
    InCriticalSobolev f := by
  obtain ⟨C,hC,hbound⟩ := rapid_coefficient_bound (of_real hf) 0
  have hc (k : Frequency d) : ‖fourierCoeff f k‖ ≤ C := by
    simpa only [pow_zero,one_mul,SmoothTorus.coefficient,HighDim.fourierCoeff] using hbound k
  refine ⟨(real_continuous hf).memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _),?_⟩
  apply (((smooth_fourier_moments hf d).mul_left ((2*Real.pi)^d*C)).subtype (fun k => k≠0)).of_nonneg_of_le
    (fun k => by unfold potentialTerm frequencyLength; positivity)
  intro k
  have hr : 0 ≤ frequencyLength k.val := Real.sqrt_nonneg _
  unfold potentialTerm
  rw [mul_pow]
  calc
    _ ≤ (2*Real.pi)^d*(1+frequencyLength k.val)^d*‖fourierCoeff f k.val‖^2 := by
      gcongr
      linarith
    _ ≤ (2*Real.pi)^d*(1+frequencyLength k.val)^d*(C*‖fourierCoeff f k.val‖) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith [hc k.val,norm_nonneg (fourierCoeff f k.val)]
    _ = _ := by simp only [Function.comp_apply]; ring

#print axioms smooth_mem_sobolev
#print axioms smooth_mem_critical
end BecknerOnofri.SmoothTorus
