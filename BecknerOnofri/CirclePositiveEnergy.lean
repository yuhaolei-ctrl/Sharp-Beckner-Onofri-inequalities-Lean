module

public import BecknerOnofri.ExtendedEntropyDefinitions
public import BecknerOnofri.LegacyBridge
public import Legacy.TorusEndpoint.SpectralEntropy

@[expose] public section

/-! The one-sided Fourier sum in the circle entropy inequality is controlled
by half the full spectral energy. All sums are extended nonnegative sums. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped BigOperators ENNReal
namespace BecknerOnofri.HighDim

private def signedFrequency (p : Bool × ℕ) : NonzeroFrequency 1 :=
  ⟨(fun _ => if p.1 then (p.2+1:ℤ) else -(p.2+1:ℤ)), by
    intro h
    have he := congrFun h 0
    rcases p with ⟨b,n⟩
    cases b <;> simp at he <;> omega⟩

private lemma signedFrequency_injective : Function.Injective signedFrequency := by
  rintro ⟨b,n⟩ ⟨c,m⟩ h
  have he := congrArg (fun k : NonzeroFrequency 1 => k.val 0) h
  cases b <;> cases c <;> simp [signedFrequency] at he ⊢ <;> omega

private lemma signedFrequency_term (ρ : ProbabilityDensity 1) (p : Bool × ℕ) :
    spectralTerm ρ (signedFrequency p) =
      ‖fourierCoeff ρ.value (fun _ => (p.2+1:ℤ))‖^2/(p.2+1:ℝ) := by
  rcases p with ⟨b,n⟩
  have hn : (0:ℝ) ≤ (n:ℝ)+1 := by positivity
  have hneg : ‖fourierCoeff ρ.value (fun _ => -(n+1:ℤ))‖ =
      ‖fourierCoeff ρ.value (fun _ => (n+1:ℤ))‖ :=
    Legacy.TorusEndpoint.densityFourier_norm_neg (Bridge.density ρ) (fun _ => (n+1:ℤ))
  cases b <;>
    simp [spectralTerm, signedFrequency, frequencyLength, hneg, Real.sqrt_sq_eq_abs,
      abs_of_nonneg hn, div_eq_mul_inv, mul_comm]
  rw [show (-1 + -(n:ℝ)) = -((n:ℝ)+1) by ring,
    show (-1 + -(n:ℤ)) = -((n:ℤ)+1) by ring, abs_neg, abs_of_nonneg hn, hneg]

lemma circlePositiveEnergy_twice_le (ρ : ProbabilityDensity 1) :
    2*circlePositiveEnergy ρ ≤ spectralEnergy ρ := by
  have h := ENNReal.tsum_comp_le_tsum_of_injective signedFrequency_injective
    (fun k => ENNReal.ofReal (spectralTerm ρ k))
  have he : (∑' p : Bool × ℕ, ENNReal.ofReal (spectralTerm ρ (signedFrequency p))) =
      2*circlePositiveEnergy ρ := by
    simp_rw [signedFrequency_term]
    rw [ENNReal.tsum_prod']
    simp [circlePositiveEnergy, tsum_fintype, two_mul]
  rw [he] at h
  exact h

#print axioms circlePositiveEnergy_twice_le
end BecknerOnofri.HighDim
