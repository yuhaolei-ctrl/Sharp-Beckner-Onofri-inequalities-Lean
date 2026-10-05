module

public import BecknerOnofri.EntropyMainTheorems
public import BecknerOnofri.OrderParameterOnset
public import BecknerOnofri.OrderParameterShell
public import BecknerOnofri.QuadraticOnsetDerivative

@[expose] public section

/-! Unconditional source-facing consequences of the full high-dimensional route. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter MeasureTheory
open scoped Topology
namespace BecknerOnofri.HighDim.OnsetConsequences

lemma pressure_monotone {d : ℕ} (hd : 0 < d) : Monotone (pressure d) := by
  intro a b hab
  apply iSup_le fun ρ => iSup_le fun hρ => ?_
  apply le_trans ?_ (le_iSup_of_le ρ (le_iSup_of_le hρ le_rfl) : pressureValue b ρ ≤ pressure d b)
  change pressureValue a ρ ≤ pressureValue b ρ
  simp only [pressureValue,spectralEnergy_coe_eq_tsum hd ρ hρ]
  rw [← EReal.coe_mul,← EReal.coe_sub,← EReal.coe_mul,← EReal.coe_sub]
  apply EReal.coe_le_coe_iff.mpr
  apply sub_le_sub_right
  apply mul_le_mul_of_nonneg_right
  · exact div_le_div_of_nonneg_right hab (by positivity [spectralThreshold_pos hd])
  · apply tsum_nonneg
    intro k
    unfold spectralTerm frequencyLength
    positivity

theorem pressure_zero_below {d : ℕ} (hd : 12 ≤ d) {β : ℝ}
    (hβ : β ≤ spectralThreshold d) : pressure d β = 0 := by
  apply le_antisymm _ (pressure_nonneg _ _)
  have h := pressure_monotone (d := d) (by omega) hβ
  rwa [(BecknerOnofri.Target.pressure_threshold d hd).1.2] at h

theorem order_parameter_onset (d : ℕ) (hd : 12 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ β in 𝓝[>] (spectralThreshold d),
      ∀ ρ : ProbabilityDensity d, IsGlobalMinimizer β ρ →
        |firstShellOrderParameter ρ.value -
          Real.sqrt (2*(d:ℝ)/kappa d)*Real.sqrt (onsetDelta d β)| ≤ C*onsetDelta d β :=
  OrderParameterOnset.all_minimizers_bound hd
    (EntropyMinorantCompletion.legacy_endpoint ScalarCertificate.CertifiedMinorant.psi_le_gamma hd)
    (EntropyMinorantCompletion.legacy_rigidity ScalarCertificate.CertifiedMinorant.psi_le_gamma hd)

/-- Both first one-sided derivatives at the spectral threshold are zero. -/
theorem pressure_derivative_at_threshold (d : ℕ) (hd : 12 ≤ d) :
    HasDerivAt (fun β => (pressure d β).toReal) 0 (spectralThreshold d) := by
  obtain ⟨ε,C,hε,hC,hbound⟩ := BecknerOnofri.Target.pressure_onset d hd
  apply zero_derivative_of_quadratic_onset (spectralThreshold_pos (by omega))
    (K := (d:ℝ)/(2*kappa d)) (by positivity [kappa_pos d hd]) hC hε
  · intro β hβ
    rw [pressure_zero_below hd hβ,EReal.toReal_zero]
  · intro β hβ hβε
    obtain ⟨p,hp,hb⟩ := hbound β hβ hβε
    simpa only [hp,EReal.toReal_coe] using hb

#print axioms pressure_monotone
#print axioms order_parameter_onset
#print axioms pressure_derivative_at_threshold
end BecknerOnofri.HighDim.OnsetConsequences
