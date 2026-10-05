import BecknerOnofri.FiniteEntropyPhysical
import BecknerOnofri.PressureDuality
import BecknerOnofri.LowDimensionDefinitions
import Legacy.BecknerOnofri.CollapseDivergence

/-! Both concentration obstructions in every positive dimension, with the
actual full finite-entropy and Sobolev variational domains. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
namespace BecknerOnofri.HighDim

lemma coefficientDefect_antitone {d : ℕ} (hd : 0 < d) : Antitone (coefficientDefect d) := by
  intro A B hAB
  apply iSup_le fun u => iSup_le fun hu => ?_
  apply le_trans ?_ (show logPartition u-((A*potentialEnergy u:ℝ):EReal) ≤ coefficientDefect d A from
    le_iSup_of_le u (le_iSup_of_le hu le_rfl))
  rw [logPartition_eq_log_integral hd u hu]
  have hE : 0 ≤ potentialEnergy u := tsum_nonneg (fun k => by
    unfold potentialTerm frequencyLength
    positivity)
  have h := sub_le_sub_left (mul_le_mul_of_nonneg_right hAB hE)
    (Real.log (∫ x, Real.exp (centered u x) ∂torusMeasure d))
  exact_mod_cast h

lemma pressure_above_collapse {d : ℕ} (hd : 0 < d) {β : ℝ} (hβ : 2*(d:ℝ) < β) :
    pressure d β = ⊤ := by
  apply (EReal.eq_top_iff_forall_lt _).mpr
  intro M
  obtain ⟨t,ht,_,hg⟩ := Legacy.BecknerOnofri.CollapseDivergence.heat_gap_unbounded
    hd (by linarith : (d:ℝ)<β/2) M
  let r := Legacy.TorusEndpoint.EndpointSharpnessHeat.heatDensity d ht
  have hr : r.FiniteEntropy := Legacy.TorusEndpoint.EndpointSharpnessHeat.heatDensity_finiteEntropy d ht
  let ρ := Bridge.rawDensity r
  have hρ : ρ.FiniteEntropy := hr
  have he : Legacy.BecknerOnofri.fourierEnergy r = ∑' k, spectralTerm ρ k :=
    tsum_congr (Bridge.densitySpectralTerm_eq ρ)
  change M < β/2*Legacy.TorusEndpoint.PhysicalGreenL2.physicalGreenEnergy r-
    Legacy.TorusEndpoint.densityEntropy r.value at hg
  rw [FiniteEntropyPhysical.physical_eq_spectral hd r hr,
    Legacy.BecknerOnofri.normalized_energy,he] at hg
  have hs : Legacy.TorusEndpoint.endpointSigma d = spectralThreshold d := rfl
  rw [hs] at hg
  change M < β/2*((∑' k, spectralTerm ρ k)/spectralThreshold d)-entropy ρ at hg
  have hv : (M:EReal) < pressureValue β ρ := by
    unfold pressureValue
    rw [spectralEnergy_coe_eq_tsum hd ρ hρ,← EReal.coe_mul,← EReal.coe_sub]
    apply EReal.coe_lt_coe_iff.mpr
    convert! hg using 1 <;> ring
  exact hv.trans_le (le_iSup_of_le ρ (le_iSup_of_le hρ le_rfl))

lemma coefficientDefect_below_collapse {d : ℕ} (hd : 0 < d) {A : ℝ}
    (hA : A < collapseCoefficient d) : coefficientDefect d A = ⊤ := by
  have hσ := spectralThreshold_pos hd
  have hdR : (0:ℝ)<d := Nat.cast_pos.mpr hd
  have hc : 0 < collapseCoefficient d := by unfold collapseCoefficient; positivity
  obtain ⟨B,hB,hBc⟩ := exists_between (max_lt hA hc)
  have hBp : 0 < B := (le_max_right A 0).trans_lt hB
  have hAB : A ≤ B := ((le_max_left A 0).trans_lt hB).le
  let β := spectralThreshold d/(2*B*(2*Real.pi)^d)
  have hβp : 0 < β := by dsimp [β]; positivity
  have hβ : 2*(d:ℝ) < β := by
    apply (lt_div_iff₀ (by positivity : 0 < 2*B*(2*Real.pi)^d)).mpr
    unfold collapseCoefficient at hBc
    have hh := (lt_div_iff₀ (by positivity : 0 < 4*(d:ℝ)*(2*Real.pi)^d)).mp hBc
    nlinarith
  have he : spectralThreshold d/(2*β*(2*Real.pi)^d) = B := by
    dsimp [β]
    field_simp
  have hInf := pressure_above_collapse hd hβ
  rw [pressure_eq_coefficientDefect hd hβp,he] at hInf
  apply top_le_iff.mp
  rw [← hInf]
  exact coefficientDefect_antitone hd hAB

#print axioms pressure_above_collapse
#print axioms coefficientDefect_below_collapse
end BecknerOnofri.HighDim
