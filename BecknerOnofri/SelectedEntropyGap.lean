import BecknerOnofri.SelectedEntropyTail
import BecknerOnofri.SpinCubeEnergy
import BecknerOnofri.EntropyEnergySplit

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open Set
namespace BecknerOnofri.HighDim.SelectedNumericalModel
open Legacy.TorusEndpoint Legacy.BecknerOnofri TorusSobolev

theorem spinDensity_continuous {u : TorusL2 12} (hu : Selected u) : Continuous (spinDensity hu).value := by
  obtain ⟨w,N,hw,hm,hSup,he⟩ := spinDensity_mixture hu
  rw [he]
  exact CosineMixtureApproximation.rho_continuous w N hw hSup

/-- The analytic assembly of the new entropy route, retaining its two separate
numerical inputs explicitly. No scalar or spin certificate is assumed internally. -/
theorem selected_entropy_deficit
    (hscalar : ∀ n : ℕ, EntropyTail.scalarTail n ≤ EntropyTail.scalarBudget n)
    {u : TorusL2 12} (hu : Selected u)
    (ψ : ℝ → ℝ) (hc : ContinuousOn ψ (Icc (0 : ℝ) 1))
    (hcv : ConvexOn ℝ (Icc (0 : ℝ) 1) ψ)
    (hminor : ∀ t ∈ Ico (0 : ℝ) 1, ψ t ≤ CircleScalar.gamma t) :
    Spin.functional (Spin.countLaw (Spin.channelLaw (spinDensity hu)))+
      12*ψ (Spin.mean (Spin.countLaw (Spin.channelLaw (spinDensity hu)))) ≤
        HighDim.entropy (spinDensity hu)-(1/2 : ℝ)*EntropyTail.fullFourierEnergy (spinDensity hu).value := by
  have htail := selected_entropy_minus_tail hscalar hu ψ hc hcv hminor
  have hcube := Spin.cube_half_energy_eq_quadratic (spinDensity hu) (spinDensity_mixture hu)
    (selected_spin_exchangeable hu)
  have hsplit := EntropyTail.fullFourierEnergy_split (spinDensity_continuous hu)
  unfold Spin.functional
  linarith

theorem selected_spin_mean_range {u : TorusL2 12} (hu : Selected u) :
    Spin.mean (Spin.countLaw (Spin.channelLaw (spinDensity hu))) ∈ Icc (0 : ℝ) 1 := by
  have heq : Spin.mean (Spin.countLaw (Spin.channelLaw (spinDensity hu))) =
      (HighDim.fourierCoeff (spinDensity hu).value (Pi.single (0 : Fin 12) (1 : ℤ))).re := by
    rw [density_axis_re hu, density_axis_mean hu]
  rw [heq]
  obtain ⟨w,N,hw,hm,hSup,he⟩ := spinDensity_mixture hu
  rw [he]
  change (densityFourier (CosineMixtureApproximation.rho w N) (Pi.single (0 : Fin 12) (1 : ℤ))).re ∈ Icc (0 : ℝ) 1
  rw [CosineMixtureTransfer.rho_fourier w N hw hm.summable, Complex.ofReal_re]
  constructor
  · exact tsum_nonneg (fun n => mul_nonneg (hw n) (RandomRectangles.componentCoeff_nonneg _ _))
  · have hsum := CosineMixtureTransfer.summable_mixture_coeff w N hw hm.summable
      (Pi.single (0 : Fin 12) (1 : ℤ))
    have hle := hsum.tsum_le_tsum (fun n => mul_le_of_le_one_right (hw n)
      (CosineMixtureTransfer.componentCoeff_le_one _ _)) hm.summable
    exact hle.trans_eq hm.tsum_eq

theorem selected_global_gap_of_certificates
    (hscalar : ∀ n : ℕ, EntropyTail.scalarTail n ≤ EntropyTail.scalarBudget n)
    (ψ : ℝ → ℝ) (hc : ContinuousOn ψ (Icc (0 : ℝ) 1))
    (hcv : ConvexOn ℝ (Icc (0 : ℝ) 1) ψ)
    (hminor : ∀ t ∈ Ico (0 : ℝ) 1, ψ t ≤ CircleScalar.gamma t)
    (hspin : ∀ q : Spin.Count → ℝ, Spin.Feasible q → Spin.mean q ∈ Icc (0 : ℝ) 1 →
      (Spin.mean q)^4/250 ≤ Spin.functional q+12*ψ (Spin.mean q))
    {u : TorusL2 12} (hu : Selected u) :
    (Spin.mean (Spin.countLaw (Spin.channelLaw (spinDensity hu))))^4/250 ≤
      HighDim.entropy (spinDensity hu)-(1/2 : ℝ)*EntropyTail.fullFourierEnergy (spinDensity hu).value :=
  (hspin _ (selected_spin_feasible hu) (selected_spin_mean_range hu)).trans
    (selected_entropy_deficit hscalar hu ψ hc hcv hminor)

#print axioms selected_global_gap_of_certificates
end BecknerOnofri.HighDim.SelectedNumericalModel
