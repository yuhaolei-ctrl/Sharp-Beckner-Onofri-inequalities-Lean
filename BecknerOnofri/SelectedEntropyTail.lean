module

public import BecknerOnofri.EntropyTailCountableMixture
public import BecknerOnofri.SelectedChannelEntropy

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open Set
namespace BecknerOnofri.HighDim.SelectedNumericalModel
open Legacy.TorusEndpoint Legacy.BecknerOnofri TorusSobolev

theorem selected_tail_of_scalar
    (hscalar : ∀ n : ℕ, EntropyTail.scalarTail n ≤ EntropyTail.scalarBudget n)
    {u : TorusL2 12} (hu : Selected u) :
    (1/2 : ℝ)*(∑' k : Frequency 12,
      EntropyTail.scalarTailWeight k*‖HighDim.fourierCoeff (spinDensity hu).value k‖^2) ≤
      (21/1000)*(∑ i : Fin 12, ‖HighDim.fourierCoeff (spinDensity hu).value (Pi.single i (2 : ℤ))‖^2)+
        (27/40)*(∑ i : Fin 12, ∑' j : ℕ,
          ‖HighDim.fourierCoeff (spinDensity hu).value (Pi.single i (j+3 : ℤ))‖^2/(j+3 : ℝ)) := by
  obtain ⟨w,N,hw,hm,hSup,he⟩ := spinDensity_mixture hu
  rw [he]
  have h := EntropyTail.countable_mixture_tail_of_scalar hscalar w N hw hm.summable hSup
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at h
  exact h

/-- The channel entropy pays for the actual singular Fourier tail. The scalar
numerical estimate remains explicit until its separate certificate is complete. -/
theorem selected_entropy_minus_tail
    (hscalar : ∀ n : ℕ, EntropyTail.scalarTail n ≤ EntropyTail.scalarBudget n)
    {u : TorusL2 12} (hu : Selected u)
    (ψ : ℝ → ℝ) (hc : ContinuousOn ψ (Icc (0 : ℝ) 1))
    (hcv : ConvexOn ℝ (Icc (0 : ℝ) 1) ψ)
    (hminor : ∀ t ∈ Ico (0 : ℝ) 1, ψ t ≤ CircleScalar.gamma t) :
    2*Spin.relativeEntropy (Spin.countLaw (Spin.channelLaw (spinDensity hu))) Spin.reference+
      12*ψ (Spin.mean (Spin.countLaw (Spin.channelLaw (spinDensity hu)))) ≤
        HighDim.entropy (spinDensity hu)-(1/2 : ℝ)*(∑' k : Frequency 12,
          EntropyTail.scalarTailWeight k*‖HighDim.fourierCoeff (spinDensity hu).value k‖^2) := by
  have htail := selected_tail_of_scalar hscalar hu
  have hent := (selected_channel_fourier_entropy hu ψ hc hcv hminor).2
  linarith

#print axioms selected_entropy_minus_tail
end BecknerOnofri.HighDim.SelectedNumericalModel
