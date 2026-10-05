import Legacy.BecknerOnofri.GaussianScalarTail
import Legacy.BecknerOnofri.MixedBinomialComparison
import Legacy.BecknerOnofri.CosineMixtureAxis

/-! The genuine spectral endpoint for strictly positive finite correlated
cosine-power mixtures in dimensions three through ten. All scalar and
mixture estimates used here are proved in the imported modules. -/

noncomputable section
open Finset MeasureTheory Legacy.TorusEndpoint

namespace Legacy.BecknerOnofri.FiniteMixtureEndpoint
open CosineMixtureEnergy GaussianScalarTail

theorem component_bound {d : ℕ} (hd3 : 3 ≤ d) (hd10 : d ≤ 10) (N : Fin d → ℕ) :
    (2 * endpointConstant d) * componentEnergy N ≤
      ∑ i, (Legacy.D10.FiniteScalar.harmonic (N i) : ℝ) := by
  have hd0 : 0 < d := by omega
  have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr hd0
  calc
    _ ≤ (2 * endpointConstant d) * ((1/(d:ℝ)) *
        ∑ i, GaussianLattice.binomialEnergy d (N i)) :=
      mul_le_mul_of_nonneg_left (MixedBinomialComparison.componentEnergy_le_average_diagonal hd0 N)
        (coefficient_nonneg hd0)
    _ = (1/(d:ℝ)) * ∑ i, (2 * endpointConstant d) *
        GaussianLattice.binomialEnergy d (N i) := by rw [← mul_sum]; ring
    _ ≤ (1/(d:ℝ)) * ∑ i, (d:ℝ) * (Legacy.D10.FiniteScalar.harmonic (N i) : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum (fun i _ => all_indices_lattice_bound hd3 hd10 (N i))
    _ = _ := by rw [← mul_sum]; field_simp

theorem finite_mixture_endpoint {α : Type*} {d : ℕ} (hd3 : 3 ≤ d) (hd10 : d ≤ 10)
    (s : Finset α) (w : α → ℝ) (N : α → Fin d → ℕ)
    (hw : ∀ a ∈ s, 0 ≤ w a) (hm : ∑ a ∈ s, w a = 1)
    (hpos : ∀ x, 0 < CosineMixture.mixture s w N x) :
    Summable (densitySpectralTerm (CosineMixture.density s w N hw hm)) ∧
      endpointConstant d * fourierEnergy (CosineMixture.density s w N hw hm) ≤
        densityEntropy (CosineMixture.density s w N hw hm).value := by
  refine ⟨spectral_summable s w N hw hm, ?_⟩
  have he : (2 * endpointConstant d) *
      fourierEnergy (CosineMixture.density s w N hw hm) ≤
        ∑ a ∈ s, ∑ b ∈ s, ∑ L ∈ Legacy.D10.latentBox (N a),
          w a * w b * Legacy.D10.latentWeight (N a) (N b) L *
            ∑ i, (Legacy.D10.FiniteScalar.harmonic (L i) : ℝ) := by
    rw [fourierEnergy_eq_latent]
    simp only [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro a ha
    apply Finset.sum_le_sum
    intro b hb
    apply Finset.sum_le_sum
    intro L hL
    have hnon := Legacy.D10.correlated_latent_nonneg w w N N a b L (hw a ha) (hw b hb)
    simpa only [Finset.mul_sum, mul_assoc, mul_left_comm] using
      mul_le_mul_of_nonneg_left (component_bound hd3 hd10 L) hnon
  have haxis := (TorusMarginals.axis_entropy_bound (by omega : 0 < d)
    (CosineMixture.density s w N hw hm) (CosineMixture.mixture_continuous s w N) hpos).2
  rw [CosineMixtureAxis.density_axis_sum_eq] at haxis
  linarith

#print axioms component_bound
#print axioms finite_mixture_endpoint
end Legacy.BecknerOnofri.FiniteMixtureEndpoint
