module

public import BecknerOnofri.GapDefinitions
public import BecknerOnofri.FiniteEntropyDualGap
public import BecknerOnofri.RawAttainment
public import BecknerOnofri.PotentialRigidity

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
namespace BecknerOnofri.HighDim.Gap
open Legacy.BecknerOnofri TorusSobolev SubcriticalAttainment SubcriticalEuler SubcriticalPrimalDual
open RawAttainment

lemma potentialEnergy_congr {d : ℕ} {u v : Torus d → ℝ}
    (he : u =ᵐ[torusMeasure d] v) : potentialEnergy u = potentialEnergy v := by
  apply tsum_congr
  intro k
  simp only [potentialTerm,HighDim.fourierCoeff_congr_ae he]

lemma potentialValue_congr {d : ℕ} (β : ℝ) {u v : Torus d → ℝ}
    (he : u =ᵐ[torusMeasure d] v) : potentialValue β u = potentialValue β v := by
  unfold potentialValue
  rw [potentialEnergy_congr he]
  congr 2
  exact integral_congr_ae (he.fun_comp Real.exp)

lemma gibbs_congr {d : ℕ} {u v : Torus d → ℝ} (he : u =ᵐ[torusMeasure d] v) :
    normalizedGibbs u =ᵐ[torusMeasure d] normalizedGibbs v := by
  have hi : (∫ x,Real.exp (u x) ∂torusMeasure d) =
      ∫ x,Real.exp (v x) ∂torusMeasure d := integral_congr_ae (he.fun_comp Real.exp)
  filter_upwards [he] with x hx
  simp only [normalizedGibbs,hi,hx]

lemma relativeEntropy_congr {d : ℕ} {f f' g g' : Torus d → ℝ}
    (hf : f =ᵐ[torusMeasure d] f') (hg : g =ᵐ[torusMeasure d] g') :
    relativeEntropy f g = relativeEntropy f' g' := by
  apply integral_congr_ae
  filter_upwards [hf,hg] with x hx hy
  rw [hx,hy]

lemma densityValue_congr {d : ℕ} (β : ℝ) {f g : Torus d → ℝ}
    (he : f =ᵐ[torusMeasure d] g) : densityValue β f = densityValue β g := by
  unfold densityValue
  congr 1
  · congr 1
    apply integral_congr_ae
    filter_upwards [he] with x hx
    apply integral_congr_ae
    filter_upwards [he] with y hy
    rw [hx,hy]
  · apply integral_congr_ae
    filter_upwards [he] with x hx
    rw [hx]

lemma densityPotential_congr {d : ℕ} (β : ℝ) {f g : Torus d → ℝ}
    (he : f =ᵐ[torusMeasure d] g) : densityPotential β f = densityPotential β g := by
  funext x
  unfold densityPotential
  congr 1
  apply integral_congr_ae
  filter_upwards [he] with y hy
  rw [hy]

lemma potential_ae {d : ℕ} (hd : 0 < d) {β : ℝ} (hβ : 0 < β)
    (r : Legacy.TorusEndpoint.ProbabilityDensity d) (hr : r.FiniteEntropy) :
    realValue (FiniteEntropyGreen.dualPotential hd (spectralThreshold d/(2*β)) r hr)
      =ᵐ[torusMeasure d] densityPotential β r.value := by
  have hσ : spectralThreshold d ≠ 0 := (Legacy.TorusEndpoint.endpointSigma_pos hd).ne'
  filter_upwards [FiniteEntropyGreen.dualPotential_ae hd (spectralThreshold d/(2*β)) r hr]
    with x hx
  rw [realValue,hx]
  unfold GreenRoughEnergy.potential GreenRoughEnergy.kernel densityPotential
  simp_rw [mul_assoc]
  rw [integral_const_mul]
  change (1/(2*(spectralThreshold d/(2*β))))*(spectralThreshold d*_) = β*_
  field_simp
  <;> ring
  rfl

lemma potentialValue_realValue {d : ℕ} (hd : 0 < d) {β : ℝ} (hβ : 0 < β)
    (u : TorusL2 d) (hu : Admissible u) :
    potentialValue β (realValue u) = functional (spectralThreshold d/(2*β)) u := by
  unfold potentialValue
  rw [realValue_energy hd u hu]
  unfold functional coefficient
  have hc : (2*Real.pi)^d ≠ 0 := (pow_pos (by positivity : 0 < 2*Real.pi) d).ne'
  congr 1
  field_simp

lemma densityValue_eq_legacy {d : ℕ} (hd : 0 < d) {β : ℝ} (hβ : 0 < β)
    (r : Legacy.TorusEndpoint.ProbabilityDensity d) (hr : r.FiniteEntropy) :
    densityValue β r.value = densityFunctional (spectralThreshold d/(2*β)) r := by
  change β/2*Legacy.TorusEndpoint.PhysicalGreenL2.physicalGreenEnergy r-
    Legacy.TorusEndpoint.densityEntropy r.value = _
  rw [FiniteEntropyPhysical.physical_eq_spectral hd r hr,normalized_energy,densityFunctional]
  have hσ : spectralThreshold d ≠ 0 := (Legacy.TorusEndpoint.endpointSigma_pos hd).ne'
  change β/2*(fourierEnergy r/spectralThreshold d)-_ = _
  congr 1
  field_simp
  <;> ring

lemma gibbs_realValue {d : ℕ} (u : TorusL2 d) :
    normalizedGibbs (realValue u) = gibbsValue u := rfl

#print axioms potential_ae
#print axioms potentialValue_realValue
#print axioms densityValue_eq_legacy
end BecknerOnofri.HighDim.Gap
