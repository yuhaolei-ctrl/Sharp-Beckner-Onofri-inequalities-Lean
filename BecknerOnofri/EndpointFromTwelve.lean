module

public import BecknerOnofri.MixtureEndpointInduction
public import BecknerOnofri.GenericCosineRepresentation
public import BecknerOnofri.SubcriticalGap
public import BecknerOnofri.EndpointDuality
public import Legacy.BecknerOnofri.SubcriticalPrimalDual
public import Legacy.BecknerOnofri.HeatDensityApproximation
public import Legacy.BecknerOnofri.EndpointClosure

@[expose] public section

/-! Genuine optimizer selection, cosine representation, and heat closure reduce
the unrestricted high-dimensional density endpoint to its exact d=12 mixture base. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Filter
open scoped BigOperators Topology ENNReal

namespace BecknerOnofri.CosineMixtureTransfer
open RectangleLattice Legacy.TorusEndpoint Legacy.BecknerOnofri
open TorusSobolev SubcriticalAttainment SubcriticalEuler SmoothFourier

/-- Identify the real-power rectangle kernel with the actual Euclidean
inverse Fourier multiplier. -/
theorem weight_nat_eq {d : ℕ} (hd : 0 < d) (k : Frequency d) :
    weight (d:ℝ) k = if k = 0 then 0 else (frequencyRadius k ^ d)⁻¹ := by
  by_cases hk : k = 0
  · subst k
    simp only [if_true]
    exact weight_zero (by exact_mod_cast hd)
  · rw [if_neg hk]
    unfold weight
    rw [Real.rpow_neg (normSq_nonneg k)]
    congr 1
    change (normSq k)^((d:ℝ)/2) = (Real.sqrt (normSq k))^d
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (normSq_nonneg k)]
    congr 1
    ring

theorem energy_eq_legacy {d : ℕ} (hd : 0 < d) (r : ProbabilityDensity d) :
    energy (d:ℝ) r.value = fourierEnergy r := by
  let f : Frequency d → ℝ := fun k => weight (d:ℝ) k * ‖densityFourier r.value k‖^2
  have hs : Function.support f ⊆ {k : Frequency d | k ≠ 0} := by
    intro k hk hz
    subst k
    exact hk (by simp [f, weight_zero (by exact_mod_cast hd : (0:ℝ) < d)])
  change (∑' k, f k) = _
  rw [← tsum_subtype_eq_of_support_subset hs]
  unfold fourierEnergy
  apply tsum_congr
  intro k
  simp only [f, weight_nat_eq hd, if_neg k.property, densitySpectralTerm]
  ring

theorem half_strictly_subcritical {d : ℕ} (hd : 12 ≤ d) :
    1 / (4 * endpointConstant d) < (1/2:ℝ) := by
  have hd0 : 0 < d := by omega
  have hσ := endpointSigma_pos hd0
  have hgap : endpointSigma d < 2*(d:ℝ) := HighDim.spectral_subcritical_gap hd
  have hC : (1/2:ℝ) < endpointConstant d := by
    unfold endpointConstant
    apply (lt_div_iff₀ hσ).mpr
    linarith
  apply (div_lt_iff₀ (by positivity : (0:ℝ) < 4*endpointConstant d)).mpr
  nlinarith

theorem actual_rough {d : ℕ} (hd : 0 < d) :
    RoughExponentialBound d (endpointConstant d/2)
      (GreenRoughEnergy.partition d (endpointConstant d/2)) := by
  have hC : 0 < endpointConstant d :=
    div_pos (Nat.cast_pos.mpr hd) (endpointSigma_pos hd)
  exact GenericAttainment.rough_bound hd (by positivity) (by linarith)

/-- Every actual admissible Sobolev potential satisfies the spectral endpoint,
provided the proved mixture endpoint holds in this dimension. -/
theorem primal_from_mixture {d : ℕ} (hd : 12 ≤ d) (hE : MixtureEndpoint d)
    (v : TorusL2 d) (hv : Admissible v) : functional (1/2) v ≤ 0 := by
  have hd0 : 0 < d := by omega
  have hR := actual_rough hd0
  obtain ⟨u, hu, hmax, hStR, hStU⟩ :=
    GenericAttainment.exists_steiner_optimizer hd0 (half_strictly_subcritical hd)
  obtain ⟨w, N, hw, hm, hSup, heq⟩ :=
    GenericCosineRepresentation.steiner_maximizer_mixture hd0 (by norm_num : (0:ℝ)<1/2)
      hu hmax hStR hStU
  have hpos : ∀ x, 0 < CosineMixtureApproximation.rho w N x := by
    rw [← heq]
    exact smoothGibbsValue_pos hR hu
  have hMix := hE w N hw hm hSup hpos
  rw [← heq] at hMix
  have hs := maximizer_fourier_summable hd0 hR (by norm_num : (0:ℝ)<1/2) hu hmax
  have hEnergy : energy (d:ℝ) (smoothGibbsValue u) = fourierEnergy (gibbsDensity hR hu) := by
    rw [show smoothGibbsValue u = (smoothGibbsDensity hR hu hs).value by rfl,
      energy_eq_legacy hd0]
    unfold fourierEnergy densitySpectralTerm
    apply tsum_congr
    intro k
    rw [smoothGibbsDensity_fourier hR hu hs]
    rfl
  have hEntropy : densityEntropy (smoothGibbsValue u) = densityEntropy (gibbsValue u) :=
    smoothGibbsDensity_entropy hR hu hs
  rw [hEnergy, hEntropy] at hMix
  have hu0 : functional (1/2) u ≤ 0 := by
    rw [maximizer_functional_eq_density hd0 hR (by norm_num : (0:ℝ)<1/2) hu hmax]
    norm_num
    linarith
  exact (hmax v hv).trans hu0

/-- The actual endpoint for every L² probability density, obtained by the
proved density/potential variational comparison. -/
theorem l2_endpoint_from_mixture {d : ℕ} (hd : 12 ≤ d) (hE : MixtureEndpoint d)
    (r : ProbabilityDensity d) (hr : MemLp r.value 2 (torusMeasure d)) :
    Summable (densitySpectralTerm r) ∧ (1/2:ℝ)*fourierEnergy r ≤ densityEntropy r.value := by
  have hd0 : 0 < d := by omega
  refine ⟨(PhysicalGreenL2.physicalGreenEnergy_eq_spectral hd0 r hr).1, ?_⟩
  have h := SubcriticalPrimalDual.density_le_dual hd0 (actual_rough hd0)
    (by norm_num : (0:ℝ)<1/2) r hr
  have hp := primal_from_mixture hd hE (SubcriticalPrimalDual.dualPotential (1/2) r hr)
    (SubcriticalPrimalDual.dualPotential_admissible hd0 (1/2) r hr)
  unfold SubcriticalPrimalDual.densityFunctional at h
  norm_num at h
  linarith

/-- Heat regularization extends the endpoint to every finite-entropy density;
Fourier-energy summability is concluded, never assumed. -/
theorem finite_entropy_endpoint_from_mixture {d : ℕ} (hd : 12 ≤ d) (hE : MixtureEndpoint d)
    (r : ProbabilityDensity d) (hr : r.FiniteEntropy) :
    Summable (densitySpectralTerm r) ∧ (1/2:ℝ)*fourierEnergy r ≤ densityEntropy r.value := by
  let t : ℕ → ℝ := fun n => 1/((n:ℝ)+1)
  have ht (n : ℕ) : 0 < t n := by dsimp [t]; positivity
  let rs : ℕ → ProbabilityDensity d := fun n => HeatDensityApproximation.heatDensity r (ht n)
  apply EndpointClosure.spectral_bound_of_fourier_limits_entropy_le (1/2) (by norm_num) rs r
  · intro n
    exact l2_endpoint_from_mixture hd hE (rs n)
      ((HeatDensityApproximation.heatValue_continuous r (ht n)).memLp_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))
  · exact HeatDensityApproximation.heatDensity_fourier_tendsto r t ht
      tendsto_one_div_add_atTop_nhds_zero_nat
  · intro n
    exact HeatDensityApproximation.heatDensity_entropy_le r hr (ht n)

/-- Exact trusted all-density endpoint in every d≥12, conditional solely on
the explicit twelve-dimensional cosine-mixture endpoint. -/
theorem density_endpoint_from_twelve (h12 : MixtureEndpoint 12) {d : ℕ} (hd : 12 ≤ d)
    (r : HighDim.ProbabilityDensity d) (hr : r.FiniteEntropy) :
    HighDim.spectralEnergy r ≤ ENNReal.ofReal (2 * HighDim.entropy r) := by
  have hE := mixture_endpoint_from_twelve h12 hd
  have h := finite_entropy_endpoint_from_mixture hd hE (HighDim.Bridge.density r) hr
  have he : HighDim.Bridge.rawDensity (HighDim.Bridge.density r) = r := by cases r; rfl
  rw [← he, HighDim.Bridge.rawDensity_spectralEnergy _ h.1]
  apply ENNReal.ofReal_le_ofReal
  change fourierEnergy (HighDim.Bridge.density r) ≤ 2 * HighDim.entropy r
  have hb := h.2
  change (1/2:ℝ)*fourierEnergy (HighDim.Bridge.density r) ≤ HighDim.entropy r at hb
  linarith


/-- The actual full d-dimensional density endpoint implies the precise mixture
base used above, since these series are continuous finite-entropy densities. -/
theorem mixture_endpoint_of_density {d : ℕ} (hd : 0 < d)
    (hD : ∀ r : HighDim.ProbabilityDensity d, r.FiniteEntropy →
      HighDim.spectralEnergy r ≤ ENNReal.ofReal (2 * HighDim.entropy r)) : MixtureEndpoint d := by
  intro w N hw hm hSup hpos
  let r := CosineMixtureApproximation.probabilityDensity w N hw hm hSup
  have hr : r.FiniteEntropy := CosineMixtureApproximation.rho_finiteEntropy w N hw hm hSup
  have hraw : (HighDim.Bridge.rawDensity r).FiniteEntropy := hr
  have hL2 : MemLp r.value 2 (torusMeasure d) :=
    (CosineMixtureApproximation.rho_continuous w N hw hSup).memLp_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hs := (PhysicalGreenL2.physicalGreenEnergy_eq_spectral hd r hL2).1
  have h := hD (HighDim.Bridge.rawDensity r) hraw
  rw [HighDim.Bridge.rawDensity_spectralEnergy r hs] at h
  have hn : 0 ≤ 2 * HighDim.entropy (HighDim.Bridge.rawDensity r) :=
    mul_nonneg (by norm_num) (HighDim.entropy_nonneg _ hraw)
  have hb := (ENNReal.ofReal_le_ofReal_iff hn).mp h
  change energy (d:ℝ) r.value ≤ 2 * densityEntropy r.value
  rw [energy_eq_legacy hd]
  exact hb

/-- Exact dimension transfer from the full twelve-dimensional density endpoint
to every finite-entropy probability density in every higher dimension. -/
theorem density_endpoint_of_twelve_density
    (h12 : ∀ r : HighDim.ProbabilityDensity 12, r.FiniteEntropy →
      HighDim.spectralEnergy r ≤ ENNReal.ofReal (2 * HighDim.entropy r))
    {d : ℕ} (hd : 12 ≤ d) (r : HighDim.ProbabilityDensity d) (hr : r.FiniteEntropy) :
    HighDim.spectralEnergy r ≤ ENNReal.ofReal (2 * HighDim.entropy r) :=
  density_endpoint_from_twelve (mixture_endpoint_of_density (by norm_num) h12) hd r hr

#print axioms primal_from_mixture
#print axioms finite_entropy_endpoint_from_mixture
#print axioms density_endpoint_from_twelve

end BecknerOnofri.CosineMixtureTransfer
