import Legacy.BecknerOnofri.EndpointDensityFinitePotential
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! A genuine Sobolev limit of the finite Fourier inverse potentials of a
finite-energy L1 probability density, together with actual a.e. convergence. -/
noncomputable section
open Set MeasureTheory Filter Classical
open scoped Topology BigOperators
namespace Legacy.BecknerOnofri.EndpointDensityFinitePotential
open Legacy.TorusEndpoint TorusSobolev SubcriticalAttainment

theorem coefficient_tendsto {d : ℕ} (r : ProbabilityDensity d) (t : ℝ) (k : Frequency d) :
    Tendsto (fun N => coefficient r t N k) atTop (𝓝 (inverseCoefficient r t k)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [(box_tendsto d).eventually (eventually_ge_atTop ({k} : Finset (Frequency d)))] with N hN
  exact (if_pos (hN (Finset.mem_singleton_self k))).symm

theorem limit_fourier {d : ℕ} (r : ProbabilityDensity d) (t : ℝ)
    {v : TorusL2 d} {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (hv : Tendsto (fun n => finitePotential r t (φ n)) atTop (𝓝 v)) (k : Frequency d) :
    fourierIsometry d v k = inverseCoefficient r t k := by
  have he := ((lp.evalCLM ℂ (fun _ : Frequency d => ℂ) 2 k).continuous.comp
    (fourierIsometry d).continuous).tendsto v |>.comp hv
  change Tendsto (fun n => fourierIsometry d (finitePotential r t (φ n)) k) atTop
    (𝓝 (fourierIsometry d v k)) at he
  have hc := (coefficient_tendsto r t k).comp hφ.tendsto_atTop
  exact tendsto_nhds_unique (by simpa only [finitePotential_fourier,Function.comp_def] using he) hc

/-- The limit is a real, mean-zero critical Sobolev potential with exactly the inverse density
Fourier coefficients. The convergence and the subsequence are derived from actual L2 compactness. -/
theorem exists_limit {d : ℕ} (hd : 0 < d) (r : ProbabilityDensity d)
    (hQ : Summable (densitySpectralTerm r)) (t : ℝ) :
    ∃ v : TorusL2 d, Admissible v ∧ criticalEnergy v ≤ t^2*fourierEnergy r ∧
      (∀ k, fourierIsometry d v k = inverseCoefficient r t k) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        Tendsto (fun n => finitePotential r t (φ n)) atTop (𝓝 v) ∧
        ∀ᵐ x ∂torusMeasure d, Tendsto (fun n => finitePotential r t (φ n) x) atTop (𝓝 (v x)) := by
  have hB : 0 ≤ t^2*fourierEnergy r := by
    apply mul_nonneg (sq_nonneg t)
    rw [← (fullTerm_hasSum r hQ).tsum_eq]
    exact tsum_nonneg (fullTerm_nonnegative r)
  obtain ⟨v,hv,φ,hφ,hlim⟩ := (realSobolevBall_isCompact hd hB).isSeqCompact
    (fun N => finitePotential_mem_ball r hQ t N)
  obtain ⟨ψ,hψ,hae⟩ := (tendstoInMeasure_of_tendsto_Lp hlim).exists_seq_tendsto_ae
  refine ⟨v,⟨hv.2,hv.1.1⟩,hv.1.2,?_,φ ∘ ψ,hφ.comp hψ,?_,hae⟩
  · exact limit_fourier r t hφ hlim
  · exact hlim.comp hψ.tendsto_atTop

theorem limit_energy {d : ℕ} (r : ProbabilityDensity d)
    (hQ : Summable (densitySpectralTerm r)) (t : ℝ) {v : TorusL2 d}
    (hv : ∀ k, fourierIsometry d v k = inverseCoefficient r t k) :
    criticalEnergy v = t^2*fourierEnergy r := by
  have he : weightedSquare (fourierIsometry d v) = fun k => t^2*SobolevDensityPairing.fullDensityTerm r k := by
    funext k
    unfold weightedSquare
    rw [hv]
    by_cases hk : k=0
    · simp [inverseCoefficient,hk,SobolevDensityPairing.fullDensityTerm]
    · have hw : frequencyRadius k^d ≠ 0 := (pow_pos (frequencyRadius_pos hk) _).ne'
      simp only [inverseCoefficient,if_neg hk,SobolevDensityPairing.fullDensityTerm,
        norm_mul,Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs,div_pow]
      field_simp
  rw [criticalEnergy,coefficientEnergy,he,tsum_mul_left,(fullTerm_hasSum r hQ).tsum_eq]

#print axioms exists_limit
#print axioms limit_energy
end Legacy.BecknerOnofri.EndpointDensityFinitePotential
