import Legacy.BecknerOnofri.EndpointDensityPotentialLimit
import BecknerOnofri.EndpointRigidity.AnalyticEndpoint
import Legacy.BecknerOnofri.YoungGapLimit

/-! Every finite-entropy endpoint equality density is a genuine Gibbs density.
The density is not assumed square-integrable: L2 follows from the Gibbs identity. -/
noncomputable section
open Set MeasureTheory Filter Classical
open scoped Topology BigOperators
namespace BecknerOnofri.EndpointRigidity.DensityGibbs
open Legacy.TorusEndpoint Legacy.BecknerOnofri
open TorusSobolev SubcriticalAttainment SubcriticalEuler
open EndpointDensityFinitePotential

private theorem shifted_product_integrable {d : ℕ} (r : ProbabilityDensity d)
    (u : TorusL2 d) (hp : Integrable (fun x => r.value x*(u x).re) (torusMeasure d)) (ell : ℝ) :
    Integrable (fun x => r.value x*((u x).re-ell)) (torusMeasure d) := by
  convert hp.sub (r.integrable.mul_const ell) using 1
  funext x
  simp only [Pi.sub_apply,mul_sub]

private theorem normalized_exp_integrable {d : ℕ} (hd : 0 < d) {C : ℝ} (hC : 0 < C) (hE : CoefficientEndpoint d C)
    (u : TorusL2 d) (hu : Admissible u) :
    Integrable (fun x => Real.exp ((u x).re-Real.log (partition u))) (torusMeasure d) := by
  have hZ := partition_pos (AnalyticEndpoint.rough_of_endpoint hd hC hE) hu
  simpa only [Real.exp_sub,Real.exp_log hZ] using (AnalyticEndpoint.onofri hd hC hE hu).1.div_const (partition u)

theorem gap_integrable {d : ℕ} (hd : 0 < d) {C : ℝ} (hC : 0 < C) (hE : CoefficientEndpoint d C) (r : ProbabilityDensity d)
    (hr : r.FiniteEntropy) (u : TorusL2 d) (hu : Admissible u)
    (hp : Integrable (fun x => r.value x*(u x).re) (torusMeasure d)) :
    Integrable (YoungGapLimit.gap r.value (fun x => (u x).re) (Real.log (partition u))) (torusMeasure d) :=
  ((hr.sub r.integrable).sub (shifted_product_integrable r u hp _)).add
    (normalized_exp_integrable hd hC hE u hu)

theorem gap_integral {d : ℕ} (hd : 0 < d) {C : ℝ} (hC : 0 < C) (hE : CoefficientEndpoint d C) (r : ProbabilityDensity d)
    (hr : r.FiniteEntropy) (u : TorusL2 d) (hu : Admissible u)
    (hp : Integrable (fun x => r.value x*(u x).re) (torusMeasure d)) :
    (∫ x, YoungGapLimit.gap r.value (fun x => (u x).re) (Real.log (partition u)) x ∂torusMeasure d) =
      densityEntropy r.value - (∫ x, r.value x*(u x).re ∂torusMeasure d) + Real.log (partition u) := by
  have hZ := partition_pos (AnalyticEndpoint.rough_of_endpoint hd hC hE) hu
  have hnorm : (∫ x, Real.exp ((u x).re-Real.log (partition u)) ∂torusMeasure d) = 1 := by
    simp only [Real.exp_sub,Real.exp_log hZ,integral_div]
    exact div_self hZ.ne'
  have hshift : (∫ x, r.value x*((u x).re-Real.log (partition u)) ∂torusMeasure d) =
      (∫ x, r.value x*(u x).re ∂torusMeasure d)-Real.log (partition u) := by
    simp only [mul_sub]
    rw [integral_sub hp (r.integrable.mul_const _),integral_mul_const,r.mass,one_mul]
  have hEnt : Integrable (fun x => r.value x*Real.log (r.value x)-r.value x) (torusMeasure d) :=
    hr.sub r.integrable
  have hDiff : Integrable (fun x => r.value x*Real.log (r.value x)-r.value x-
      r.value x*((u x).re-Real.log (partition u))) (torusMeasure d) :=
    hEnt.sub (shifted_product_integrable r u hp _)
  unfold YoungGapLimit.gap
  rw [integral_add hDiff (normalized_exp_integrable hd hC hE u hu),
    integral_sub hEnt (shifted_product_integrable r u hp _),
    integral_sub hr r.integrable,r.mass,hshift,hnorm]
  unfold densityEntropy
  ring

theorem gap_nonnegative {d : ℕ} (r : ProbabilityDensity d) (u : TorusL2 d) (ell : ℝ) :
    ∀ᵐ x ∂torusMeasure d, 0 ≤ YoungGapLimit.gap r.value (fun x => (u x).re) ell x := by
  filter_upwards [r.nonneg] with x hx
  have h := entropy_young (r.value x) ((u x).re-ell) hx
  unfold YoungGapLimit.gap
  linarith

theorem finite_gap_upper {d : ℕ} (hd : 0 < d) {C : ℝ} (hC : 0 < C) (hE : CoefficientEndpoint d C) (r : ProbabilityDensity d)
    (hr : r.FiniteEntropy) (N : ℕ) :
    (∫ x, YoungGapLimit.gap r.value (fun x => (finitePotential r (2*C) N x).re)
      (Real.log (partition (finitePotential r (2*C) N))) x ∂torusMeasure d) ≤
      densityEntropy r.value-C*partialEnergy r N := by
  have hu := finitePotential_admissible r (2*C) N
  rw [gap_integral hd hC hE r hr _ hu (finitePotential_pair_integrable r _ N),finitePotential_pairing]
  have h := (AnalyticEndpoint.onofri hd hC hE hu).2
  rw [finitePotential_energy] at h
  have hc : AnalyticEndpoint.coefficient C*(2*C)^2 = C := by
    unfold AnalyticEndpoint.coefficient
    field_simp [(hC).ne']
    ring
  rw [← mul_assoc,hc] at h
  linarith

theorem finite_gap_tendsto_zero {d : ℕ} (hd : 0 < d) {C : ℝ} (hC : 0 < C) (hE : CoefficientEndpoint d C) (r : ProbabilityDensity d)
    (hr : r.FiniteEntropy) (he : C*fourierEnergy r = densityEntropy r.value) :
    Tendsto (fun N => ∫ x, YoungGapLimit.gap r.value
      (fun x => (finitePotential r (2*C) N x).re)
      (Real.log (partition (finitePotential r (2*C) N))) x ∂torusMeasure d)
      atTop (𝓝 0) := by
  apply squeeze_zero (fun N => integral_nonneg_of_ae (gap_nonnegative r _ _))
    (finite_gap_upper hd hC hE r hr)
  have hh := (tendsto_const_nhds (x := densityEntropy r.value)).sub ((partialEnergy_tendsto r (hE r hr).1).const_mul (C))
  simpa only [← he,sub_self] using hh

/-- The actual inverse Fourier potential realizes equality in the Gibbs variational principle. -/
theorem exists_gibbs_of_equality {d : ℕ} (hd : 0 < d) {C : ℝ} (hC : 0 < C) (hE : CoefficientEndpoint d C) (r : ProbabilityDensity d)
    (hr : r.FiniteEntropy) (he : C*fourierEnergy r = densityEntropy r.value) :
    ∃ u : TorusL2 d, Admissible u ∧
      (∀ k, fourierIsometry d u k = inverseCoefficient r (2*C) k) ∧
      criticalEnergy u = (2*C)^2*fourierEnergy r ∧
      r.value =ᵐ[torusMeasure d] gibbsValue u := by
  let hR := AnalyticEndpoint.rough_of_endpoint hd hC hE
  obtain ⟨u,hu,hB,hcoef,φ,hφ,hlim,hae⟩ := exists_limit hd r (hE r hr).1 (2*C)
  have hub : u ∈ realSobolevBall d ((2*C)^2*fourierEnergy r) := ⟨⟨hu.2,hB⟩,hu.1⟩
  have hlog : Tendsto (fun n => Real.log (partition (finitePotential r (2*C) (φ n))))
      atTop (𝓝 (Real.log (partition u))) :=
    ((log_partition_continuousOn_ball (hC) hR) u hub).tendsto.comp
      (tendsto_nhdsWithin_iff.mpr ⟨hlim,Filter.Eventually.of_forall (fun n => finitePotential_mem_ball r (hE r hr).1 _ (φ n))⟩)
  have hg := YoungGapLimit.eq_exp_of_gap_integrals_tendsto_zero r.nonneg
    (fun n => gap_integrable hd hC hE r hr _ (finitePotential_admissible r _ (φ n))
      (finitePotential_pair_integrable r _ (φ n)))
    (hae.mono (fun x hx => Complex.continuous_re.continuousAt.tendsto.comp hx)) hlog
    ((finite_gap_tendsto_zero hd hC hE r hr he).comp hφ.tendsto_atTop)
  refine ⟨u,hu,hcoef,limit_energy r (hE r hr).1 _ hcoef,?_⟩
  change r.value =ᵐ[torusMeasure d] fun x => Real.exp (u x).re/partition u
  simpa only [Real.exp_sub,Real.exp_log (partition_pos hR hu)] using hg

/-- Finite entropy and endpoint equality force actual L2 regularity; it is a conclusion. -/
theorem memLp_two_of_equality {d : ℕ} (hd : 0 < d) {C : ℝ} (hC : 0 < C) (hE : CoefficientEndpoint d C) (r : ProbabilityDensity d)
    (hr : r.FiniteEntropy) (he : C*fourierEnergy r = densityEntropy r.value) :
    MemLp r.value 2 (torusMeasure d) := by
  obtain ⟨u,hu,_,_,hg⟩ := exists_gibbs_of_equality hd hC hE r hr he
  exact (gibbsValue_memLp_two (AnalyticEndpoint.rough_of_endpoint hd hC hE) hu).ae_eq hg.symm

#print axioms exists_gibbs_of_equality
#print axioms memLp_two_of_equality
end BecknerOnofri.EndpointRigidity.DensityGibbs
