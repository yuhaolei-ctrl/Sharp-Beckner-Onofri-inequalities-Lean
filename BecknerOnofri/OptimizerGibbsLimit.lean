import Legacy.BecknerOnofri.EndpointDensityPotentialLimit
import Legacy.BecknerOnofri.YoungGapLimit

/-! An actual finite-entropy primal optimizer is a Gibbs density.
The proof uses finite Fourier inverse potentials and vanishing Young gaps;
no endpoint inequality or prior square-integrability of the density is assumed. -/
noncomputable section
open Set MeasureTheory Filter Classical
open scoped Topology BigOperators
namespace BecknerOnofri.OptimizerGibbsLimit
open Legacy.TorusEndpoint Legacy.BecknerOnofri
open TorusSobolev SubcriticalAttainment SubcriticalEuler
open EndpointDensityFinitePotential

private theorem shifted_product_integrable {d : ℕ} (r : ProbabilityDensity d)
    (u : TorusL2 d) (hp : Integrable (fun x => r.value x*(u x).re) (torusMeasure d)) (ell : ℝ) :
    Integrable (fun x => r.value x*((u x).re-ell)) (torusMeasure d) := by
  convert hp.sub (r.integrable.mul_const ell) using 1
  funext x
  simp only [Pi.sub_apply,mul_sub]

private theorem normalized_exp_integrable {d : ℕ} {b Ab : ℝ} (hR : RoughExponentialBound d b Ab)
    (u : TorusL2 d) (hu : Admissible u) :
    Integrable (fun x => Real.exp ((u x).re-Real.log (partition u))) (torusMeasure d) := by
  have hZ := partition_pos hR hu
  simpa only [Real.exp_sub,Real.exp_log hZ] using (partition_integrable hR hu).div_const (partition u)

theorem gap_integrable {d : ℕ} {b Ab : ℝ} (hR : RoughExponentialBound d b Ab) (r : ProbabilityDensity d)
    (hr : r.FiniteEntropy) (u : TorusL2 d) (hu : Admissible u)
    (hp : Integrable (fun x => r.value x*(u x).re) (torusMeasure d)) :
    Integrable (YoungGapLimit.gap r.value (fun x => (u x).re) (Real.log (partition u))) (torusMeasure d) :=
  ((hr.sub r.integrable).sub (shifted_product_integrable r u hp _)).add
    (normalized_exp_integrable hR u hu)

theorem gap_integral {d : ℕ} {b Ab : ℝ} (hR : RoughExponentialBound d b Ab) (r : ProbabilityDensity d)
    (hr : r.FiniteEntropy) (u : TorusL2 d) (hu : Admissible u)
    (hp : Integrable (fun x => r.value x*(u x).re) (torusMeasure d)) :
    (∫ x, YoungGapLimit.gap r.value (fun x => (u x).re) (Real.log (partition u)) x ∂torusMeasure d) =
      densityEntropy r.value - (∫ x, r.value x*(u x).re ∂torusMeasure d) + Real.log (partition u) := by
  have hZ := partition_pos hR hu
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
  rw [integral_add hDiff (normalized_exp_integrable hR u hu),
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

theorem finite_gap_upper {d : ℕ} {b Ab C : ℝ}
    (hR : RoughExponentialBound d b Ab) (hC : 0 < C) (r : ProbabilityDensity d)
    (hr : r.FiniteEntropy)
    (hBound : ∀ v : TorusL2 d, Admissible v →
      functional (1/(4*C)) v ≤ C*fourierEnergy r-densityEntropy r.value) (N : ℕ) :
    (∫ x, YoungGapLimit.gap r.value (fun x => (finitePotential r (2*C) N x).re)
      (Real.log (partition (finitePotential r (2*C) N))) x ∂torusMeasure d) ≤
      C*(fourierEnergy r-partialEnergy r N) := by
  have hu := finitePotential_admissible r (2*C) N
  rw [gap_integral hR r hr _ hu (finitePotential_pair_integrable r _ N),finitePotential_pairing]
  have h := hBound _ hu
  rw [functional, finitePotential_energy] at h
  have hc : (1/(4*C))*(2*C)^2 = C := by
    field_simp [hC.ne']
    ring
  rw [← mul_assoc,hc] at h
  nlinarith

theorem finite_gap_tendsto_zero {d : ℕ} {b Ab C : ℝ}
    (hR : RoughExponentialBound d b Ab) (hC : 0 < C) (r : ProbabilityDensity d)
    (hr : r.FiniteEntropy) (hQ : Summable (densitySpectralTerm r))
    (hBound : ∀ v : TorusL2 d, Admissible v →
      functional (1/(4*C)) v ≤ C*fourierEnergy r-densityEntropy r.value) :
    Tendsto (fun N => ∫ x, YoungGapLimit.gap r.value
      (fun x => (finitePotential r (2*C) N x).re)
      (Real.log (partition (finitePotential r (2*C) N))) x ∂torusMeasure d)
      atTop (𝓝 0) := by
  apply squeeze_zero (fun N => integral_nonneg_of_ae (gap_nonnegative r _ _))
    (finite_gap_upper hR hC r hr hBound)
  simpa only [sub_self,mul_zero] using
    ((tendsto_const_nhds (x := fourierEnergy r)).sub (partialEnergy_tendsto r hQ)).const_mul C

/-- Finite entropy and optimality yield an admissible Gibbs potential which
itself maximizes the complete Sobolev dual problem. -/
theorem exists_gibbs_optimizer {d : ℕ} (hd : 0 < d) {b Ab C : ℝ}
    (hb : 0 < b) (hR : RoughExponentialBound d b Ab) (hC : 0 < C)
    (r : ProbabilityDensity d) (hr : r.FiniteEntropy) (hQ : Summable (densitySpectralTerm r))
    (hBound : ∀ v : TorusL2 d, Admissible v →
      functional (1/(4*C)) v ≤ C*fourierEnergy r-densityEntropy r.value) :
    ∃ u : TorusL2 d, Admissible u ∧
      r.value =ᵐ[torusMeasure d] gibbsValue u ∧
      functional (1/(4*C)) u = C*fourierEnergy r-densityEntropy r.value ∧
      ∀ v : TorusL2 d, Admissible v → functional (1/(4*C)) v ≤ functional (1/(4*C)) u := by
  obtain ⟨u,hu,hB,hcoef,φ,hφ,hlim,hae⟩ := exists_limit hd r hQ (2*C)
  have hub : u ∈ realSobolevBall d ((2*C)^2*fourierEnergy r) := ⟨⟨hu.2,hB⟩,hu.1⟩
  have hlog : Tendsto (fun n => Real.log (partition (finitePotential r (2*C) (φ n))))
      atTop (𝓝 (Real.log (partition u))) :=
    ((log_partition_continuousOn_ball hb hR) u hub).tendsto.comp
      (tendsto_nhdsWithin_iff.mpr ⟨hlim,Filter.Eventually.of_forall (fun n => finitePotential_mem_ball r hQ _ (φ n))⟩)
  have hgap := (finite_gap_tendsto_zero hR hC r hr hQ hBound).comp hφ.tendsto_atTop
  have hg := YoungGapLimit.eq_exp_of_gap_integrals_tendsto_zero r.nonneg
    (fun n => gap_integrable hR r hr _ (finitePotential_admissible r _ (φ n))
      (finitePotential_pair_integrable r _ (φ n)))
    (hae.mono (fun x hx => Complex.continuous_re.continuousAt.tendsto.comp hx)) hlog hgap
  have hgap' := ((tendsto_const_nhds (x := densityEntropy r.value)).sub
    (((partialEnergy_tendsto r hQ).comp hφ.tendsto_atTop).const_mul (2*C))).add hlog
  have hz : densityEntropy r.value-(2*C)*fourierEnergy r+Real.log (partition u) = 0 := by
    apply tendsto_nhds_unique hgap' ?_
    convert hgap using 1
    funext n
    dsimp only [Function.comp_apply]
    rw [gap_integral hR r hr _ (finitePotential_admissible r _ (φ n))
      (finitePotential_pair_integrable r _ (φ n)),finitePotential_pairing]
  have hE := limit_energy r hQ (2*C) hcoef
  have hc : (1/(4*C))*(2*C)^2 = C := by
    field_simp [hC.ne']
    ring
  have hvalue : functional (1/(4*C)) u = C*fourierEnergy r-densityEntropy r.value := by
    rw [functional,hE,← mul_assoc,hc]
    linarith
  refine ⟨u,hu,?_,hvalue,?_⟩
  · change r.value =ᵐ[torusMeasure d] fun x => Real.exp (u x).re/partition u
    simpa only [Real.exp_sub,Real.exp_log (partition_pos hR hu)] using hg
  · intro v hv
    rw [hvalue]
    exact hBound v hv

#print axioms exists_gibbs_optimizer
end BecknerOnofri.OptimizerGibbsLimit
