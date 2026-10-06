module

public import Legacy.BecknerOnofri.SubcriticalAttainment
public import Legacy.TorusEndpoint.EntropyVariational

@[expose] public section

/-! The actual Gibbs density of every admissible potential, and its exact entropy identity. -/
noncomputable section
open MeasureTheory Legacy.TorusEndpoint
open scoped ENNReal
namespace Legacy.BecknerOnofri.SubcriticalEuler
open TorusSobolev SubcriticalAttainment

def gibbsValue {d : ℕ} (u : TorusL2 d) (x : Torus d) : ℝ := Real.exp (u x).re / partition u

theorem gibbsValue_pos {d : ℕ} {b Ab : ℝ} (hR : RoughExponentialBound d b Ab)
    {u : TorusL2 d} (hu : Admissible u) (x : Torus d) : 0 < gibbsValue u x :=
  div_pos (Real.exp_pos _) (partition_pos hR hu)

theorem gibbsValue_integrable {d : ℕ} {b Ab : ℝ} (hR : RoughExponentialBound d b Ab)
    {u : TorusL2 d} (hu : Admissible u) : Integrable (gibbsValue u) (torusMeasure d) :=
  (partition_integrable hR hu).div_const _

theorem gibbsValue_mass {d : ℕ} {b Ab : ℝ} (hR : RoughExponentialBound d b Ab)
    {u : TorusL2 d} (hu : Admissible u) : (∫ x, gibbsValue u x ∂torusMeasure d) = 1 := by
  unfold gibbsValue
  rw [integral_div]
  exact div_self (partition_pos hR hu).ne'

def gibbsDensity {d : ℕ} {b Ab : ℝ} (hR : RoughExponentialBound d b Ab)
    {u : TorusL2 d} (hu : Admissible u) : ProbabilityDensity d where
  value := gibbsValue u
  nonneg := Filter.Eventually.of_forall (fun x => (gibbsValue_pos hR hu x).le)
  integrable := gibbsValue_integrable hR hu
  mass := gibbsValue_mass hR hu

theorem gibbsValue_memLp_two {d : ℕ} {b Ab : ℝ} (hR : RoughExponentialBound d b Ab)
    {u : TorusL2 d} (hu : Admissible u) : MemLp (gibbsValue u) 2 (torusMeasure d) := by
  simpa only [gibbsValue, div_eq_mul_inv] using!
    (ExponentialPartitionContinuity.exp_memLp_two u (rough_integrable hR hu (by norm_num : (0:ℝ)<2))).mul_const
      (partition u)⁻¹

theorem gibbsValue_product_integrable {d : ℕ} {b Ab : ℝ} (hR : RoughExponentialBound d b Ab)
    {u : TorusL2 d} (hu : Admissible u) (v : TorusL2 d) :
    Integrable (fun x => gibbsValue u x*(v x).re) (torusMeasure d) :=
  (gibbsValue_memLp_two hR hu).integrable_mul (Lp.memLp v).re

theorem log_gibbsValue {d : ℕ} {b Ab : ℝ} (hR : RoughExponentialBound d b Ab)
    {u : TorusL2 d} (hu : Admissible u) (x : Torus d) :
    Real.log (gibbsValue u x) = (u x).re-Real.log (partition u) := by
  rw [gibbsValue, Real.log_div (Real.exp_pos _).ne' (partition_pos hR hu).ne', Real.log_exp]

theorem gibbsDensity_finiteEntropy {d : ℕ} {b Ab : ℝ} (hR : RoughExponentialBound d b Ab)
    {u : TorusL2 d} (hu : Admissible u) : (gibbsDensity hR hu).FiniteEntropy := by
  change Integrable (fun x => gibbsValue u x*Real.log (gibbsValue u x)) (torusMeasure d)
  simp_rw [log_gibbsValue hR hu, mul_sub]
  exact (gibbsValue_product_integrable hR hu u).sub ((gibbsValue_integrable hR hu).mul_const _)

theorem gibbsDensity_entropy {d : ℕ} {b Ab : ℝ} (hR : RoughExponentialBound d b Ab)
    {u : TorusL2 d} (hu : Admissible u) :
    densityEntropy (gibbsValue u) = (∫ x, gibbsValue u x*(u x).re ∂torusMeasure d)-Real.log (partition u) := by
  unfold densityEntropy
  simp_rw [log_gibbsValue hR hu, mul_sub]
  rw [integral_sub (gibbsValue_product_integrable hR hu u) ((gibbsValue_integrable hR hu).mul_const _),
    integral_mul_const, gibbsValue_mass hR hu, one_mul]

/-- The supporting inequality comes from the proved entropy variational principle. -/
theorem log_partition_support {d : ℕ} {b Ab : ℝ} (hR : RoughExponentialBound d b Ab)
    {u v : TorusL2 d} (hu : Admissible u) (hv : Admissible v) :
    (∫ x, gibbsValue u x*((v x).re-(u x).re) ∂torusMeasure d) ≤
      Real.log (partition v)-Real.log (partition u) := by
  have h := entropy_variational_of_integrable
    (gibbsDensity hR hu).nonneg (gibbsDensity hR hu).mass
    (gibbsDensity hR hu).integrable (gibbsDensity_finiteEntropy hR hu)
    (gibbsValue_product_integrable hR hu v) (partition_integrable hR hv)
  change (∫ x, gibbsValue u x*(v x).re ∂torusMeasure d)-Real.log (partition v) ≤ densityEntropy (gibbsValue u) at h
  rw [gibbsDensity_entropy hR hu] at h
  simp_rw [mul_sub]
  rw [integral_sub (gibbsValue_product_integrable hR hu v) (gibbsValue_product_integrable hR hu u)]
  linarith

/-- At a genuine global maximizer, the Gibbs pairing is controlled by the actual energy difference.
-/
theorem maximizer_variation_inequality {d : ℕ} {b Ab A : ℝ} (hR : RoughExponentialBound d b Ab)
    {u : TorusL2 d} (hu : Admissible u)
    (hmax : ∀ v : TorusL2 d, Admissible v → functional A v ≤ functional A u)
    {v : TorusL2 d} (hv : Admissible v) :
    (∫ x, gibbsValue u x*((v x).re-(u x).re) ∂torusMeasure d) ≤
      A*(criticalEnergy v-criticalEnergy u) := by
  have hs := log_partition_support hR hu hv
  have hm := hmax v hv
  unfold functional at hm
  linarith

#print axioms gibbsDensity_finiteEntropy
#print axioms maximizer_variation_inequality
end Legacy.BecknerOnofri.SubcriticalEuler
