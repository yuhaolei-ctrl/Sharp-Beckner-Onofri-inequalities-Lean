module

public import Legacy.BecknerOnofri.SubcriticalPrimalDual
public import Legacy.BecknerOnofri.EntropyVariationalEquality

@[expose] public section

/-! Recovery of the actual Euler density from a global L2 density maximizer,
including the equality argument needed after entropy-preserving rearrangement. -/
namespace Legacy.BecknerOnofri.SubcriticalPrimalDual
open MeasureTheory Legacy.TorusEndpoint TorusSobolev SubcriticalAttainment SubcriticalEuler
open GreenDensityPotentialL2

theorem density_eq_gibbs_of_dual_eq {d : ℕ} (hd : 0 < d) {b Ab A : ℝ}
    (hR : RoughExponentialBound d b Ab) (hA : 0 < A)
    (r : ProbabilityDensity d) (hr : MemLp r.value 2 (torusMeasure d))
    (he : functional A (dualPotential A r hr) = densityFunctional A r) :
    r.value =ᵐ[torusMeasure d] gibbsValue (dualPotential A r hr) := by
  let v := dualPotential A r hr
  have hv := dualPotential_admissible hd A r hr
  have hE : criticalEnergy v = (1/(2*A))^2 * fourierEnergy r := by
    dsimp only [v, dualPotential]
    rw [criticalEnergy_smul_real, potentialLp_energy hd]
  have hcoef : A*((1/(2*A))^2*fourierEnergy r) = (1/(4*A))*fourierEnergy r := by
    field_simp
    ring
  have hpA : 1/(2*A) = 2*(1/(4*A)) := by field_simp; norm_num
  have hp := scaledPotential_pairing hd r hr (1/(2*A))
  change (∫ x, r.value x*(v x).re ∂torusMeasure d) = _ at hp
  have hh : densityEntropy r.value =
      (∫ x, r.value x*(v x).re ∂torusMeasure d)-Real.log (partition v) := by
    change functional A v = densityFunctional A r at he
    rw [functional, hE, hcoef, densityFunctional] at he
    rw [hp, hpA]
    linarith
  have h := EntropyVariationalEquality.eq_normalized_exp_of_variational_eq
    r.nonneg r.mass r.integrable (PhysicalGreenL2.finiteEntropy_of_memLp r hr)
    (hr.integrable_mul (Lp.memLp v).re) (partition_integrable hR hv) hh
  exact h

theorem density_maximizer_gibbs {d : ℕ} (hd : 0 < d) {b Ab A : ℝ}
    (hR : RoughExponentialBound d b Ab) (hA : 0 < A)
    (r : ProbabilityDensity d) (hr : MemLp r.value 2 (torusMeasure d))
    (hmax : ∀ q : ProbabilityDensity d, MemLp q.value 2 (torusMeasure d) →
      densityFunctional A q ≤ densityFunctional A r) :
    r.value =ᵐ[torusMeasure d] gibbsValue (dualPotential A r hr) :=
  density_eq_gibbs_of_dual_eq hd hR hA r hr (density_maximizer_dual hd hR hA r hr hmax).1

theorem density_maximizer_fourier {d : ℕ} (hd : 0 < d) {b Ab A : ℝ}
    (hR : RoughExponentialBound d b Ab) (hA : 0 < A)
    (r : ProbabilityDensity d) (hr : MemLp r.value 2 (torusMeasure d))
    (hmax : ∀ q : ProbabilityDensity d, MemLp q.value 2 (torusMeasure d) →
      densityFunctional A q ≤ densityFunctional A r) {k : Frequency d} (hk : k ≠ 0) :
    densityFourier r.value k = ((2*A*frequencyRadius k^d : ℝ) : ℂ) *
      fourierIsometry d (dualPotential A r hr) k := by
  have he := density_maximizer_gibbs hd hR hA r hr hmax
  have hf : densityFourier r.value k = densityFourier (gibbsValue (dualPotential A r hr)) k := by
    apply integral_congr_ae
    filter_upwards [he] with x hx
    rw [hx]
  rw [hf]
  exact maximizer_fourier_equation hR (dualPotential_admissible hd A r hr)
    (density_maximizer_dual hd hR hA r hr hmax).2 hk

/-- Entropy preservation and energy increase force a rearranged L2 density
to be a global maximizer too. No rearrangement or energy comparison is assumed
proved by this generic interface. -/
theorem rearranged_density_maximizer {d : ℕ} {A : ℝ} (hA : 0 < A)
    (r q : ProbabilityDensity d) (hq : MemLp q.value 2 (torusMeasure d))
    (hmax : ∀ s : ProbabilityDensity d, MemLp s.value 2 (torusMeasure d) →
      densityFunctional A s ≤ densityFunctional A r)
    (hEnt : densityEntropy q.value = densityEntropy r.value)
    (hQ : fourierEnergy r ≤ fourierEnergy q) :
    densityFunctional A q = densityFunctional A r ∧
      ∀ s : ProbabilityDensity d, MemLp s.value 2 (torusMeasure d) →
        densityFunctional A s ≤ densityFunctional A q := by
  have hle : densityFunctional A r ≤ densityFunctional A q := by
    unfold densityFunctional
    rw [hEnt]
    exact sub_le_sub_right (mul_le_mul_of_nonneg_left hQ (by positivity)) _
  have he := le_antisymm (hmax q hq) hle
  exact ⟨he, fun s hs => (hmax s hs).trans he.ge⟩

theorem rearranged_density_gibbs {d : ℕ} (hd : 0 < d) {b Ab A : ℝ}
    (hR : RoughExponentialBound d b Ab) (hA : 0 < A)
    (r q : ProbabilityDensity d) (hq : MemLp q.value 2 (torusMeasure d))
    (hmax : ∀ s : ProbabilityDensity d, MemLp s.value 2 (torusMeasure d) →
      densityFunctional A s ≤ densityFunctional A r)
    (hEnt : densityEntropy q.value = densityEntropy r.value)
    (hQ : fourierEnergy r ≤ fourierEnergy q) :
    q.value =ᵐ[torusMeasure d] gibbsValue (dualPotential A q hq) :=
  density_maximizer_gibbs hd hR hA q hq (rearranged_density_maximizer hA r q hq hmax hEnt hQ).2

#print axioms density_maximizer_gibbs
#print axioms density_maximizer_fourier
#print axioms rearranged_density_gibbs
end Legacy.BecknerOnofri.SubcriticalPrimalDual
