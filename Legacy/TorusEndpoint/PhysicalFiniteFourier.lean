module

public import Legacy.TorusEndpoint.SpectralEntropy
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-!
# Actual finite-kernel interaction and Fourier energy

The energy on the left is an actual Haar double integral of a finite kernel,
not a definition in terms of Fourier coefficients. Integrability and the
factorization are proved. No entropy, smoothness of the density, sign of the
real kernel coefficients, or symmetry of the frequency set is assumed.
-/

open MeasureTheory
open scoped BigOperators ComplexConjugate

namespace Legacy.TorusEndpoint.PhysicalFiniteFourier

set_option maxHeartbeats 800000

lemma character_sub {d : ℕ} (k : Frequency d) (x y : Torus d) :
    UnitAddTorus.mFourier k (x - y) =
      UnitAddTorus.mFourier k x * UnitAddTorus.mFourier (-k) y := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, sub_eq_add_neg,
    Pi.add_apply, Pi.neg_apply, fourier_apply, smul_add, smul_neg, AddCircle.toCircle_add,
    Circle.coe_mul, neg_smul, Finset.prod_mul_distrib]

noncomputable def complexInteraction {d : ℕ} (rho : ProbabilityDensity d)
    (k : Frequency d) (xy : Torus d × Torus d) : ℂ :=
  UnitAddTorus.mFourier k (xy.1 - xy.2) *
    (rho.value xy.1 : ℂ) * (rho.value xy.2 : ℂ)

lemma complexInteraction_factor {d : ℕ} (rho : ProbabilityDensity d)
    (k : Frequency d) (xy : Torus d × Torus d) :
    complexInteraction rho k xy =
      (UnitAddTorus.mFourier k xy.1 * (rho.value xy.1 : ℂ)) *
      (UnitAddTorus.mFourier (-k) xy.2 * (rho.value xy.2 : ℂ)) := by
  rw [complexInteraction, character_sub]
  ring

theorem complexInteraction_integrable {d : ℕ} (rho : ProbabilityDensity d)
    (k : Frequency d) :
    Integrable (complexInteraction rho k) ((torusMeasure d).prod (torusMeasure d)) := by
  have hplus : Integrable
      (fun x => UnitAddTorus.mFourier k x * (rho.value x : ℂ)) (torusMeasure d) := by
    simpa only [neg_neg] using densityFourier_integrable rho (-k)
  have hprod := hplus.mul_prod (densityFourier_integrable rho k)
  apply hprod.congr
  exact ae_of_all _ (fun xy => (complexInteraction_factor rho k xy).symm)

theorem complexInteraction_integral {d : ℕ} (rho : ProbabilityDensity d)
    (k : Frequency d) :
    (∫ xy, complexInteraction rho k xy ∂(torusMeasure d).prod (torusMeasure d)) =
      ((‖densityFourier rho.value k‖ ^ 2 : ℝ) : ℂ) := by
  calc
    _ = ∫ xy,
        (UnitAddTorus.mFourier k xy.1 * (rho.value xy.1 : ℂ)) *
        (UnitAddTorus.mFourier (-k) xy.2 * (rho.value xy.2 : ℂ))
        ∂(torusMeasure d).prod (torusMeasure d) := by
      apply integral_congr_ae
      exact ae_of_all _ (complexInteraction_factor rho k)
    _ = (∫ x, UnitAddTorus.mFourier k x * (rho.value x : ℂ) ∂torusMeasure d) *
        (∫ y, UnitAddTorus.mFourier (-k) y * (rho.value y : ℂ) ∂torusMeasure d) :=
      integral_prod_mul
        (fun x : Torus d => UnitAddTorus.mFourier k x * (rho.value x : ℂ))
        (fun y : Torus d => UnitAddTorus.mFourier (-k) y * (rho.value y : ℂ))
    _ = densityFourier rho.value (-k) * densityFourier rho.value k := by
      simp only [densityFourier, neg_neg]
    _ = _ := by
      rw [densityFourier_neg, ← Complex.normSq_eq_conj_mul_self,
        Complex.normSq_eq_norm_sq]

noncomputable def realInteraction {d : ℕ} (rho : ProbabilityDensity d)
    (k : Frequency d) (xy : Torus d × Torus d) : ℝ :=
  (UnitAddTorus.mFourier k (xy.1 - xy.2)).re * rho.value xy.1 * rho.value xy.2

lemma realInteraction_eq_re {d : ℕ} (rho : ProbabilityDensity d)
    (k : Frequency d) (xy : Torus d × Torus d) :
    realInteraction rho k xy = (complexInteraction rho k xy).re := by
  simp [realInteraction, complexInteraction, Complex.mul_re]

theorem realInteraction_integrable {d : ℕ} (rho : ProbabilityDensity d)
    (k : Frequency d) :
    Integrable (realInteraction rho k) ((torusMeasure d).prod (torusMeasure d)) := by
  have h := (complexInteraction_integrable rho k).re
  apply h.congr
  exact ae_of_all _ (fun xy => (realInteraction_eq_re rho k xy).symm)

theorem realInteraction_integral {d : ℕ} (rho : ProbabilityDensity d)
    (k : Frequency d) :
    (∫ xy, realInteraction rho k xy ∂(torusMeasure d).prod (torusMeasure d)) =
      ‖densityFourier rho.value k‖ ^ 2 := by
  calc
    _ = ∫ xy, (complexInteraction rho k xy).re
        ∂(torusMeasure d).prod (torusMeasure d) := by
      apply integral_congr_ae
      exact ae_of_all _ (realInteraction_eq_re rho k)
    _ = (∫ xy, complexInteraction rho k xy
        ∂(torusMeasure d).prod (torusMeasure d)).re :=
      integral_re (complexInteraction_integrable rho k)
    _ = _ := by rw [complexInteraction_integral, Complex.ofReal_re]

/-- A finite, actual real-valued Fourier kernel on the torus. -/
noncomputable def finiteKernel {d : ℕ} (s : Finset (Frequency d))
    (b : Frequency d → ℝ) (z : Torus d) : ℝ :=
  ∑ k ∈ s, b k * (UnitAddTorus.mFourier k z).re

lemma finiteKernel_interaction_eq_sum {d : ℕ} (rho : ProbabilityDensity d)
    (s : Finset (Frequency d)) (b : Frequency d → ℝ) (xy : Torus d × Torus d) :
    finiteKernel s b (xy.1 - xy.2) * rho.value xy.1 * rho.value xy.2 =
      ∑ k ∈ s, b k * realInteraction rho k xy := by
  simp only [finiteKernel, Finset.sum_mul, realInteraction]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem finiteKernel_interaction_integrable {d : ℕ} (rho : ProbabilityDensity d)
    (s : Finset (Frequency d)) (b : Frequency d → ℝ) :
    Integrable (fun xy : Torus d × Torus d =>
      finiteKernel s b (xy.1 - xy.2) * rho.value xy.1 * rho.value xy.2)
      ((torusMeasure d).prod (torusMeasure d)) := by
  have h : Integrable
      (fun xy => ∑ k ∈ s, b k * realInteraction rho k xy)
      ((torusMeasure d).prod (torusMeasure d)) :=
    integrable_finsetSum s (fun k _ => (realInteraction_integrable rho k).const_mul (b k))
  apply h.congr
  exact ae_of_all _ (fun xy => (finiteKernel_interaction_eq_sum rho s b xy).symm)

theorem finiteKernel_product_integral {d : ℕ} (rho : ProbabilityDensity d)
    (s : Finset (Frequency d)) (b : Frequency d → ℝ) :
    (∫ xy : Torus d × Torus d,
      finiteKernel s b (xy.1 - xy.2) * rho.value xy.1 * rho.value xy.2
      ∂(torusMeasure d).prod (torusMeasure d)) =
      ∑ k ∈ s, b k * ‖densityFourier rho.value k‖ ^ 2 := by
  calc
    _ = ∫ xy, ∑ k ∈ s, b k * realInteraction rho k xy
        ∂(torusMeasure d).prod (torusMeasure d) := by
      apply integral_congr_ae
      exact ae_of_all _ (finiteKernel_interaction_eq_sum rho s b)
    _ = ∑ k ∈ s, ∫ xy, b k * realInteraction rho k xy
        ∂(torusMeasure d).prod (torusMeasure d) :=
      integral_finsetSum s (fun k _ => (realInteraction_integrable rho k).const_mul (b k))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      rw [integral_const_mul, realInteraction_integral]

/-- This is the physical double integral, not a spectral-energy placeholder. -/
noncomputable def finitePhysicalEnergy {d : ℕ} (rho : ProbabilityDensity d)
    (s : Finset (Frequency d)) (b : Frequency d → ℝ) : ℝ :=
  ∫ x, ∫ y, finiteKernel s b (x - y) * rho.value x * rho.value y
    ∂torusMeasure d ∂torusMeasure d

theorem finitePhysicalEnergy_eq_spectral {d : ℕ} (rho : ProbabilityDensity d)
    (s : Finset (Frequency d)) (b : Frequency d → ℝ) :
    finitePhysicalEnergy rho s b =
      ∑ k ∈ s, b k * ‖densityFourier rho.value k‖ ^ 2 := by
  unfold finitePhysicalEnergy
  calc
    _ = ∫ xy : Torus d × Torus d,
        finiteKernel s b (xy.1 - xy.2) * rho.value xy.1 * rho.value xy.2
        ∂(torusMeasure d).prod (torusMeasure d) :=
      (integral_prod _ (finiteKernel_interaction_integrable rho s b)).symm
    _ = _ := finiteKernel_product_integral rho s b

end Legacy.TorusEndpoint.PhysicalFiniteFourier

#print axioms Legacy.TorusEndpoint.PhysicalFiniteFourier.character_sub
#print axioms Legacy.TorusEndpoint.PhysicalFiniteFourier.complexInteraction_integrable
#print axioms Legacy.TorusEndpoint.PhysicalFiniteFourier.complexInteraction_integral
#print axioms Legacy.TorusEndpoint.PhysicalFiniteFourier.finiteKernel_interaction_integrable
#print axioms Legacy.TorusEndpoint.PhysicalFiniteFourier.finitePhysicalEnergy_eq_spectral
