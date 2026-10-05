import Legacy.TorusEndpoint.GreenMultiplierSummability
import Legacy.TorusEndpoint.PhysicalFiniteFourier
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# A real representative of the actual Haar L² Green function

Reality is proved from genuine Fourier uniqueness and conjugate symmetry,
not imposed as a hypothesis. No pointwise singularity or lower bound is
asserted here.
-/

open MeasureTheory Filter
open scoped BigOperators ComplexConjugate ENNReal Topology

namespace Legacy.TorusEndpoint.GreenKernelReal

open GreenMultiplierSummability

set_option maxHeartbeats 800000

theorem L2_eq_of_fourierCoeff_eq {d : ℕ}
    (f g : Lp ℂ 2 (torusMeasure d))
    (h : ∀ k : Frequency d, UnitAddTorus.mFourierCoeff f k =
      UnitAddTorus.mFourierCoeff g k) : f = g := by
  apply (UnitAddTorus.mFourierBasis (d := Fin d)).repr.injective
  ext k
  calc
    _ = UnitAddTorus.mFourierCoeff f k := UnitAddTorus.mFourierBasis_repr f k
    _ = UnitAddTorus.mFourierCoeff g k := h k
    _ = _ := (UnitAddTorus.mFourierBasis_repr g k).symm

lemma fourierCoeff_star {d : ℕ} (f : Lp ℂ 2 (torusMeasure d))
    (k : Frequency d) :
    UnitAddTorus.mFourierCoeff (star f : Lp ℂ 2 (torusMeasure d)) k =
      conj (UnitAddTorus.mFourierCoeff f (-k)) := by
  unfold UnitAddTorus.mFourierCoeff
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_star f] with x hx
  simp only [hx, Pi.star_apply, neg_neg, smul_eq_mul, map_mul,
    ← UnitAddTorus.mFourier_neg]
  rfl

theorem greenL2_star_eq (d : ℕ) : star (greenL2 d) = greenL2 d := by
  apply L2_eq_of_fourierCoeff_eq
  intro k
  calc
    _ = conj (UnitAddTorus.mFourierCoeff (greenL2 d) (-k)) :=
      fourierCoeff_star (greenL2 d) k
    _ = _ := by rw [greenL2_fourierCoeff, greenL2_fourierCoeff]; simp

theorem greenL2_im_ae_zero (d : ℕ) :
    ∀ᵐ x ∂torusMeasure d, (greenL2 d x).im = 0 := by
  have h := Lp.coeFn_star (greenL2 d)
  rw [greenL2_star_eq] at h
  filter_upwards [h] with x hx
  have him : (greenL2 d x).im = -(greenL2 d x).im := by
    simpa using congrArg Complex.im hx
  linarith

/-- The actual real part of the constructed Haar L² representative. -/
noncomputable def realGreen (d : ℕ) (x : Torus d) : ℝ := (greenL2 d x).re

theorem realGreen_coe_ae (d : ℕ) :
    (fun x => (realGreen d x : ℂ)) =ᵐ[torusMeasure d] greenL2 d := by
  filter_upwards [greenL2_im_ae_zero d] with x hx
  apply Complex.ext
  · rfl
  · simpa using hx.symm

theorem realGreen_memLp (d : ℕ) : MemLp (realGreen d) 2 (torusMeasure d) :=
  (Lp.memLp (greenL2 d)).re

theorem realGreen_integrable (d : ℕ) : Integrable (realGreen d) (torusMeasure d) :=
  (greenL2_integrable d).re

theorem realGreen_fourierCoeff (d : ℕ) (k : Frequency d) :
    densityFourier (realGreen d) k = (greenMultiplier d k : ℂ) := by
  calc
    _ = UnitAddTorus.mFourierCoeff (greenL2 d) k := by
      unfold densityFourier UnitAddTorus.mFourierCoeff
      change (∫ x, UnitAddTorus.mFourier (-k) x * (realGreen d x : ℂ)
          ∂torusMeasure d) =
        ∫ x, UnitAddTorus.mFourier (-k) x * greenL2 d x ∂torusMeasure d
      apply integral_congr_ae
      filter_upwards [realGreen_coe_ae d] with x hx
      rw [hx]
    _ = _ := greenL2_fourierCoeff d k

theorem realGreen_integral_zero (d : ℕ) :
    (∫ x, realGreen d x ∂torusMeasure d) = 0 := by
  change (∫ x, (greenL2 d x).re ∂torusMeasure d) = 0
  calc
    _ = (∫ x, greenL2 d x ∂torusMeasure d).re := integral_re (greenL2_integrable d)
    _ = 0 := by rw [greenL2_integral_zero]; rfl

theorem greenL2_unique {d : ℕ} (f : Lp ℂ 2 (torusMeasure d))
    (h : ∀ k : Frequency d,
      UnitAddTorus.mFourierCoeff f k = (greenMultiplier d k : ℂ)) :
    f = greenL2 d := by
  apply L2_eq_of_fourierCoeff_eq
  intro k
  exact (h k).trans (greenL2_fourierCoeff d k).symm

open PhysicalFiniteFourier

/-- The genuine continuous finite Fourier polynomial placed in Haar L². -/
noncomputable def complexPartialLp {d : ℕ} (s : Finset (Frequency d)) :
    Lp ℂ 2 (torusMeasure d) :=
  ContinuousMap.toLp 2 (torusMeasure d) ℂ
    (fourierPolynomial s (fun k => (greenMultiplier d k : ℂ)))

lemma complexPartialLp_eq_sum {d : ℕ} (s : Finset (Frequency d)) :
    complexPartialLp s = ∑ k ∈ s, (greenMultiplier d k : ℂ) •
      UnitAddTorus.mFourierLp 2 k := by
  unfold complexPartialLp fourierPolynomial
  calc
    _ = ∑ k ∈ s, ContinuousMap.toLp 2 (torusMeasure d) ℂ
        ((greenMultiplier d k : ℂ) • UnitAddTorus.mFourier k) :=
      map_sum (ContinuousMap.toLp (E := ℂ) 2 (torusMeasure d) ℂ) _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      exact (ContinuousMap.toLp (E := ℂ) 2 (torusMeasure d) ℂ).map_smul
        (greenMultiplier d k : ℂ) (UnitAddTorus.mFourier k)

theorem complexPartialLp_tendsto {d : ℕ} (s : ℕ → Finset (Frequency d))
    (hs : Tendsto s atTop atTop) :
    Tendsto (fun n => complexPartialLp (s n)) atTop (𝓝 (greenL2 d)) := by
  convert! (hasSum_greenL2 d).comp hs using 1
  funext n
  exact complexPartialLp_eq_sum (s n)

lemma finiteKernel_eq_re_fourierPolynomial {d : ℕ} (s : Finset (Frequency d))
    (x : Torus d) :
    finiteKernel s (greenMultiplier d) x =
      (fourierPolynomial s (fun k => (greenMultiplier d k : ℂ)) x).re := by
  simp [finiteKernel, fourierPolynomial, Complex.re_sum, Complex.mul_re]

/-- The real part map on the actual complex L² limit. -/
noncomputable def realGreenLp (d : ℕ) : Lp ℝ 2 (torusMeasure d) :=
  Complex.reCLM.compLp (greenL2 d)

/-- The real part of an actual finite Fourier sum in L². -/
noncomputable def realPartialLp {d : ℕ} (s : Finset (Frequency d)) :
    Lp ℝ 2 (torusMeasure d) := Complex.reCLM.compLp (complexPartialLp s)

lemma realGreenLp_coe_ae (d : ℕ) :
    realGreenLp d =ᵐ[torusMeasure d] realGreen d :=
  Complex.reCLM.coeFn_compLp (greenL2 d)

lemma realPartialLp_coe_ae {d : ℕ} (s : Finset (Frequency d)) :
    realPartialLp s =ᵐ[torusMeasure d] finiteKernel s (greenMultiplier d) := by
  filter_upwards [Complex.reCLM.coeFn_compLp (complexPartialLp s),
    ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := (2 : ℝ≥0∞)) (torusMeasure d)
      (fourierPolynomial s (fun k => (greenMultiplier d k : ℂ)))] with x hx hy
  change (realPartialLp s) x = (complexPartialLp s x).re at hx
  change complexPartialLp s x = _ at hy
  rw [hx, hy, ← finiteKernel_eq_re_fourierPolynomial]

theorem realPartialLp_tendsto {d : ℕ} (s : ℕ → Finset (Frequency d))
    (hs : Tendsto s atTop atTop) :
    Tendsto (fun n => realPartialLp (s n)) atTop (𝓝 (realGreenLp d)) := by
  have hc : Continuous
      (Complex.reCLM.compLp : Lp ℂ 2 (torusMeasure d) → Lp ℝ 2 (torusMeasure d)) :=
    Complex.reCLM.lipschitz.continuous_compLp (map_zero Complex.reCLM)
  exact (hc.tendsto (greenL2 d)).comp (complexPartialLp_tendsto s hs)

/--
Every cofinal sequence of finite real Fourier sums has an a.e. convergent
subsequence. No common pointwise lower bound is asserted. In particular,
the theorem applies to cofinal symmetric finite cutoffs, but symmetry is
not needed because the real part is taken explicitly.
-/
theorem exists_subsequence_finiteKernel_tendsto_ae {d : ℕ}
    (s : ℕ → Finset (Frequency d)) (hs : Tendsto s atTop atTop) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ x ∂torusMeasure d,
      Tendsto (fun n => finiteKernel (s (ns n)) (greenMultiplier d) x) atTop
        (𝓝 (realGreen d x)) := by
  obtain ⟨ns, hns, hae⟩ :=
    (tendstoInMeasure_of_tendsto_Lp (realPartialLp_tendsto s hs)).exists_seq_tendsto_ae
  refine ⟨ns, hns, ?_⟩
  filter_upwards [hae, ae_all_iff.mpr (fun n => realPartialLp_coe_ae (s n)),
    realGreenLp_coe_ae d] with x hx hy hz
  simpa only [hy, hz] using hx

end Legacy.TorusEndpoint.GreenKernelReal

#print axioms Legacy.TorusEndpoint.GreenKernelReal.L2_eq_of_fourierCoeff_eq
#print axioms Legacy.TorusEndpoint.GreenKernelReal.fourierCoeff_star
#print axioms Legacy.TorusEndpoint.GreenKernelReal.greenL2_im_ae_zero
#print axioms Legacy.TorusEndpoint.GreenKernelReal.realGreen_fourierCoeff
#print axioms Legacy.TorusEndpoint.GreenKernelReal.realGreen_integral_zero
#print axioms Legacy.TorusEndpoint.GreenKernelReal.greenL2_unique
#print axioms Legacy.TorusEndpoint.GreenKernelReal.realPartialLp_tendsto
#print axioms Legacy.TorusEndpoint.GreenKernelReal.exists_subsequence_finiteKernel_tendsto_ae
