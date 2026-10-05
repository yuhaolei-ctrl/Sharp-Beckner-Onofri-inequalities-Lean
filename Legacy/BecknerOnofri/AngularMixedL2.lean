module

public import Legacy.BecknerOnofri.AngularMixedTerms
public import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum

@[expose] public section

/-! Actual L2 convergence of the angular mixed-derivative series and its
identification with the genuine differentiated profile. -/
noncomputable section
namespace Legacy.BecknerOnofri.AngularMixedL2
open MeasureTheory Legacy.TorusEndpoint TorusSobolev RadialWiener ChebyshevMixedSeries
open AngularMixedTerms JacobiTensor
open scoped ENNReal

theorem majorant_nonneg {d : ℕ} (a : Frequency d → ℂ) (is : List (Fin d)) (k : Frequency d) :
    0 ≤ majorant a is k := by
  have hr := frequencyRadius_nonneg k
  unfold majorant radialWeight
  positivity

theorem angularTerm_memLp {d : ℕ} (a : Frequency d → ℂ) (is : List (Fin d)) (k : Frequency d) :
    MemLp (angularTerm a is k) 2 (JacobiTensor.measure d) :=
  MemLp.of_bound (angularTerm_contDiff a is k).continuous.aestronglyMeasurable
    (majorant a is k) (ae_of_all _ (angularTerm_bound a is k))

def termVector {d : ℕ} (a : Frequency d → ℂ) (is : List (Fin d)) (k : Frequency d) : TensorL2 d :=
  (angularTerm_memLp a is k).toLp (angularTerm a is k)

theorem termVector_ae {d : ℕ} (a : Frequency d → ℂ) (is : List (Fin d)) (k : Frequency d) :
    termVector a is k =ᵐ[JacobiTensor.measure d] angularTerm a is k := (angularTerm_memLp a is k).coeFn_toLp

theorem termVector_norm_le {d : ℕ} (a : Frequency d → ℂ) (is : List (Fin d)) (k : Frequency d) :
    ‖termVector a is k‖ ≤ (measureUnivNNReal (JacobiTensor.measure d) : ℝ)^((2:ℝ≥0∞).toReal⁻¹) *
      majorant a is k := by
  apply Lp.norm_le_of_ae_bound (majorant_nonneg a is k)
  filter_upwards [termVector_ae a is k] with x hx
  rw [hx]
  exact angularTerm_bound a is k x

theorem termVector_norm_summable {d : ℕ} (a : Frequency d → ℂ)
    (ha : ∀ m : ℕ, RadialSummable a m) (is : List (Fin d)) :
    Summable (fun k => ‖termVector a is k‖) :=
  ((majorant_summable a ha is).mul_left
    ((measureUnivNNReal (JacobiTensor.measure d) : ℝ)^((2:ℝ≥0∞).toReal⁻¹))).of_nonneg_of_le
      (fun _ => norm_nonneg _) (termVector_norm_le a is)

def vector {d : ℕ} (a : Frequency d → ℂ) (is : List (Fin d)) : TensorL2 d := ∑' k, termVector a is k

theorem vector_hasSum {d : ℕ} (a : Frequency d → ℂ)
    (ha : ∀ m : ℕ, RadialSummable a m) (is : List (Fin d)) :
    HasSum (termVector a is) (vector a is) :=
  (termVector_norm_summable a ha is).of_norm.hasSum

theorem termVector_eq_zero {d : ℕ} (a : Frequency d → ℂ) (is : List (Fin d))
    (k : Frequency d) (i : Fin d) (hi : (k i).natAbs < is.count i) : termVector a is k = 0 := by
  apply Lp.ext
  filter_upwards [termVector_ae a is k, Lp.coeFn_zero ℝ 2 (JacobiTensor.measure d)] with x hx hz
  rw [hx, hz, angularTerm_eq_zero_of_frequency_lt a is k i hi]
  rfl

theorem termVector_eq_tensor {d : ℕ} (a : Frequency d → ℂ) (is : List (Fin d))
    (k : Frequency d) (hk : ∀ i, is.count i ≤ (k i).natAbs) :
    termVector a is k = ((a k).re * normalization is (shiftedIndex is k)) •
      tensorVector (countIndex is) (shiftedIndex is k) := by
  apply Lp.ext
  filter_upwards [termVector_ae a is k,
    Lp.coeFn_smul ((a k).re * normalization is (shiftedIndex is k))
      (tensorVector (countIndex is) (shiftedIndex is k)),
    tensorVector_ae_eq (countIndex is) (shiftedIndex is k)] with x hx hs ht
  rw [hx, hs]
  change angularTerm a is k x = (a k).re * normalization is (shiftedIndex is k) * _
  rw [ht]
  exact angularTerm_eq_tensor a is k hk x

theorem vector_ae {d : ℕ} (a : Frequency d → ℂ)
    (ha : ∀ m : ℕ, RadialSummable a m) (is : List (Fin d)) :
    vector a is =ᵐ[JacobiTensor.measure d] fun x => weight is x * FiniteDifferences.mixedPartial is
      (fun z => ChebyshevProfile.profile a (CubeProfileMonotone.fromUnitCube z)) (angularCube x) := by
  have hnorm := termVector_norm_summable a ha is
  have he := Lp.coeFn_tsum (f := termVector a is)
    (tsum_enorm_ne_top_iff_summable_norm.mpr hnorm)
  have hall : ∀ᵐ x ∂JacobiTensor.measure d, ∀ k, termVector a is k x = angularTerm a is k x :=
    ae_all_iff.mpr (fun k => termVector_ae a is k)
  filter_upwards [he, hall] with x hx hk
  rw [angular_mixedPartial_series a ha is]
  exact hx.trans (tsum_congr (hk))

#print axioms vector_hasSum
#print axioms vector_ae
#print axioms termVector_eq_tensor
end Legacy.BecknerOnofri.AngularMixedL2
