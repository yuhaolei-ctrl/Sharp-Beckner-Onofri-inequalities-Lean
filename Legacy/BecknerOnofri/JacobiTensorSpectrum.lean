import Legacy.BecknerOnofri.JacobiTensorCompleteness
import Legacy.BecknerOnofri.SpectralHeatCompact
import Legacy.TorusEndpoint.GreenMultiplierSummability

/-! The concrete positive Jacobi tensor spectrum, heat and inverse powers.
The critical inverse symbol is square summable by an injective embedding into
the actual nonzero integer lattice. -/
noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff Topology BigOperators
namespace Legacy.BecknerOnofri.JacobiTensorSpectrum
open JacobiTensor

variable {d : ℕ}

theorem active_of_ne_zero (a : Index d) (ha : a ≠ 0) : ∃ i, 0 < a i := by
  by_contra h
  push Not at h
  apply ha
  funext i
  exact Nat.eq_zero_of_le_zero (h i)

theorem dimension_pos (a : Index d) (ha : a ≠ 0) : 0 < d := by
  obtain ⟨i, _⟩ := active_of_ne_zero a ha
  exact Fin.pos i

def positiveSpectrum (a : Index d) (ha : a ≠ 0) : SpectralHeatInverse.PositiveSpectrum (Index d) where
  value := tensorEigenvalue a
  gap := spectralBottom a
  gap_pos := spectralBottom_pos a (active_of_ne_zero a ha)
  lower := spectralBottom_le a

def heat (a : Index d) (ha : a ≠ 0) (t : ℝ) : TensorL2 d →L[ℝ] TensorL2 d :=
  SpectralHeatInverse.heat (hilbertBasis a) (positiveSpectrum a ha) t

def inversePower (a : Index d) (ha : a ≠ 0) (s : ℝ) (hs : 0 < s) :
    TensorL2 d →L[ℝ] TensorL2 d :=
  SpectralHeatInverse.inversePower (hilbertBasis a) (positiveSpectrum a ha) s hs

theorem repr_heat (a : Index d) (ha : a ≠ 0) {t : ℝ} (ht : 0 ≤ t)
    (u : TensorL2 d) (n : Index d) :
    (hilbertBasis a).repr (heat a ha t u) n =
      Real.exp (-t*tensorEigenvalue a n) * (hilbertBasis a).repr u n :=
  SpectralHeatInverse.repr_heat _ _ ht u n

theorem repr_inversePower (a : Index d) (ha : a ≠ 0) (s : ℝ) (hs : 0 < s)
    (u : TensorL2 d) (n : Index d) :
    (hilbertBasis a).repr (inversePower a ha s hs u) n =
      (tensorEigenvalue a n)^(-s) * (hilbertBasis a).repr u n :=
  SpectralHeatInverse.repr_inversePower _ _ s hs u n

theorem heat_zero (a : Index d) (ha : a ≠ 0) :
    heat a ha 0 = ContinuousLinearMap.id ℝ (TensorL2 d) := by
  apply ContinuousLinearMap.ext
  intro u
  apply (hilbertBasis a).repr.injective
  ext n
  simp [repr_heat a ha (le_refl 0)]

theorem heat_add (a : Index d) (ha : a ≠ 0) {t r : ℝ} (ht : 0 ≤ t) (hr : 0 ≤ r) :
    heat a ha (t+r) = (heat a ha t).comp (heat a ha r) := by
  apply ContinuousLinearMap.ext
  intro u
  apply (hilbertBasis a).repr.injective
  ext n
  simp only [ContinuousLinearMap.comp_apply, repr_heat a ha (add_nonneg ht hr),
    repr_heat a ha ht, repr_heat a ha hr, ← mul_assoc, ← Real.exp_add]
  congr 2
  ring

theorem heat_symmetric (a : Index d) (ha : a ≠ 0) (t : ℝ) : (heat a ha t).IsSymmetric :=
  SpectralHeatInverse.heat_symmetric _ _ t

theorem inversePower_symmetric (a : Index d) (ha : a ≠ 0) (s : ℝ) (hs : 0 < s) :
    (inversePower a ha s hs).IsSymmetric :=
  SpectralHeatInverse.inversePower_symmetric _ _ s hs

theorem heat_norm_le (a : Index d) (ha : a ≠ 0) {t : ℝ} (ht : 0 ≤ t) :
    ‖heat a ha t‖ ≤ Real.exp (-spectralBottom a*t) :=
  SpectralHeatInverse.heat_norm_le _ _ ht

theorem inversePower_norm_le (a : Index d) (ha : a ≠ 0) (s : ℝ) (hs : 0 < s) :
    ‖inversePower a ha s hs‖ ≤ (spectralBottom a)^(-s) :=
  SpectralHeatInverse.inversePower_norm_le _ _ s hs

theorem heat_integrable (a : Index d) (ha : a ≠ 0) {s : ℝ} (hs : 0 < s)
    (u : TensorL2 d) : IntegrableOn (fun t : ℝ => t^(s-1) • heat a ha t u) (Ioi 0) :=
  SpectralHeatInverse.heat_integrable _ _ hs u

theorem heat_integral_eq_inversePower (a : Index d) (ha : a ≠ 0) {s : ℝ} (hs : 0 < s)
    (u : TensorL2 d) :
    (Real.Gamma s)⁻¹ • (∫ t : ℝ in Ioi 0, t^(s-1) • heat a ha t u) = inversePower a ha s hs u :=
  SpectralHeatInverse.heat_integral_eq_inversePower _ _ hs u

theorem inversePower_compact (a : Index d) (ha : a ≠ 0) (s : ℝ) (hs : 0 < s) :
    IsCompactOperator (inversePower a ha s hs) :=
  SpectralHeatInverse.inversePower_compact _ _ (finite_sublevel a) s hs

theorem heat_compact (a : Index d) (ha : a ≠ 0) {t : ℝ} (ht : 0 < t) :
    IsCompactOperator (heat a ha t) := by
  let b : SpectralHeatInverse.Symbol (Index d) := SpectralHeatInverse.boundedSymbol
    (fun n => tensorEigenvalue a n * Real.exp (-t*tensorEigenvalue a n)) (1/t) (by
      intro n
      rw [Real.norm_of_nonneg (mul_nonneg (tensorEigenvalue_nonneg a n) (Real.exp_nonneg _))]
      exact SpectralHeatInverse.scalar_derivative_bound ht ((positiveSpectrum a ha).value_pos n))
  have he : heat a ha t = (inversePower a ha 1 (by norm_num)).comp
      (SpectralHeatInverse.diagonal (hilbertBasis a) b) := by
    apply ContinuousLinearMap.ext
    intro u
    apply (hilbertBasis a).repr.injective
    ext n
    simp only [ContinuousLinearMap.comp_apply, repr_heat a ha ht.le,
      repr_inversePower, SpectralHeatInverse.repr_diagonal]
    change Real.exp (-t*tensorEigenvalue a n)*(hilbertBasis a).repr u n =
      (tensorEigenvalue a n)^(-(1:ℝ)) *
        ((tensorEigenvalue a n*Real.exp (-t*tensorEigenvalue a n))*(hilbertBasis a).repr u n)
    rw [Real.rpow_neg_one]
    have hn : tensorEigenvalue a n ≠ 0 := ne_of_gt ((positiveSpectrum a ha).value_pos n)
    field_simp [hn]
  rw [he]
  exact (inversePower_compact a ha 1 (by norm_num)).comp_clm _

def latticeIndex (a n : Index d) : Legacy.TorusEndpoint.Frequency d := fun i => ((n i+a i:ℕ):ℤ)

theorem latticeIndex_injective (a : Index d) : Function.Injective (latticeIndex a) := by
  intro n l h
  funext i
  have hh := congrFun h i
  exact Nat.add_right_cancel (Int.ofNat_inj.mp hh)

theorem latticeIndex_ne_zero (a : Index d) (ha : a ≠ 0) (n : Index d) : latticeIndex a n ≠ 0 := by
  obtain ⟨i, hi⟩ := active_of_ne_zero a ha
  intro h
  have hh := congrFun h i
  change ((n i+a i:ℕ):ℤ) = 0 at hh
  have hpos : (0 : ℤ) < ((n i+a i:ℕ):ℤ) := by exact_mod_cast (Nat.add_pos_right (n i) hi)
  exact (ne_of_gt hpos) hh

theorem latticeIndex_radiusSq (a n : Index d) :
    Legacy.TorusEndpoint.GreenMultiplierSummability.radiusSq (latticeIndex a n) = tensorEigenvalue a n := by
  simp only [Legacy.TorusEndpoint.GreenMultiplierSummability.radiusSq, latticeIndex,
    tensorEigenvalue, JacobiEigenfunctions.eigenvalue, Int.cast_natCast]

theorem inverse_dimension_summable (a : Index d) (ha : a ≠ 0) :
    Summable (fun n : Index d => (tensorEigenvalue a n)^(-(d:ℝ))) := by
  have hs := (Legacy.TorusEndpoint.GreenMultiplierSummability.summable_nonzero_radial_inverse d).comp_injective
    (latticeIndex_injective a)
  apply hs.congr
  intro n
  simp only [Function.comp_apply]
  rw [if_neg (latticeIndex_ne_zero a ha n), latticeIndex_radiusSq]
  rw [Real.rpow_neg (tensorEigenvalue_nonneg a n), Real.rpow_natCast, inv_pow]

theorem criticalExponent_pos (a : Index d) (ha : a ≠ 0) : (0 : ℝ) < (d:ℝ)/2 := by
  have hd : (0 : ℝ) < (d:ℝ) := by exact_mod_cast dimension_pos a ha
  positivity

def criticalSymbol (a : Index d) (ha : a ≠ 0) : SpectralHeatInverse.Symbol (Index d) :=
  (positiveSpectrum a ha).inverseSymbol ((d:ℝ)/2) (criticalExponent_pos a ha)

def criticalInverse (a : Index d) (ha : a ≠ 0) : TensorL2 d →L[ℝ] TensorL2 d :=
  inversePower a ha ((d:ℝ)/2) (criticalExponent_pos a ha)

theorem criticalSymbol_apply (a : Index d) (ha : a ≠ 0) (n : Index d) :
    criticalSymbol a ha n = (tensorEigenvalue a n)^(-((d:ℝ)/2)) := rfl

theorem criticalSymbol_sq (a : Index d) (ha : a ≠ 0) (n : Index d) :
    (criticalSymbol a ha n)^2 = (tensorEigenvalue a n)^(-(d:ℝ)) := by
  rw [criticalSymbol_apply]
  calc
    ((tensorEigenvalue a n)^(-((d:ℝ)/2)))^2 =
        (tensorEigenvalue a n)^(-((d:ℝ)/2)*(2:ℝ)) := by
      rw [Real.rpow_mul (tensorEigenvalue_nonneg a n), Real.rpow_two]
    _ = _ := by congr 1; ring

theorem criticalSymbol_sq_summable (a : Index d) (ha : a ≠ 0) :
    Summable (fun n : Index d => (criticalSymbol a ha n)^2) :=
  (inverse_dimension_summable a ha).congr (fun n => (criticalSymbol_sq a ha n).symm)

theorem criticalInverse_compact (a : Index d) (ha : a ≠ 0) :
    IsCompactOperator (criticalInverse a ha) := inversePower_compact a ha _ _

theorem critical_heat_integrable (a : Index d) (ha : a ≠ 0) (u : TensorL2 d) :
    IntegrableOn (fun t : ℝ => t^((d:ℝ)/2-1) • heat a ha t u) (Ioi 0) :=
  heat_integrable a ha (criticalExponent_pos a ha) u

theorem critical_heat_integral (a : Index d) (ha : a ≠ 0) (u : TensorL2 d) :
    (Real.Gamma ((d:ℝ)/2))⁻¹ • (∫ t : ℝ in Ioi 0, t^((d:ℝ)/2-1) • heat a ha t u) =
      criticalInverse a ha u := heat_integral_eq_inversePower a ha (criticalExponent_pos a ha) u

#print axioms inverse_dimension_summable
#print axioms criticalSymbol_sq_summable
#print axioms critical_heat_integral
#print axioms criticalInverse_compact
end Legacy.BecknerOnofri.JacobiTensorSpectrum
