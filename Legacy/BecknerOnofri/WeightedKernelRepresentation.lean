module

public import Legacy.BecknerOnofri.BoundedL2Multiplier
public import Legacy.BecknerOnofri.PositiveKernelComparison

@[expose] public section

/-! Actual kernel representations and strict comparisons survive bounded
positive multiplication on both sides of the L2 operator. -/
noncomputable section
namespace Legacy.BecknerOnofri.BoundedL2Multiplier.Weight
open MeasureTheory PositiveOperatorNeumann
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ] (w : Weight μ)

def kernel (c : ℝ) (K : X × X → ℝ) (z : X × X) : ℝ :=
  c*w.value z.1*K z*w.value z.2

-- Product-measure lifting retains the ambient finite-measure instance.
theorem kernel_measurable (c : ℝ) {K : X × X → ℝ}
    (hK : AEStronglyMeasurable K (μ.prod μ)) : AEStronglyMeasurable (w.kernel c K) (μ.prod μ) :=
  (((aestronglyMeasurable_const.mul w.measurable.comp_fst).mul hK).mul w.measurable.comp_snd)

theorem kernel_nonnegative {c : ℝ} (hc : 0 ≤ c) (hw : ∀ᵐ x ∂μ, 0 ≤ w.value x)
    {K : X × X → ℝ} (hK : ∀ᵐ z ∂μ.prod μ, 0 ≤ K z) :
    ∀ᵐ z ∂μ.prod μ, 0 ≤ w.kernel c K z := by
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hw,
    Measure.quasiMeasurePreserving_snd.ae hw, hK] with z hx hy hk
  exact mul_nonneg (mul_nonneg (mul_nonneg hc hx) hk) hy

theorem kernel_strict_comparison {c : ℝ} (hc : 0 < c) (hw : ∀ᵐ x ∂μ, 0 < w.value x)
    {K L : X × X → ℝ} (hKL : ∀ᵐ z ∂μ.prod μ, K z < L z) :
    ∀ᵐ z ∂μ.prod μ, w.kernel c K z < w.kernel c L z := by
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hw,
    Measure.quasiMeasurePreserving_snd.ae hw, hKL] with z hx hy hkl
  exact mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left hkl (mul_pos hc hx)) hy

omit [IsFiniteMeasure μ] in
theorem kernel_symmetric (c : ℝ) {K : X × X → ℝ}
    (hK : ∀ᵐ z ∂μ.prod μ, K z.swap = K z) :
    ∀ᵐ z ∂μ.prod μ, w.kernel c K z.swap = w.kernel c K z := by
  filter_upwards [hK] with z hz
  dsimp [kernel]
  rw [hz]
  ring

theorem kernel_representation (c : ℝ) (T : Operator μ) (K : X × X → ℝ)
    (hrep : ∀ f : RealL2 μ, ∀ᵐ x ∂μ,
      Integrable (fun y => K (x,y)*f y) μ ∧ (∫ y, K (x,y)*f y ∂μ) = T f x)
    (f : RealL2 μ) : ∀ᵐ x ∂μ,
      Integrable (fun y => w.kernel c K (x,y)*f y) μ ∧
        (∫ y, w.kernel c K (x,y)*f y ∂μ) = w.conjugate c T f x := by
  filter_upwards [hrep (w.operator f), w.operator_ae (T (w.operator f)),
    Lp.coeFn_smul c (w.operator (T (w.operator f)))] with x hr hw hc
  have he : (fun y => w.kernel c K (x,y)*f y) =ᵐ[μ]
      (fun y => (c*w.value x)*(K (x,y)*(w.operator f) y)) := by
    filter_upwards [w.operator_ae f] with y hy
    rw [hy]
    dsimp [kernel]
    ring
  refine ⟨(hr.1.const_mul (c*w.value x)).congr he.symm, ?_⟩
  rw [integral_congr_ae he, integral_const_mul, hr.2]
  change c*w.value x*(T (w.operator f)) x = (c • w.operator (T (w.operator f))) x
  rw [hc]
  change c*w.value x*(T (w.operator f)) x = c*(w.operator (T (w.operator f))) x
  rw [hw]
  ring

#print axioms kernel_representation
#print axioms kernel_strict_comparison
end Legacy.BecknerOnofri.BoundedL2Multiplier.Weight

namespace Legacy.BecknerOnofri.PositiveKernelImproving
open MeasureTheory PositiveOperatorNeumann
variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]

theorem image_strict_positive (T : Operator μ) (K : X × X → ℝ)
    (hK : ∀ᵐ z ∂μ.prod μ, 0 < K z)
    (hrep : ∀ f : RealL2 μ, ∀ᵐ x ∂μ,
      Integrable (fun y => K (x,y)*f y) μ ∧ (∫ y, K (x,y)*f y ∂μ) = T f x)
    (f : RealL2 μ) (hf : Nonnegative μ f) (hne : f ≠ 0) : ∀ᵐ x ∂μ, 0 < T f x := by
  have hslice : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, 0 < K (x,y) := Measure.ae_ae_of_ae_prod hK
  filter_upwards [hslice, hrep f] with x hk hi
  rw [← hi.2]
  have hp : ∀ᵐ y ∂μ, 0 ≤ K (x,y)*f y := by
    filter_upwards [hk, hf] with y hk hf
    exact mul_nonneg hk.le hf
  apply lt_of_le_of_ne (integral_nonneg_of_ae hp)
  intro hz
  have he := (integral_eq_zero_iff_of_nonneg_ae hp hi.1).mp hz.symm
  apply hne
  apply Lp.ext
  filter_upwards [he, hk, Lp.coeFn_zero ℝ 2 μ] with y he hk hy
  rw [hy]
  exact (mul_eq_zero.mp he).resolve_left hk.ne'

#print axioms image_strict_positive
end Legacy.BecknerOnofri.PositiveKernelImproving
