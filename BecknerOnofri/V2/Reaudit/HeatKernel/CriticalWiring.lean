module

public import BecknerOnofri.V2.Reaudit.HeatKernel.MellinWiring
public import BecknerOnofri.GeneralEuler.CriticalComparison

@[expose] public section

/-! # Mellin kernels and the strict weighted-operator comparison on the new heat-kernel inputs
(U05/S015)

Re-proofs, with identical statements, of
`JacobiTensorMellin.kernel_nonnegative(_ae)`, `JacobiTensorMellin.kernel_lt_single_ae`,
`JacobiTensorMellin.inversePower_positive`,
`GeneralEuler.CriticalComparison.criticalInverse_positive` and
`GeneralEuler.CriticalComparison.higher_norm_lt_one`, the one-dimensional inputs being
`KernelDomination` (resolvent-comparison route).  Statement identity is certified by the
`type_of%` equalities at the end of the file.
-/

noncomputable section
open Set MeasureTheory Filter Classical
open scoped Topology BigOperators
namespace BecknerOnofri.V2.Reaudit.HeatKernel.Wiring
open Legacy.BecknerOnofri Legacy.BecknerOnofri.JacobiTensor
open Legacy.BecknerOnofri.JacobiTensorMellin

theorem mellin_kernel_nonnegative_V2 {d : ℕ} (a : Index d) {s : ℝ} (hs : 0 < s)
    {z : Space d × Space d} (hx : ∀ i, z.1 i ∈ Icc 0 Real.pi)
    (hy : ∀ i, z.2 i ∈ Icc 0 Real.pi) : 0 ≤ JacobiTensorMellin.kernel a s z := by
  apply mul_nonneg (inv_nonneg.mpr (Real.Gamma_pos_of_pos hs).le)
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact mul_nonneg (Real.rpow_nonneg ht.le _) (kernel_nonnegative_V2 a ht hx hy)

theorem mellin_kernel_nonnegative_ae_V2 {d : ℕ} (a : Index d) {s : ℝ} (hs : 0 < s) :
    ∀ᵐ z ∂pairMeasure d, 0 ≤ JacobiTensorMellin.kernel a s z := by
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae (ae_mem_box d),
    Measure.quasiMeasurePreserving_snd.ae (ae_mem_box d)] with z hx hy
  exact mellin_kernel_nonnegative_V2 a hs (fun i => ⟨(hx i).1.le, (hx i).2.le⟩)
    (fun i => ⟨(hy i).1.le, (hy i).2.le⟩)

theorem mellin_kernel_lt_single_ae_V2 {d : ℕ} (a : Index d) (i : Fin d) (hai : 1 ≤ a i)
    (hne : a ≠ Pi.single i 1) {s : ℝ} (hs : 0 < s) :
    ∀ᵐ z ∂pairMeasure d, JacobiTensorMellin.kernel a s z <
      JacobiTensorMellin.kernel (Pi.single i 1) s z := by
  have ha : a ≠ 0 := by
    intro h
    rw [h] at hai
    simp at hai
  have hb : (Pi.single i 1 : Index d) ≠ 0 := by
    intro h
    have hi := congrFun h i
    simp at hi
  filter_upwards [time_integrable_ae_V2 a ha hs, time_integrable_ae_V2 (Pi.single i 1) hb hs,
    Measure.quasiMeasurePreserving_fst.ae (ae_mem_box d),
    Measure.quasiMeasurePreserving_snd.ae (ae_mem_box d)] with z hz hzb hx hy
  apply mul_lt_mul_of_pos_left _ (inv_pos.mpr (Real.Gamma_pos_of_pos hs))
  apply integral_strict_mono hz hzb
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact mul_lt_mul_of_pos_left (kernel_lt_single_V2 a i hai hne ht hx hy)
    (Real.rpow_pos_of_pos ht _)

theorem inversePower_positive_V2 {d : ℕ} (a : Index d) (ha : a ≠ 0) {s : ℝ} (hs : 0 < s) :
    PositiveOperatorNeumann.Positive (JacobiTensor.measure d)
      (JacobiTensorSpectrum.inversePower a ha s hs) :=
  PositiveKernelRayleigh.represented_kernel_positive (JacobiTensor.measure d)
    (JacobiTensorSpectrum.inversePower a ha s hs) (JacobiTensorMellin.kernel a s)
    (mellin_kernel_nonnegative_ae_V2 a hs)
    (fun f => (kernel_representation_V2 a ha hs f).mono (fun _ h => h.2.symm))

end BecknerOnofri.V2.Reaudit.HeatKernel.Wiring

/-! ### Weighted Euler operators -/

namespace BecknerOnofri.V2.Reaudit.HeatKernel.Wiring
open MeasureTheory
open Legacy.BecknerOnofri
open Legacy.TorusEndpoint TorusSobolev SubcriticalAttainment SubcriticalEuler
open WienerFourier SmoothFourier SteinerSelection
open AngularMixedTerms JacobiTensor JacobiTensorSpectrum
open BecknerOnofri.GeneralEuler BecknerOnofri.GeneralEuler.CriticalComparison
open BecknerOnofri.GeneralEuler.WeightedEquation PositiveOperatorNeumann

theorem criticalInverse_positive_V2 {d : ℕ} (a : Index d) (ha : a ≠ 0) :
    Positive (JacobiTensor.measure d) (criticalInverse a ha) :=
  inversePower_positive_V2 a ha (criticalExponent_pos a ha)

section HigherNorm
variable {d : ℕ} (hd : 0 < d) {b Ab A : ℝ}
  (hR : RoughExponentialBound d b Ab) (hA : 0 < A) {u : TorusL2 d}
  (hu : SubcriticalAttainment.Admissible u)
  (hE : Regularity.Data A u)
  (hStR : Steiner (smoothGibbsValue u))
  (hStU : Steiner (fun x => (representative u x).re))

include hd hR hA hu hE hStR hStU
/-- Statement-identical to `GeneralEuler.CriticalComparison.higher_norm_lt_one`. -/
theorem higher_norm_lt_one_V2 (is : List (Fin d)) (his : is ≠ []) (hlong : 1 < is.length)
    (i : Fin d) (hi : i ∈ is) (hne : W hd hR hA hu hE hStR [i] ≠ 0) :
    ‖S hd hR hA hu hE hStR is his‖ < 1 := by
  let a := countIndex is
  let a₁ := countIndex [i]
  have ha : a ≠ 0 := BecknerOnofri.GeneralEuler.SpectralIntertwining.countIndex_ne_zero is his
  have ha₁ : a₁ ≠ 0 :=
    BecknerOnofri.GeneralEuler.SpectralIntertwining.countIndex_ne_zero [i] (by simp)
  have hs : (0 : ℝ) < (d : ℝ)/2 := criticalExponent_pos a ha
  have hc : 0 < 1/(2*A) := by positivity
  have hw : ∀ᵐ x ∂JacobiTensor.measure d,
      0 < (sqrtDensityWeight hd hR hA hu hE hStR).value x :=
    ae_of_all _ (sqrtDensity_pos hd hR hA hu hE hStR)
  have hK : ∀ᵐ z ∂(JacobiTensor.measure d).prod (JacobiTensor.measure d),
      0 < JacobiTensorMellin.kernel a₁ ((d:ℝ)/2) z := by
    simpa only [a₁, countIndex_single] using kernel_single_pos_ae_V2 i hs
  have hKL : ∀ᵐ z ∂(JacobiTensor.measure d).prod (JacobiTensor.measure d),
      JacobiTensorMellin.kernel a ((d:ℝ)/2) z < JacobiTensorMellin.kernel a₁ ((d:ℝ)/2) z := by
    have hh := countIndex_strict_comparison_data is hlong hi
    simpa only [a, a₁, countIndex_single] using
      mellin_kernel_lt_single_ae_V2 (countIndex is) i hh.1 hh.2 hs
  exact WeightedStrictComparison.norm_lt_one (sqrtDensityWeight hd hR hA hu hE hStR)
    hc hw (criticalInverse a₁ ha₁) (criticalInverse a ha)
    (JacobiTensorMellin.kernel a₁ ((d:ℝ)/2)) (JacobiTensorMellin.kernel a ((d:ℝ)/2))
    (JacobiTensorMellin.kernel_aestronglyMeasurable a₁ _)
    (JacobiTensorMellin.kernel_aestronglyMeasurable a _)
    hK (mellin_kernel_nonnegative_ae_V2 a hs) hKL
    (JacobiTensorMellin.kernel_symmetric_ae a₁ _) (JacobiTensorMellin.kernel_symmetric_ae a _)
    (kernel_representation_V2 a₁ ha₁ hs)
    (kernel_representation_V2 a ha hs)
    (criticalInverse_compact a ha) (W hd hR hA hu hE hStR [i])
    (W_first_nonnegative hd hR hA hu hE hStR hStU i) hne
    (first_eigen_equation hd hR hA hu hE hStR hStU i)

end HigherNorm

/-! ### Statement identity with the legacy declarations -/

theorem criticalInverse_positive_V2_type :
    (type_of% @criticalInverse_positive_V2) =
      (type_of% @BecknerOnofri.GeneralEuler.CriticalComparison.criticalInverse_positive) := rfl

theorem higher_norm_lt_one_V2_type :
    (type_of% @higher_norm_lt_one_V2) =
      (type_of% @BecknerOnofri.GeneralEuler.CriticalComparison.higher_norm_lt_one) := rfl

theorem inversePower_positive_V2_type :
    (type_of% @inversePower_positive_V2) =
      (type_of% @Legacy.BecknerOnofri.JacobiTensorMellin.inversePower_positive) := rfl

theorem mellin_kernel_lt_single_ae_V2_type :
    (type_of% @mellin_kernel_lt_single_ae_V2) =
      (type_of% @Legacy.BecknerOnofri.JacobiTensorMellin.kernel_lt_single_ae) := rfl

theorem mellin_kernel_nonnegative_ae_V2_type :
    (type_of% @mellin_kernel_nonnegative_ae_V2) =
      (type_of% @Legacy.BecknerOnofri.JacobiTensorMellin.kernel_nonnegative_ae) := rfl

end BecknerOnofri.V2.Reaudit.HeatKernel.Wiring
