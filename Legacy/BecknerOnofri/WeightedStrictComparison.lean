module

public import Legacy.BecknerOnofri.WeightedKernelRepresentation

@[expose] public section

/-! Actual weighted Schur normalization from a nonzero nonnegative Euler
eigenvector, followed by strict comparison and the positive Neumann inverse. -/
noncomputable section
namespace Legacy.BecknerOnofri.WeightedStrictComparison
open MeasureTheory PositiveOperatorNeumann PositiveKernelRayleigh BoundedL2Multiplier
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

theorem weighted_kernel_positive (w : Weight μ) {c : ℝ} (hc : 0 < c)
    (hw : ∀ᵐ x ∂μ, 0 < w.value x) {K : X × X → ℝ} (hK : ∀ᵐ z ∂μ.prod μ, 0 < K z) :
    ∀ᵐ z ∂μ.prod μ, 0 < w.kernel c K z := by
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hw,
    Measure.quasiMeasurePreserving_snd.ae hw, hK] with z hx hy hk
  exact mul_pos (mul_pos (mul_pos hc hx) hk) hy

theorem schur_of_weighted_eigenvector (w : Weight μ) {c : ℝ} (hc : 0 < c)
    (hw : ∀ᵐ x ∂μ, 0 < w.value x) (T : Operator μ) (K : X × X → ℝ)
    (hm : AEStronglyMeasurable K (μ.prod μ))
    (hK : ∀ᵐ z ∂μ.prod μ, 0 < K z) (hs : ∀ᵐ z ∂μ.prod μ, K z.swap = K z)
    (hrep : ∀ f : RealL2 μ, ∀ᵐ x ∂μ,
      Integrable (fun y => K (x,y)*f y) μ ∧ (∫ y, K (x,y)*f y ∂μ) = T f x)
    (φ : RealL2 μ) (hφ : Nonnegative μ φ) (hne : φ ≠ 0) (heigen : w.conjugate c T φ = φ) :
    SchurData μ (w.kernel c K) φ := by
  have hpos := weighted_kernel_positive w hc hw hK
  have hr := w.kernel_representation c T K hrep
  have hφpos := PositiveKernelImproving.image_strict_positive μ (w.conjugate c T)
    (w.kernel c K) hpos hr φ hφ hne
  rw [heigen] at hφpos
  exact SchurData.of_eigenfunction μ (w.conjugate c T) (w.kernel c K) φ (w.kernel_measurable c hm)
    (hpos.mono (fun _ h => h.le)) (w.kernel_symmetric c hs) hφpos
    ((hr φ).mono (fun _ h => h.1)) ((hr φ).mono (fun _ h => h.2.symm)) heigen

theorem norm_lt_one (w : Weight μ) {c : ℝ} (hc : 0 < c)
    (hw : ∀ᵐ x ∂μ, 0 < w.value x) (T R : Operator μ) (K L : X × X → ℝ)
    (hmK : AEStronglyMeasurable K (μ.prod μ)) (hmL : AEStronglyMeasurable L (μ.prod μ))
    (hK : ∀ᵐ z ∂μ.prod μ, 0 < K z) (hL : ∀ᵐ z ∂μ.prod μ, 0 ≤ L z)
    (hKL : ∀ᵐ z ∂μ.prod μ, L z < K z)
    (hsK : ∀ᵐ z ∂μ.prod μ, K z.swap = K z) (hsL : ∀ᵐ z ∂μ.prod μ, L z.swap = L z)
    (hrepK : ∀ f : RealL2 μ, ∀ᵐ x ∂μ,
      Integrable (fun y => K (x,y)*f y) μ ∧ (∫ y, K (x,y)*f y ∂μ) = T f x)
    (hrepL : ∀ f : RealL2 μ, ∀ᵐ x ∂μ,
      Integrable (fun y => L (x,y)*f y) μ ∧ (∫ y, L (x,y)*f y ∂μ) = R f x)
    (hcompact : IsCompactOperator R) (φ : RealL2 μ) (hφ : Nonnegative μ φ)
    (hne : φ ≠ 0) (heigen : w.conjugate c T φ = φ) : ‖w.conjugate c R‖ < 1 := by
  apply strict_kernel_norm_lt_one μ (w.conjugate c R)
    (schur_of_weighted_eigenvector w hc hw T K hmK hK hsK hrepK φ hφ hne heigen)
    (w.kernel_measurable c hmL)
    (w.kernel_nonnegative hc.le (hw.mono (fun _ h => h.le)) hL)
    (w.kernel_strict_comparison hc hw hKL) (w.kernel_symmetric c hsL)
    (fun f => (w.kernel_representation c R L hrepL f).mono (fun _ h => h.2.symm))
    (w.conjugate_compact c hcompact)

theorem nonnegative_of_residual (w : Weight μ) {c : ℝ} (hc : 0 < c)
    (hw : ∀ᵐ x ∂μ, 0 < w.value x) (T R : Operator μ) (K L : X × X → ℝ)
    (hmK : AEStronglyMeasurable K (μ.prod μ)) (hmL : AEStronglyMeasurable L (μ.prod μ))
    (hK : ∀ᵐ z ∂μ.prod μ, 0 < K z) (hL : ∀ᵐ z ∂μ.prod μ, 0 ≤ L z)
    (hKL : ∀ᵐ z ∂μ.prod μ, L z < K z)
    (hsK : ∀ᵐ z ∂μ.prod μ, K z.swap = K z) (hsL : ∀ᵐ z ∂μ.prod μ, L z.swap = L z)
    (hrepK : ∀ f : RealL2 μ, ∀ᵐ x ∂μ,
      Integrable (fun y => K (x,y)*f y) μ ∧ (∫ y, K (x,y)*f y ∂μ) = T f x)
    (hrepL : ∀ f : RealL2 μ, ∀ᵐ x ∂μ,
      Integrable (fun y => L (x,y)*f y) μ ∧ (∫ y, L (x,y)*f y ∂μ) = R f x)
    (hcompact : IsCompactOperator R) (φ : RealL2 μ) (hφ : Nonnegative μ φ)
    (hne : φ ≠ 0) (heigen : w.conjugate c T φ = φ)
    (v : RealL2 μ) (hv : Nonnegative μ (v-w.conjugate c R v)) : Nonnegative μ v := by
  apply nonnegative_of_sub μ
    (w.conjugate_positive hc.le (hw.mono (fun _ h => h.le))
      (represented_kernel_positive μ R L hL (fun f => (hrepL f).mono (fun _ h => h.2.symm))))
    (norm_lt_one w hc hw T R K L hmK hmL hK hL hKL hsK hsL hrepK hrepL hcompact φ hφ hne heigen)
    v hv

#print axioms schur_of_weighted_eigenvector
#print axioms nonnegative_of_residual
end Legacy.BecknerOnofri.WeightedStrictComparison
