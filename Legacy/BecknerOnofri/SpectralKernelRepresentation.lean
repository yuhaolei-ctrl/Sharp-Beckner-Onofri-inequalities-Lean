module

public import Legacy.BecknerOnofri.SpectralKernelTensor
public import Mathlib.MeasureTheory.Function.LpSeminorm.Prod
public import Mathlib.MeasureTheory.Function.AEEqOfIntegral

@[expose] public section

/-! Reconstruction of the genuine a.e. integral representation of a Hilbert diagonal operator.
Square summability is a hypothesis on the actual symbol. Kernel norm convergence and
representation are conclusions, not auxiliary hypotheses. -/
noncomputable section
open MeasureTheory Filter Set Classical
open scoped Topology ENNReal BigOperators
namespace Legacy.BecknerOnofri.SpectralKernel
open SpectralHeatInverse
variable {α ι : Type*} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ]

/-- Every square-summable scalar family defines an actual l2 coordinate vector. -/
def coefficientVector (a : ι→ℝ) (ha : Summable (fun i => a i^2)) : Coordinates ι :=
  ⟨a,memℓp_gen (by simpa using ha)⟩

/-- Square summability proves boundedness, so no independent bound on the symbol is assumed. -/
def squareSummableSymbol (a : ι→ℝ) (ha : Summable (fun i => a i^2)) : Symbol ι :=
  boundedSymbol a ‖coefficientVector a ha‖ (by
    intro i
    exact lp.norm_apply_le_norm (by norm_num : (2:ℝ≥0∞)≠0) (coefficientVector a ha) i)

@[simp] theorem squareSummableSymbol_apply (a : ι→ℝ) (ha : Summable (fun i => a i^2)) (i : ι) :
    squareSummableSymbol a ha i=a i := rfl

/-- The L2 kernel series has exactly the bilinear form of the genuine diagonal operator. -/
theorem spectralKernel_pairing (e : HilbertBasis ι ℝ (RealL2 μ)) (a : Symbol ι)
    (ha : Summable (fun i => (a i)^2)) (f g : RealL2 μ) :
    inner ℝ (tensor μ g f) (spectralKernel μ e a) = inner ℝ g (diagonal e a f) := by
  have hK := (spectralKernel_hasSum μ e a ha).mapL (innerSL ℝ (tensor μ g f))
  have hT := e.hasSum_inner_mul_inner g (diagonal e a f)
  apply hK.unique
  apply hT.congr_fun
  intro i
  simp only [innerSL_apply_apply,inner_smul_right,inner_tensor]
  rw [← e.repr_apply_apply,repr_diagonal,e.repr_apply_apply,real_inner_comm (e i) f]
  ring

/-- A genuine L2 kernel paired against a product tensor is the iterated kernel pairing. -/
theorem kernel_pairing (K : KernelL2 μ) (f g : RealL2 μ) :
    inner ℝ (tensor μ g f) K = ∫ x, g x * (∫ y, K (x,y)*f y ∂μ) ∂μ := by
  have hprod : Integrable (fun z : α×α => g z.1*(K z*f z.2)) (μ.prod μ) := by
    apply (L2.integrable_inner (𝕜:=ℝ) (tensor μ g f) K).congr
    filter_upwards [tensor_coe μ g f] with z hz
    simp only [RCLike.inner_apply,conj_trivial,hz]
    ring
  rw [L2.inner_def]
  calc
    (∫ z, inner ℝ (tensor μ g f z) (K z) ∂μ.prod μ) =
        ∫ z : α×α, g z.1*(K z*f z.2) ∂μ.prod μ := by
      apply integral_congr_ae
      filter_upwards [tensor_coe μ g f] with z hz
      simp only [RCLike.inner_apply,conj_trivial,hz]
      ring
    _ = ∫ x, g x*(∫ y, K (x,y)*f y ∂μ) ∂μ := by
      rw [integral_prod _ hprod]
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [integral_const_mul]

section Finite
variable [IsFiniteMeasure μ]

/-- L2 Cauchy–Schwarz on the product gives integrability before taking slices. -/
theorem kernel_action_integrable (K : KernelL2 μ) (f : RealL2 μ) :
    Integrable (fun z : α×α => K z*f z.2) (μ.prod μ) := by
  exact (Lp.memLp K).integrable_mul ((Lp.memLp f).comp_snd μ)

theorem kernel_action_slices (K : KernelL2 μ) (f : RealL2 μ) :
    ∀ᵐ x ∂μ, Integrable (fun y => K (x,y)*f y) μ :=
  (kernel_action_integrable μ K f).prod_right_ae

/-- The actual L2 spectral kernel represents the diagonal operator on every L2 input. -/
theorem spectralKernel_represents (e : HilbertBasis ι ℝ (RealL2 μ)) (a : Symbol ι)
    (ha : Summable (fun i => (a i)^2)) (f : RealL2 μ) :
    (fun x => ∫ y, spectralKernel μ e a (x,y)*f y ∂μ) =ᵐ[μ] diagonal e a f := by
  apply Integrable.ae_eq_of_forall_setIntegral_eq _ _
    (kernel_action_integrable μ (spectralKernel μ e a) f).integral_prod_left
    ((Lp.memLp (diagonal e a f)).integrable (by norm_num))
  intro s hs hμs
  let g : RealL2 μ := indicatorConstLp 2 hs hμs.ne (1:ℝ)
  rw [← L2.inner_indicatorConstLp_one hs hμs.ne (diagonal e a f)]
  change (∫ x in s, ∫ y, spectralKernel μ e a (x,y)*f y ∂μ ∂μ) = inner ℝ g (diagonal e a f)
  rw [← spectralKernel_pairing μ e a ha f g,kernel_pairing]
  rw [← integral_indicator hs]
  apply integral_congr_ae
  filter_upwards [@indicatorConstLp_coeFn α _ _ 2 μ _ s hs hμs.ne (1:ℝ)] with x hx
  change s.indicator (fun x => ∫ y, spectralKernel μ e a (x,y)*f y ∂μ) x =
    g x*(∫ y, spectralKernel μ e a (x,y)*f y ∂μ)
  change indicatorConstLp 2 hs hμs.ne (1:ℝ) x = _ at hx
  rw [show g x = s.indicator (fun _ => (1:ℝ)) x from hx]
  by_cases hx' : x∈s <;> simp [hx']

/-- Both the a.e. slice integrability and the actual operator identity are proved. -/
theorem spectralKernel_representation (e : HilbertBasis ι ℝ (RealL2 μ)) (a : Symbol ι)
    (ha : Summable (fun i => (a i)^2)) (f : RealL2 μ) :
    ∀ᵐ x ∂μ, Integrable (fun y => spectralKernel μ e a (x,y)*f y) μ ∧
      (∫ y, spectralKernel μ e a (x,y)*f y ∂μ) = diagonal e a f x :=
  (kernel_action_slices μ _ f).and (spectralKernel_represents μ e a ha f)
/-- The reconstruction also accepts a plain square-summable coefficient family. -/
theorem squareSummable_representation (e : HilbertBasis ι ℝ (RealL2 μ)) (a : ι→ℝ)
    (ha : Summable (fun i => a i^2)) (f : RealL2 μ) :
    ∀ᵐ x ∂μ, Integrable (fun y => spectralKernel μ e a (x,y)*f y) μ ∧
      (∫ y, spectralKernel μ e a (x,y)*f y ∂μ) = diagonal e (squareSummableSymbol a ha) f x := by
  exact spectralKernel_representation μ e (squareSummableSymbol a ha) ha f

/-- The actual inverse spectral power has the actual reconstructed L2 kernel whenever its
squared spectral coefficients are summable. The spectral summability remains explicit. -/
theorem inversePower_kernel_representation (e : HilbertBasis ι ℝ (RealL2 μ))
    (D : PositiveSpectrum ι) (s : ℝ) (hs : 0<s)
    (hseries : Summable (fun i => (D.value i^(-s))^2)) (f : RealL2 μ) :
    ∀ᵐ x ∂μ, Integrable (fun y => spectralKernel μ e (fun i => D.value i^(-s)) (x,y)*f y) μ ∧
      (∫ y, spectralKernel μ e (fun i => D.value i^(-s)) (x,y)*f y ∂μ) = inversePower e D s hs f x := by
  exact spectralKernel_representation μ e (D.inverseSymbol s hs) hseries f

end Finite

#print axioms spectralKernel_pairing
#print axioms spectralKernel_representation
end Legacy.BecknerOnofri.SpectralKernel
