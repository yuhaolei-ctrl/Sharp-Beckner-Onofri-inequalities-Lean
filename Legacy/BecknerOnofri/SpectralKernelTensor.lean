import Legacy.BecknerOnofri.SpectralHeatCompact
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod

/-! Genuine real L2 product tensors and square-summable diagonal kernel series. -/
noncomputable section
open MeasureTheory Filter Set Classical
open scoped Topology ENNReal BigOperators
namespace Legacy.BecknerOnofri.SpectralKernel
variable {α ι : Type*} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ]
abbrev RealL2 := Lp ℝ 2 μ
abbrev KernelL2 := Lp ℝ 2 (μ.prod μ)

/-- The separated product of two genuine L2 representatives is square-integrable. -/
theorem tensor_memLp (f g : RealL2 μ) :
    MemLp (fun z : α×α => f z.1*g z.2) 2 (μ.prod μ) := by
  apply (memLp_two_iff_integrable_sq
    (((Lp.aestronglyMeasurable f).comp_fst (ν:=μ)).mul
      ((Lp.aestronglyMeasurable g).comp_snd (μ:=μ)))).mpr
  simpa only [Pi.mul_apply,mul_pow] using (Lp.memLp f).integrable_sq.mul_prod (Lp.memLp g).integrable_sq

def tensor (f g : RealL2 μ) : KernelL2 μ :=
  (tensor_memLp μ f g).toLp (fun z : α×α => f z.1*g z.2)

theorem tensor_coe (f g : RealL2 μ) :
    (tensor μ f g : α×α→ℝ) =ᵐ[μ.prod μ] fun z => f z.1*g z.2 :=
  (tensor_memLp μ f g).coeFn_toLp

theorem inner_tensor (f g u v : RealL2 μ) :
    inner ℝ (tensor μ f g) (tensor μ u v) = inner ℝ f u * inner ℝ g v := by
  rw [L2.inner_def,L2.inner_def,L2.inner_def,← integral_prod_mul]
  apply integral_congr_ae
  filter_upwards [tensor_coe μ f g,tensor_coe μ u v] with z hz hz'
  simp only [hz,hz',RCLike.inner_apply,conj_trivial]
  ring

theorem norm_tensor (f g : RealL2 μ) : ‖tensor μ f g‖=‖f‖*‖g‖ := by
  have h := inner_tensor μ f g f g
  simp only [real_inner_self_eq_norm_sq] at h
  apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg f) (norm_nonneg g))).mp
  simpa only [mul_pow] using h

theorem tensor_orthonormal (e : HilbertBasis ι ℝ (RealL2 μ)) :
    Orthonormal ℝ (fun i => tensor μ (e i) (e i)) := by
  rw [orthonormal_iff_ite]
  intro i j
  rw [inner_tensor]
  simp only [orthonormal_iff_ite.mp e.orthonormal]
  split_ifs <;> norm_num

/-- Square summability of the symbol gives actual norm summability of the L2 kernel series. -/
theorem kernel_summable (e : HilbertBasis ι ℝ (RealL2 μ)) (a : ι→ℝ)
    (ha : Summable (fun i => a i^2)) :
    Summable (fun i => a i • tensor μ (e i) (e i)) := by
  have h := (tensor_orthonormal μ e).orthogonalFamily.summable_iff_norm_sq_summable a
  simpa only [LinearIsometry.toSpanSingleton_apply,Real.norm_eq_abs,sq_abs] using h.mpr
    (by simpa only [Real.norm_eq_abs,sq_abs] using ha)

/-- This definition lives in L2 of the product measure, not in a formal kernel space. -/
def spectralKernel (e : HilbertBasis ι ℝ (RealL2 μ)) (a : ι→ℝ) : KernelL2 μ :=
  ∑' i, a i • tensor μ (e i) (e i)

theorem spectralKernel_hasSum (e : HilbertBasis ι ℝ (RealL2 μ)) (a : ι→ℝ)
    (ha : Summable (fun i => a i^2)) :
    HasSum (fun i => a i • tensor μ (e i) (e i)) (spectralKernel μ e a) :=
  (kernel_summable μ e a ha).hasSum

#print axioms inner_tensor
#print axioms spectralKernel_hasSum
end Legacy.BecknerOnofri.SpectralKernel
