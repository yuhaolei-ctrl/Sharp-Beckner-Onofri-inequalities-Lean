module

public import Legacy.BecknerOnofri.PositiveOperatorNeumann
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-! Actual weighted Schur estimates for symmetric nonnegative kernels on real L2.
The weighted quotient is not assumed integrable: Tonelli/Fubini proves its integrability
from the positive eigenfunction identity.
-/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Legacy.BecknerOnofri.PositiveKernelRayleigh
open PositiveOperatorNeumann

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ]

/-- All hypotheses concern the displayed genuine kernel and its eigenfunction. -/
structure SchurData (K : α × α → ℝ) (φ : RealL2 μ) : Prop where
  measurable : AEStronglyMeasurable K (μ.prod μ)
  nonnegative : ∀ᵐ z ∂μ.prod μ, 0 ≤ K z
  symmetric : ∀ᵐ z ∂μ.prod μ, K z.swap = K z
  positive : ∀ᵐ x ∂μ, 0 < φ x
  slices : ∀ᵐ x ∂μ, Integrable (fun y => K (x,y)*φ y) μ
  eigen : ∀ᵐ x ∂μ, (∫ y, K (x,y)*φ y ∂μ) = φ x

/-- Assemble the kernel hypotheses from a genuine operator eigenvector equation. -/
theorem SchurData.of_eigenfunction (T : Operator μ) (K : α × α → ℝ) (φ : RealL2 μ)
    (hm : AEStronglyMeasurable K (μ.prod μ))
    (hn : ∀ᵐ z ∂μ.prod μ, 0 ≤ K z)
    (hs : ∀ᵐ z ∂μ.prod μ, K z.swap = K z)
    (hp : ∀ᵐ x ∂μ, 0 < φ x)
    (hi : ∀ᵐ x ∂μ, Integrable (fun y => K (x,y)*φ y) μ)
    (heq : ∀ᵐ x ∂μ, T φ x = ∫ y, K (x,y)*φ y ∂μ)
    (heigen : T φ = φ) : SchurData μ K φ := by
  refine ⟨hm,hn,hs,hp,hi,?_⟩
  filter_upwards [heq] with x hx
  simpa only [heigen] using hx.symm

/-- The quotient only occurs inside the complete product majorant. -/
def weightedMajorant (K : α × α → ℝ) (φ f : RealL2 μ) (z : α × α) : ℝ :=
  f z.1^2 / φ z.1 * (K z * φ z.2)

theorem square_integral (f : RealL2 μ) : (∫ x, f x^2 ∂μ) = ‖f‖^2 := by
  rw [← real_inner_self_eq_norm_sq]
  rw [L2.inner_def]
  simp only [RCLike.inner_apply, conj_trivial, sq]

private theorem weighted_measurable {K : α × α → ℝ} {φ : RealL2 μ}
    (h : SchurData μ K φ) (f : RealL2 μ) :
    AEStronglyMeasurable (weightedMajorant μ K φ f) (μ.prod μ) := by
  have hf := (Lp.aestronglyMeasurable f).comp_fst (ν:=μ)
  have hp := (Lp.aestronglyMeasurable φ).comp_fst (ν:=μ)
  have hq := (Lp.aestronglyMeasurable φ).comp_snd (μ:=μ)
  exact ((hf.aemeasurable.pow_const 2).div hp.aemeasurable).aestronglyMeasurable.mul
    (h.measurable.mul hq)

private theorem weighted_nonnegative {K : α × α → ℝ} {φ : RealL2 μ}
    (h : SchurData μ K φ) (f : RealL2 μ) :
    ∀ᵐ z ∂μ.prod μ, 0 ≤ weightedMajorant μ K φ f z := by
  have hp : ∀ᵐ z ∂μ.prod μ, 0 < φ z.1 := Measure.quasiMeasurePreserving_fst.ae h.positive
  have hq : ∀ᵐ z ∂μ.prod μ, 0 < φ z.2 := Measure.quasiMeasurePreserving_snd.ae h.positive
  filter_upwards [hp,hq,h.nonnegative] with z hz hz' hk
  exact mul_nonneg (div_nonneg (sq_nonneg _) hz.le) (mul_nonneg hk hz'.le)

private theorem weighted_slice_integral {K : α × α → ℝ} {φ : RealL2 μ}
    (h : SchurData μ K φ) (f : RealL2 μ) :
    ∀ᵐ x ∂μ, (∫ y, weightedMajorant μ K φ f (x,y) ∂μ) = f x^2 := by
  filter_upwards [h.positive,h.eigen] with x hp he
  change (∫ y, f x^2/φ x*(K (x,y)*φ y) ∂μ) = _
  rw [integral_const_mul, he]
  field_simp

/-- Product integrability follows from Tonelli; no integrability of `f²/φ` is assumed. -/
theorem weighted_integrable {K : α × α → ℝ} {φ : RealL2 μ}
    (h : SchurData μ K φ) (f : RealL2 μ) :
    Integrable (weightedMajorant μ K φ f) (μ.prod μ) := by
  apply (integrable_prod_iff (weighted_measurable μ h f)).mpr
  constructor
  · filter_upwards [h.slices] with x hx
    exact hx.const_mul (f x^2/φ x)
  · apply (Lp.memLp f).integrable_sq.congr
    filter_upwards [weighted_slice_integral μ h f,
      Measure.ae_ae_of_ae_prod (weighted_nonnegative μ h f)] with x hx hn
    rw [← hx]
    apply integral_congr_ae
    filter_upwards [hn] with y hy
    exact (Real.norm_of_nonneg hy).symm

theorem weighted_integral {K : α × α → ℝ} {φ : RealL2 μ}
    (h : SchurData μ K φ) (f : RealL2 μ) :
    (∫ z, weightedMajorant μ K φ f z ∂μ.prod μ) = ‖f‖^2 := by
  rw [integral_prod _ (weighted_integrable μ h f)]
  rw [integral_congr_ae (weighted_slice_integral μ h f), square_integral]

/-- The elementary weighted square inequality with positive weights. -/
theorem weighted_product_bound {a b p q k : ℝ} (hp : 0<p) (hq : 0<q) (hk : 0≤k) :
    |k*a*b| ≤ (a^2/p*(k*q)+b^2/q*(k*p))/2 := by
  have hpq : 0 < p*q := mul_pos hp hq
  have hs : 2 * |a| * |b| *(p*q) ≤ a^2*q^2+b^2*p^2 := by
    nlinarith [sq_nonneg (|a| * q - |b| * p), sq_abs a, sq_abs b]
  have hd : 2 * |a| * |b| ≤ a^2/p*q+b^2/q*p := by
    apply (le_of_mul_le_mul_right _ hpq)
    convert! hs using 1 <;> field_simp <;> ring
  rw [abs_mul,abs_mul,abs_of_nonneg hk]
  have hm := mul_le_mul_of_nonneg_left hd hk
  nlinarith only [hm]

/-- A bound for arbitrary pairs, strong enough to prove the operator contraction. -/
theorem kernel_pair_integrable {K : α × α → ℝ} {φ : RealL2 μ}
    (h : SchurData μ K φ) (f g : RealL2 μ) :
    Integrable (fun z => K z*f z.1*g z.2) (μ.prod μ) := by
  have hI := ((weighted_integrable μ h f).add (weighted_integrable μ h g).swap).div_const 2
  apply hI.mono'
  · exact (h.measurable.mul (Lp.aestronglyMeasurable f).comp_fst).mul
      (Lp.aestronglyMeasurable g).comp_snd
  · have hp : ∀ᵐ z ∂μ.prod μ, 0<φ z.1 := Measure.quasiMeasurePreserving_fst.ae h.positive
    have hq : ∀ᵐ z ∂μ.prod μ, 0<φ z.2 := Measure.quasiMeasurePreserving_snd.ae h.positive
    filter_upwards [hp,hq,h.nonnegative,h.symmetric] with z hp hq hk hs
    simp only [Pi.div_apply, Pi.add_apply, Function.comp_apply, weightedMajorant,
      Real.norm_eq_abs, hs]
    exact weighted_product_bound hp hq hk

theorem kernel_pair_abs_le {K : α × α → ℝ} {φ : RealL2 μ}
    (h : SchurData μ K φ) (f g : RealL2 μ) :
    |∫ z, K z*f z.1*g z.2 ∂μ.prod μ| ≤ (‖f‖^2+‖g‖^2)/2 := by
  have hI := ((weighted_integrable μ h f).add (weighted_integrable μ h g).swap).div_const 2
  have hbound : ∀ᵐ z ∂μ.prod μ, |K z*f z.1*g z.2| ≤
      (weightedMajorant μ K φ f z + weightedMajorant μ K φ g z.swap)/2 := by
    have hp : ∀ᵐ z ∂μ.prod μ, 0<φ z.1 := Measure.quasiMeasurePreserving_fst.ae h.positive
    have hq : ∀ᵐ z ∂μ.prod μ, 0<φ z.2 := Measure.quasiMeasurePreserving_snd.ae h.positive
    filter_upwards [hp,hq,h.nonnegative,h.symmetric] with z hp hq hk hs
    simpa only [weightedMajorant,Prod.swap, show K (z.2,z.1) = K z from hs] using weighted_product_bound
      (a:=f z.1) (b:=g z.2) hp hq hk
  calc
    _ ≤ ∫ z, |K z*f z.1*g z.2| ∂μ.prod μ := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (fun z => K z*f z.1*g z.2) (μ:=μ.prod μ)
    _ ≤ ∫ z, (weightedMajorant μ K φ f z+weightedMajorant μ K φ g z.swap)/2 ∂μ.prod μ :=
      integral_mono_ae (kernel_pair_integrable μ h f g).abs hI hbound
    _ = _ := by
      have hgs : Integrable (fun z => weightedMajorant μ K φ g z.swap) (μ.prod μ) :=
        (weighted_integrable μ h g).swap
      rw [integral_div, integral_add (weighted_integrable μ h f) hgs, weighted_integral μ h f]
      rw [integral_prod_swap, weighted_integral μ h g]

/-- The bounded operator is identified with the actual kernel, not a formal pairing. -/
theorem inner_eq_kernel_pair (T : Operator μ) (K : α × α → ℝ) (φ : RealL2 μ)
    (h : SchurData μ K φ)
    (heq : ∀ f : RealL2 μ, ∀ᵐ x ∂μ, T f x = ∫ y, K (x,y)*f y ∂μ)
    (f g : RealL2 μ) :
    inner ℝ f (T g) = ∫ z, K z*f z.1*g z.2 ∂μ.prod μ := by
  rw [L2.inner_def, integral_prod _ (kernel_pair_integrable μ h f g)]
  apply integral_congr_ae
  filter_upwards [heq g] with x hx
  simp only [RCLike.inner_apply, conj_trivial, hx]
  rw [← integral_mul_const]
  apply integral_congr_ae
  exact ae_of_all _ (fun y => by ring)

theorem inner_abs_le (T : Operator μ) (K : α × α → ℝ) (φ : RealL2 μ)
    (h : SchurData μ K φ)
    (heq : ∀ f : RealL2 μ, ∀ᵐ x ∂μ, T f x = ∫ y, K (x,y)*f y ∂μ)
    (f g : RealL2 μ) : |inner ℝ f (T g)| ≤ (‖f‖^2+‖g‖^2)/2 := by
  rw [inner_eq_kernel_pair μ T K φ h heq]
  exact kernel_pair_abs_le μ h f g

/-- The actual operator norm is at most one; take `f=Tg` in the proved bilinear bound. -/
theorem norm_le_one (T : Operator μ) (K : α × α → ℝ) (φ : RealL2 μ)
    (h : SchurData μ K φ)
    (heq : ∀ f : RealL2 μ, ∀ᵐ x ∂μ, T f x = ∫ y, K (x,y)*f y ∂μ) : ‖T‖ ≤ 1 := by
  apply T.opNorm_le_bound (by norm_num)
  intro g
  have hb := inner_abs_le μ T K φ h heq (T g) g
  rw [real_inner_self_eq_norm_sq, abs_of_nonneg (sq_nonneg _)] at hb
  simp only [one_mul]
  nlinarith [norm_nonneg g, norm_nonneg (T g)]

theorem rayleigh_le_one (T : Operator μ) (K : α × α → ℝ) (φ : RealL2 μ)
    (h : SchurData μ K φ)
    (heq : ∀ f : RealL2 μ, ∀ᵐ x ∂μ, T f x = ∫ y, K (x,y)*f y ∂μ)
    (f : RealL2 μ) : inner ℝ f (T f) ≤ ‖f‖^2 := by
  have hb := inner_abs_le μ T K φ h heq f f
  linarith [le_abs_self (inner ℝ f (T f))]

#print axioms weighted_integrable
#print axioms kernel_pair_abs_le
#print axioms norm_le_one
#print axioms rayleigh_le_one
end Legacy.BecknerOnofri.PositiveKernelRayleigh
