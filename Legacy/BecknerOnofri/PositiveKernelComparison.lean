module

public import Legacy.BecknerOnofri.PositiveKernelSpectrum

@[expose] public section

/-! Genuine dominated-kernel modulus and strict compact comparison.
The top eigenvector and strict norm conclusion are derived, not assumed.
-/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Legacy.BecknerOnofri.PositiveKernelRayleigh
open PositiveOperatorNeumann
variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ]

theorem pair_measurable {L : α × α → ℝ}
    (hL : AEStronglyMeasurable L (μ.prod μ)) (f g : RealL2 μ) :
    AEStronglyMeasurable (fun z => L z*f z.1*g z.2) (μ.prod μ) :=
  (hL.mul (Lp.aestronglyMeasurable f).comp_fst).mul (Lp.aestronglyMeasurable g).comp_snd

/-- Product integrability is inherited from the proved Schur majorant. -/
theorem dominated_pair_integrable {K L : α × α → ℝ} {φ : RealL2 μ}
    (hK : SchurData μ K φ) (hL : AEStronglyMeasurable L (μ.prod μ))
    (hdom : ∀ᵐ z ∂μ.prod μ, |L z| ≤ K z) (f g : RealL2 μ) :
    Integrable (fun z => L z*f z.1*g z.2) (μ.prod μ) := by
  apply (kernel_pair_integrable μ hK f g).abs.mono' (pair_measurable μ hL f g)
  filter_upwards [hdom,hK.nonnegative] with z hz hk
  simp only [Real.norm_eq_abs,abs_mul,abs_of_nonneg hk]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hz (abs_nonneg _)) (abs_nonneg _)

/-- Moving modulus to the two actual L2 arguments is justified by their a.e. representatives. -/
theorem integral_abs_pair_eq {L : α × α → ℝ}
    (hn : ∀ᵐ z ∂μ.prod μ, 0 ≤ L z) (f g : RealL2 μ) :
    (∫ z, |L z*f z.1*g z.2| ∂μ.prod μ) =
      ∫ z, L z*(|f|) z.1*(|g|) z.2 ∂μ.prod μ := by
  have hf : ∀ᵐ z ∂μ.prod μ, (|f|) z.1 = |f z.1| :=
    Measure.quasiMeasurePreserving_fst.ae (Lp.coeFn_abs f)
  have hg : ∀ᵐ z ∂μ.prod μ, (|g|) z.2 = |g z.2| :=
    Measure.quasiMeasurePreserving_snd.ae (Lp.coeFn_abs g)
  apply integral_congr_ae
  filter_upwards [hf,hg,hn] with z hf hg hn
  simp only [hf,hg,abs_mul,abs_of_nonneg hn]

/-- Schur also bounds the integral of the pointwise absolute value, not only the integral's modulus. -/
theorem kernel_abs_integral_le {K : α × α → ℝ} {φ : RealL2 μ}
    (hK : SchurData μ K φ) (f g : RealL2 μ) :
    (∫ z, |K z*f z.1*g z.2| ∂μ.prod μ) ≤ (‖f‖^2+‖g‖^2)/2 := by
  rw [integral_abs_pair_eq μ hK.nonnegative f g]
  have hb := kernel_pair_abs_le μ hK |f| |g|
  simp only [norm_abs_eq_norm] at hb
  exact (le_abs_self _).trans hb

/-- A generic actual kernel pairing identity, requiring the proved pair integrability. -/
theorem represented_inner (S : Operator μ) (L : α × α → ℝ)
    (heq : ∀ f : RealL2 μ, ∀ᵐ x ∂μ, S f x = ∫ y, L (x,y)*f y ∂μ)
    (f g : RealL2 μ)
    (hi : Integrable (fun z => L z*f z.1*g z.2) (μ.prod μ)) :
    inner ℝ f (S g) = ∫ z, L z*f z.1*g z.2 ∂μ.prod μ := by
  rw [L2.inner_def,integral_prod _ hi]
  apply integral_congr_ae
  filter_upwards [heq g] with x hx
  simp only [RCLike.inner_apply,conj_trivial,hx]
  rw [← integral_mul_const]
  apply integral_congr_ae
  exact ae_of_all _ (fun y => by ring)

/-- The modulus comparison is proved for actual dominated nonnegative integral kernels. -/
theorem dominated_kernel_modulus (S : Operator μ) {K L : α × α → ℝ} {φ : RealL2 μ}
    (hK : SchurData μ K φ) (hL : AEStronglyMeasurable L (μ.prod μ))
    (hn : ∀ᵐ z ∂μ.prod μ, 0 ≤ L z)
    (hdom : ∀ᵐ z ∂μ.prod μ, |L z| ≤ K z)
    (heq : ∀ f : RealL2 μ, ∀ᵐ x ∂μ, S f x = ∫ y, L (x,y)*f y ∂μ)
    (f : RealL2 μ) : |inner ℝ f (S f)| ≤ inner ℝ |f| (S |f|) := by
  rw [represented_inner μ S L heq f f (dominated_pair_integrable μ hK hL hdom f f),
    represented_inner μ S L heq |f| |f| (dominated_pair_integrable μ hK hL hdom |f| |f|)]
  rw [← integral_abs_pair_eq μ hn f f]
  simpa only [Real.norm_eq_abs] using
    norm_integral_le_integral_norm (fun z => L z*f z.1*f z.2) (μ:=μ.prod μ)

/-- Symmetry of the true kernel gives self-adjointness of its represented bounded operator. -/
theorem dominated_kernel_symmetric (S : Operator μ) {K L : α × α → ℝ} {φ : RealL2 μ}
    (hK : SchurData μ K φ) (hL : AEStronglyMeasurable L (μ.prod μ))
    (hdom : ∀ᵐ z ∂μ.prod μ, |L z| ≤ K z)
    (hs : ∀ᵐ z ∂μ.prod μ, L z.swap = L z)
    (heq : ∀ f : RealL2 μ, ∀ᵐ x ∂μ, S f x = ∫ y, L (x,y)*f y ∂μ) : S.IsSymmetric := by
  intro f g
  change inner ℝ (S f) g = inner ℝ f (S g)
  rw [real_inner_comm g (S f),
    represented_inner μ S L heq g f (dominated_pair_integrable μ hK hL hdom g f),
    represented_inner μ S L heq f g (dominated_pair_integrable μ hK hL hdom f g)]
  rw [← integral_prod_swap (fun z => L z*f z.1*g z.2)]
  apply integral_congr_ae
  filter_upwards [hs] with z hz
  change L z*g z.1*f z.2 = L z.swap*f z.2*g z.1
  rw [hz]
  ring

/-- Actual nonnegative top eigenvectors exist for every nonzero compact dominated kernel operator. -/
theorem dominated_kernel_nonnegative_top (S : Operator μ) {K L : α × α → ℝ} {φ : RealL2 μ}
    (hK : SchurData μ K φ) (hL : AEStronglyMeasurable L (μ.prod μ))
    (hn : ∀ᵐ z ∂μ.prod μ, 0 ≤ L z)
    (hdom : ∀ᵐ z ∂μ.prod μ, |L z| ≤ K z)
    (hs : ∀ᵐ z ∂μ.prod μ, L z.swap = L z)
    (heq : ∀ f : RealL2 μ, ∀ᵐ x ∂μ, S f x = ∫ y, L (x,y)*f y ∂μ)
    (hc : IsCompactOperator S) (hne : S ≠ 0) :
    ∃ f : RealL2 μ, f ≠ 0 ∧ Nonnegative μ f ∧ S f = ‖S‖ • f :=
  exists_nonnegative_top_of_modulus μ S hc
    (dominated_kernel_symmetric μ S hK hL hdom hs heq) hne
    (dominated_kernel_modulus μ S hK hL hn hdom heq)

theorem nonzero_not_ae_zero (f : RealL2 μ) (hf : f ≠ 0) :
    ¬ (∀ᵐ x ∂μ, f x = 0) := by
  intro hh
  apply hf
  apply Lp.ext
  filter_upwards [hh,Lp.coeFn_zero ℝ 2 μ] with x hx hz
  simpa only [Pi.zero_apply,hx] using hz.symm

/-- A nonzero L2 function cannot vanish in at least one coordinate of almost every pair. -/
theorem nonzero_pair (f : RealL2 μ) (hf : f ≠ 0) :
    ¬ (∀ᵐ z ∂μ.prod μ, f z.1 = 0 ∨ f z.2 = 0) := by
  intro hh
  have hn := nonzero_not_ae_zero μ f hf
  have hr := Measure.ae_ae_of_ae_prod hh
  have hx : ∃ x, f x ≠ 0 ∧ (∀ᵐ y ∂μ, f x = 0 ∨ f y = 0) := by
    by_contra! hno
    apply hn
    filter_upwards [hr] with x hx
    by_contra hfx
    apply hno x hfx
    filter_upwards [hx] with y hy
    tauto
  obtain ⟨x,hx,hrow⟩ := hx
  apply hn
  filter_upwards [hrow] with y hy
  exact hy.resolve_left hx

/-- Strict kernel domination gives a strict integral gap for every nonzero L2 vector. -/
theorem strict_kernel_integral (K L : α × α → ℝ) (f : RealL2 μ) (hf : f ≠ 0)
    (hn : ∀ᵐ z ∂μ.prod μ, 0 ≤ L z)
    (hlt : ∀ᵐ z ∂μ.prod μ, L z < K z)
    (hL : Integrable (fun z => L z*f z.1*f z.2) (μ.prod μ))
    (hK : Integrable (fun z => K z*f z.1*f z.2) (μ.prod μ)) :
    (∫ z, |L z*f z.1*f z.2| ∂μ.prod μ) <
      ∫ z, |K z*f z.1*f z.2| ∂μ.prod μ := by
  have hle : (fun z => |L z*f z.1*f z.2|) ≤ᵐ[μ.prod μ]
      (fun z => |K z*f z.1*f z.2|) := by
    filter_upwards [hn,hlt] with z hn hl
    simp only [abs_mul,abs_of_nonneg hn,abs_of_nonneg (hn.trans hl.le)]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hl.le (abs_nonneg _)) (abs_nonneg _)
  have hne : ¬ (fun z => |L z*f z.1*f z.2|) =ᵐ[μ.prod μ]
      (fun z => |K z*f z.1*f z.2|) := by
    intro he
    apply nonzero_pair μ f hf
    filter_upwards [he,hn,hlt] with z he hn hl
    by_contra! hpair
    have hx := abs_pos.mpr hpair.1
    have hy := abs_pos.mpr hpair.2
    have hh := mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_right hl hx) hy
    simp only [abs_mul,abs_of_nonneg hn,abs_of_nonneg (hn.trans hl.le)] at he
    exact ne_of_lt hh he
  have hneInt := (integral_eq_iff_of_ae_le hL.abs hK.abs hle).not.mpr hne
  exact lt_of_le_of_ne (integral_mono_ae hL.abs hK.abs hle) hneInt

/-- The final strict compact kernel comparison has no Rayleigh or eigenvector-existence premise. -/
theorem strict_kernel_norm_lt_one (S : Operator μ) {K L : α × α → ℝ} {φ : RealL2 μ}
    (hK : SchurData μ K φ) (hL : AEStronglyMeasurable L (μ.prod μ))
    (hn : ∀ᵐ z ∂μ.prod μ, 0 ≤ L z)
    (hlt : ∀ᵐ z ∂μ.prod μ, L z < K z)
    (hs : ∀ᵐ z ∂μ.prod μ, L z.swap = L z)
    (heq : ∀ f : RealL2 μ, ∀ᵐ x ∂μ, S f x = ∫ y, L (x,y)*f y ∂μ)
    (hc : IsCompactOperator S) : ‖S‖ < 1 := by
  have hdom : ∀ᵐ z ∂μ.prod μ, |L z| ≤ K z := by
    filter_upwards [hn,hlt] with z hn hl
    simpa only [abs_of_nonneg hn] using hl.le
  apply norm_lt_one_of_strict_rayleigh S hc
    (dominated_kernel_symmetric μ S hK hL hdom hs heq)
  intro f hf
  rw [represented_inner μ S L heq f f (dominated_pair_integrable μ hK hL hdom f f)]
  have hgap := strict_kernel_integral μ K L f hf hn hlt
    (dominated_pair_integrable μ hK hL hdom f f) (kernel_pair_integrable μ hK f f)
  have hnorm : |∫ z, L z*f z.1*f z.2 ∂μ.prod μ| ≤
      ∫ z, |L z*f z.1*f z.2| ∂μ.prod μ := by
    simpa only [Real.norm_eq_abs] using
      norm_integral_le_integral_norm (fun z => L z*f z.1*f z.2) (μ:=μ.prod μ)
  have hupper := kernel_abs_integral_le μ hK f f
  exact (hnorm.trans_lt hgap).trans_le (by linarith only [hupper])

/-- The actual represented nonnegative kernel preserves the L2 positive cone. -/
theorem represented_kernel_positive (S : Operator μ) (L : α × α → ℝ)
    (hn : ∀ᵐ z ∂μ.prod μ, 0 ≤ L z)
    (heq : ∀ f : RealL2 μ, ∀ᵐ x ∂μ, S f x = ∫ y, L (x,y)*f y ∂μ) :
    Positive μ S := by
  intro f hf
  filter_upwards [heq f,Measure.ae_ae_of_ae_prod hn] with x hx hn
  rw [hx]
  apply integral_nonneg_of_ae
  filter_upwards [hn,hf] with y hn hf
  exact mul_nonneg hn hf

/-- Strict compact kernel comparison followed by the genuine positive Neumann inverse. -/
theorem strict_kernel_nonnegative_of_sub (S : Operator μ) {K L : α × α → ℝ} {φ : RealL2 μ}
    (hK : SchurData μ K φ) (hL : AEStronglyMeasurable L (μ.prod μ))
    (hn : ∀ᵐ z ∂μ.prod μ, 0 ≤ L z)
    (hlt : ∀ᵐ z ∂μ.prod μ, L z < K z)
    (hs : ∀ᵐ z ∂μ.prod μ, L z.swap = L z)
    (heq : ∀ f : RealL2 μ, ∀ᵐ x ∂μ, S f x = ∫ y, L (x,y)*f y ∂μ)
    (hc : IsCompactOperator S) (x : RealL2 μ) (hx : Nonnegative μ (x-S x)) :
    Nonnegative μ x :=
  nonnegative_of_sub μ (represented_kernel_positive μ S L hn heq)
    (strict_kernel_norm_lt_one μ S hK hL hn hlt hs heq hc) x hx

#print axioms dominated_kernel_nonnegative_top
#print axioms strict_kernel_integral
#print axioms strict_kernel_norm_lt_one
#print axioms strict_kernel_nonnegative_of_sub
end Legacy.BecknerOnofri.PositiveKernelRayleigh
