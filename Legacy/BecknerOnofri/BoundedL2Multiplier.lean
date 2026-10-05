module

public import Legacy.BecknerOnofri.PositiveOperatorNeumann
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.Analysis.Normed.Operator.Compact.Basic

@[expose] public section

/-! Genuine bounded multiplication and symmetric weighted operators in real L2. -/
noncomputable section
namespace Legacy.BecknerOnofri.BoundedL2Multiplier
open MeasureTheory PositiveOperatorNeumann
open scoped ENNReal
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)
variable [IsFiniteMeasure μ]

structure Weight where
  value : X → ℝ
  measurable : AEStronglyMeasurable value μ
  bound : ℝ
  nonneg_bound : 0 ≤ bound
  bounded : ∀ᵐ x ∂μ, ‖value x‖ ≤ bound

namespace Weight
variable {μ} (w : Weight μ)

theorem memLp_top : MemLp w.value ∞ μ := MemLp.of_bound w.measurable w.bound w.bounded

theorem product_memLp (f : RealL2 μ) : MemLp (fun x => w.value x*f x) 2 μ :=
  w.memLp_top.fun_mul (Lp.memLp f)

def product (f : RealL2 μ) : RealL2 μ := (w.product_memLp f).toLp (fun x => w.value x*f x)

theorem product_ae (f : RealL2 μ) : w.product f =ᵐ[μ] fun x => w.value x*f x :=
  (w.product_memLp f).coeFn_toLp

theorem product_add (f g : RealL2 μ) : w.product (f+g) = w.product f+w.product g := by
  apply Lp.ext
  filter_upwards [w.product_ae (f+g), w.product_ae f, w.product_ae g,
    Lp.coeFn_add f g, Lp.coeFn_add (w.product f) (w.product g)] with x hfg hf hg ha hb
  simpa only [ha, hb, hf, hg, Pi.add_apply, mul_add] using hfg

theorem product_smul (c : ℝ) (f : RealL2 μ) : w.product (c • f) = c • w.product f := by
  apply Lp.ext
  filter_upwards [w.product_ae (c • f), w.product_ae f,
    Lp.coeFn_smul c f, Lp.coeFn_smul c (w.product f)] with x hcf hf hs ht
  rw [hcf, ht]
  simp only [Pi.smul_apply, smul_eq_mul, hf] at hs ⊢
  rw [hs]
  ring

theorem product_norm_le (f : RealL2 μ) : ‖w.product f‖ ≤ w.bound*‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [w.product_ae f, w.bounded] with x he hb
  rw [he, norm_mul]
  exact mul_le_mul_of_nonneg_right hb (norm_nonneg _)

def operator : Operator μ :=
  LinearMap.mkContinuous
    { toFun := w.product
      map_add' := w.product_add
      map_smul' := w.product_smul }
    w.bound w.product_norm_le

theorem operator_ae (f : RealL2 μ) : w.operator f =ᵐ[μ] fun x => w.value x*f x := w.product_ae f

theorem operator_norm_le : ‖w.operator‖ ≤ w.bound :=
  w.operator.opNorm_le_bound w.nonneg_bound w.product_norm_le

theorem operator_symmetric : w.operator.IsSymmetric := by
  intro f g
  change inner ℝ (w.operator f) g = inner ℝ f (w.operator g)
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [w.operator_ae f, w.operator_ae g] with x hf hg
  simp only [hf, hg, RCLike.inner_apply, conj_trivial]
  ring

theorem operator_positive (hw : ∀ᵐ x ∂μ, 0 ≤ w.value x) : Positive μ w.operator := by
  intro f hf
  filter_upwards [hw, hf, w.operator_ae f] with x hw hf he
  rw [he]
  exact mul_nonneg hw hf

theorem nonnegative_of_operator (hw : ∀ᵐ x ∂μ, 0 < w.value x) {f : RealL2 μ}
    (hf : Nonnegative μ (w.operator f)) : Nonnegative μ f := by
  filter_upwards [hw, hf, w.operator_ae f] with x hw hf he
  rw [he] at hf
  exact (mul_nonneg_iff_of_pos_left hw).mp hf

theorem operator_eq_zero_iff (hw : ∀ᵐ x ∂μ, 0 < w.value x) (f : RealL2 μ) :
    w.operator f = 0 ↔ f = 0 := by
  constructor
  · intro he
    apply Lp.ext
    have hae := w.operator_ae f
    rw [he] at hae
    filter_upwards [hae, hw, Lp.coeFn_zero ℝ 2 μ] with x hx hp hz
    rw [hz]
    have h : w.value x*f x = 0 := by rw [← hx, hz]; rfl
    exact (mul_eq_zero.mp h).resolve_left hp.ne'
  · intro he
    rw [he, map_zero]

def conjugate (c : ℝ) (T : Operator μ) : Operator μ := c • w.operator.comp (T.comp w.operator)

theorem conjugate_apply (c : ℝ) (T : Operator μ) (f : RealL2 μ) :
    w.conjugate c T f = c • w.operator (T (w.operator f)) := rfl

theorem conjugate_symmetric (c : ℝ) {T : Operator μ} (hT : T.IsSymmetric) :
    (w.conjugate c T).IsSymmetric := by
  intro f g
  change inner ℝ (w.conjugate c T f) g = inner ℝ f (w.conjugate c T g)
  rw [conjugate_apply, conjugate_apply, real_inner_smul_left, real_inner_smul_right]
  congr 1
  calc
    _ = inner ℝ (T (w.operator f)) (w.operator g) := w.operator_symmetric _ _
    _ = inner ℝ (w.operator f) (T (w.operator g)) := hT _ _
    _ = _ := w.operator_symmetric _ _

theorem conjugate_positive {c : ℝ} (hc : 0 ≤ c) (hw : ∀ᵐ x ∂μ, 0 ≤ w.value x)
    {T : Operator μ} (hT : Positive μ T) : Positive μ (w.conjugate c T) := by
  intro f hf
  have hp := w.operator_positive hw _ (hT _ (w.operator_positive hw f hf))
  filter_upwards [hp, Lp.coeFn_smul c (w.operator (T (w.operator f)))] with x hx he
  change 0 ≤ (c • w.operator (T (w.operator f))) x
  rw [he]
  exact mul_nonneg hc hx

theorem conjugate_compact (c : ℝ) {T : Operator μ} (hT : IsCompactOperator T) :
    IsCompactOperator (w.conjugate c T) :=
  ((hT.comp_clm w.operator).clm_comp w.operator).smul c

#print axioms operator_symmetric
#print axioms conjugate_positive
end Weight
end Legacy.BecknerOnofri.BoundedL2Multiplier
