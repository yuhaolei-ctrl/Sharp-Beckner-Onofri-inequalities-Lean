module

public import Mathlib.MeasureTheory.Function.LpOrder
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Topology.Algebra.InfiniteSum.Module
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Tactic

@[expose] public section

/-! The positive cone of actual real L2 and its norm-convergent positive Neumann inverse.
No pointwise convergence, closed-cone property, or inverse positivity is assumed.
-/
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators
namespace Legacy.BecknerOnofri.PositiveOperatorNeumann

variable {α : Type*} [MeasurableSpace α] (μ : Measure α)
abbrev RealL2 := Lp ℝ 2 μ
abbrev Operator := RealL2 μ →L[ℝ] RealL2 μ

def Nonnegative (x : RealL2 μ) : Prop := ∀ᵐ a ∂μ, 0 ≤ x a

def Positive (T : Operator μ) : Prop := ∀ x, Nonnegative μ x → Nonnegative μ (T x)

theorem nonnegative_iff (x : RealL2 μ) : Nonnegative μ x ↔ 0 ≤ x :=
  Lp.coeFn_nonneg x

/-- The actual a.e. nonnegative cone is closed in the L2 norm topology. -/
theorem nonnegative_cone_closed : IsClosed {x : RealL2 μ | Nonnegative μ x} := by
  have he : {x : RealL2 μ | Nonnegative μ x} = Set.Ici (0 : RealL2 μ) := by
    ext x
    exact nonnegative_iff μ x
  rw [he]
  exact isClosed_Ici

theorem nonnegative_of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot]
    {f : ι → RealL2 μ} {x : RealL2 μ} (hf : ∀ᶠ i in l, Nonnegative μ (f i))
    (hlim : Tendsto f l (𝓝 x)) : Nonnegative μ x :=
  (nonnegative_cone_closed μ).mem_of_tendsto hlim hf

theorem positive_pow {T : Operator μ} (hT : Positive μ T) (n : ℕ) : Positive μ (T^n) := by
  intro x hx
  induction n with
  | zero => simpa using hx
  | succ n ih =>
    simpa only [pow_succ', ContinuousLinearMap.mul_apply] using hT _ ih

/-- The actual Neumann operator is the norm sum in the Banach algebra of bounded operators. -/
def neumannOperator (T : Operator μ) : Operator μ := ∑' n : ℕ, T^n

theorem operator_hasSum {T : Operator μ} (hT : ‖T‖ < 1) :
    HasSum (fun n : ℕ => T^n) (neumannOperator μ T) :=
  (summable_geometric_of_norm_lt_one hT).hasSum

/-- Applying the operator series gives a genuine norm-convergent L2 series. -/
theorem neumann_hasSum {T : Operator μ} (hT : ‖T‖ < 1) (x : RealL2 μ) :
    HasSum (fun n : ℕ => (T^n) x) (neumannOperator μ T x) := by
  simpa only [ContinuousLinearMap.apply_apply] using
    (operator_hasSum μ hT).mapL (ContinuousLinearMap.apply ℝ (RealL2 μ) x)

theorem neumann_nonnegative {T : Operator μ} (hT : Positive μ T) (hnorm : ‖T‖ < 1)
    {x : RealL2 μ} (hx : Nonnegative μ x) : Nonnegative μ (neumannOperator μ T x) := by
  apply (nonnegative_iff μ _).mpr
  exact HasSum.nonneg (fun n => (nonnegative_iff μ _).mp (positive_pow μ hT n x hx))
    (neumann_hasSum μ hnorm x)

theorem neumann_left_inverse {T : Operator μ} (hT : ‖T‖ < 1) (x : RealL2 μ) :
    neumannOperator μ T (x-T x) = x := by
  have h := congrArg (fun A : Operator μ => A x) (geom_series_mul_neg T hT)
  simpa only [neumannOperator, ContinuousLinearMap.mul_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.one_apply] using h

theorem neumann_right_inverse {T : Operator μ} (hT : ‖T‖ < 1) (x : RealL2 μ) :
    neumannOperator μ T x - T (neumannOperator μ T x) = x := by
  have h := congrArg (fun A : Operator μ => A x) (mul_neg_geom_series T hT)
  simpa only [neumannOperator, ContinuousLinearMap.mul_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.one_apply] using h

/-- Positivity of the actual inverse is proved by the nonnegative norm-convergent series. -/
theorem nonnegative_of_sub {T : Operator μ} (hT : Positive μ T) (hnorm : ‖T‖ < 1)
    (x : RealL2 μ) (hx : Nonnegative μ (x-T x)) : Nonnegative μ x := by
  have h := neumann_nonnegative μ hT hnorm hx
  rwa [neumann_left_inverse μ hnorm x] at h

/-- A constructive positive solution, including the actual L2 HasSum assertion. -/
theorem exists_nonnegative_solution {T : Operator μ} (hT : Positive μ T) (hnorm : ‖T‖ < 1)
    (y : RealL2 μ) (hy : Nonnegative μ y) :
    ∃ x : RealL2 μ, Nonnegative μ x ∧ x-T x = y ∧ HasSum (fun n : ℕ => (T^n) y) x :=
  ⟨neumannOperator μ T y, neumann_nonnegative μ hT hnorm hy,
    neumann_right_inverse μ hnorm y, neumann_hasSum μ hnorm y⟩

theorem telescoping_sum (T : Operator μ) (x : RealL2 μ) (n : ℕ) :
    (∑ j ∈ Finset.range n, (T^j) (x-T x)) = x-(T^n) x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    simp only [ContinuousLinearMap.mul_apply, map_sub]
    abel

/-- The same comparison works whenever one actual operator power is a contraction. -/
theorem nonnegative_of_sub_of_power {T : Operator μ} (hT : Positive μ T)
    {n : ℕ} (hnorm : ‖T^n‖ < 1) (x : RealL2 μ) (hx : Nonnegative μ (x-T x)) :
    Nonnegative μ x := by
  apply nonnegative_of_sub μ (positive_pow μ hT n) hnorm x
  rw [← telescoping_sum μ T x n]
  apply (nonnegative_iff μ _).mpr
  exact Finset.sum_nonneg (fun j _ => (nonnegative_iff μ _).mp (positive_pow μ hT j _ hx))

theorem nonnegative_of_sub_of_exists_power {T : Operator μ} (hT : Positive μ T)
    (hnorm : ∃ n : ℕ, ‖T^n‖ < 1) (x : RealL2 μ) (hx : Nonnegative μ (x-T x)) :
    Nonnegative μ x := by
  obtain ⟨n, hn⟩ := hnorm
  exact nonnegative_of_sub_of_power μ hT hn x hx

/-- A nonnegative integral kernel preserves a.e. nonnegativity, with genuine integrable slices. -/
theorem integral_kernel_nonnegative (K : α → α → ℝ) (f : RealL2 μ)
    (hK : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, 0 ≤ K x y) (hf : Nonnegative μ f)
    (hi : ∀ᵐ x ∂μ, Integrable (fun y => K x y * f y) μ) :
    ∀ᵐ x ∂μ, 0 ≤ ∫ y, K x y * f y ∂μ := by
  filter_upwards [hK, hi] with x hx hix
  have h := integral_mono_ae (integrable_zero α ℝ μ) hix (by
    filter_upwards [hx, hf] with y hy hfy
    exact mul_nonneg hy hfy)
  simpa only [Pi.zero_apply, integral_zero] using h

/-- A bounded operator identified with that actual kernel is therefore positive. -/
theorem positive_of_integral_kernel (T : Operator μ) (K : α → α → ℝ)
    (hK : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, 0 ≤ K x y)
    (hi : ∀ f : RealL2 μ, ∀ᵐ x ∂μ, Integrable (fun y => K x y * f y) μ)
    (heq : ∀ f : RealL2 μ, ∀ᵐ x ∂μ, T f x = ∫ y, K x y * f y ∂μ) : Positive μ T := by
  intro f hf
  filter_upwards [heq f, integral_kernel_nonnegative μ K f hK hf (hi f)] with x hx hp
  rwa [hx]

#print axioms nonnegative_cone_closed
#print axioms neumann_hasSum
#print axioms nonnegative_of_sub
#print axioms nonnegative_of_sub_of_exists_power
#print axioms positive_of_integral_kernel
end Legacy.BecknerOnofri.PositiveOperatorNeumann
