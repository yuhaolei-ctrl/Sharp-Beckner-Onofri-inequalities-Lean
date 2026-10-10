module

public import BecknerOnofri.V2.Reaudit.SpinChannel.Cylinder
public import BecknerOnofri.ConditionalWeightedTower

@[expose] public section

/-!
# The conditional density `p_i(· | x_{<i})` tested against arbitrary bounded functions

`conditionalDensity f i x` (a ratio of prefix marginals) is the conditional density of `x_i` given
`x_{<i}`.  The tower identity of `ConditionalWeightedTower`, proved there for cosines only, holds for
every bounded measurable test function `g` of the circle variable; this is the statement that
`conditionalDensity` is a version of the conditional density (`condInt` is `E[g(x_i) | x_{<i}]`).
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Function
open scoped BigOperators
namespace BecknerOnofri.V2.Reaudit.SpinChannel
open BecknerOnofri.HighDim BecknerOnofri.HighDim.EntropyShearer BecknerOnofri.HighDim.ConditionalEntropy

/-- `E[g(x_i) | x_{<i}] = ∫ g(z) p_i(z | x_{<i}) dz` as a function of `x`. -/
def condInt {d : ℕ} (f : Torus d → ℝ) (i : Fin d) (g : UnitAddCircle → ℝ) (x : Torus d) : ℝ :=
  ∫ z, conditionalDensity f i x z * g z ∂AddCircle.haarAddCircle

/-- A bounded measurable function of the circle variable `x_i`. -/
def BMC (g : UnitAddCircle → ℝ) : Prop := Measurable g ∧ ∃ B : ℝ, ∀ z, ‖g z‖ ≤ B

theorem BMC.coord {d : ℕ} {g : UnitAddCircle → ℝ} (hg : BMC g) (i : Fin d) :
    BoundedMeasurable (fun x : Torus d => g (x i)) := by
  obtain ⟨hm, B, hB⟩ := hg
  exact ⟨hm.comp (measurable_pi_apply i), B, fun x => hB _⟩

theorem condInt_formula {d : ℕ} (f : Torus d → ℝ) (i : Fin d) (g : UnitAddCircle → ℝ) :
    condInt f i g = fun x =>
      avg {i} (fun y => prefixDensity f (i.val + 1) y * g (y i)) x / prefixDensity f i.val x := by
  funext x
  rw [avg_singleton]
  simp only [condInt, conditionalDensity, Function.update_self]
  simp_rw [div_mul_eq_mul_div]
  rw [integral_div]

theorem condInt_bounded {d : ℕ} {f : Torus d → ℝ} (hf : PositiveBounded f) (i : Fin d)
    {g : UnitAddCircle → ℝ} (hg : BMC g) : BoundedMeasurable (condInt f i g) := by
  rw [condInt_formula f]
  simpa only [div_eq_mul_inv] using
    (((prefix_positive hf (i.val + 1)).bounded.mul (hg.coord i)).avg {i}).mul
      (prefix_positive hf i.val).invBounded

theorem condInt_prefix_congr {d : ℕ} (f : Torus d → ℝ) (i : Fin d) (g : UnitAddCircle → ℝ)
    {x y : Torus d} (hxy : ∀ j : Fin d, j.val < i.val → x j = y j) :
    condInt f i g x = condInt f i g y := by
  unfold condInt
  rw [conditional_density_prefix_congr f i hxy]

theorem condInt_cos {d : ℕ} (f : Torus d → ℝ) (i : Fin d) (n : ℕ) :
    condInt f i (fun z => (fourier (n : ℤ) z).re) = conditionalCosineMoment f i n := rfl

/-- **Weighted tower identity for an arbitrary bounded test function** (the general form of
`conditional_moment_weighted_tower`). -/
theorem condInt_weighted_tower {d : ℕ} {f w : Torus d → ℝ} (hf : PositiveBounded f)
    (hw : BoundedMeasurable w) (i : Fin d) {g : UnitAddCircle → ℝ} (hg : BMC g)
    (hpre : ∀ x y : Torus d, (∀ j : Fin d, j.val < i.val → x j = y j) → w x = w y) :
    (∫ x, f x * (w x * condInt f i g x) ∂torusMeasure d) =
      ∫ x, f x * (w x * g (x i)) ∂torusMeasure d := by
  let a := prefixDensity f (i.val + 1)
  let b := prefixDensity f i.val
  let c : Torus d → ℝ := fun x => g (x i)
  have ha : PositiveBounded a := prefix_positive hf _
  have hb : PositiveBounded b := prefix_positive hf _
  have hc : BoundedMeasurable c := hg.coord i
  have hwi (x : Torus d) (y : suffixCoordinates d i.val → UnitAddCircle) :
      w (updateFinset x (suffixCoordinates d i.val) y) = w x := by
    apply hpre
    intro j hj
    simp [updateFinset, Nat.not_le_of_lt hj]
  have hwfuture (x : Torus d) (y : suffixCoordinates d (i.val + 1) → UnitAddCircle) :
      w (updateFinset x (suffixCoordinates d (i.val + 1)) y) = w x := by
    apply hpre
    intro j hj
    have hlt : j.val < i.val + 1 := by omega
    simp [updateFinset, Nat.not_le_of_lt hlt]
  have hwsingle (x : Torus d) (y : ({i} : Finset (Fin d)) → UnitAddCircle) :
      w (updateFinset x {i} y) = w x := by
    apply hpre
    intro j hj
    have hne : j ≠ i := by intro he; subst j; omega
    simp [updateFinset, hne]
  calc
    _ = ∫ x, b x * (w x * condInt f i g x) ∂torusMeasure d :=
      integral_pairing _ hf.bounded (hw.mul (condInt_bounded hf i hg))
        (fun x y => by simp only [hwi, condInt, conditional_density_suffix_update])
    _ = ∫ x, avg {i} (fun y => a y * c y) x * w x ∂torusMeasure d := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [condInt_formula f]
      change b x * (w x * (avg {i} (fun y => a y * c y) x / b x)) = _
      field_simp [(hb.pos x).ne']
    _ = ∫ x, (a x * c x) * w x ∂torusMeasure d :=
      (integral_pairing {i} (ha.bounded.mul hc) hw hwsingle).symm
    _ = ∫ x, a x * (w x * c x) ∂torusMeasure d := by
      apply integral_congr_ae
      filter_upwards [] with x
      ring
    _ = _ := (integral_pairing (suffixCoordinates d (i.val + 1)) hf.bounded (hw.mul hc)
      (fun x y => by
        rw [hwfuture]
        have hi : i ∉ suffixCoordinates d (i.val + 1) := by simp
        simp [c, updateFinset, hi])).symm

end BecknerOnofri.V2.Reaudit.SpinChannel
