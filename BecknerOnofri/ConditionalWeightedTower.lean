module

public import BecknerOnofri.ConditionalExpectations

@[expose] public section

/-! The conditional tower identity with a likelihood depending on earlier
coordinates. This is the angle-to-spin posterior identity in the manuscript. -/

noncomputable section
open MeasureTheory Function

namespace BecknerOnofri.HighDim.ConditionalEntropy
open EntropyShearer

theorem conditional_moment_weighted_tower {d : ℕ} {f w : Torus d → ℝ}
    (hf : PositiveBounded f) (hw : BoundedMeasurable w) (i : Fin d) (n : ℕ)
    (hpre : ∀ x y : Torus d, (∀ j : Fin d, j.val < i.val → x j = y j) → w x = w y) :
    (∫ x, f x * (w x * conditionalCosineMoment f i n x) ∂torusMeasure d) =
      ∫ x, f x * (w x * (fourier (n : ℤ) (x i)).re) ∂torusMeasure d := by
  let a := prefixDensity f (i.val + 1)
  let b := prefixDensity f i.val
  let c : Torus d → ℝ := fun x => (fourier (n : ℤ) (x i)).re
  have ha : PositiveBounded a := prefix_positive hf _
  have hb : PositiveBounded b := prefix_positive hf _
  have hc : BoundedMeasurable c := cosine_bounded i n
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
    _ = ∫ x, b x * (w x * conditionalCosineMoment f i n x) ∂torusMeasure d :=
      integral_pairing _ hf.bounded (hw.mul (conditional_moment_bounded hf i n))
        (fun x y => by simp only [hwi, conditionalCosineMoment, conditional_density_suffix_update])
    _ = ∫ x, avg {i} (fun y => a y * c y) x * w x ∂torusMeasure d := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [conditional_moment_formula f]
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

#print axioms conditional_moment_weighted_tower

end BecknerOnofri.HighDim.ConditionalEntropy
