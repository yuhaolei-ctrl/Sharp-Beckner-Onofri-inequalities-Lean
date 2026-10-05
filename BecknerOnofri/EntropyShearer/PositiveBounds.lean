module

public import BecknerOnofri.EntropyShearer.Marginal
public import BecknerOnofri.Entropy

@[expose] public section

noncomputable section
open MeasureTheory Function

namespace BecknerOnofri.HighDim.EntropyShearer

/-- A genuine measurable density bounded above and uniformly away from zero. -/
def PositiveBounded {d : ℕ} (f : Torus d → ℝ) : Prop :=
  Measurable f ∧ ∃ c B : ℝ, 0 < c ∧ ∀ x, c ≤ f x ∧ f x ≤ B

theorem PositiveBounded.pos {d : ℕ} {f : Torus d → ℝ}
    (hf : PositiveBounded f) (x : Torus d) : 0 < f x := by
  obtain ⟨hm, c, B, hc, hb⟩ := hf
  exact hc.trans_le (hb x).1

theorem PositiveBounded.bounded {d : ℕ} {f : Torus d → ℝ}
    (hf : PositiveBounded f) : BoundedMeasurable f := by
  obtain ⟨hm, c, B, hc, hb⟩ := hf
  refine ⟨hm, B, fun x => ?_⟩
  simpa only [Real.norm_eq_abs, abs_of_pos (hc.trans_le (hb x).1)] using (hb x).2

theorem PositiveBounded.logBounded {d : ℕ} {f : Torus d → ℝ}
    (hf : PositiveBounded f) : BoundedMeasurable (fun x => Real.log (f x)) := by
  obtain ⟨hm, c, B, hc, hb⟩ := hf
  refine ⟨Real.measurable_log.comp hm, |Real.log c| + |Real.log B|, fun x => ?_⟩
  have hlo := Real.log_le_log hc (hb x).1
  have hhi := Real.log_le_log (hc.trans_le (hb x).1) (hb x).2
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · linarith [neg_abs_le (Real.log c), abs_nonneg (Real.log B)]
  · linarith [le_abs_self (Real.log B), abs_nonneg (Real.log c)]

theorem PositiveBounded.invBounded {d : ℕ} {f : Torus d → ℝ}
    (hf : PositiveBounded f) : BoundedMeasurable (fun x => (f x)⁻¹) := by
  obtain ⟨hm, c, B, hc, hb⟩ := hf
  refine ⟨hm.inv, c⁻¹, fun x => ?_⟩
  rw [norm_inv, Real.norm_eq_abs, abs_of_pos (hc.trans_le (hb x).1)]
  simpa only [one_div] using one_div_le_one_div_of_le hc (hb x).1

theorem PositiveBounded.avg {d : ℕ} {f : Torus d → ℝ}
    (hf : PositiveBounded f) (s : Finset (Fin d)) : PositiveBounded (avg s f) := by
  obtain ⟨hm, c, B, hc, hb⟩ := hf
  refine ⟨avg_measurable s hm, c, B, hc, fun x => ?_⟩
  have hi : Integrable (fun y : s → UnitAddCircle => f (updateFinset x s y))
      (Measure.pi (fun _ : s => AddCircle.haarAddCircle)) := by
    apply (integrable_const B).mono' (hm.comp measurable_updateFinset).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun y => by
      change ‖f (updateFinset x s y)‖ ≤ B
      rw [Real.norm_eq_abs, abs_of_pos (hc.trans_le (hb _).1)]
      exact (hb _).2)
  constructor
  · have h := integral_mono (integrable_const c) hi (fun y => (hb _).1)
    simpa [EntropyShearer.avg] using h
  · have h := integral_mono hi (integrable_const B) (fun y => (hb _).2)
    simpa [EntropyShearer.avg] using h

theorem positiveBounded_of_continuous_pos {d : ℕ} {f : Torus d → ℝ}
    (hf : Continuous f) (hpos : ∀ x, 0 < f x) : PositiveBounded f := by
  obtain ⟨xmin, _, hmin⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty hf.continuousOn
  obtain ⟨xmax, _, hmax⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hf.continuousOn
  exact ⟨hf.measurable, f xmin, f xmax, hpos xmin,
    fun x => ⟨hmin (Set.mem_univ x), hmax (Set.mem_univ x)⟩⟩

/-- The scalar log-sum tangent inequality used in actual marginal contraction. -/
theorem relative_young {a b c e : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (he : 0 < e) :
    a * (Real.log c - Real.log e) ≤
      a * (Real.log a - Real.log b) - a + b * (c / e) := by
  have h := entropy_young a (Real.log c - Real.log e + Real.log b) ha.le
  rw [Real.exp_add, Real.exp_sub, Real.exp_log hc, Real.exp_log he, Real.exp_log hb] at h
  nlinarith

end BecknerOnofri.HighDim.EntropyShearer
