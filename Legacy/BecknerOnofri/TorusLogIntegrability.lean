module

public import Legacy.BecknerOnofri.HeatDensityApproximation
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral

@[expose] public section

/-! Integrability of a logarithmic singularity on the actual Haar torus.
The quotient map from a centered fundamental cell is proved measure preserving.
-/
namespace Legacy.BecknerOnofri.TorusLogIntegrability
open MeasureTheory Set Legacy.TorusEndpoint
open scoped BigOperators

def centeredCell (d : ℕ) : Set (Fin d → ℝ) :=
  Set.univ.pi (fun _ => Ioc (-(1 / 2 : ℝ)) (1 / 2))

def quotientPoint {d : ℕ} (x : Fin d → ℝ) : Torus d := fun i => (x i : UnitAddCircle)

theorem centeredCell_measurable (d : ℕ) : MeasurableSet (centeredCell d) :=
  MeasurableSet.univ_pi (fun _ => measurableSet_Ioc)

theorem quotientPoint_measurePreserving (d : ℕ) :
    MeasurePreserving (@quotientPoint d) (volume.restrict (centeredCell d)) (torusMeasure d) := by
  have hc : MeasurePreserving ((↑) : ℝ → UnitAddCircle)
      (volume.restrict (Ioc (-(1 / 2 : ℝ)) (1 / 2))) AddCircle.haarAddCircle := by
    have h := AddCircle.measurePreserving_mk (T := 1) (-(1 / 2 : ℝ))
    have hv : (volume : Measure UnitAddCircle) = AddCircle.haarAddCircle := by
      simpa only [ENNReal.ofReal_one, one_smul] using
        (AddCircle.volume_eq_smul_haarAddCircle (T := 1))
    norm_num only [show -(1 / 2 : ℝ) + 1 = 1 / 2 by norm_num] at h
    rwa [hv] at h
  have h := measurePreserving_pi (fun _ : Fin d =>
      volume.restrict (Ioc (-(1 / 2 : ℝ)) (1 / 2)))
    (fun _ : Fin d => AddCircle.haarAddCircle) (fun _ => hc)
  rw [← Measure.restrict_pi_pi, ← volume_pi] at h
  exact h

theorem centeredCell_coordinates {d : ℕ} {x : Fin d → ℝ} (hx : x ∈ centeredCell d)
    (i : Fin d) : |x i| ≤ 1 / 2 := by
  have hi := hx i (Set.mem_univ i)
  exact abs_le.mpr ⟨hi.1.le, hi.2⟩

theorem ae_of_cell_except_zero {d : ℕ} (hd : 0 < d) {p : Torus d → Prop}
    (hp : MeasurableSet {z | p z})
    (h : ∀ x ∈ centeredCell d, x ≠ 0 → p (quotientPoint x)) :
    ∀ᵐ z ∂torusMeasure d, p z := by
  rw [← (quotientPoint_measurePreserving d).map_eq]
  apply (ae_map_iff (quotientPoint_measurePreserving d).aemeasurable hp).2
  have hzero : ∀ᵐ x : Fin d → ℝ ∂volume, x ≠ 0 := by
    filter_upwards [Measure.ae_eval_ne (fun _ : Fin d => (volume : Measure ℝ)) ⟨0, hd⟩ 0] with x hx
    intro hx0
    apply hx
    simp [hx0]
  filter_upwards [ae_restrict_mem (centeredCell_measurable d), ae_restrict_of_ae hzero] with x hx hx0
  exact h x hx hx0

theorem norm_rpow_integrableOn_cell {d : ℕ} (hd : 0 < d) {a : ℝ} (ha : a < d) :
    IntegrableOn (fun x : Fin d → ℝ => ‖x‖ ^ (-a)) (centeredCell d) := by
  have hm : AEStronglyMeasurable (fun x : Fin d → ℝ => ‖x‖ ^ (-a)) volume := by
    exact (measurable_norm.pow_const (-a)).aestronglyMeasurable
  have hl : LocallyIntegrable (fun x : Fin d → ℝ => ‖x‖ ^ (-a)) volume := by
    refine locallyIntegrable_of_norm_le_rpow (C := 1) (α := a)
      (by simpa using Nat.succ_le_of_lt hd : 1 ≤ Module.finrank ℝ (Fin d → ℝ)) ?_ ?_ hm
    · simpa using ha
    · filter_upwards [] with x
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _), one_mul]
  apply (hl.integrableOn_isCompact (isCompact_Icc :
    IsCompact (Icc (fun _ : Fin d => -(1 / 2 : ℝ)) (fun _ => (1 / 2 : ℝ))))).mono_set
  intro x hx
  exact ⟨fun i => (hx i (Set.mem_univ i)).1.le, fun i => (hx i (Set.mem_univ i)).2⟩

theorem exp_integrable_of_log_norm_bound {d : ℕ} (hd : 0 < d) {a C : ℝ}
    (ha0 : 0 ≤ a) (had : a < d) (F : Torus d → ℝ)
    (hF : AEStronglyMeasurable F (torusMeasure d))
    (hbound : ∀ x ∈ centeredCell d, x ≠ 0 → F (quotientPoint x) ≤ C - Real.log ‖x‖) :
    Integrable (fun z => Real.exp (a * F z)) (torusMeasure d) := by
  have hE : AEStronglyMeasurable (fun z => Real.exp (a * F z)) (torusMeasure d) :=
    Real.continuous_exp.comp_aestronglyMeasurable (hF.const_mul a)
  apply ((quotientPoint_measurePreserving d).integrable_comp hE).mp
  have hm := (norm_rpow_integrableOn_cell hd had).const_mul (Real.exp (a * C))
  apply hm.mono' (hE.comp_measurePreserving (quotientPoint_measurePreserving d))
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hzero : ∀ᵐ x : Fin d → ℝ ∂volume, x ≠ 0 := by
    filter_upwards [Measure.ae_eval_ne (fun _ : Fin d => (volume : Measure ℝ)) ⟨0, hd⟩ 0] with x hx
    intro hx0
    apply hx
    simp [hx0]
  filter_upwards [ae_restrict_mem (centeredCell_measurable d), ae_restrict_of_ae hzero] with x hx hx0
  dsimp only [Function.comp_apply]
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  calc
    Real.exp (a * F (quotientPoint x)) ≤ Real.exp (a * (C - Real.log ‖x‖)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hbound x hx hx0) ha0)
    _ = Real.exp (a * C) * ‖x‖ ^ (-a) := by
      rw [mul_sub, Real.exp_sub, Real.rpow_def_of_pos (norm_pos_iff.mpr hx0)]
      rw [show Real.log ‖x‖ * -a = -(a * Real.log ‖x‖) by ring, Real.exp_neg]
      rfl

theorem norm_le_radius {d : ℕ} (x : Fin d → ℝ) : ‖x‖ ≤ Real.sqrt (∑ i, (x i)^2) := by
  apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2
  intro i
  rw [Real.norm_eq_abs]
  apply (Real.le_sqrt (abs_nonneg _) (Finset.sum_nonneg (fun j _ => sq_nonneg (x j)))).2
  rw [sq_abs]
  exact Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)

theorem exp_integrable_of_log_radius_bound {d : ℕ} (hd : 0 < d) {a C : ℝ}
    (ha0 : 0 ≤ a) (had : a < d) (F : Torus d → ℝ)
    (hF : AEStronglyMeasurable F (torusMeasure d))
    (hbound : ∀ x ∈ centeredCell d, x ≠ 0 →
      F (quotientPoint x) ≤ -Real.log (Real.sqrt (∑ i, (x i)^2)) + C) :
    Integrable (fun z => Real.exp (a * F z)) (torusMeasure d) := by
  apply exp_integrable_of_log_norm_bound (C := C) hd ha0 had F hF
  intro x hx hx0
  have hlog := Real.log_le_log (norm_pos_iff.mpr hx0) (norm_le_radius x)
  linarith [hbound x hx hx0]

/-- An exponential upper tail and a lower bound give an actual L2 representative. -/
theorem memLp_two_of_lower_and_exp_integrable {d : ℕ} (F : Torus d → ℝ)
    (hF : AEStronglyMeasurable F (torusMeasure d)) {a B : ℝ} (ha : 0 < a)
    (hlower : ∀ᵐ x ∂torusMeasure d, -B ≤ F x)
    (hexp : Integrable (fun x => Real.exp (a * F x)) (torusMeasure d)) :
    MemLp F 2 (torusMeasure d) := by
  apply (memLp_two_iff_integrable_sq hF).2
  have hm := (hexp.const_mul (2 / a^2)).add
    (integrable_const (B^2) : Integrable (fun _ : Torus d => B^2) (torusMeasure d))
  apply hm.mono' (hF.pow 2)
  filter_upwards [hlower] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hap : 0 < a^2 := sq_pos_of_pos ha
  have hi : a^2 * (2 / a^2) = 2 := by field_simp
  by_cases hf : 0 ≤ F x
  · have he := Real.quadratic_le_exp_of_nonneg (mul_nonneg ha.le hf)
    have hb : F x ^ 2 ≤ (2 / a^2) * Real.exp (a * F x) := by
      apply (mul_le_mul_iff_right₀ hap).mp
      rw [← mul_assoc, hi]
      nlinarith [mul_nonneg ha.le hf]
    exact hb.trans (le_add_of_nonneg_right (sq_nonneg B))
  · have hs : F x^2 ≤ B^2 := by
      nlinarith [mul_nonneg (show 0 ≤ B + F x by linarith)
        (show 0 ≤ B - F x by linarith)]
    exact hs.trans (le_add_of_nonneg_left (by positivity))

#print axioms quotientPoint_measurePreserving
#print axioms exp_integrable_of_log_norm_bound
#print axioms exp_integrable_of_log_radius_bound
#print axioms memLp_two_of_lower_and_exp_integrable
end Legacy.BecknerOnofri.TorusLogIntegrability
