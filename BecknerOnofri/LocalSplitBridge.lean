module

public import BecknerOnofri.LocalNegativity
public import BecknerOnofri.FirstShellSharpness

@[expose] public section

/-! Identification of the local split pressure with the trusted actual dual functional. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate
namespace BecknerOnofri.HighDim
open Legacy.BecknerOnofri.TorusSobolev
open Legacy.BecknerOnofri.SubcriticalAttainment
open Legacy.BecknerOnofri.SubcriticalEuler

lemma axisFrequency_injective {d : ℕ} : Function.Injective (@axisFrequency d) := by
  intro i j h
  by_contra hij
  have hh := congrFun h i
  simp [axisFrequency, hij] at hh

lemma neg_axisFrequency_ne_axisFrequency {d : ℕ} (i j : Fin d) :
    -axisFrequency i ≠ axisFrequency j := by
  intro h
  have hh := congrFun h i
  by_cases hij : i = j <;> simp [axisFrequency, hij] at hh

/-- Add a finite collection of actual first-shell L² modes to a higher-mode potential. -/
def addFirstShell {d : ℕ} (w : TorusL2 d) (t : Fin d → ℝ) (s : Finset (Fin d)) : TorusL2 d :=
  w + ∑ i ∈ s, firstShellLp i (t i)

lemma addFirstShell_empty {d : ℕ} (w : TorusL2 d) (t : Fin d → ℝ) :
    addFirstShell w t ∅ = w := by simp [addFirstShell]

lemma addFirstShell_insert {d : ℕ} (w : TorusL2 d) (t : Fin d → ℝ)
    (s : Finset (Fin d)) (i : Fin d) (hi : i ∉ s) :
    addFirstShell w t (insert i s) = perturb (addFirstShell w t s) (axisFrequency i) (t i : ℂ) 1 := by
  classical
  simp [addFirstShell, Finset.sum_insert hi, perturb, firstShellLp, add_comm, add_left_comm]

lemma addFirstShell_admissible {d : ℕ} (w : TorusL2 d) (hw : Admissible w)
    (t : Fin d → ℝ) (s : Finset (Fin d)) : Admissible (addFirstShell w t s) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [addFirstShell_empty] using hw
  | @insert i s hi ih =>
    rw [addFirstShell_insert w t s i hi]
    exact perturb_admissible ih (axisFrequency_ne_zero i) _ _

lemma firstShellLp_axis_coefficient {d : ℕ} (i j : Fin d) (t : ℝ) :
    fourierIsometry d (firstShellLp j t) (axisFrequency i) = if i = j then (t : ℂ) else 0 := by
  classical
  rw [firstShellLp, fourier_mode]
  simp only [lp.coeFn_add, Pi.add_apply, lp.single_apply]
  have hneq : axisFrequency i ≠ -axisFrequency j := (neg_axisFrequency_ne_axisFrequency j i).symm
  simp only [Pi.single_eq_of_ne hneq, add_zero]
  by_cases hij : i = j
  · subst j
    simp
  · rw [Pi.single_eq_of_ne (fun he => hij (axisFrequency_injective he)), if_neg hij]

lemma addFirstShell_new_coefficient (w : TorusL2 12) (hh : HasOnlyHigherModes w)
    (t : Fin 12 → ℝ) (s : Finset (Fin 12)) (i : Fin 12) (hi : i ∉ s) :
    fourierIsometry 12 (addFirstShell w t s) (axisFrequency i) = 0 := by
  classical
  have hlow : localRadiusSq (axisFrequency i) ≤ 1 := by
    simp [localRadiusSq, axisFrequency]
  unfold addFirstShell
  rw [map_add, map_sum]
  simp only [lp.coeFn_add, Pi.add_apply, lp.coeFn_sum, hh _ hlow]
  rw [zero_add, Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro j hj
  rw [firstShellLp_axis_coefficient, if_neg (by intro he; subst j; exact hi hj)]

lemma addFirstShell_energy (w : TorusL2 12) (hw : Admissible w) (hh : HasOnlyHigherModes w)
    (t : Fin 12 → ℝ) (s : Finset (Fin 12)) :
    criticalEnergy (addFirstShell w t s) = criticalEnergy w + 2 * ∑ i ∈ s, t i ^ 2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [addFirstShell_empty]
  | @insert i s hi ih =>
    rw [addFirstShell_insert w t s i hi,
      energy_perturb (addFirstShell_admissible w hw t s) (axisFrequency_ne_zero i),
      addFirstShell_new_coefficient w hh t s i hi, frequencyRadius_axisFrequency, ih]
    simp [Finset.sum_insert hi, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    ring

lemma addFirstShell_coe {d : ℕ} (w : TorusL2 d) (t : Fin d → ℝ) (s : Finset (Fin d)) :
    (fun x => (addFirstShell w t s x).re) =ᵐ[torusMeasure d]
      (fun x => (w x).re + ∑ i ∈ s, 2 * t i * circleCosine (x i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [addFirstShell_empty]
  | @insert i s hi ih =>
    have he : addFirstShell w t (insert i s) = addFirstShell w t s + firstShellLp i (t i) := by
      simp [addFirstShell, Finset.sum_insert hi, add_comm, add_left_comm]
    rw [he]
    filter_upwards [Lp.coeFn_add (addFirstShell w t s) (firstShellLp i (t i)),
      ih, firstShellLp_coe i (t i)] with x hx h1 h2
    rw [hx, Pi.add_apply, Complex.add_re, h1, h2, Finset.sum_insert hi]
    ring

lemma addFirstShell_partition (w : TorusL2 12) (t : Fin 12 → ℝ) :
    partition (addFirstShell w t Finset.univ) =
      ∫ x, Real.exp (firstShellPotential t x + (w x).re) ∂torusMeasure 12 := by
  unfold partition
  apply integral_congr_ae
  filter_upwards [addFirstShell_coe w t Finset.univ] with x hx
  rw [hx]
  congr 1
  unfold firstShellPotential
  ring

lemma localSplitPressure_eq_functional (w : TorusL2 12) (hw : Admissible w)
    (hh : HasOnlyHigherModes w) (t : Fin 12 → ℝ) :
    localSplitPressure t w = functional (1 / 2) (addFirstShell w t Finset.univ) := by
  rw [functional, addFirstShell_partition, addFirstShell_energy w hw hh]
  unfold localSplitPressure
  ring

lemma spectral_dual_eq_raw {d : ℕ} (hd : 0 < d) (u : Torus d → ℝ) :
    dualFunctional (spectralThreshold d) u = RawAttainment.rawFunctional (spectralCoefficient d) u := by
  rw [RawAttainment.dualFunctional_eq_raw]
  congr 1
  have hs : spectralThreshold d ≠ 0 := (Legacy.TorusEndpoint.endpointSigma_pos hd).ne'
  unfold spectralCoefficient
  field_simp

/-- The trusted dual functional is strictly negative for every nonzero local
first-shell/higher-mode potential satisfying the explicit d=12 exit bounds. -/
theorem local_dualFunctional_lt_zero (t : Fin 12 → ℝ)
    (ht : ∀ i, 0 ≤ t i) (hta : ∀ i, t i ≤ 1 / 14)
    (w : TorusL2 12) (hw : Admissible w) (hh : HasOnlyHigherModes w)
    (hbound : ∀ᵐ x ∂torusMeasure 12, |(w x).re| ≤ (1 / 30 : ℝ))
    (hne : t ≠ 0 ∨ w ≠ 0) :
    dualFunctional (spectralThreshold 12)
      (RawAttainment.realValue (addFirstShell w t Finset.univ)) < 0 := by
  rw [spectral_dual_eq_raw (by norm_num), RawAttainment.rawFunctional_realValue (by norm_num)
    _ _ (addFirstShell_admissible w hw t Finset.univ)]
  have he : spectralCoefficient 12 * (2 * Real.pi) ^ 12 = (1 / 2 : ℝ) := by
    unfold spectralCoefficient
    field_simp
  rw [he, ← localSplitPressure_eq_functional w hw hh t]
  exact_mod_cast localSplitPressure_lt_zero t ht hta w hw.2 hh hbound hne

#print axioms local_dualFunctional_lt_zero
end BecknerOnofri.HighDim
