import BecknerOnofri.LocalSplitBridge
import Legacy.BecknerOnofri.WienerRepresentative

/-! The local exit criterion stated directly using the Fourier coefficients of an
actual real Sobolev potential. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace BecknerOnofri.HighDim
open Legacy.BecknerOnofri.TorusSobolev
open Legacy.BecknerOnofri.SubcriticalAttainment
open Legacy.BecknerOnofri.SubcriticalEuler
open Legacy.BecknerOnofri.WienerFourier

lemma low_radiusSq_classification {d : ℕ} (k : Frequency d) (hk : localRadiusSq k ≤ 1) :
    k = 0 ∨ ∃ i : Fin d, k = axisFrequency i ∨ k = -axisFrequency i := by
  classical
  by_cases hz : k = 0
  · exact Or.inl hz
  right
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hz
  have hsum : (∑ j : Fin d, (k j) ^ 2 : ℤ) ≤ 1 := by
    unfold localRadiusSq at hk
    exact_mod_cast hk
  have hi0 : k i ≠ 0 := hi
  have hi1 : (k i) ^ 2 = 1 := by
    have hh := (Finset.single_le_sum (s := Finset.univ) (f := fun j : Fin d => (k j) ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)).trans hsum
    have hp : (0 : ℤ) < (k i) ^ 2 := sq_pos_of_ne_zero hi0
    omega
  have hrest (j : Fin d) (hji : j ≠ i) : k j = 0 := by
    have he := Finset.sum_erase_add (s := Finset.univ) (f := fun j : Fin d => (k j) ^ 2)
      (Finset.mem_univ i)
    have hj := Finset.single_le_sum (s := Finset.univ.erase i) (f := fun j : Fin d => (k j) ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩)
    have hjzero : (k j) ^ 2 = 0 := by nlinarith [sq_nonneg (k j)]
    exact (sq_eq_zero_iff).mp hjzero
  refine ⟨i, ?_⟩
  rcases sq_eq_one_iff.mp hi1 with hi | hi
  · left
    ext j
    by_cases hji : j = i <;> simp [axisFrequency, hji, hi, hrest]
  · right
    ext j
    by_cases hji : j = i <;> simp [axisFrequency, hji, hi, hrest]

lemma firstShellLp_fourier_higher (i : Fin 12) (t : ℝ) (k : HigherFrequency 12) :
    fourierIsometry 12 (firstShellLp i t) k.val = 0 := by
  classical
  have hp : k.val ≠ axisFrequency i := by
    intro he
    have h := k.property
    simp [he, localRadiusSq, axisFrequency] at h
  have hn : k.val ≠ -axisFrequency i := by
    intro he
    have h := k.property
    simp [he, localRadiusSq, axisFrequency] at h
  rw [firstShellLp, fourier_mode]
  simp [lp.single_apply, Pi.single_eq_of_ne hp, Pi.single_eq_of_ne hn]

lemma addFirstShell_fourier_higher (u : TorusL2 12) (t : Fin 12 → ℝ) (s : Finset (Fin 12))
    (k : HigherFrequency 12) :
    fourierIsometry 12 (addFirstShell u t s) k.val = fourierIsometry 12 u k.val := by
  unfold addFirstShell
  rw [map_add, map_sum]
  simp only [lp.coeFn_add, Pi.add_apply, lp.coeFn_sum, Finset.sum_apply,
    firstShellLp_fourier_higher, Finset.sum_const_zero, add_zero]

lemma addFirstShell_axis_coefficient (u : TorusL2 12) (t : Fin 12 → ℝ) (i : Fin 12) :
    fourierIsometry 12 (addFirstShell u t Finset.univ) (axisFrequency i) =
      fourierIsometry 12 u (axisFrequency i) + (t i : ℂ) := by
  unfold addFirstShell
  rw [map_add, map_sum]
  simp only [lp.coeFn_add, Pi.add_apply, lp.coeFn_sum, Finset.sum_apply,
    firstShellLp_axis_coefficient]
  simp

lemma firstShellLp_neg {d : ℕ} (i : Fin d) (t : ℝ) :
    firstShellLp i (-t) = -firstShellLp i t := by
  simp [firstShellLp, mode, neg_smul, add_comm]

lemma addFirstShell_cancel (u : TorusL2 12) (t : Fin 12 → ℝ) :
    addFirstShell (addFirstShell u (-t) Finset.univ) t Finset.univ = u := by
  unfold addFirstShell
  simp only [Pi.neg_apply, firstShellLp_neg, Finset.sum_neg_distrib]
  abel

lemma removeFirstShell_higher (u : TorusL2 12) (hu : Admissible u) (t : Fin 12 → ℝ)
    (ht : ∀ i, fourierIsometry 12 u (axisFrequency i) = (t i : ℂ)) :
    HasOnlyHigherModes (addFirstShell u (-t) Finset.univ) := by
  have hadm := addFirstShell_admissible u hu (-t) Finset.univ
  intro k hk
  rcases low_radiusSq_classification k hk with rfl | ⟨i, hi | hi⟩
  · exact hadm.2.1
  · rw [hi, addFirstShell_axis_coefficient, ht]
    simp
  · rw [hi, fourier_real_symmetry hadm.1, addFirstShell_axis_coefficient, ht]
    simp

lemma higher_fourier_sum_bounds_function (w : TorusL2 12) (hh : HasOnlyHigherModes w)
    (hs : Summable (fun k : HigherFrequency 12 => ‖fourierIsometry 12 w k.val‖))
    (hb : (∑' k : HigherFrequency 12, ‖fourierIsometry 12 w k.val‖) ≤ (1 / 30 : ℝ)) :
    ∀ᵐ x ∂torusMeasure 12, |(w x).re| ≤ (1 / 30 : ℝ) := by
  have hsupp : Function.support (fun k : Frequency 12 => ‖fourierIsometry 12 w k‖) ⊆
      {k : Frequency 12 | 1 < localRadiusSq k} := by
    intro k hk
    by_contra hlow
    have hc := hh k (le_of_not_gt hlow)
    simp [hc] at hk
  have hall := (hasSum_subtype_iff_of_support_subset hsupp).mp hs.hasSum
  have hae := representative_ae_eq w hall.summable
  filter_upwards [hae] with x hx
  have hnormsum : Summable (fun k : Frequency 12 =>
      ‖fourierIsometry 12 w k * UnitAddTorus.mFourier k x‖) := by
    simpa only [norm_mul, Legacy.TorusEndpoint.mFourier_norm_apply, mul_one] using hall.summable
  calc
    |(w x).re| ≤ ‖w x‖ := Complex.abs_re_le_norm _
    _ = ‖representative w x‖ := by rw [hx]
    _ ≤ ∑' k : Frequency 12, ‖fourierIsometry 12 w k * UnitAddTorus.mFourier k x‖ :=
      norm_tsum_le_tsum_norm hnormsum
    _ = ∑' k : HigherFrequency 12, ‖fourierIsometry 12 w k.val‖ := by
      simp only [norm_mul, Legacy.TorusEndpoint.mFourier_norm_apply, mul_one]
      exact hall.tsum_eq
    _ ≤ _ := hb

/-- Explicit local negativity, with the original potential's actual Fourier
coefficients as hypotheses. Absolute summability is needed only on its higher shell. -/
theorem local_fourier_exit (u : TorusL2 12) (hu : Admissible u) (t : Fin 12 → ℝ)
    (htcoeff : ∀ i, fourierIsometry 12 u (axisFrequency i) = (t i : ℂ))
    (ht : ∀ i, 0 ≤ t i) (hta : ∀ i, t i ≤ 1 / 14)
    (hs : Summable (fun k : HigherFrequency 12 => ‖fourierIsometry 12 u k.val‖))
    (hb : (∑' k : HigherFrequency 12, ‖fourierIsometry 12 u k.val‖) ≤ (1 / 30 : ℝ))
    (hne : u ≠ 0) :
    dualFunctional (spectralThreshold 12) (RawAttainment.realValue u) < 0 := by
  let w := addFirstShell u (-t) Finset.univ
  have hw : Admissible w := addFirstShell_admissible u hu (-t) Finset.univ
  have hh : HasOnlyHigherModes w := removeFirstShell_higher u hu t htcoeff
  have hs' : Summable (fun k : HigherFrequency 12 => ‖fourierIsometry 12 w k.val‖) := by
    simpa only [w, addFirstShell_fourier_higher] using hs
  have hb' : (∑' k : HigherFrequency 12, ‖fourierIsometry 12 w k.val‖) ≤ (1 / 30 : ℝ) := by
    simpa only [w, addFirstShell_fourier_higher] using hb
  have hn : t ≠ 0 ∨ w ≠ 0 := by
    by_contra h
    push Not at h
    have he := addFirstShell_cancel u t
    change addFirstShell w t Finset.univ = u at he
    rw [h.1, h.2] at he
    simp [addFirstShell, firstShellLp, mode] at he
    exact hne he.symm
  have h := local_dualFunctional_lt_zero t ht hta w hw hh
    (higher_fourier_sum_bounds_function w hh hs' hb') hn
  simpa only [w, addFirstShell_cancel] using h

#print axioms local_fourier_exit
end BecknerOnofri.HighDim
