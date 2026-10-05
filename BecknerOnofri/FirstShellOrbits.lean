import BecknerOnofri.PermutationSymmetry
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-! Actual torus translations remove every complex first-shell phase.
The translation orbits are precisely the coordinatewise modulus level sets. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped ComplexConjugate
namespace BecknerOnofri.HighDim.ContinuousSymmetry
open ContinuousGibbs ContinuousFirstShell

/-- A concrete torus translation built from the arguments of the complex modes. -/
def phaseNormalizer {d : ℕ} (z : Coordinates d) : Torus d :=
  fun i => (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm
    (Circle.exp ((z i).arg))

theorem phaseNormalizer_toCircle {d : ℕ} (z : Coordinates d) (i : Fin d) :
    AddCircle.toCircle (phaseNormalizer z i) = Circle.exp ((z i).arg) := by
  rw [← AddCircle.homeomorphCircle_apply one_ne_zero]
  exact (AddCircle.homeomorphCircle one_ne_zero).apply_symm_apply _

/-- The normalization also works at zero coordinates, with no nonvanishing hypothesis. -/
theorem phaseNormalizer_spec {d : ℕ} (z : Coordinates d) :
    phaseCoordinates (phaseNormalizer z) z = fun i => (‖z i‖ : ℂ) := by
  funext i
  rw [phaseCoordinates_apply, UnitAddTorus.mFourier_neg, mFourier_axisFrequency,
    fourier_one, phaseNormalizer_toCircle, ← Circle.coe_inv_eq_conj, Circle.coe_inv]
  have hpolar : (‖z i‖ : ℂ) * (Circle.exp ((z i).arg) : ℂ) = z i :=
    Complex.norm_mul_exp_arg_mul_I (z i)
  have hc : (Circle.exp ((z i).arg) : ℂ) ≠ 0 := (Circle.exp ((z i).arg)).coe_ne_zero
  calc
    _ = (Circle.exp ((z i).arg) : ℂ)⁻¹ *
        ((‖z i‖ : ℂ) * (Circle.exp ((z i).arg) : ℂ)) := by rw [hpolar]
    _ = _ := by field_simp

/-- Every full complex first-shell vector has a nonnegative real amplitude representative. -/
theorem exists_phase_nonnegative {d : ℕ} (z : Coordinates d) :
    ∃ a : Torus d, phaseCoordinates a z = fun i => (‖z i‖ : ℂ) :=
  ⟨phaseNormalizer z, phaseNormalizer_spec z⟩

@[simp] theorem phase_coordinate_norm {d : ℕ} (a : Torus d) (z : Coordinates d) (i : Fin d) :
    ‖phaseCoordinates a z i‖ = ‖z i‖ := by
  rw [phaseCoordinates_apply, norm_mul, mFourier_norm_apply, one_mul]

/-- Equality of every coordinate modulus exactly characterizes actual translation orbits. -/
theorem phase_orbit_iff {d : ℕ} (z w : Coordinates d) :
    (∃ a : Torus d, phaseCoordinates a z = w) ↔ ∀ i, ‖z i‖ = ‖w i‖ := by
  constructor
  · rintro ⟨a, rfl⟩ i
    exact (phase_coordinate_norm a z i).symm
  · intro h
    refine ⟨phaseNormalizer z - phaseNormalizer w, ?_⟩
    have hn : (fun i => (‖z i‖ : ℂ)) = (fun i => (‖w i‖ : ℂ)) := by
      funext i
      rw [h i]
    rw [sub_eq_add_neg, ← phaseCoordinates_add, phaseNormalizer_spec, hn,
      ← phaseNormalizer_spec w, phaseCoordinates_add, add_neg_cancel, phaseCoordinates_zero]

/-- The coordinate character is faithful on the unit-period circle. -/
theorem axis_phase_eq_one_iff {d : ℕ} (a : Torus d) (i : Fin d) :
    UnitAddTorus.mFourier (-axisFrequency i) a = 1 ↔ a i = 0 := by
  rw [UnitAddTorus.mFourier_neg, mFourier_axisFrequency, fourier_one]
  constructor
  · intro h
    have hc : (AddCircle.toCircle (a i) : ℂ) = 1 := by
      simpa using congrArg conj h
    apply AddCircle.injective_toCircle one_ne_zero
    apply Subtype.ext
    simpa using hc
  · intro h
    simp [h]

/-- Active coordinates force their translating component to vanish; inactive
coordinates have the full circle as stabilizer. -/
theorem phase_stabilizer_iff {d : ℕ} (a : Torus d) (z : Coordinates d) :
    phaseCoordinates a z = z ↔ ∀ i, z i ≠ 0 → a i = 0 := by
  constructor
  · intro h i hi
    have he := congrFun h i
    change UnitAddTorus.mFourier (-axisFrequency i) a * z i = z i at he
    have hp : UnitAddTorus.mFourier (-axisFrequency i) a = 1 :=
      (mul_right_cancel₀ hi) (he.trans (one_mul _).symm)
    exact (axis_phase_eq_one_iff a i).mp hp
  · intro h
    funext i
    by_cases hi : z i = 0
    · simp [phaseCoordinates_apply, hi]
    · rw [phaseCoordinates_apply, (axis_phase_eq_one_iff a i).mpr (h i hi), one_mul]

/-- Full support gives a trivial translation stabilizer. -/
theorem phase_stabilizer_trivial_of_full_support {d : ℕ} (z : Coordinates d)
    (hz : ∀ i, z i ≠ 0) (a : Torus d) : phaseCoordinates a z = z ↔ a = 0 := by
  rw [phase_stabilizer_iff]
  constructor
  · intro h
    funext i
    exact h i (hz i)
  · rintro rfl i _
    rfl

/-- A half-period shift in just one coordinate. -/
def halfTranslation {d : ℕ} (i : Fin d) : Torus d :=
  Pi.single i (((1/2 : ℝ) : UnitAddCircle))

theorem fourier_one_half : fourier (1 : ℤ) (((1/2 : ℝ) : UnitAddCircle)) = -1 := by
  simpa using (fourier_add_half_inv_index (T := (1:ℝ)) (n := 1)
    (by norm_num) (by norm_num) (0 : UnitAddCircle))

theorem phase_halfTranslation {d : ℕ} (i j : Fin d) (z : Coordinates d) :
    phaseCoordinates (halfTranslation i) z j = if j = i then -z j else z j := by
  classical
  rw [phaseCoordinates_apply, UnitAddTorus.mFourier_neg, mFourier_axisFrequency]
  by_cases hij : j = i
  · subst j
    simp only [halfTranslation, Pi.single_eq_same, fourier_one_half,
      map_neg, map_one, neg_one_mul, ite_true]
  · have he : halfTranslation i j = 0 := by simp [halfTranslation, hij]
    rw [he]
    simp [hij]

/-- A universal half-period translation flips every complex first-shell coordinate. -/
def allHalfTranslation (d : ℕ) : Torus d := fun _ => (((1/2 : ℝ) : UnitAddCircle))

theorem phase_allHalfTranslation {d : ℕ} (z : Coordinates d) :
    phaseCoordinates (allHalfTranslation d) z = -z := by
  funext i
  rw [phaseCoordinates_apply, UnitAddTorus.mFourier_neg, mFourier_axisFrequency]
  change conj (fourier 1 (((1/2 : ℝ) : UnitAddCircle))) * z i = -z i
  rw [fourier_one_half]
  simp

theorem halfTranslation_fixes_of_zero {d : ℕ} (i : Fin d) (z : Coordinates d) (hi : z i = 0) :
    phaseCoordinates (halfTranslation i) z = z := by
  classical
  funext j
  rw [phase_halfTranslation]
  by_cases hij : j = i <;> simp [hij, hi]

/-- Any vector fixed by the entire stabilizer of z vanishes on z's inactive coordinates. -/
theorem zero_coordinate_of_stabilizer {d : ℕ} (z w : Coordinates d)
    (h : ∀ a : Torus d, phaseCoordinates a z = z → phaseCoordinates a w = w)
    (i : Fin d) (hi : z i = 0) : w i = 0 := by
  classical
  have he := congrFun (h (halfTranslation i) (halfTranslation_fixes_of_zero i z hi)) i
  rw [phase_halfTranslation, if_pos rfl] at he
  have htwo : (2 : ℂ) * w i = 0 := by linear_combination -he
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

open scoped Topology
open ReducedEquation

/-- The exact reduced equation vanishes in every inactive complex coordinate. -/
theorem reduced_zero_on_inactive {d : ℕ} (hd : 12 ≤ d) :
    ∀ᶠ x in 𝓝 (1, (0 : Coordinates d)), ∀ i, x.2 i = 0 → reduced hd x i = 0 := by
  filter_upwards [reduced_translation hd] with x hx
  intro i hi
  apply zero_coordinate_of_stabilizer x.2 (reduced hd x) _ i hi
  intro a ha
  have h := hx a
  rw [ha, Prod.eta] at h
  exact h.symm

/-- Restriction to nonnegative amplitudes retains exactly the actual reduced zero set. -/
theorem reduced_nonnegative_zero_iff {d : ℕ} (hd : 12 ≤ d) :
    ∀ᶠ x in 𝓝 (1, (0 : Coordinates d)),
      reduced hd (x.1, fun i => (‖x.2 i‖ : ℂ)) = 0 ↔ reduced hd x = 0 := by
  filter_upwards [reduced_zero_translation_iff hd] with x hx
  simpa only [phaseNormalizer_spec] using hx (phaseNormalizer x.2)

/-- Simultaneous sign reversal makes the actual reduced vector field odd. -/
theorem reduced_neg {d : ℕ} (hd : 12 ≤ d) :
    ∀ᶠ x in 𝓝 (1, (0 : Coordinates d)), reduced hd (x.1, -x.2) = -reduced hd x := by
  filter_upwards [reduced_translation hd] with x hx
  simpa only [phase_allHalfTranslation] using hx (allHalfTranslation d)

/-- The same half-period translation identifies the actual two graph potentials. -/
theorem potential_neg {d : ℕ} (hd : 12 ≤ d) :
    ∀ᶠ x in 𝓝 (1, (0 : Coordinates d)),
      potential hd (x.1, -x.2) = translation (allHalfTranslation d) (potential hd x) := by
  filter_upwards [potential_translation hd] with x hx
  simpa only [phase_allHalfTranslation] using hx (allHalfTranslation d)

#print axioms reduced_zero_on_inactive

#print axioms exists_phase_nonnegative
#print axioms phase_orbit_iff
#print axioms phase_stabilizer_iff
end BecknerOnofri.HighDim.ContinuousSymmetry
