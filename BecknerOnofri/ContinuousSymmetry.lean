module

public import BecknerOnofri.Translation
public import BecknerOnofri.ContinuousComplement

@[expose] public section

/-! Translation on the actual continuous torus Banach space and its full first shell. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators ComplexConjugate
namespace BecknerOnofri.HighDim.ContinuousSymmetry
open ContinuousGibbs ContinuousFirstShell

private def translateContinuous {d : ℕ} (a : Torus d) (u : Space d) : Space d :=
  ⟨fun x => u (x-a), u.continuous.comp (continuous_id.sub continuous_const)⟩

private theorem translateContinuous_norm_le {d : ℕ} (a : Torus d) (u : Space d) :
    ‖translateContinuous a u‖ ≤ ‖u‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg u)).mpr
  intro x
  exact u.norm_coe_le_norm (x-a)

/-- Pullback by x ↦ x-a is a real linear isometric equivalence of C(Tᵈ). -/
def translation {d : ℕ} (a : Torus d) : Space d ≃ₗᵢ[ℝ] Space d where
  toFun := translateContinuous a
  invFun := translateContinuous (-a)
  left_inv u := by ext x; simp [translateContinuous]
  right_inv u := by ext x; simp [translateContinuous]
  map_add' u v := by ext x; rfl
  map_smul' c u := by ext x; rfl
  norm_map' u := by
    apply le_antisymm (translateContinuous_norm_le a u)
    have h := translateContinuous_norm_le (-a) (translateContinuous a u)
    have he : translateContinuous (-a) (translateContinuous a u) = u := by
      ext x
      simp [translateContinuous]
    rwa [he] at h

@[simp] theorem translation_apply {d : ℕ} (a : Torus d) (u : Space d) (x : Torus d) :
    translation a u x = u (x-a) := rfl

@[simp] theorem translation_zero {d : ℕ} (u : Space d) : translation (0 : Torus d) u = u := by
  ext x
  simp

theorem translation_add {d : ℕ} (a b : Torus d) (u : Space d) :
    translation b (translation a u) = translation (a+b) u := by
  ext x
  simp only [translation_apply]
  congr 1
  abel

@[simp] theorem translation_const {d : ℕ} (a : Torus d) (c : ℝ) :
    translation a (ContinuousMap.const (Torus d) c) = ContinuousMap.const (Torus d) c := by
  ext x
  rfl

@[simp] theorem translation_one {d : ℕ} (a : Torus d) : translation a (1 : Space d) = 1 := by
  ext x
  rfl

@[simp] theorem mean_translation {d : ℕ} (a : Torus d) (u : Space d) :
    mean d (translation a u) = mean d u := integral_translate u a

@[simp] theorem partition_translation {d : ℕ} (a : Torus d) (u : Space d) :
    partition (translation a u) = partition u := by
  simp only [partition, mean_apply, exponential_apply, translation_apply]
  exact integral_translate (fun x => Real.exp (u x)) a

theorem exponential_translation {d : ℕ} (a : Torus d) (u : Space d) :
    exponential (translation a u) = translation a (exponential u) := by
  ext x
  simp

/-- Gibbs normalization commutes with the actual Haar translation. -/
theorem normalized_translation {d : ℕ} (a : Torus d) (u : Space d) :
    normalized (translation a u) = translation a (normalized u) := by
  simp only [normalized, partition_translation, exponential_translation, map_smul]

theorem center_translation {d : ℕ} (a : Torus d) (u : Space d) :
    center d (translation a u) = translation a (center d u) := by
  ext x
  simp only [center_apply, translation_apply, mean_translation]

theorem nonlinearRemainder_translation {d : ℕ} (a : Torus d) (u : Space d) :
    nonlinearRemainder (translation a u) = translation a (nonlinearRemainder u) := by
  simp only [nonlinearRemainder, normalized_translation, center_translation, map_sub,
    translation_one]

/-- The exact phase is the negative-frequency character evaluated at the translation. -/
theorem coefficient_translation {d : ℕ} (a : Torus d) (u : Space d) (k : Frequency d) :
    coefficient k (translation a u) = UnitAddTorus.mFourier (-k) a * coefficient k u := by
  rw [coefficient_eq_fourierCoeff, coefficient_eq_fourierCoeff]
  exact fourierCoeff_translate u a k

private theorem mFourier_neg_argument {d : ℕ} (k : Frequency d) (a : Torus d) :
    UnitAddTorus.mFourier k (-a) = UnitAddTorus.mFourier (-k) a := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, Pi.neg_apply, fourier_apply,
    zsmul_neg, neg_zsmul]

private theorem mFourier_sub_argument {d : ℕ} (k : Frequency d) (x a : Torus d) :
    UnitAddTorus.mFourier k (x-a) =
      UnitAddTorus.mFourier k x * UnitAddTorus.mFourier (-k) a := by
  rw [sub_eq_add_neg, mFourier_add_argument, mFourier_neg_argument]

/-- Full complex coordinates rotate by their actual torus character phases. -/
def phaseCoordinates {d : ℕ} (a : Torus d) (z : Coordinates d) : Coordinates d :=
  fun i => UnitAddTorus.mFourier (-axisFrequency i) a * z i

@[simp] theorem phaseCoordinates_apply {d : ℕ} (a : Torus d) (z : Coordinates d) (i : Fin d) :
    phaseCoordinates a z i = UnitAddTorus.mFourier (-axisFrequency i) a * z i := rfl

theorem coordinates_translation {d : ℕ} (a : Torus d) (u : Space d) :
    coordinates d (translation a u) = phaseCoordinates a (coordinates d u) := by
  ext i
  exact coefficient_translation a u (axisFrequency i)

theorem translation_synthesis {d : ℕ} (a : Torus d) (k : Frequency d) (z : ℂ) :
    translation a (synthesis k z) = synthesis k (UnitAddTorus.mFourier (-k) a * z) := by
  ext x
  simp only [translation_apply, synthesis_apply, mFourier_sub_argument]
  congr 2
  ring

/-- Synthesis intertwines translation with all d complex phase rotations. -/
theorem translation_assembly {d : ℕ} (a : Torus d) (z : Coordinates d) :
    translation a (assembly d z) = assembly d (phaseCoordinates a z) := by
  simp only [assembly_apply, map_sum, translation_synthesis, phaseCoordinates_apply]

theorem projection_translation {d : ℕ} (a : Torus d) (u : Space d) :
    projection d (translation a u) = translation a (projection d u) := by
  rw [← assembly_coordinates, coordinates_translation, ← translation_assembly,
    assembly_coordinates]

theorem meanProjection_translation {d : ℕ} (a : Torus d) (u : Space d) :
    meanProjection d (translation a u) = translation a (meanProjection d u) := by
  simp only [meanProjection_apply, mean_translation, translation_const]

theorem complementProjection_translation {d : ℕ} (a : Torus d) (u : Space d) :
    complementProjection d (translation a u) = translation a (complementProjection d u) := by
  simp only [complementProjection_apply, meanProjection_translation, projection_translation, map_sub]

@[simp] theorem translation_mem_complement_iff {d : ℕ} (a : Torus d) (u : Space d) :
    translation a u ∈ complement d ↔ u ∈ complement d := by
  change (mean d (translation a u) = 0 ∧ projection d (translation a u) = 0) ↔ _
  rw [mean_translation, projection_translation, (translation a).map_eq_zero_iff]
  rfl

/-- Translation restricts to the actual closed Fourier complement. -/
def complementTranslation {d : ℕ} (a : Torus d) : complement d ≃ₗᵢ[ℝ] complement d where
  toFun u := ⟨translation a u, (translation_mem_complement_iff a u).mpr u.property⟩
  invFun u := ⟨translation (-a) u, (translation_mem_complement_iff (-a) u).mpr u.property⟩
  left_inv u := by apply Subtype.ext; ext x; simp
  right_inv u := by apply Subtype.ext; ext x; simp
  map_add' u v := by apply Subtype.ext; exact map_add (translation a) (u : Space d) (v : Space d)
  map_smul' c u := by apply Subtype.ext; exact map_smul (translation a) c (u : Space d)
  norm_map' u := (translation a).norm_map u

@[simp] theorem complementTranslation_coe {d : ℕ} (a : Torus d) (u : complement d) :
    (complementTranslation a u : Space d) = translation a (u : Space d) := rfl

theorem complementMap_translation {d : ℕ} (a : Torus d) (u : Space d) :
    complementMap d (translation a u) = complementTranslation a (complementMap d u) := by
  apply Subtype.ext
  exact complementProjection_translation a u

@[simp] theorem phaseCoordinates_zero {d : ℕ} (z : Coordinates d) :
    phaseCoordinates (0 : Torus d) z = z := by
  apply assembly_injective d
  rw [← translation_assembly, translation_zero]

theorem phaseCoordinates_add {d : ℕ} (a b : Torus d) (z : Coordinates d) :
    phaseCoordinates b (phaseCoordinates a z) = phaseCoordinates (a+b) z := by
  ext i
  simp only [phaseCoordinates_apply, mFourier_add_argument]
  ring

theorem phaseCoordinates_norm {d : ℕ} (a : Torus d) (z : Coordinates d) :
    ‖phaseCoordinates a z‖ = ‖z‖ := by
  have hn (i : Fin d) : ‖phaseCoordinates a z i‖₊ = ‖z i‖₊ := by
    apply NNReal.coe_injective
    simp only [coe_nnnorm, phaseCoordinates_apply, norm_mul, mFourier_norm_apply, one_mul]
  simp only [Pi.norm_def, hn]

/-- Character rotations preserve the full 2d-dimensional real coordinate norm. -/
def coordinateTranslation {d : ℕ} (a : Torus d) : Coordinates d ≃ₗᵢ[ℝ] Coordinates d where
  toFun := phaseCoordinates a
  invFun := phaseCoordinates (-a)
  left_inv z := by rw [phaseCoordinates_add, add_neg_cancel, phaseCoordinates_zero]
  right_inv z := by rw [phaseCoordinates_add, neg_add_cancel, phaseCoordinates_zero]
  map_add' z w := by ext i; simp [phaseCoordinates, mul_add]
  map_smul' c z := by ext i; simp [phaseCoordinates]; ring
  norm_map' := phaseCoordinates_norm a

@[simp] theorem coordinateTranslation_apply {d : ℕ} (a : Torus d) (z : Coordinates d) :
    coordinateTranslation a z = phaseCoordinates a z := rfl

open ContinuousComplement

theorem reconstruction_translation {d : ℕ} (a : Torus d)
    (z : Coordinates d) (w : complement d) :
    reconstruction d (phaseCoordinates a z, complementTranslation a w) =
      translation a (reconstruction d (z,w)) := by
  simp only [reconstruction_apply, ← translation_assembly, complementTranslation_coe, map_add]

/-- Covariance of the genuine projected equation for a commuting Green operator. -/
theorem projectedEquation_translation {d : ℕ} (a : Torus d)
    (G : Space d →L[ℝ] Space d)
    (hG : ∀ u, G (translation a u) = translation a (G u))
    (μ : ℝ) (z : Coordinates d) (w : complement d) :
    projectedEquation G ((μ, phaseCoordinates a z), complementTranslation a w) =
      complementTranslation a (projectedEquation G ((μ,z),w)) := by
  unfold projectedEquation
  rw [reconstruction_translation, normalized_translation]
  have he : translation a (normalized (reconstruction d (z,w))) - 1 =
      translation a (normalized (reconstruction d (z,w)) - 1) := by
    rw [map_sub, translation_one]
  rw [he, hG, complementMap_translation]
  simp only [map_sub, map_smul]

#print axioms normalized_translation
#print axioms translation_assembly
#print axioms complementMap_translation
end BecknerOnofri.HighDim.ContinuousSymmetry
