module

public import BecknerOnofri.LocalElevenContinuousInverse
public import BecknerOnofri.QuarticSignsEleven
public import BecknerOnofri.ReflectionSymmetry
public import BecknerOnofri.LocalElevenCore.PermutationSymmetry

@[expose] public section

/-! Spatial inversion and complex conjugation symmetry of the actual torus
Gibbs map and its uniquely constructed complementary graph. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Filter
open scoped BigOperators Topology ComplexConjugate
namespace BecknerOnofri.HighDim.LocalEleven.ContinuousSymmetry

open BecknerOnofri.HighDim.ContinuousSymmetry hiding center_permutation coefficient_permutation coefficient_reflection complementMap_permutation complementMap_reflection complementPermutation complementPermutation_coe complementProjection_permutation complementProjection_reflection complementReflection complementReflection_coe conjugateCoordinates conjugateCoordinates_apply conjugateCoordinates_norm coordinatePermutation coordinatePermutation_apply coordinates_permutation coordinates_reflection correction_permutation correction_reflection correction_translation exponential_permutation exponential_reflection firstShell_permutation_iff frequencyLength_permutation frequencyPermutation frequencyPermutation_axis frequencyPermutation_eq_zero_iff frequencyPermutation_neg full_translation green_permutation green_reflection green_translation integral_pointPermutation latticeSquare_permutation meanProjection_permutation meanProjection_reflection mean_permutation mean_reflection nonlinearRemainder_permutation normalized_permutation normalized_reflection partition_permutation partition_reflection permutation permutation_apply permutation_assembly permutation_const permutation_mem_complement_iff permutation_one permuteCoordinates permuteCoordinates_norm pointPermutation pointPermutation_apply pointPermutation_continuous pointPermutation_isometry pointPermutation_measurePreserving potential_permutation potential_reflection potential_translation projectedEquation_permutation projectedEquation_reflection projection_permutation projection_reflection reconstructed_correction_translation reconstruction_permutation reconstruction_reflection reduced_permutation reduced_reflection reduced_translation reduced_zero_permutation_iff reduced_zero_translation_iff reflection reflection_apply reflection_assembly reflection_const reflection_involutive reflection_mem_complement_iff reflection_one reflection_synthesis
open BecknerOnofri.HighDim.GreenLocalBranch hiding correction correction_analytic correction_axis correction_base correction_derivative_zero correction_quadratic correction_solves correction_unique exists_analytic_complement green_assembly green_first_complement_zero linearPart_eq zero_axis_of_unique
open BecknerOnofri.HighDim.ReducedEquation hiding complementMap_assembly complementMap_reconstruction coordinates_complement coordinates_green coordinates_one coordinates_reconstruction full full_complement full_coordinates full_mean full_zero_iff graph_full_iff_reduced local_full_iff_reduced meanZero_zero_iff mean_green potential potential_analytic reduced reduced_analytic
open ContinuousGibbs ContinuousFirstShell ContinuousComplement GreenLocalBranch ReducedEquation

local instance : (AddCircle.haarAddCircle (T := 1)).IsNegInvariant := by
  have h : AddCircle.haarAddCircle (T := 1) = (volume : Measure UnitAddCircle) := by
    simpa using (AddCircle.volume_eq_smul_haarAddCircle (T := 1)).symm
  rw [h]
  infer_instance
local instance (d : ℕ) : (torusMeasure d).IsNegInvariant := by
  unfold torusMeasure
  infer_instance

def reflectContinuous {d : ℕ} (u : Space d) : Space d :=
  ⟨fun x => u (-x), u.continuous.comp continuous_neg⟩

theorem reflectContinuous_norm_le {d : ℕ} (u : Space d) :
    ‖reflectContinuous u‖ ≤ ‖u‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg u)).mpr
  intro x
  exact u.norm_coe_le_norm (-x)

/-- Pullback by inversion of the actual torus. -/
def reflection (d : ℕ) : Space d ≃ₗᵢ[ℝ] Space d where
  toFun := reflectContinuous
  invFun := reflectContinuous
  left_inv u := by ext x; simp [reflectContinuous]
  right_inv u := by ext x; simp [reflectContinuous]
  map_add' u v := by ext x; rfl
  map_smul' c u := by ext x; rfl
  norm_map' u := by
    apply le_antisymm (reflectContinuous_norm_le u)
    have hh := reflectContinuous_norm_le (reflectContinuous u)
    have he : reflectContinuous (reflectContinuous u) = u := by ext x; simp [reflectContinuous]
    rwa [he] at hh

@[simp] theorem reflection_apply {d : ℕ} (u : Space d) (x : Torus d) :
    reflection d u x = u (-x) := rfl

@[simp] theorem reflection_involutive {d : ℕ} (u : Space d) :
    reflection d (reflection d u) = u := by ext x; simp

@[simp] theorem reflection_const {d : ℕ} (c : ℝ) :
    reflection d (ContinuousMap.const (Torus d) c) = ContinuousMap.const (Torus d) c := by ext x; rfl

@[simp] theorem reflection_one (d : ℕ) : reflection d (1 : Space d) = 1 := by ext x; rfl

@[simp] theorem mean_reflection {d : ℕ} (u : Space d) : mean d (reflection d u) = mean d u :=
  integral_neg_eq_self u (torusMeasure d)

@[simp] theorem partition_reflection {d : ℕ} (u : Space d) : partition (reflection d u) = partition u := by
  simp only [partition, mean_apply, exponential_apply, reflection_apply]
  exact integral_neg_eq_self (fun x => Real.exp (u x)) (torusMeasure d)

theorem exponential_reflection {d : ℕ} (u : Space d) :
    exponential (reflection d u) = reflection d (exponential u) := by ext x; simp

theorem normalized_reflection {d : ℕ} (u : Space d) :
    normalized (reflection d u) = reflection d (normalized u) := by
  simp only [normalized, partition_reflection, exponential_reflection, map_smul]

theorem character_neg_argument {d : ℕ} (k : Frequency d) (x : Torus d) :
    UnitAddTorus.mFourier k (-x) = UnitAddTorus.mFourier (-k) x := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, Pi.neg_apply, fourier_apply,
    zsmul_neg, neg_zsmul]

/-- Exact transformation of each Haar Fourier coefficient. -/
theorem coefficient_reflection {d : ℕ} (u : Space d) (k : Frequency d) :
    coefficient k (reflection d u) = conj (coefficient k u) := by
  rw [← coefficient_neg, coefficient_integral, coefficient_integral]
  rw [← integral_neg_eq_self (fun x => UnitAddTorus.mFourier (-k) x * (reflection d u x : ℂ))]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by
    simp only [character_neg_argument, reflection_apply, neg_neg])

def conjugateCoordinates {d : ℕ} (z : Coordinates d) : Coordinates d := fun i => conj (z i)

@[simp] theorem conjugateCoordinates_apply {d : ℕ} (z : Coordinates d) (i : Fin d) :
    conjugateCoordinates z i = conj (z i) := rfl

theorem conjugateCoordinates_norm {d : ℕ} (z : Coordinates d) : ‖conjugateCoordinates z‖ = ‖z‖ := by
  have hn (i : Fin d) : ‖conjugateCoordinates z i‖₊ = ‖z i‖₊ := by
    apply NNReal.coe_injective
    simp only [coe_nnnorm, conjugateCoordinates_apply, Complex.norm_conj]
  simp only [Pi.norm_def, hn]

theorem coordinates_reflection {d : ℕ} (u : Space d) :
    coordinates d (reflection d u) = conjugateCoordinates (coordinates d u) := by
  ext i
  exact coefficient_reflection u (axisFrequency i)

theorem reflection_synthesis {d : ℕ} (k : Frequency d) (z : ℂ) :
    reflection d (synthesis k z) = synthesis k (conj z) := by
  ext x
  simp only [reflection_apply, synthesis_apply, character_neg_argument, UnitAddTorus.mFourier_neg,
    Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

theorem reflection_assembly {d : ℕ} (z : Coordinates d) :
    reflection d (assembly d z) = assembly d (conjugateCoordinates z) := by
  simp only [assembly_apply, map_sum, reflection_synthesis, conjugateCoordinates_apply]

theorem projection_reflection {d : ℕ} (u : Space d) :
    projection d (reflection d u) = reflection d (projection d u) := by
  rw [← assembly_coordinates, coordinates_reflection, ← reflection_assembly, assembly_coordinates]

theorem meanProjection_reflection {d : ℕ} (u : Space d) :
    meanProjection d (reflection d u) = reflection d (meanProjection d u) := by
  simp only [meanProjection_apply, mean_reflection, reflection_const]

theorem complementProjection_reflection {d : ℕ} (u : Space d) :
    complementProjection d (reflection d u) = reflection d (complementProjection d u) := by
  simp only [complementProjection_apply, meanProjection_reflection, projection_reflection, map_sub]

@[simp] theorem reflection_mem_complement_iff {d : ℕ} (u : Space d) :
    reflection d u ∈ complement d ↔ u ∈ complement d := by
  change (mean d (reflection d u) = 0 ∧ projection d (reflection d u) = 0) ↔ _
  rw [mean_reflection, projection_reflection, (reflection d).map_eq_zero_iff]
  rfl

def complementReflection (d : ℕ) : complement d ≃ₗᵢ[ℝ] complement d where
  toFun u := ⟨reflection d u, (reflection_mem_complement_iff (u : Space d)).mpr u.property⟩
  invFun u := ⟨reflection d u, (reflection_mem_complement_iff (u : Space d)).mpr u.property⟩
  left_inv u := by apply Subtype.ext; exact reflection_involutive (u : Space d)
  right_inv u := by apply Subtype.ext; exact reflection_involutive (u : Space d)
  map_add' u v := by apply Subtype.ext; exact map_add (reflection d) (u : Space d) (v : Space d)
  map_smul' c u := by apply Subtype.ext; exact map_smul (reflection d) c (u : Space d)
  norm_map' u := (reflection d).norm_map u

@[simp] theorem complementReflection_coe {d : ℕ} (u : complement d) :
    (complementReflection d u : Space d) = reflection d (u : Space d) := rfl

theorem complementMap_reflection {d : ℕ} (u : Space d) :
    complementMap d (reflection d u) = complementReflection d (complementMap d u) := by
  apply Subtype.ext
  exact complementProjection_reflection u

theorem green_reflection {d : ℕ} (hd : 0 < d) (u : Space d) :
    greenContinuous d (reflection d u) = reflection d (greenContinuous d u) := by
  apply coefficient_ext
  intro k
  simp only [coefficient_green hd, coefficient_reflection, map_mul, Complex.conj_ofReal]

theorem reconstruction_reflection {d : ℕ} (z : Coordinates d) (w : complement d) :
    reconstruction d (conjugateCoordinates z, complementReflection d w) =
      reflection d (reconstruction d (z,w)) := by
  simp only [reconstruction_apply, ← reflection_assembly, complementReflection_coe, map_add]

theorem projectedEquation_reflection {d : ℕ} (hd : 0 < d)
    (μ : ℝ) (z : Coordinates d) (w : complement d) :
    projectedEquation (greenContinuous d) ((μ,conjugateCoordinates z),complementReflection d w) =
      complementReflection d (projectedEquation (greenContinuous d) ((μ,z),w)) := by
  unfold projectedEquation
  rw [reconstruction_reflection, normalized_reflection]
  have he : reflection d (normalized (reconstruction d (z,w))) - 1 =
      reflection d (normalized (reconstruction d (z,w))-1) := by rw [map_sub, reflection_one]
  rw [he, green_reflection hd, complementMap_reflection]
  simp only [map_sub, map_smul]

theorem correction_reflection {d : ℕ} (hd : 11 ≤ d) :
    ∀ᶠ x in 𝓝 (1, (0 : Coordinates d)),
      correction hd (x.1,conjugateCoordinates x.2) = complementReflection d (correction hd x) := by
  obtain ⟨ε,hε,hUnique⟩ := Metric.eventually_nhds_iff.mp (correction_unique hd)
  have ht : Tendsto (fun x : ℝ × Coordinates d => (x,correction hd x))
      (𝓝 (1,(0 : Coordinates d))) (𝓝 ((1,(0 : Coordinates d)),(0 : complement d))) := by
    simpa only [correction_base, id_eq] using
      (continuousAt_id.prodMk (correction_analytic hd).continuousAt).tendsto
  have hn : ∀ᶠ x in 𝓝 (1,(0 : Coordinates d)),
      dist (x,correction hd x) ((1,(0 : Coordinates d)),(0 : complement d)) < ε :=
    ht.eventually (Metric.ball_mem_nhds _ hε)
  filter_upwards [correction_solves hd,hn] with x hx hnear
  have hr : dist ((x.1,conjugateCoordinates x.2),complementReflection d (correction hd x))
      ((1,(0 : Coordinates d)),(0 : complement d)) < ε := by
    simpa only [Prod.dist_eq, dist_zero_right, conjugateCoordinates_norm,
      (complementReflection d).norm_map] using hnear
  apply (hUnique hr).mp
  rw [projectedEquation_reflection (by omega)]
  change complementReflection d (projectedEquation (greenContinuous d) (x,correction hd x)) = 0
  rw [hx, map_zero]

theorem potential_reflection {d : ℕ} (hd : 11 ≤ d) :
    ∀ᶠ x in 𝓝 (1,(0 : Coordinates d)),
      potential hd (x.1,conjugateCoordinates x.2) = reflection d (potential hd x) := by
  filter_upwards [correction_reflection hd] with x hx
  simp only [potential, hx, reconstruction_reflection]

theorem reduced_reflection {d : ℕ} (hd : 11 ≤ d) :
    ∀ᶠ x in 𝓝 (1,(0 : Coordinates d)),
      reduced hd (x.1,conjugateCoordinates x.2) = conjugateCoordinates (reduced hd x) := by
  filter_upwards [potential_reflection hd] with x hx
  simp only [reduced, hx, normalized_reflection, coordinates_reflection]
  ext i
  simp only [Pi.sub_apply, Pi.smul_apply, conjugateCoordinates_apply, map_sub,
    Complex.real_smul, map_mul, Complex.conj_ofReal]

#print axioms coefficient_reflection
#print axioms reduced_reflection
end BecknerOnofri.HighDim.LocalEleven.ContinuousSymmetry
