module

public import BecknerOnofri.LocalElevenContinuousInverse
public import BecknerOnofri.PermutationSymmetry
public import BecknerOnofri.LocalElevenCore.ReducedSymmetry
public import Mathlib.MeasureTheory.Integral.Pi

@[expose] public section

/-! Coordinate permutation covariance of the actual torus Gibbs problem. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

open MeasureTheory
open scoped BigOperators Topology
namespace BecknerOnofri.HighDim.LocalEleven.ContinuousSymmetry

open BecknerOnofri.HighDim.ContinuousSymmetry hiding center_permutation coefficient_permutation complementMap_permutation complementPermutation complementPermutation_coe complementProjection_permutation coordinatePermutation coordinatePermutation_apply coordinates_permutation correction_permutation correction_translation exponential_permutation firstShell_permutation_iff frequencyLength_permutation frequencyPermutation frequencyPermutation_axis frequencyPermutation_eq_zero_iff frequencyPermutation_neg full_translation green_permutation green_translation integral_pointPermutation latticeSquare_permutation meanProjection_permutation mean_permutation nonlinearRemainder_permutation normalized_permutation partition_permutation permutation permutation_apply permutation_assembly permutation_const permutation_mem_complement_iff permutation_one permuteCoordinates permuteCoordinates_norm pointPermutation pointPermutation_apply pointPermutation_continuous pointPermutation_isometry pointPermutation_measurePreserving potential_permutation potential_translation projectedEquation_permutation projection_permutation reconstructed_correction_translation reconstruction_permutation reduced_permutation reduced_translation reduced_zero_permutation_iff reduced_zero_translation_iff
open BecknerOnofri.HighDim.GreenLocalBranch hiding correction correction_analytic correction_axis correction_base correction_derivative_zero correction_quadratic correction_solves correction_unique exists_analytic_complement green_assembly green_first_complement_zero linearPart_eq zero_axis_of_unique
open BecknerOnofri.HighDim.ReducedEquation hiding complementMap_assembly complementMap_reconstruction coordinates_complement coordinates_green coordinates_one coordinates_reconstruction full full_complement full_coordinates full_mean full_zero_iff graph_full_iff_reduced local_full_iff_reduced meanZero_zero_iff mean_green potential potential_analytic reduced reduced_analytic
open ContinuousGibbs ContinuousFirstShell ContinuousComplement GreenLocalBranch ReducedEquation

/-- Reindex the actual torus coordinates by the inverse permutation. -/
def pointPermutation {d : ℕ} (σ : Equiv.Perm (Fin d)) : Torus d ≃ᵐ Torus d :=
  MeasurableEquiv.piCongrLeft (fun _ : Fin d => UnitAddCircle) σ

@[simp] theorem pointPermutation_apply {d : ℕ} (σ : Equiv.Perm (Fin d)) (x : Torus d) (i : Fin d) :
    pointPermutation σ x i = x (σ.symm i) := by
  simp [pointPermutation, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]

theorem pointPermutation_isometry {d : ℕ} (σ : Equiv.Perm (Fin d)) :
    Isometry (pointPermutation σ : Torus d → Torus d) :=
  (IsometryEquiv.piCongrLeft (Y := fun _ : Fin d => UnitAddCircle) σ).isometry

theorem pointPermutation_continuous {d : ℕ} (σ : Equiv.Perm (Fin d)) :
    Continuous (pointPermutation σ : Torus d → Torus d) := by
  apply continuous_pi
  intro i
  simpa only [pointPermutation_apply] using continuous_apply (σ.symm i)

theorem pointPermutation_measurePreserving {d : ℕ} (σ : Equiv.Perm (Fin d)) :
    MeasurePreserving (pointPermutation σ) (torusMeasure d) (torusMeasure d) :=
  measurePreserving_piCongrLeft (fun _ : Fin d => AddCircle.haarAddCircle) σ

theorem integral_pointPermutation {d : ℕ} (σ : Equiv.Perm (Fin d))
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : Torus d → E) :
    (∫ x, f (pointPermutation σ x) ∂torusMeasure d) = ∫ x, f x ∂torusMeasure d :=
  (pointPermutation_measurePreserving σ).integral_comp' f

private def permuteContinuous {d : ℕ} (σ : Equiv.Perm (Fin d)) (u : Space d) : Space d :=
  ⟨fun x => u (pointPermutation σ x), u.continuous.comp (pointPermutation_continuous σ)⟩

private theorem permuteContinuous_norm_le {d : ℕ} (σ : Equiv.Perm (Fin d)) (u : Space d) :
    ‖permuteContinuous σ u‖ ≤ ‖u‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg u)).mpr
  intro x
  exact u.norm_coe_le_norm _

/-- Coordinate permutation is a real linear isometric equivalence of C(Tᵈ). -/
def permutation {d : ℕ} (σ : Equiv.Perm (Fin d)) : Space d ≃ₗᵢ[ℝ] Space d where
  toFun := permuteContinuous σ
  invFun := permuteContinuous σ.symm
  left_inv u := by
    ext x
    change u (pointPermutation σ (pointPermutation σ.symm x)) = u x
    congr 1
    ext i
    simp
  right_inv u := by
    ext x
    change u (pointPermutation σ.symm (pointPermutation σ x)) = u x
    congr 1
    ext i
    simp
  map_add' u v := by ext x; rfl
  map_smul' c u := by ext x; rfl
  norm_map' u := by
    apply le_antisymm (permuteContinuous_norm_le σ u)
    have h := permuteContinuous_norm_le σ.symm (permuteContinuous σ u)
    have he : permuteContinuous σ.symm (permuteContinuous σ u) = u := by
      ext x
      change u (pointPermutation σ (pointPermutation σ.symm x)) = u x
      congr 1
      ext i
      simp
    rwa [he] at h

@[simp] theorem permutation_apply {d : ℕ} (σ : Equiv.Perm (Fin d)) (u : Space d) (x : Torus d) :
    permutation σ u x = u (pointPermutation σ x) := rfl

@[simp] theorem permutation_const {d : ℕ} (σ : Equiv.Perm (Fin d)) (c : ℝ) :
    permutation σ (ContinuousMap.const (Torus d) c) = ContinuousMap.const (Torus d) c := by
  ext x
  rfl

@[simp] theorem permutation_one {d : ℕ} (σ : Equiv.Perm (Fin d)) :
    permutation σ (1 : Space d) = 1 := by ext x; rfl

@[simp] theorem mean_permutation {d : ℕ} (σ : Equiv.Perm (Fin d)) (u : Space d) :
    mean d (permutation σ u) = mean d u := integral_pointPermutation σ u

@[simp] theorem partition_permutation {d : ℕ} (σ : Equiv.Perm (Fin d)) (u : Space d) :
    partition (permutation σ u) = partition u := by
  simp only [partition, mean_apply, exponential_apply, permutation_apply]
  exact integral_pointPermutation σ (fun x => Real.exp (u x))

theorem exponential_permutation {d : ℕ} (σ : Equiv.Perm (Fin d)) (u : Space d) :
    exponential (permutation σ u) = permutation σ (exponential u) := by ext x; simp

theorem normalized_permutation {d : ℕ} (σ : Equiv.Perm (Fin d)) (u : Space d) :
    normalized (permutation σ u) = permutation σ (normalized u) := by
  simp only [normalized, partition_permutation, exponential_permutation, map_smul]

def frequencyPermutation {d : ℕ} (σ : Equiv.Perm (Fin d)) (k : Frequency d) : Frequency d :=
  fun i => k (σ.symm i)

@[simp] theorem frequencyPermutation_axis {d : ℕ} (σ : Equiv.Perm (Fin d)) (i : Fin d) :
    frequencyPermutation σ (axisFrequency i) = axisFrequency (σ i) := by
  ext j
  simp only [frequencyPermutation, axisFrequency]
  congr 1
  exact propext σ.symm_apply_eq

@[simp] theorem frequencyPermutation_neg {d : ℕ} (σ : Equiv.Perm (Fin d)) (k : Frequency d) :
    frequencyPermutation σ (-k) = -frequencyPermutation σ k := rfl

@[simp] theorem frequencyLength_permutation {d : ℕ} (σ : Equiv.Perm (Fin d)) (k : Frequency d) :
    frequencyLength (frequencyPermutation σ k) = frequencyLength k := by
  unfold frequencyLength frequencyPermutation
  exact congrArg Real.sqrt (Equiv.sum_comp σ.symm (fun i => (k i : ℝ)^2))

@[simp] theorem latticeSquare_permutation {d : ℕ} (σ : Equiv.Perm (Fin d)) (k : Frequency d) :
    latticeSquare (frequencyPermutation σ k) = latticeSquare k := by
  unfold latticeSquare frequencyPermutation
  exact Equiv.sum_comp σ.symm (fun i => (k i).natAbs^2)

@[simp] theorem frequencyPermutation_eq_zero_iff {d : ℕ} (σ : Equiv.Perm (Fin d)) (k : Frequency d) :
    frequencyPermutation σ k = 0 ↔ k = 0 := by
  rw [← latticeSquare_eq_zero_iff, latticeSquare_permutation, latticeSquare_eq_zero_iff]

@[simp] theorem firstShell_permutation_iff {d : ℕ} (σ : Equiv.Perm (Fin d)) (k : Frequency d) :
    InFirstShell (frequencyPermutation σ k) ↔ InFirstShell k := by
  rw [← latticeSquare_eq_one_iff, latticeSquare_permutation, latticeSquare_eq_one_iff]

private theorem mFourier_pointPermutation {d : ℕ} (σ : Equiv.Perm (Fin d))
    (k : Frequency d) (x : Torus d) :
    UnitAddTorus.mFourier k (pointPermutation σ x) =
      UnitAddTorus.mFourier (frequencyPermutation σ.symm k) x := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, pointPermutation_apply,
    frequencyPermutation, Equiv.symm_symm]
  rw [← Equiv.prod_comp σ (fun i => fourier (k i) (x (σ.symm i)))]
  simp

/-- Exact reindexing of every actual Haar Fourier coefficient. -/
theorem coefficient_permutation {d : ℕ} (σ : Equiv.Perm (Fin d))
    (u : Space d) (k : Frequency d) :
    coefficient k (permutation σ u) = coefficient (frequencyPermutation σ k) u := by
  rw [coefficient_integral, coefficient_integral]
  rw [← integral_pointPermutation σ.symm
    (fun x => UnitAddTorus.mFourier (-k) x * (permutation σ u x : ℂ))]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by
    dsimp only
    rw [mFourier_pointPermutation]
    simp only [Equiv.symm_symm, frequencyPermutation_neg, permutation_apply]
    have he : pointPermutation σ (pointPermutation σ.symm x) = x := by
      ext i
      simp
    rw [he])

/-- The coordinate action on the full complex first shell. -/
def permuteCoordinates {d : ℕ} (σ : Equiv.Perm (Fin d)) (z : Coordinates d) : Coordinates d :=
  fun i => z (σ i)

theorem coordinates_permutation {d : ℕ} (σ : Equiv.Perm (Fin d)) (u : Space d) :
    coordinates d (permutation σ u) = permuteCoordinates σ (coordinates d u) := by
  ext i
  simp only [coordinates_apply, coefficient_permutation, frequencyPermutation_axis, permuteCoordinates]

private theorem coefficient_projection {d : ℕ} (u : Space d) (k : Frequency d) :
    coefficient k (projection d u) = if InFirstShell k then coefficient k u else 0 := by
  classical
  by_cases hk : InFirstShell k
  · rw [if_pos hk]
    obtain ⟨i, rfl | rfl⟩ := hk
    · exact first_coefficient_projection u i
    · rw [coefficient_neg, coefficient_neg, first_coefficient_projection]
  · rw [if_neg hk]
    exact coefficient_projection_off_shell u k hk

theorem projection_permutation {d : ℕ} (σ : Equiv.Perm (Fin d)) (u : Space d) :
    projection d (permutation σ u) = permutation σ (projection d u) := by
  apply coefficient_ext
  intro k
  simp only [coefficient_projection, coefficient_permutation, firstShell_permutation_iff]

theorem permutation_assembly {d : ℕ} (σ : Equiv.Perm (Fin d)) (z : Coordinates d) :
    permutation σ (assembly d z) = assembly d (permuteCoordinates σ z) := by
  calc
    _ = projection d (permutation σ (assembly d z)) := by
      rw [projection_permutation, projection_assembly]
    _ = assembly d (coordinates d (permutation σ (assembly d z))) :=
      (assembly_coordinates _).symm
    _ = _ := by rw [coordinates_permutation, coordinates_assembly]

theorem meanProjection_permutation {d : ℕ} (σ : Equiv.Perm (Fin d)) (u : Space d) :
    meanProjection d (permutation σ u) = permutation σ (meanProjection d u) := by
  simp only [meanProjection_apply, mean_permutation, permutation_const]

theorem complementProjection_permutation {d : ℕ} (σ : Equiv.Perm (Fin d)) (u : Space d) :
    complementProjection d (permutation σ u) = permutation σ (complementProjection d u) := by
  simp only [complementProjection_apply, meanProjection_permutation, projection_permutation, map_sub]

@[simp] theorem permutation_mem_complement_iff {d : ℕ} (σ : Equiv.Perm (Fin d)) (u : Space d) :
    permutation σ u ∈ complement d ↔ u ∈ complement d := by
  change (mean d (permutation σ u) = 0 ∧ projection d (permutation σ u) = 0) ↔ _
  rw [mean_permutation, projection_permutation, (permutation σ).map_eq_zero_iff]
  rfl

def complementPermutation {d : ℕ} (σ : Equiv.Perm (Fin d)) : complement d ≃ₗᵢ[ℝ] complement d where
  toFun u := ⟨permutation σ u, (permutation_mem_complement_iff σ u).mpr u.property⟩
  invFun u := ⟨permutation σ.symm u, (permutation_mem_complement_iff σ.symm u).mpr u.property⟩
  left_inv u := by
    apply Subtype.ext
    ext x
    change (u : Space d) (pointPermutation σ (pointPermutation σ.symm x)) = (u : Space d) x
    congr 1
    ext i
    simp
  right_inv u := by
    apply Subtype.ext
    ext x
    change (u : Space d) (pointPermutation σ.symm (pointPermutation σ x)) = (u : Space d) x
    congr 1
    ext i
    simp
  map_add' u v := by apply Subtype.ext; exact map_add (permutation σ) (u : Space d) (v : Space d)
  map_smul' c u := by apply Subtype.ext; exact map_smul (permutation σ) c (u : Space d)
  norm_map' u := (permutation σ).norm_map u

@[simp] theorem complementPermutation_coe {d : ℕ} (σ : Equiv.Perm (Fin d)) (u : complement d) :
    (complementPermutation σ u : Space d) = permutation σ (u : Space d) := rfl

theorem complementMap_permutation {d : ℕ} (σ : Equiv.Perm (Fin d)) (u : Space d) :
    complementMap d (permutation σ u) = complementPermutation σ (complementMap d u) := by
  apply Subtype.ext
  exact complementProjection_permutation σ u

theorem permuteCoordinates_norm {d : ℕ} (σ : Equiv.Perm (Fin d)) (z : Coordinates d) :
    ‖permuteCoordinates σ z‖ = ‖z‖ := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg z)).mpr
    intro i
    exact norm_le_pi_norm z (σ i)
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg (permuteCoordinates σ z))).mpr
    intro i
    simpa only [permuteCoordinates, Equiv.apply_symm_apply] using
      norm_le_pi_norm (permuteCoordinates σ z) (σ.symm i)

def coordinatePermutation {d : ℕ} (σ : Equiv.Perm (Fin d)) : Coordinates d ≃ₗᵢ[ℝ] Coordinates d where
  toFun := permuteCoordinates σ
  invFun := permuteCoordinates σ.symm
  left_inv z := by ext i; simp [permuteCoordinates]
  right_inv z := by ext i; simp [permuteCoordinates]
  map_add' z w := rfl
  map_smul' c z := rfl
  norm_map' := permuteCoordinates_norm σ

@[simp] theorem coordinatePermutation_apply {d : ℕ} (σ : Equiv.Perm (Fin d)) (z : Coordinates d) :
    coordinatePermutation σ z = permuteCoordinates σ z := rfl

theorem center_permutation {d : ℕ} (σ : Equiv.Perm (Fin d)) (u : Space d) :
    center d (permutation σ u) = permutation σ (center d u) := by
  ext x
  simp only [center_apply, permutation_apply, mean_permutation]

theorem nonlinearRemainder_permutation {d : ℕ} (σ : Equiv.Perm (Fin d)) (u : Space d) :
    nonlinearRemainder (permutation σ u) = permutation σ (nonlinearRemainder u) := by
  simp only [nonlinearRemainder, normalized_permutation, center_permutation, map_sub, permutation_one]

theorem green_permutation {d : ℕ} (hd : 0 < d) (σ : Equiv.Perm (Fin d)) (u : Space d) :
    greenContinuous d (permutation σ u) = permutation σ (greenContinuous d u) := by
  apply coefficient_ext
  intro k
  simp only [coefficient_green hd, coefficient_permutation,
    frequencyLength_permutation, frequencyPermutation_eq_zero_iff]

theorem reconstruction_permutation {d : ℕ} (σ : Equiv.Perm (Fin d))
    (z : Coordinates d) (w : complement d) :
    reconstruction d (permuteCoordinates σ z, complementPermutation σ w) =
      permutation σ (reconstruction d (z,w)) := by
  simp only [reconstruction_apply, ← permutation_assembly, complementPermutation_coe, map_add]

theorem projectedEquation_permutation {d : ℕ} (hd : 0 < d) (σ : Equiv.Perm (Fin d))
    (μ : ℝ) (z : Coordinates d) (w : complement d) :
    projectedEquation (greenContinuous d) ((μ, permuteCoordinates σ z), complementPermutation σ w) =
      complementPermutation σ (projectedEquation (greenContinuous d) ((μ,z),w)) := by
  unfold projectedEquation
  rw [reconstruction_permutation, normalized_permutation]
  have he : permutation σ (normalized (reconstruction d (z,w))) - 1 =
      permutation σ (normalized (reconstruction d (z,w)) - 1) := by
    rw [map_sub, permutation_one]
  rw [he, green_permutation hd, complementMap_permutation]
  simp only [map_sub, map_smul]

private theorem permuted_graph_dist {d : ℕ} (σ : Equiv.Perm (Fin d))
    (x : ℝ × Coordinates d) (w : complement d) :
    dist ((x.1, permuteCoordinates σ x.2), complementPermutation σ w)
        ((1, (0 : Coordinates d)), (0 : complement d)) =
      dist (x,w) ((1, (0 : Coordinates d)), (0 : complement d)) := by
  simp only [Prod.dist_eq, dist_zero_right, permuteCoordinates_norm,
    (complementPermutation σ).norm_map]

/-- A single parameter neighbourhood works simultaneously for every permutation. -/
theorem correction_permutation {d : ℕ} (hd : 11 ≤ d) :
    ∀ᶠ x in 𝓝 (1, (0 : Coordinates d)), ∀ σ : Equiv.Perm (Fin d),
      correction hd (x.1, permuteCoordinates σ x.2) =
        complementPermutation σ (correction hd x) := by
  obtain ⟨ε, hε, hUnique⟩ := Metric.eventually_nhds_iff.mp (correction_unique hd)
  have ht : Filter.Tendsto (fun x : ℝ × Coordinates d => (x, correction hd x))
      (𝓝 (1, (0 : Coordinates d)))
      (𝓝 ((1, (0 : Coordinates d)), (0 : complement d))) := by
    simpa only [correction_base, id_eq] using
      (continuousAt_id.prodMk (correction_analytic hd).continuousAt).tendsto
  have hNear : ∀ᶠ x in 𝓝 (1, (0 : Coordinates d)),
      dist (x, correction hd x) ((1, (0 : Coordinates d)), (0 : complement d)) < ε :=
    ht.eventually (Metric.ball_mem_nhds _ hε)
  filter_upwards [correction_solves hd, hNear] with x hx hdist
  intro σ
  have hdist' : dist ((x.1, permuteCoordinates σ x.2), complementPermutation σ (correction hd x))
      ((1, (0 : Coordinates d)), (0 : complement d)) < ε := by
    rw [permuted_graph_dist]
    exact hdist
  apply (hUnique hdist').mp
  rw [projectedEquation_permutation (by omega)]
  change complementPermutation σ (projectedEquation (greenContinuous d) (x, correction hd x)) = 0
  rw [hx, map_zero]

theorem potential_permutation {d : ℕ} (hd : 11 ≤ d) :
    ∀ᶠ x in 𝓝 (1, (0 : Coordinates d)), ∀ σ : Equiv.Perm (Fin d),
      potential hd (x.1, permuteCoordinates σ x.2) = permutation σ (potential hd x) := by
  filter_upwards [correction_permutation hd] with x hx
  intro σ
  simp only [potential, hx σ, reconstruction_permutation]

theorem reduced_permutation {d : ℕ} (hd : 11 ≤ d) :
    ∀ᶠ x in 𝓝 (1, (0 : Coordinates d)), ∀ σ : Equiv.Perm (Fin d),
      reduced hd (x.1, permuteCoordinates σ x.2) = permuteCoordinates σ (reduced hd x) := by
  filter_upwards [potential_permutation hd] with x hx
  intro σ
  simp only [reduced, hx σ, normalized_permutation, coordinates_permutation]
  change coordinatePermutation σ x.2 - x.1 •
      coordinatePermutation σ (coordinates d (normalized (potential hd x))) =
    coordinatePermutation σ (x.2 - x.1 • coordinates d (normalized (potential hd x)))
  simp only [map_sub, map_smul]

theorem reduced_zero_permutation_iff {d : ℕ} (hd : 11 ≤ d) :
    ∀ᶠ x in 𝓝 (1, (0 : Coordinates d)), ∀ σ : Equiv.Perm (Fin d),
      reduced hd (x.1, permuteCoordinates σ x.2) = 0 ↔ reduced hd x = 0 := by
  filter_upwards [reduced_permutation hd] with x hx
  intro σ
  rw [hx σ]
  change coordinatePermutation σ (reduced hd x) = 0 ↔ reduced hd x = 0
  exact (coordinatePermutation σ).map_eq_zero_iff

#print axioms correction_permutation
#print axioms reduced_permutation

#print axioms coefficient_permutation
#print axioms complementMap_permutation
end BecknerOnofri.HighDim.LocalEleven.ContinuousSymmetry
