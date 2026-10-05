import BecknerOnofri.GreenLocalBranch

/-! Exact finite-dimensional reduction of the genuine preconditioned torus
Euler equation; no polynomial substitute is used for the Gibbs map. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Topology
namespace BecknerOnofri.HighDim.ReducedEquation
open ContinuousGibbs ContinuousFirstShell ContinuousComplement GreenLocalBranch

/-- Actual normalized, preconditioned Euler equation in continuous potentials. -/
def full (d : ℕ) (μ : ℝ) (u : Space d) : Space d :=
  u - μ • greenContinuous d (normalized u - 1)

theorem mean_green {d : ℕ} (hd : 0 < d) (u : Space d) : mean d (greenContinuous d u) = 0 := by
  apply Complex.ofReal_injective
  rw [← coefficient_zero, coefficient_green hd]
  simp

theorem coordinates_green {d : ℕ} (hd : 0 < d) (u : Space d) :
    coordinates d (greenContinuous d u) = coordinates d u := by
  funext i
  simp only [coordinates_apply, coefficient_green hd]
  simp [axisFrequency_ne_zero, frequencyLength_pow_eq, latticeSquare_axis]

@[simp] theorem coordinates_one (d : ℕ) : coordinates d (1 : Space d) = 0 := by
  funext i
  change coefficient (axisFrequency i) (ContinuousMap.const (Torus d) 1) = 0
  rw [coefficient_const]
  simp [axisFrequency_ne_zero]

theorem coordinates_complement {d : ℕ} (w : complement d) :
    coordinates d (w : Space d) = 0 := by
  funext i
  exact (mem_complement_iff w.val).mp w.property |>.2 i

@[simp] theorem coordinates_reconstruction {d : ℕ} (x : Coordinates d × complement d) :
    coordinates d (reconstruction d x) = x.1 := by
  rcases x with ⟨z, w⟩
  rw [reconstruction_apply, map_add, coordinates_assembly, coordinates_complement, add_zero]

@[simp] theorem complementMap_assembly {d : ℕ} (z : Coordinates d) :
    complementMap d (assembly d z) = 0 := by
  apply Subtype.ext
  change complementProjection d (assembly d z) = 0
  rw [complementProjection_apply, meanProjection_apply, mean_assembly, projection_assembly]
  simp

@[simp] theorem complementMap_reconstruction {d : ℕ} (x : Coordinates d × complement d) :
    complementMap d (reconstruction d x) = x.2 := by
  rcases x with ⟨z, w⟩
  rw [reconstruction_apply, map_add, complementMap_assembly, complementMap_subtype, zero_add]

theorem full_mean {d : ℕ} (hd : 0 < d) (μ : ℝ) (x : Coordinates d × complement d) :
    mean d (full d μ (reconstruction d x)) = 0 := by
  simp only [full, map_sub, map_smul, mean_reconstruction, mean_green hd, smul_zero, sub_zero]

theorem full_coordinates {d : ℕ} (hd : 0 < d) (μ : ℝ) (x : Coordinates d × complement d) :
    coordinates d (full d μ (reconstruction d x)) =
      x.1 - μ • coordinates d (normalized (reconstruction d x)) := by
  simp only [full, map_sub, map_smul, coordinates_reconstruction, coordinates_green hd,
    coordinates_one, sub_zero]

theorem full_complement {d : ℕ} (μ : ℝ) (z : Coordinates d) (w : complement d) :
    complementMap d (full d μ (reconstruction d (z,w))) =
      projectedEquation (greenContinuous d) ((μ,z),w) := by
  simp only [full, map_sub, map_smul, complementMap_reconstruction, projectedEquation]

theorem meanZero_zero_iff {d : ℕ} (u : Space d) (hu : mean d u = 0) :
    u = 0 ↔ coordinates d u = 0 ∧ complementMap d u = 0 := by
  constructor
  · rintro rfl
    simp
  · rintro ⟨hz, hw⟩
    rw [decomposition u, meanProjection_apply, hu, hz, hw]
    simp

theorem full_zero_iff {d : ℕ} (hd : 0 < d) (μ : ℝ) (z : Coordinates d) (w : complement d) :
    full d μ (reconstruction d (z,w)) = 0 ↔
      z - μ • coordinates d (normalized (reconstruction d (z,w))) = 0 ∧
      projectedEquation (greenContinuous d) ((μ,z),w) = 0 := by
  rw [meanZero_zero_iff _ (full_mean hd μ (z,w)), full_coordinates hd, full_complement]

/-- The genuine potential on the locally solved complementary graph. -/
def potential {d : ℕ} (hd : 12 ≤ d) (x : ℝ × Coordinates d) : Space d :=
  reconstruction d (x.2, correction hd x)

/-- Exact reduced equation in all d complex first-shell coordinates. -/
def reduced {d : ℕ} (hd : 12 ≤ d) (x : ℝ × Coordinates d) : Coordinates d :=
  x.2 - x.1 • coordinates d (normalized (potential hd x))

theorem potential_analytic {d : ℕ} (hd : 12 ≤ d) :
    AnalyticAt ℝ (potential hd) (1,0) := by
  have hi : AnalyticAt ℝ (fun x : ℝ × Coordinates d => (x.2, correction hd x)) (1,0) :=
    analyticAt_snd.prod (correction_analytic hd)
  exact ((reconstruction d).analyticAt _).comp hi

theorem reduced_analytic {d : ℕ} (hd : 12 ≤ d) :
    AnalyticAt ℝ (reduced hd) (1,0) := by
  have hn := (normalized_analytic (potential hd (1,0))).comp (potential_analytic hd)
  have hc := ((coordinates d).analyticAt (normalized (potential hd (1,0)))).comp
    (f := fun x : ℝ × Coordinates d => normalized (potential hd x)) hn
  exact analyticAt_snd.sub (analyticAt_fst.smul hc)

theorem local_full_iff_reduced {d : ℕ} (hd : 12 ≤ d) :
    ∀ᶠ x in 𝓝 ((1, (0 : Coordinates d)), (0 : complement d)),
      full d x.1.1 (reconstruction d (x.1.2,x.2)) = 0 ↔
        correction hd x.1 = x.2 ∧ reduced hd x.1 = 0 := by
  filter_upwards [correction_unique hd] with x hx
  rw [full_zero_iff (by omega), hx]
  constructor
  · rintro ⟨hred, hw⟩
    refine ⟨hw, ?_⟩
    simpa only [reduced, potential, hw] using hred
  · rintro ⟨hw, hred⟩
    refine ⟨?_, hw⟩
    simpa only [reduced, potential, hw] using hred

theorem graph_full_iff_reduced {d : ℕ} (hd : 12 ≤ d) :
    ∀ᶠ x in 𝓝 (1, (0 : Coordinates d)),
      full d x.1 (potential hd x) = 0 ↔ reduced hd x = 0 := by
  filter_upwards [correction_solves hd] with x hx
  rw [potential, full_zero_iff (by omega)]
  exact and_iff_left hx

#print axioms local_full_iff_reduced
#print axioms reduced_analytic
end BecknerOnofri.HighDim.ReducedEquation
