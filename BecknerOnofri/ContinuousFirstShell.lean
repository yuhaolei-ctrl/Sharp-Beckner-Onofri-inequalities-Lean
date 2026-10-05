module

public import BecknerOnofri.ContinuousGibbs
public import BecknerOnofri.FirstShellSharpness
public import BecknerOnofri.ComplementGap
public import Legacy.BecknerOnofri.SobolevCentering

@[expose] public section

/-! Continuous projections onto the constant and full cosine/sine first shell.
The coefficients are those of the actual normalized torus Fourier transform. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate
namespace BecknerOnofri.HighDim.ContinuousFirstShell
open ContinuousGibbs
open Legacy.BecknerOnofri.TorusSobolev Legacy.BecknerOnofri.SubcriticalEuler

/-- Inclusion of real continuous functions in the complex torus Hilbert space. -/
def toL2 (d : ℕ) : Space d →L[ℝ] TorusL2 d :=
  (ContinuousMap.toLp 2 (torusMeasure d) ℝ).comp
    (Complex.ofRealCLM.compLeftContinuous ℝ (Torus d))

theorem toL2_ae {d : ℕ} (u : Space d) :
    toL2 d u =ᵐ[torusMeasure d] (fun x => (u x : ℂ)) :=
  ContinuousMap.coeFn_toLp (torusMeasure d) _

/-- The inclusion into normalized Haar L² has operator norm at most one. -/
theorem toL2_norm_le (d : ℕ) : ‖toL2 d‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  let v : C(Torus d, ℂ) := Complex.ofRealCLM.compLeftContinuous ℝ (Torus d) u
  have hv : ‖v‖ ≤ ‖u‖ := by
    apply (ContinuousMap.norm_le _ (norm_nonneg u)).mpr
    intro x
    change ‖(u x : ℂ)‖ ≤ ‖u‖
    simpa only [Complex.norm_real] using u.norm_coe_le_norm x
  have hT : ‖(ContinuousMap.toLp 2 (torusMeasure d) ℝ : C(Torus d, ℂ) →L[ℝ] TorusL2 d)‖ ≤ 1 := by
    simpa [measureUnivNNReal] using (ContinuousMap.toLp_norm_le (p := 2) (E := ℂ) (𝕜 := ℝ) (torusMeasure d))
  change ‖ContinuousMap.toLp 2 (torusMeasure d) ℝ v‖ ≤ 1 * ‖u‖
  calc
    _ ≤ ‖(ContinuousMap.toLp 2 (torusMeasure d) ℝ : C(Torus d, ℂ) →L[ℝ] TorusL2 d)‖ * ‖v‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖u‖ := mul_le_mul hT hv (norm_nonneg _) zero_le_one

def coefficient {d : ℕ} (k : Frequency d) : Space d →L[ℝ] ℂ :=
  (ContinuousLinearMap.restrictScalars ℝ
    ((lp.evalCLM ℂ (fun _ : Frequency d => ℂ) 2 k).comp
      (fourierIsometry d).toContinuousLinearEquiv.toContinuousLinearMap)).comp (toL2 d)

theorem coefficient_apply {d : ℕ} (k : Frequency d) (u : Space d) :
    coefficient k u = fourierIsometry d (toL2 d u) k := rfl

theorem coefficient_integral {d : ℕ} (k : Frequency d) (u : Space d) :
    coefficient k u = ∫ x, UnitAddTorus.mFourier (-k) x * (u x : ℂ) ∂torusMeasure d := by
  rw [coefficient_apply, fourierIsometry_apply]
  apply integral_congr_ae
  filter_upwards [toL2_ae u] with x hx
  simp only [smul_eq_mul, hx]

/-- Agreement with the Fourier coefficients appearing in the trusted theorem. -/
theorem coefficient_eq_fourierCoeff {d : ℕ} (k : Frequency d) (u : Space d) :
    coefficient k u = fourierCoeff u k := coefficient_integral k u

theorem coefficient_zero {d : ℕ} (u : Space d) :
    coefficient 0 u = (mean d u : ℂ) := by
  rw [coefficient_integral]
  simp only [neg_zero, UnitAddTorus.mFourier_zero, ContinuousMap.one_apply, one_mul,
    mean_apply]
  exact integral_ofReal (𝕜 := ℂ) (μ := torusMeasure d) (f := fun x => u x)

theorem coefficient_neg {d : ℕ} (k : Frequency d) (u : Space d) :
    coefficient (-k) u = conj (coefficient k u) := by
  simp only [coefficient_apply]
  apply fourier_real_symmetry
  filter_upwards [toL2_ae u] with x hx
  simp [hx]

theorem toL2_injective (d : ℕ) : Function.Injective (toL2 d) := by
  intro u v h
  have hae : (fun x => u x) =ᵐ[torusMeasure d] (fun x => v x) := by
    filter_upwards [toL2_ae u, toL2_ae v] with x hu hv
    apply Complex.ofReal_injective
    rw [← hu, ← hv, h]
  haveI : (torusMeasure d).IsOpenPosMeasure := by
    unfold torusMeasure
    infer_instance
  exact ContinuousMap.ext (congrFun (Measure.eq_of_ae_eq hae u.continuous v.continuous))

/-- Continuous real functions are determined by these actual Fourier coefficients. -/
theorem coefficient_ext {d : ℕ} {u v : Space d}
    (h : ∀ k, coefficient k u = coefficient k v) : u = v := by
  apply toL2_injective d
  apply (fourierIsometry d).injective
  exact lp.ext (funext h)

/-- The real mode with Fourier coefficient z at k and conjugate z at -k. -/
def synthesis {d : ℕ} (k : Frequency d) : ℂ →L[ℝ] Space d :=
  Complex.reCLM.smulRight ((2 : ℝ) • Complex.reCLM.compLeftContinuous ℝ (Torus d) (UnitAddTorus.mFourier k)) -
  Complex.imCLM.smulRight ((2 : ℝ) • Complex.imCLM.compLeftContinuous ℝ (Torus d) (UnitAddTorus.mFourier k))

@[simp] theorem synthesis_apply {d : ℕ} (k : Frequency d) (z : ℂ) (x : Torus d) :
    synthesis k z x = 2 * (z * UnitAddTorus.mFourier k x).re := by
  simp [synthesis, Complex.mul_re]
  ring

theorem toL2_synthesis {d : ℕ} (k : Frequency d) (z : ℂ) :
    toL2 d (synthesis k z) = mode k z := by
  apply Lp.ext
  filter_upwards [toL2_ae (synthesis k z), mode_coe k z] with x hl hr
  rw [hl, hr, synthesis_apply, UnitAddTorus.mFourier_neg]
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

theorem coefficient_synthesis {d : ℕ} (k j : Frequency d) (z : ℂ) :
    coefficient j (synthesis k z) = (if j = k then z else 0) +
      (if j = -k then conj z else 0) := by
  classical
  rw [coefficient_apply, toL2_synthesis, fourier_mode]
  simp [lp.single_apply, Pi.single_apply]

private theorem axis_injective {d : ℕ} : Function.Injective (@axisFrequency d) := by
  intro i j h
  by_contra hij
  have hh := congrFun h i
  simp [axisFrequency, hij] at hh

private theorem axis_ne_neg {d : ℕ} (i j : Fin d) : axisFrequency i ≠ -axisFrequency j := by
  intro h
  have hh := congrFun h j
  by_cases hij : j = i <;> simp [axisFrequency, hij] at hh

def projection (d : ℕ) : Space d →L[ℝ] Space d :=
  ∑ i : Fin d, (synthesis (axisFrequency i)).comp (coefficient (axisFrequency i))

theorem projection_apply {d : ℕ} (u : Space d) :
    projection d u = ∑ i : Fin d, synthesis (axisFrequency i) (coefficient (axisFrequency i) u) := by
  simp [projection]

theorem first_coefficient_projection {d : ℕ} (u : Space d) (j : Fin d) :
    coefficient (axisFrequency j) (projection d u) = coefficient (axisFrequency j) u := by
  classical
  rw [projection_apply, map_sum]
  simp [coefficient_synthesis, axis_injective.eq_iff, axis_ne_neg]

theorem mean_projection {d : ℕ} (u : Space d) : mean d (projection d u) = 0 := by
  apply Complex.ofReal_injective
  rw [← coefficient_zero, projection_apply, map_sum]
  simp [coefficient_synthesis, axisFrequency_ne_zero, eq_comm]

theorem projection_idempotent (d : ℕ) : (projection d).comp (projection d) = projection d := by
  apply ContinuousLinearMap.ext
  intro u
  change projection d (projection d u) = projection d u
  rw [projection_apply (projection d u)]
  simp only [first_coefficient_projection]
  exact (projection_apply u).symm

theorem projection_zero_iff {d : ℕ} (u : Space d) :
    projection d u = 0 ↔ ∀ i, coefficient (axisFrequency i) u = 0 := by
  constructor
  · intro h i
    rw [← first_coefficient_projection u i, h, map_zero]
  · intro h
    simp [projection_apply, h]

theorem coefficient_projection_off_shell {d : ℕ} (u : Space d) (k : Frequency d)
    (hk : ¬ InFirstShell k) : coefficient k (projection d u) = 0 := by
  classical
  rw [projection_apply, map_sum]
  apply Finset.sum_eq_zero
  intro i _
  have ha : k ≠ axisFrequency i := fun h => hk ⟨i, Or.inl h⟩
  have hb : k ≠ -axisFrequency i := fun h => hk ⟨i, Or.inr h⟩
  simp [coefficient_synthesis, ha, hb]

theorem coefficient_const {d : ℕ} (c : ℝ) (k : Frequency d) :
    coefficient k (ContinuousMap.const (Torus d) c) = if k = 0 then (c : ℂ) else 0 := by
  classical
  have h : toL2 d (ContinuousMap.const (Torus d) c) =
      Legacy.BecknerOnofri.SobolevCentering.constant d (c : ℂ) := by
    apply Lp.ext
    exact (toL2_ae _).trans (Legacy.BecknerOnofri.SobolevCentering.constant_ae d (c : ℂ)).symm
  rw [coefficient_apply, h, Legacy.BecknerOnofri.SobolevCentering.constant_fourier]

@[simp] theorem mean_const {d : ℕ} (c : ℝ) : mean d (ContinuousMap.const (Torus d) c) = c := by
  simp [mean_apply]

@[simp] theorem projection_const {d : ℕ} (c : ℝ) :
    projection d (ContinuousMap.const (Torus d) c) = 0 := by
  rw [projection_zero_iff]
  intro i
  simp [coefficient_const, axisFrequency_ne_zero]

/-- Projection onto the constant functions. -/
def meanProjection (d : ℕ) : Space d →L[ℝ] Space d :=
  (ContinuousLinearMap.const ℝ (Torus d)).comp (mean d)

@[simp] theorem meanProjection_apply {d : ℕ} (u : Space d) :
    meanProjection d u = ContinuousMap.const (Torus d) (mean d u) := rfl

theorem meanProjection_idempotent (d : ℕ) :
    (meanProjection d).comp (meanProjection d) = meanProjection d := by
  ext u x
  simp [meanProjection_apply]

/-- Projection onto mean-zero functions orthogonal to the whole first shell. -/
def complementProjection (d : ℕ) : Space d →L[ℝ] Space d :=
  ContinuousLinearMap.id ℝ (Space d) - meanProjection d - projection d

theorem complementProjection_apply {d : ℕ} (u : Space d) :
    complementProjection d u = u - meanProjection d u - projection d u := rfl

@[simp] theorem mean_complementProjection {d : ℕ} (u : Space d) :
    mean d (complementProjection d u) = 0 := by
  simp only [complementProjection_apply, map_sub, meanProjection_apply, mean_const, mean_projection, sub_self]

@[simp] theorem projection_complementProjection {d : ℕ} (u : Space d) :
    projection d (complementProjection d u) = 0 := by
  have hi := DFunLike.congr_fun (projection_idempotent d) u
  simp only [ContinuousLinearMap.comp_apply] at hi
  simp only [complementProjection_apply, map_sub, meanProjection_apply, projection_const, hi, sub_zero, sub_self]

def complement (d : ℕ) : Submodule ℝ (Space d) := (mean d).ker ⊓ (projection d).ker

@[simp] theorem mem_complement_iff {d : ℕ} (u : Space d) :
    u ∈ complement d ↔ mean d u = 0 ∧ ∀ i, coefficient (axisFrequency i) u = 0 := by
  change (mean d u = 0 ∧ projection d u = 0) ↔ _
  rw [projection_zero_iff]

theorem complement_closed (d : ℕ) : IsClosed (complement d : Set (Space d)) :=
  (mean d).isClosed_ker.inter (projection d).isClosed_ker

instance complement_completeSpace (d : ℕ) : CompleteSpace (complement d) :=
  (complement_closed d).completeSpace_coe

theorem complementProjection_mem {d : ℕ} (u : Space d) : complementProjection d u ∈ complement d := by
  exact ⟨mean_complementProjection u, projection_complementProjection u⟩

theorem complementProjection_eq_self {d : ℕ} {u : Space d} (hu : u ∈ complement d) :
    complementProjection d u = u := by
  have hm : mean d u = 0 := hu.1
  have hp : projection d u = 0 := hu.2
  simp only [complementProjection_apply, meanProjection_apply, hm, hp, ContinuousMap.const_zero, sub_zero]

theorem complementProjection_idempotent (d : ℕ) :
    (complementProjection d).comp (complementProjection d) = complementProjection d := by
  ext u x
  exact congrFun (congrArg DFunLike.coe (complementProjection_eq_self (complementProjection_mem u))) x

theorem mem_complement_fourier_iff {d : ℕ} (u : Space d) :
    u ∈ complement d ↔ ∀ k, ¬ ComplementFrequency k → coefficient k u = 0 := by
  rw [mem_complement_iff]
  constructor
  · rintro ⟨hm, hp⟩ k hk
    by_cases hz : k = 0
    · subst k
      rw [coefficient_zero, hm, Complex.ofReal_zero]
    · have hs : InFirstShell k := Classical.byContradiction (fun hs => hk ⟨hz, hs⟩)
      obtain ⟨i, rfl | rfl⟩ := hs
      · exact hp i
      · rw [coefficient_neg, hp i, map_zero]
  · intro h
    constructor
    · apply Complex.ofReal_injective
      rw [← coefficient_zero]
      exact h 0 (by simp [ComplementFrequency])
    · intro i
      exact h _ (fun hk => hk.2 ⟨i, Or.inl rfl⟩)

/-- The complement projection with its closed Banach-space codomain. -/
def complementMap (d : ℕ) : Space d →L[ℝ] complement d :=
  (complementProjection d).codRestrict (complement d) complementProjection_mem

@[simp] theorem complementMap_coe {d : ℕ} (u : Space d) :
    (complementMap d u : Space d) = complementProjection d u := rfl

@[simp] theorem complementMap_subtype {d : ℕ} (u : complement d) :
    complementMap d (u : Space d) = u := by
  apply Subtype.ext
  exact complementProjection_eq_self u.property

/-- The full first-shell parameter space has d complex, hence 2d real, coordinates. -/
abbrev Coordinates (d : ℕ) := Fin d → ℂ

def coordinates (d : ℕ) : Space d →L[ℝ] Coordinates d :=
  ContinuousLinearMap.pi (fun i => coefficient (axisFrequency i))

@[simp] theorem coordinates_apply {d : ℕ} (u : Space d) (i : Fin d) :
    coordinates d u i = coefficient (axisFrequency i) u := rfl

def assembly (d : ℕ) : Coordinates d →L[ℝ] Space d :=
  ∑ i : Fin d, (synthesis (axisFrequency i)).comp (ContinuousLinearMap.proj i)

theorem assembly_apply {d : ℕ} (z : Coordinates d) :
    assembly d z = ∑ i, synthesis (axisFrequency i) (z i) := by simp [assembly]

theorem coordinates_assembly {d : ℕ} (z : Coordinates d) : coordinates d (assembly d z) = z := by
  classical
  ext j
  rw [coordinates_apply, assembly_apply, map_sum]
  simp [coefficient_synthesis, axis_injective.eq_iff, axis_ne_neg]

theorem assembly_injective (d : ℕ) : Function.Injective (assembly d) :=
  Function.LeftInverse.injective (coordinates_assembly (d := d))

theorem assembly_coordinates {d : ℕ} (u : Space d) : assembly d (coordinates d u) = projection d u := by
  rw [assembly_apply, projection_apply]
  rfl

theorem projection_assembly {d : ℕ} (z : Coordinates d) : projection d (assembly d z) = assembly d z := by
  rw [← assembly_coordinates, coordinates_assembly]

theorem mean_assembly {d : ℕ} (z : Coordinates d) : mean d (assembly d z) = 0 := by
  rw [← projection_assembly z]
  exact mean_projection _

/-- Exact real-space decomposition into a constant, all first-shell modes, and the closed complement. -/
theorem decomposition {d : ℕ} (u : Space d) :
    u = meanProjection d u + assembly d (coordinates d u) + (complementMap d u : Space d) := by
  rw [assembly_coordinates, complementMap_coe, complementProjection_apply]
  abel

#print axioms projection_idempotent
#print axioms complementProjection_idempotent
#print axioms mem_complement_fourier_iff
end BecknerOnofri.HighDim.ContinuousFirstShell
