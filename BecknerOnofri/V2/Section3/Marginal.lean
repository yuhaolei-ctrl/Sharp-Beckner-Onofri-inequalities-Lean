module

public import BecknerOnofri.V2.Section3.Lemma32
public import BecknerOnofri.EntropyShearer.PaperStatement
public import BecknerOnofri.MixtureMarginals

@[expose] public section

/-! # The circle marginal of a finite-entropy density (G04, R2)

For `ρ` a probability density on `𝕋^{n+1}` and a coordinate `i` the Fubini marginal
`circleMarginal ρ i : 𝕋 → ℝ` is a probability density on the circle (no continuity or positivity is
assumed), with Fourier coefficients `ρ̂(j e_i)` and entropy `coordinateMarginalEntropy ρ {i}`.
Combined with the repository's Shearer inequality for arbitrary finite-entropy densities
(`EntropyShearer.subset_entropy`, `r = 1`) and Lemma 3.2 this gives
`eq:circle-marginal-fourier-control`:
`∑_i ∑_{j ≥ 1} |ρ̂(j e_i)|² / j ≤ ∑_i Ent(ρ_i) ≤ Ent(ρ)`. -/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal

namespace BecknerOnofri.V2.Section3
open BecknerOnofri.HighDim BecknerOnofri.V2.Vocab

variable {n : ℕ}

/-- The Fubini marginal of `ρ` on coordinate `i`, as a function on the circle. -/
def circleMarginal (ρ : ProbabilityDensity (n + 1)) (i : Fin (n + 1)) : UnitAddCircle → ℝ :=
  Legacy.D10.coordinateMarginal
    (μ := fun _ : Fin (n + 1) => (AddCircle.haarAddCircle : Measure UnitAddCircle)) ρ.value i

theorem circleMarginal_integrable (ρ : ProbabilityDensity (n + 1)) (i : Fin (n + 1)) :
    Integrable (circleMarginal ρ i) AddCircle.haarAddCircle := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => UnitAddCircle) i
  have he := (measurePreserving_piFinSuccAbove
    (fun _ : Fin (n + 1) => (AddCircle.haarAddCircle : Measure UnitAddCircle)) i).symm
  have hi : Integrable (fun z => ρ.value (e.symm z))
      (AddCircle.haarAddCircle.prod (Measure.pi fun j : Fin n => AddCircle.haarAddCircle)) :=
    (he.integrable_comp_emb e.symm.measurableEmbedding).mpr ρ.integrable
  exact hi.integral_prod_left

theorem circleMarginal_nonneg_ae (ρ : ProbabilityDensity (n + 1)) (i : Fin (n + 1)) :
    ∀ᵐ y ∂(AddCircle.haarAddCircle : Measure UnitAddCircle), 0 ≤ circleMarginal ρ i y := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => UnitAddCircle) i
  have he := (measurePreserving_piFinSuccAbove
    (fun _ : Fin (n + 1) => (AddCircle.haarAddCircle : Measure UnitAddCircle)) i).symm
  have h1 := he.quasiMeasurePreserving.ae ρ.nonneg
  have h2 := Measure.ae_ae_of_ae_prod h1
  filter_upwards [h2] with y hy
  exact integral_nonneg_of_ae hy

theorem circleMarginal_mass (ρ : ProbabilityDensity (n + 1)) (i : Fin (n + 1)) :
    (∫ y, circleMarginal ρ i y ∂(AddCircle.haarAddCircle : Measure UnitAddCircle)) = 1 :=
  (Legacy.D10.coordinateMarginal_mass
    (μ := fun _ : Fin (n + 1) => (AddCircle.haarAddCircle : Measure UnitAddCircle))
    ρ.integrable i).trans ρ.mass


/-- The circle marginal as a probability density on `𝕋¹`. -/
def axisDensity (ρ : ProbabilityDensity (n + 1)) (i : Fin (n + 1)) : ProbabilityDensity 1 where
  value := fun y => circleMarginal ρ i (y 0)
  nonneg :=
    (measurePreserving_eval (fun _ : Fin 1 => (AddCircle.haarAddCircle : Measure UnitAddCircle))
      0).quasiMeasurePreserving.ae (circleMarginal_nonneg_ae ρ i)
  integrable := integrable_comp_eval
    (μ := fun _ : Fin 1 => (AddCircle.haarAddCircle : Measure UnitAddCircle)) (i := 0)
    (circleMarginal_integrable ρ i)
  mass := by
    change (∫ x : Fin 1 → UnitAddCircle, circleMarginal ρ i (x 0)
      ∂Measure.pi (fun _ : Fin 1 => (AddCircle.haarAddCircle : Measure UnitAddCircle))) = 1
    rw [integral_comp_eval (μ := fun _ : Fin 1 => (AddCircle.haarAddCircle : Measure UnitAddCircle))
      (i := (0 : Fin 1)) (circleMarginal_integrable ρ i).aestronglyMeasurable]
    exact circleMarginal_mass ρ i

@[simp] theorem axisDensity_value (ρ : ProbabilityDensity (n + 1)) (i : Fin (n + 1)) :
    (axisDensity ρ i).value = fun y => circleMarginal ρ i (y 0) := rfl

/-- Fubini pairing against bounded measurable circle functions. -/
theorem axisDensity_pairing (ρ : ProbabilityDensity (n + 1)) (i : Fin (n + 1))
    {u : Torus 1 → ℝ} {B : ℝ} (hu : Measurable u) (hB : ∀ x, ‖u x‖ ≤ B) :
    (∫ x, ρ.value x * u (fun _ : Fin 1 => x i) ∂torusMeasure (n + 1)) =
      ∫ y, (axisDensity ρ i).value y * u y ∂torusMeasure 1 := by
  have hdiag : Measurable (fun y : UnitAddCircle => (fun _ : Fin 1 => y)) := by
    fun_prop
  have he (x : Torus 1) : (fun _ : Fin 1 => x 0) = x := by
    funext j
    have hj : j = 0 := Subsingleton.elim _ _
    simp [hj]
  calc
    _ = ∫ y : UnitAddCircle, circleMarginal ρ i y * u (fun _ : Fin 1 => y)
        ∂AddCircle.haarAddCircle :=
      Legacy.D10.coordinateMarginal_pairing
        (μ := fun _ : Fin (n + 1) => (AddCircle.haarAddCircle : Measure UnitAddCircle))
        ρ.integrable i (u := fun y => u (fun _ : Fin 1 => y)) (hu.comp hdiag) (fun _ => hB _)
    _ = ∫ x : Torus 1, circleMarginal ρ i (x 0) * u (fun _ : Fin 1 => x 0) ∂torusMeasure 1 :=
      (integral_comp_eval (μ := fun _ : Fin 1 => (AddCircle.haarAddCircle : Measure UnitAddCircle))
        (i := (0 : Fin 1)) ((circleMarginal_integrable ρ i).aestronglyMeasurable.mul
          (hu.comp hdiag).aestronglyMeasurable)).symm
    _ = _ := by
      simp only [axisDensity_value, he]

/-- The Fourier coefficients of the circle marginal are the axis Fourier coefficients of `ρ`. -/
theorem axisDensity_fourier (ρ : ProbabilityDensity (n + 1)) (i : Fin (n + 1)) (k : ℤ) :
    fourierCoeff (axisDensity ρ i).value (fun _ => k) = fourierCoeff ρ.value (Pi.single i k) := by
  have hax (x : Torus (n + 1)) :
      UnitAddTorus.mFourier (-(Pi.single i k : Frequency (n + 1))) x =
        UnitAddTorus.mFourier (-(fun _ : Fin 1 => k)) (fun _ : Fin 1 => x i) := by
    rw [UnitAddTorus.mFourier_neg, UnitAddTorus.mFourier_neg, Legacy.D10.mFourier_single_int]
    congr 1
    simp [UnitAddTorus.mFourier]
  apply Complex.ext
  · have h1 := Legacy.TorusEndpoint.densityFourier_re_moment (Bridge.density (axisDensity ρ i))
      (fun _ => k)
    have h2 := Legacy.TorusEndpoint.densityFourier_re_moment (Bridge.density ρ)
      (Pi.single i k)
    have h := axisDensity_pairing ρ i
      (Legacy.TorusEndpoint.fourierRealFeature_measurable ((fun _ : Fin 1 => k), false))
      (Legacy.TorusEndpoint.fourierRealFeature_bound ((fun _ : Fin 1 => k), false))
    simp only [Legacy.TorusEndpoint.fourierRealFeature, Bool.false_eq_true, ite_false] at h
    have h2' : (∫ x, ρ.value x * ((UnitAddTorus.mFourier (-(Pi.single i k : Frequency (n + 1)))) x).re
        ∂torusMeasure (n + 1)) =
        ∫ x, ρ.value x * ((UnitAddTorus.mFourier (-(fun _ : Fin 1 => k))) (fun _ : Fin 1 => x i)).re
          ∂torusMeasure (n + 1) := by
      simp only [hax]
    exact h1.symm.trans (h.symm.trans (h2'.symm.trans h2))
  · have h1 := Legacy.TorusEndpoint.densityFourier_im_moment (Bridge.density (axisDensity ρ i))
      (fun _ => k)
    have h2 := Legacy.TorusEndpoint.densityFourier_im_moment (Bridge.density ρ)
      (Pi.single i k)
    have h := axisDensity_pairing ρ i
      (Legacy.TorusEndpoint.fourierRealFeature_measurable ((fun _ : Fin 1 => k), true))
      (Legacy.TorusEndpoint.fourierRealFeature_bound ((fun _ : Fin 1 => k), true))
    simp only [Legacy.TorusEndpoint.fourierRealFeature, ite_true] at h
    have h2' : (∫ x, ρ.value x * ((UnitAddTorus.mFourier (-(Pi.single i k : Frequency (n + 1)))) x).im
        ∂torusMeasure (n + 1)) =
        ∫ x, ρ.value x * ((UnitAddTorus.mFourier (-(fun _ : Fin 1 => k))) (fun _ : Fin 1 => x i)).im
          ∂torusMeasure (n + 1) := by
      simp only [hax]
    exact h1.symm.trans (h.symm.trans (h2'.symm.trans h2))

/-! ### Entropy -/

/-- The ambient-coordinate marginal of `ρ` on `{i}` is the circle marginal composed with the `i`-th
coordinate, pointwise. -/
theorem coordinateMarginal_singleton (ρ : ProbabilityDensity (n + 1)) (i : Fin (n + 1))
    (x : Torus (n + 1)) :
    coordinateMarginal ρ {i} x = circleMarginal ρ i (x i) := by
  unfold coordinateMarginal circleMarginal Legacy.D10.coordinateMarginal
  have hfun (y : Torus (n + 1)) :
      (fun j => if j ∈ ({i} : Finset (Fin (n + 1))) then x j else y j) =
        i.insertNth (x i) (CosineMixtureTransfer.drop i y) := by
    funext j
    by_cases hj : j = i
    · subst hj
      simp
    · obtain ⟨j', rfl⟩ := Fin.exists_succAbove_eq hj
      simp [CosineMixtureTransfer.drop, Fin.insertNth_apply_succAbove, hj]
  simp_rw [hfun]
  have h := CosineMixtureTransfer.integral_drop i (fun z => ρ.value (i.insertNth (x i) z))
  refine h.trans ?_
  simp [MeasurableEquiv.piFinSuccAbove_symm_apply]
  rfl

theorem circleMarginal_entropy_integrable (ρ : ProbabilityDensity (n + 1)) (i : Fin (n + 1))
    (hρ : ρ.FiniteEntropy) :
    Integrable (fun y => circleMarginal ρ i y * Real.log (circleMarginal ρ i y))
      AddCircle.haarAddCircle := by
  have hM := (circleMarginal_integrable ρ i).aestronglyMeasurable
  have hF : AEStronglyMeasurable (fun y => circleMarginal ρ i y * Real.log (circleMarginal ρ i y))
      (AddCircle.haarAddCircle : Measure UnitAddCircle) :=
    hM.mul (Real.measurable_log.comp_aemeasurable hM.aemeasurable).aestronglyMeasurable
  have h := (EntropyShearer.coordinateMarginal_finiteEntropy ρ hρ {i}).1
  simp_rw [coordinateMarginal_singleton] at h
  exact ((measurePreserving_eval (fun _ : Fin (n + 1) =>
    (AddCircle.haarAddCircle : Measure UnitAddCircle)) i).integrable_comp hF).mp h

theorem axisDensity_finiteEntropy (ρ : ProbabilityDensity (n + 1)) (i : Fin (n + 1))
    (hρ : ρ.FiniteEntropy) : (axisDensity ρ i).FiniteEntropy :=
  integrable_comp_eval (μ := fun _ : Fin 1 => (AddCircle.haarAddCircle : Measure UnitAddCircle))
    (i := 0) (f := fun y => circleMarginal ρ i y * Real.log (circleMarginal ρ i y))
    (circleMarginal_entropy_integrable ρ i hρ)

theorem axisDensity_entropy (ρ : ProbabilityDensity (n + 1)) (i : Fin (n + 1))
    (hρ : ρ.FiniteEntropy) :
    entropy (axisDensity ρ i) = coordinateMarginalEntropy ρ {i} := by
  have hF := (circleMarginal_entropy_integrable ρ i hρ).aestronglyMeasurable
  unfold entropy coordinateMarginalEntropy
  simp_rw [coordinateMarginal_singleton, axisDensity_value]
  exact (integral_comp_eval (μ := fun _ : Fin 1 => (AddCircle.haarAddCircle : Measure UnitAddCircle))
      (i := (0 : Fin 1)) (f := fun y => circleMarginal ρ i y * Real.log (circleMarginal ρ i y)) hF).trans
    (integral_comp_eval (μ := fun _ : Fin (n + 1) => (AddCircle.haarAddCircle : Measure UnitAddCircle))
      (i := i) (f := fun y => circleMarginal ρ i y * Real.log (circleMarginal ρ i y)) hF).symm

/-! ### The marginal bound -/

/-- The axis Fourier term `|ρ̂(j e_i)|² / j`, `j ≥ 1`, shifted to start at `0`. -/
def axisTerm {d : ℕ} (ρ : ProbabilityDensity d) (i : Fin d) (j : ℕ) : ℝ :=
  ‖fourierCoeff ρ.value (Pi.single i ((j : ℤ) + 1))‖ ^ 2 / ((j : ℝ) + 1)

theorem axisTerm_nonneg {d : ℕ} (ρ : ProbabilityDensity d) (i : Fin d) (j : ℕ) :
    0 ≤ axisTerm ρ i j :=
  div_nonneg (sq_nonneg _) (by positivity)

theorem circleTerm_axisDensity (ρ : ProbabilityDensity (n + 1)) (i : Fin (n + 1)) :
    circleTerm (axisDensity ρ i) = axisTerm ρ i := by
  funext j
  simp only [circleTerm, axisTerm, axisDensity_fourier]

/-- **`eq:circle-marginal-fourier-control`.**  For every finite-entropy density on `𝕋^d`,
`∑_i ∑_{j ≥ 1} |ρ̂(j e_i)|² / j ≤ ∑_i Ent(ρ_i) ≤ Ent(ρ)`. -/
theorem axis_marginal_bound {d : ℕ} (hd : 0 < d) (ρ : ProbabilityDensity d)
    (hρ : ρ.FiniteEntropy) :
    (∀ i : Fin d, Summable (axisTerm ρ i)) ∧
      ∑ i : Fin d, ∑' j, axisTerm ρ i j ≤ entropy ρ := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd.ne'
  have hcirc (i : Fin (n + 1)) :
      Summable (axisTerm ρ i) ∧ ∑' j, axisTerm ρ i j ≤ coordinateMarginalEntropy ρ {i} := by
    have h := lemma_3_2_finite (axisDensity ρ i) (axisDensity_finiteEntropy ρ i hρ)
    rw [circleTerm_axisDensity, ← entropy_eq_toReal_torusEntropy _ (axisDensity_finiteEntropy ρ i hρ),
      axisDensity_entropy ρ i hρ] at h
    exact h
  refine ⟨fun i => (hcirc i).1, ?_⟩
  have hsh := EntropyShearer.subset_entropy (d := n + 1) (r := 1) le_rfl (by omega) ρ hρ
  rw [Finset.powersetCard_one, Finset.sum_map] at hsh
  simp only [Nat.choose_one_right, Nat.cast_one, one_mul, ne_eq, Nat.cast_add, Nat.cast_one,
    Finset.sum_map, Function.Embedding.coeFn_mk] at hsh
  have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
  rw [div_self hn, one_mul] at hsh
  exact (Finset.sum_le_sum fun i _ => (hcirc i).2).trans hsh

#print axioms axis_marginal_bound

end BecknerOnofri.V2.Section3
