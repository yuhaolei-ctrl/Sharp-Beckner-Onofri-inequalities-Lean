module

public import BecknerOnofri.CommonCubicPaper
public import BecknerOnofri.OptimizerTranslation
public import BecknerOnofri.FullHessianDecomposition
public import BecknerOnofri.PartitionRegularity
public import BecknerOnofri.V2.Transfer.Characters

@[expose] public section

/-! # Lemma 5.9: symmetry of maximizers (`lem:common-cubic`, S041)

Source statement: every smooth global maximizer `u ∈ H_0^{d/2}(𝕋^d)` of
`Φ(u) = log Z(u) - ‖u‖²_{Ḣ^{d/2}} / (2 (2π)^d)` with nonnegative Fourier coefficients satisfies
`u(ε_1 x_{σ(1)},…,ε_d x_{σ(d)}) = u(x)` for all signs `ε` and permutations `σ`.

The repository theorem `HighDim.CosineCoefficientLattice.smooth_optimizer_signed_permutation` has the
same conclusion for a smooth `u ∈ H^{d/2}`, mean zero, with nonnegative real Fourier coefficients that
maximizes `dualFunctional β` over **all** of `H^{d/2}` (not only the mean-zero subspace), for any `β > 0`.
Here `Φ = dualFunctional β_s` on `H_0^{d/2}` (`Phi_eq_dualFunctional`) and `dualFunctional` is invariant
under subtracting the mean (`dualFunctional_centered`), which bridges the two comparison classes.  No
symmetry hypothesis is imposed on `u`.  `common_cubic_symmetry_translate` is the translation-allowed
form. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

namespace BecknerOnofri.V2.Transfer
open BecknerOnofri.HighDim

/-- `Φ(u) = log Z(u) - ‖u‖²_{Ḣ^{d/2}} / (2 (2π)^d)`, with the repository normalizations
(`logPartition u = log ∫ e^{u - ū}`, which is `log Z(u)` for mean-zero `u`, and
`potentialEnergy u = ‖u‖²_{Ḣ^{d/2}} = ∑_{k≠0} (2π|k|)^d |û(k)|²`). -/
def Phi (d : ℕ) (u : Torus d → ℝ) : EReal :=
  logPartition u - ((1 / (2 * (2 * Real.pi) ^ d) * potentialEnergy u : ℝ) : EReal)

/-- For mean-zero `u`, `logPartition u` is literally `log ∫ e^u`. -/
theorem logPartition_of_meanZero {d : ℕ} {u : Torus d → ℝ} (hm : MeanZero u) :
    logPartition u = ENNReal.log (∫⁻ x, ENNReal.ofReal (Real.exp (u x)) ∂torusMeasure d) := by
  unfold logPartition centered
  have : ∀ x, u x - ∫ y, u y ∂torusMeasure d = u x := by
    intro x; rw [show (∫ y, u y ∂torusMeasure d) = 0 from hm, sub_zero]
  simp only [this]

/-- `Φ` is the repository's `dualFunctional` at the spectral coupling `β_s(d)`. -/
theorem Phi_eq_dualFunctional {d : ℕ} (hd : 0 < d) (u : Torus d → ℝ) :
    Phi d u = dualFunctional (spectralThreshold d) u := by
  have hσ := spectralThreshold_pos hd
  unfold Phi dualFunctional normalizedPotentialEnergy
  have : (1 / (2 * (2 * Real.pi) ^ d) * potentialEnergy u : ℝ) =
      spectralThreshold d / (2 * spectralThreshold d) * (potentialEnergy u / (2 * Real.pi) ^ d) := by
    field_simp
  rw [this]

/-- The domain `H_0^{d/2}(𝕋^d)`. -/
def InH0 (d : ℕ) (u : Torus d → ℝ) : Prop := InCriticalSobolev u ∧ MeanZero u

/-- `u` is a global maximizer of `Φ` on `H_0^{d/2}(𝕋^d)`. -/
def IsPhiMaximizer (d : ℕ) (u : Torus d → ℝ) : Prop :=
  InH0 d u ∧ ∀ v : Torus d → ℝ, InH0 d v → Phi d v ≤ Phi d u

lemma fourierCoeff_const_nonzero {d : ℕ} (c : ℝ) (k : Frequency d) (hk : k ≠ 0) :
    HighDim.fourierCoeff (fun _ : Torus d => c) k = 0 := by
  unfold HighDim.fourierCoeff
  have : ∀ x : Torus d, UnitAddTorus.mFourier (-k) x * ((c : ℝ) : ℂ) =
      ((c : ℝ) : ℂ) * UnitAddTorus.mFourier (-k) x := fun x => mul_comm _ _
  simp_rw [this]
  rw [integral_const_mul, integral_mFourier]
  simp [hk]

lemma fourierCoeff_centered {d : ℕ} {u : Torus d → ℝ} (hu : MemLp u 2 (torusMeasure d))
    (k : Frequency d) (hk : k ≠ 0) :
    HighDim.fourierCoeff (centered u) k = HighDim.fourierCoeff u k := by
  have h := FullHessianDecomposition.fourierCoeff_sub u (fun _ => ∫ y, u y ∂torusMeasure d) hu (memLp_const _) k
  rw [fourierCoeff_const_nonzero _ k hk, sub_zero] at h
  exact h

lemma potentialEnergy_centered {d : ℕ} {u : Torus d → ℝ} (hu : MemLp u 2 (torusMeasure d)) :
    potentialEnergy (centered u) = potentialEnergy u := by
  unfold potentialEnergy
  refine tsum_congr (fun k => ?_)
  simp only [potentialTerm, fourierCoeff_centered hu k.1 k.2]

lemma inH0_centered {d : ℕ} {u : Torus d → ℝ} (hu : InCriticalSobolev u) :
    InH0 d (centered u) := by
  have hi : Integrable u (torusMeasure d) := hu.1.integrable (by norm_num)
  refine ⟨⟨?_, ?_⟩, centered_integral u hi⟩
  · exact hu.1.sub (memLp_const _)
  · have : potentialTerm (centered u) = potentialTerm u := by
      funext k
      simp only [potentialTerm, fourierCoeff_centered hu.1 k.1 k.2]
    rw [this]
    exact hu.2

theorem dualFunctional_centered {d : ℕ} (β : ℝ) {u : Torus d → ℝ} (hu : InCriticalSobolev u) :
    dualFunctional β (centered u) = dualFunctional β u := by
  have hi : Integrable u (torusMeasure d) := hu.1.integrable (by norm_num)
  have hlog : logPartition (centered u) = logPartition u := by
    unfold logPartition centered
    rw [show (∫ y, (u y - ∫ z, u z ∂torusMeasure d) ∂torusMeasure d) = 0 from
      centered_integral u hi]
    simp only [sub_zero]
  unfold dualFunctional normalizedPotentialEnergy
  rw [hlog, potentialEnergy_centered hu.1]

/-- A maximizer of `Φ` on `H_0^{d/2}` is a maximizer of `dualFunctional β_s` on all of `H^{d/2}`. -/
theorem dualFunctional_max_of_phiMaximizer {d : ℕ} (hd : 0 < d) {u : Torus d → ℝ}
    (hmax : IsPhiMaximizer d u) :
    ∀ v : Torus d → ℝ, InCriticalSobolev v →
      dualFunctional (spectralThreshold d) v ≤ dualFunctional (spectralThreshold d) u := by
  intro v hv
  have h := hmax.2 (centered v) (inH0_centered hv)
  rw [Phi_eq_dualFunctional hd, Phi_eq_dualFunctional hd, dualFunctional_centered _ hv] at h
  exact h

/-- **Lemma 5.9.**  Every smooth global maximizer `u ∈ H_0^{d/2}(𝕋^d)` of `Φ` with nonnegative
Fourier coefficients is invariant under all signed permutations of the coordinates. -/
theorem common_cubic_symmetry {d : ℕ} (hd : 0 < d) {u : Torus d → ℝ}
    (hmax : IsPhiMaximizer d u) (hs : SmoothOnTorus u)
    (hN : ∀ k : Frequency d, (fourierCoeff u k).im = 0 ∧ 0 ≤ (fourierCoeff u k).re)
    (σ : Equiv.Perm (Fin d)) (ε : Fin d → ℤ) (hε : ∀ i, ε i = 1 ∨ ε i = -1) (x : Torus d) :
    u (fun i => ε i • x (σ i)) = u x :=
  CosineCoefficientLattice.smooth_optimizer_signed_permutation hd (spectralThreshold_pos hd) u
    hmax.1.1 hmax.1.2 hs hN (dualFunctional_max_of_phiMaximizer hd hmax) σ ε hε x

/-- Translation preserves smoothness. -/
theorem smoothOnTorus_translate {d : ℕ} {u : Torus d → ℝ} (hs : SmoothOnTorus u) (a : Torus d) :
    SmoothOnTorus (translate u a) := by
  obtain ⟨t, ht⟩ : ∃ t : Fin d → ℝ, a = fun j => (t j : UnitAddCircle) := by
    refine ⟨fun j => (a j).out, ?_⟩
    funext j
    exact (QuotientAddGroup.out_eq' (a j)).symm
  unfold SmoothOnTorus at hs ⊢
  have : (fun x : Fin d → ℝ => translate u a (fun j => (x j : UnitAddCircle))) =
      (fun x : Fin d → ℝ => u (fun j => (x j : UnitAddCircle))) ∘ (fun x => x - t) := by
    funext x
    simp only [translate, Function.comp, ht]
    congr 1
  rw [this]
  exact hs.comp (contDiff_id.sub contDiff_const)

/-- **Lemma 5.9, translation-allowed form.**  If `u` is a smooth global maximizer of `Φ` on
`H_0^{d/2}` and some translate `x ↦ u(x - a)` has nonnegative Fourier coefficients, then this
translate is invariant under all signed permutations. -/
theorem common_cubic_symmetry_translate {d : ℕ} (hd : 0 < d) {u : Torus d → ℝ}
    (hmax : IsPhiMaximizer d u) (hs : SmoothOnTorus u) (a : Torus d)
    (hN : ∀ k : Frequency d,
      (fourierCoeff (translate u a) k).im = 0 ∧ 0 ≤ (fourierCoeff (translate u a) k).re)
    (σ : Equiv.Perm (Fin d)) (ε : Fin d → ℤ) (hε : ∀ i, ε i = 1 ∨ ε i = -1) (x : Torus d) :
    translate u a (fun i => ε i • x (σ i)) = translate u a x := by
  have hmax' : IsPhiMaximizer d (translate u a) := by
    refine ⟨⟨(inCriticalSobolev_translate_iff u a).mpr hmax.1.1,
      (meanZero_translate_iff u a).mpr hmax.1.2⟩, fun v hv => ?_⟩
    rw [Phi_eq_dualFunctional hd, Phi_eq_dualFunctional hd]
    rw [dualFunctional_translate]
    have := hmax.2 v hv
    rwa [Phi_eq_dualFunctional hd, Phi_eq_dualFunctional hd] at this
  exact common_cubic_symmetry hd hmax' (smoothOnTorus_translate hs a) hN σ ε hε x

end BecknerOnofri.V2.Transfer
