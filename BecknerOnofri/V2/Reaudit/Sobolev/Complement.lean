module

public import BecknerOnofri.V2.Reaudit.Sobolev.GibbsMap
public import BecknerOnofri.QuadraticModes
public import BecknerOnofri.LocalElevenContinuousInverse
public import BecknerOnofri.ContinuousComplement
public import BecknerOnofri.LocalElevenCore.GreenLocalBranch

@[expose] public section

/-! # The first-shell complement `K^⊥` inside the Sobolev Banach algebra `H^s`

Setup of the Lyapunov--Schmidt reduction of Section 5 (before `lem:section5-quartic-reduction`):
`K = span{cos 2π x_j, sin 2π x_j}`, `P_K`, and `K^⊥ = P_{K^⊥} H^s` (mean zero, first-shell Fourier
coefficients zero), realized as closed subspaces of the Banach algebra `Hs d s` of `Space.lean`:

* `HsC d s` : the closed subspace `K^⊥ ⊂ H^s_0`;
* `Hs.complMap : H^s → K^⊥` : `P_{K^⊥}` (kills the mean and the first shell);
* `Hs.assemblyH : ℂ^d → H^s` : the first-shell potential `v = Σ_j (z_j e^{2πi x_j} + conj)`;
* `Hs.reconstructionH (z, w) = v(z) + w`;
* `HsC.linearPart = P_{K^⊥} T|_{K^⊥}` and the explicit inverse multiplier of
  `Id - τ P_{K^⊥} T` on `K^⊥` (Fourier symbol `(1 - τ/|k|^d)^{-1}`, `|k|^d ≥ 2^{d/2}` on `K^⊥`),
  with the bound `16/15` for `d ≥ 11`, `0 ≤ τ ≤ 2`. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped ENNReal Topology

namespace BecknerOnofri.V2.Reaudit.Sobolev
open BecknerOnofri.HighDim ContinuousGibbs ContinuousFirstShell ContinuousComplement

variable {d : ℕ} {s : ℝ} [SobolevIndex d s]

/-! ## The subspace `K^⊥` -/

/-- `K^⊥ ⊂ H^s_0`: the closed subspace of `H^s` of mean-zero functions with vanishing first-shell
Fourier coefficients. -/
def HsC (d : ℕ) (s : ℝ) [SobolevIndex d s] : Submodule ℝ (Hs d s) :=
  Submodule.comap (Hs.toSpaceCLM d s : Hs d s →ₗ[ℝ] Space d) (complement d)

theorem HsC.mem_iff (u : Hs d s) : u ∈ HsC d s ↔ u.val ∈ complement d := Iff.rfl

theorem HsC.isClosed : IsClosed (HsC d s : Set (Hs d s)) :=
  (complement_closed d).preimage (Hs.toSpaceCLM d s).continuous

instance : CompleteSpace (HsC d s) := HsC.isClosed.completeSpace_coe

/-- The inclusion `K^⊥ ⊂ H^s ⊂ C(𝕋^d)` with values in the continuous complement. -/
def HsC.toComplement (d : ℕ) (s : ℝ) [SobolevIndex d s] : HsC d s →L[ℝ] complement d :=
  ((Hs.toSpaceCLM d s).comp (HsC d s).subtypeL).codRestrict (complement d) (fun w => w.property)

@[simp] theorem HsC.toComplement_val (w : HsC d s) :
    (HsC.toComplement d s w : Space d) = (w : Hs d s).val := rfl

/-! ## The projection `P_{K^⊥}` on `H^s` -/

theorem complementProjection_coeff_le (u : Space d) (k : Frequency d) :
    ‖coefficient k (complementProjection d u)‖ ≤ 1 * ‖coefficient k u‖ := by
  classical
  have h := QuadraticModes.complementMap_coefficient u k
  rw [complementMap_coe] at h
  rw [h, one_mul]
  split_ifs
  · exact le_rfl
  · simp

/-- `P_{K^⊥} f = f - ∫ f - P_K f` on `H^s` (`eq:section5-complement-projection`). -/
def Hs.complProj (d : ℕ) (s : ℝ) [SobolevIndex d s] : Hs d s →L[ℝ] Hs d s :=
  Hs.restrictCLM (complementProjection d) 1 zero_le_one complementProjection_coeff_le

@[simp] theorem Hs.complProj_val (u : Hs d s) :
    (Hs.complProj d s u).val = complementProjection d u.val := rfl

theorem Hs.complProj_mem (u : Hs d s) : Hs.complProj d s u ∈ HsC d s :=
  complementProjection_mem u.val

/-- `P_{K^⊥} : H^s → K^⊥`. -/
def Hs.complMap (d : ℕ) (s : ℝ) [SobolevIndex d s] : Hs d s →L[ℝ] HsC d s :=
  (Hs.complProj d s).codRestrict (HsC d s) Hs.complProj_mem

@[simp] theorem Hs.complMap_val (u : Hs d s) :
    ((Hs.complMap d s u : HsC d s) : Hs d s).val = complementProjection d u.val := rfl

theorem Hs.toComplement_complMap (u : Hs d s) :
    HsC.toComplement d s (Hs.complMap d s u) = complementMap d u.val := rfl

@[simp] theorem Hs.complMap_subtype (w : HsC d s) : Hs.complMap d s (w : Hs d s) = w := by
  apply Subtype.ext
  apply Hs.ext
  exact complementProjection_eq_self w.property

open scoped Classical in
theorem Hs.coeff_complMap (u : Hs d s) (k : Frequency d) :
    coefficient k ((Hs.complMap d s u : HsC d s) : Hs d s).val =
      if ComplementFrequency k then coefficient k u.val else 0 :=
  QuadraticModes.complementMap_coefficient u.val k

/-! ## The first-shell potential `v` as an element of `H^s` -/

theorem coefficient_assembly_off_shell (z : Coordinates d) (k : Frequency d)
    (hk : ¬ InFirstShell k) : coefficient k (assembly d z) = 0 := by
  have h := coefficient_projection_off_shell (assembly d z) k hk
  rwa [projection_assembly] at h

omit [SobolevIndex d s] in
theorem inSobolev_assembly (z : Coordinates d) : InSobolev s ⇑(assembly d z) := by
  classical
  rw [inSobolev_iff_memℓp, memℓp_gen_iff (by norm_num : (0:ℝ) < (2:ℝ≥0∞).toReal)]
  refine summable_of_ne_finset_zero
    (s := (Finset.univ.image axisFrequency) ∪ (Finset.univ.image fun i : Fin d => -axisFrequency i))
    fun k hk => ?_
  have hk' : ¬ InFirstShell k := by
    rintro ⟨i, h | h⟩
    · exact hk (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, h.symm⟩))
    · exact hk (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, h.symm⟩))
  simp [scaledCoeff, coefficient_assembly_off_shell z k hk']

/-- The first-shell potential `v(x) = Σ_j (z_j e^{2πi x_j} + conj)` as a linear map
`ℂ^d → H^s` (`eq:section5-first-shell-coordinates`). -/
def Hs.assemblyH (d : ℕ) (s : ℝ) [SobolevIndex d s] : Coordinates d →L[ℝ] Hs d s :=
  LinearMap.toContinuousLinearMap
    { toFun := fun z => Hs.mk (assembly d z) (inSobolev_assembly z)
      map_add' := fun z w => Hs.ext (by simp)
      map_smul' := fun c z => Hs.ext (by simp) }

@[simp] theorem Hs.assemblyH_val (z : Coordinates d) :
    (Hs.assemblyH d s z).val = assembly d z := rfl

/-- `(z, w) ↦ v(z) + w`. -/
def Hs.reconstructionH (d : ℕ) (s : ℝ) [SobolevIndex d s] : Coordinates d × HsC d s →L[ℝ] Hs d s :=
  (Hs.assemblyH d s).comp (ContinuousLinearMap.fst ℝ _ _) +
    (HsC d s).subtypeL.comp (ContinuousLinearMap.snd ℝ _ _)

@[simp] theorem Hs.reconstructionH_apply (z : Coordinates d) (w : HsC d s) :
    Hs.reconstructionH d s (z, w) = Hs.assemblyH d s z + (w : Hs d s) := rfl

theorem Hs.reconstructionH_val (x : Coordinates d × HsC d s) :
    (Hs.reconstructionH d s x).val = reconstruction d (x.1, HsC.toComplement d s x.2) := rfl

@[simp] theorem Hs.meanCLM_reconstructionH (x : Coordinates d × HsC d s) :
    Hs.meanCLM d s (Hs.reconstructionH d s x) = 0 := by
  rw [Hs.meanCLM_apply, Hs.reconstructionH_val]
  exact mean_reconstruction _

@[simp] theorem Hs.center_reconstructionH (x : Coordinates d × HsC d s) :
    Hs.center d s (Hs.reconstructionH d s x) = Hs.reconstructionH d s x := by
  rw [Hs.center_apply, Hs.meanCLM_reconstructionH, zero_smul, sub_zero]

/-- The first-shell part of `T v` is `v` itself, so `P_{K^⊥} T v = 0` for `v ∈ K`. -/
theorem Hs.complMap_greenH_assemblyH (z : Coordinates d) :
    Hs.complMap d s (Hs.greenH d s (Hs.assemblyH d s z)) = 0 := by
  apply Subtype.ext
  apply Hs.ext
  simp only [Hs.complMap_val, Hs.greenH_val, Hs.assemblyH_val]
  have h := LocalEleven.GreenLocalBranch.green_first_complement_zero (SobolevIndex.hd d s) z
  exact congrArg (fun w : complement d => (w : Space d)) h

/-! ## The linearization on `K^⊥` and its explicit inverse multiplier -/

/-- The linear part `P_{K^⊥} T|_{K^⊥}` of the complement equation. -/
def HsC.linearPart (d : ℕ) (s : ℝ) [SobolevIndex d s] : HsC d s →L[ℝ] HsC d s :=
  (Hs.complMap d s).comp ((Hs.greenH d s).comp (HsC d s).subtypeL)

theorem HsC.toComplement_linearPart (w : HsC d s) :
    HsC.toComplement d s (HsC.linearPart d s w) =
      ContinuousComplement.linearPart (greenContinuous d) (HsC.toComplement d s w) := rfl

theorem HsC.linearPart_val (w : HsC d s) :
    ((HsC.linearPart d s w : HsC d s) : Hs d s).val = greenContinuous d (w : Hs d s).val := by
  show complementProjection d (greenContinuous d (w : Hs d s).val) = _
  exact complementProjection_eq_self (greenContinuous_mem_complement (SobolevIndex.hd d s) ⟨_, w.property⟩)

section Inverse
variable (hd11 : 11 ≤ d) {μ : ℝ} (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2)
include hd11 hμ0 hμ2

/-- The explicit inverse of `Id - P_{K^⊥} T` on the continuous complement, extended by `0` to
`C(𝕋^d)` (via `P_{K^⊥}`). -/
def complInvC : Space d →L[ℝ] Space d :=
  (complement d).subtypeL.comp
    (((LocalEleven.continuousComplementContinuousLinearEquiv hd11 hμ0 hμ2).symm : complement d →L[ℝ] complement d).comp (complementMap d))

theorem coefficient_complInvC (f : Space d) (k : Frequency d) :
    coefficient k (complInvC hd11 hμ0 hμ2 f) =
      (complementInverseMultiplier μ k : ℂ) * coefficient k f := by
  classical
  have h := LocalEleven.continuousComplementInverseValue_fourier hd11 hμ0 hμ2 (complementMap d f) k
  change coefficient k (LocalEleven.continuousComplementInverseValue hd11 hμ0 hμ2 (complementMap d f)) = _
  rw [h]
  change (complementInverseMultiplier μ k : ℂ) *
    coefficient k (complementMap d f).val = _
  rw [QuadraticModes.complementMap_coefficient]
  by_cases hk : ComplementFrequency k
  · simp [hk]
  · simp [hk, complementInverseMultiplier]

theorem complInvC_coeff_le (f : Space d) (k : Frequency d) :
    ‖coefficient k (complInvC hd11 hμ0 hμ2 f)‖ ≤ (16/15 : ℝ) * ‖coefficient k f‖ := by
  rw [coefficient_complInvC, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (LocalEleven.complementInverseMultiplier_nonneg hd11 hμ0 hμ2 k)]
  exact mul_le_mul_of_nonneg_right
    (LocalEleven.complementInverseMultiplier_bound hd11 hμ0 hμ2 k)
    (norm_nonneg _)

/-- The inverse multiplier on `H^s`. -/
def Hs.complInv : Hs d s →L[ℝ] Hs d s :=
  Hs.restrictCLM (complInvC hd11 hμ0 hμ2) (16/15) (by norm_num) (complInvC_coeff_le hd11 hμ0 hμ2)

theorem Hs.complInv_mem (w : HsC d s) : Hs.complInv hd11 hμ0 hμ2 (w : Hs d s) ∈ HsC d s := by
  change (complInvC hd11 hμ0 hμ2 (w : Hs d s).val) ∈ complement d
  exact Subtype.property _

/-- `(Id - P_{K^⊥} T)^{-1}` on `K^⊥`: the Fourier multiplier of symbol `(1 - |k|^{-d})^{-1}`,
bounded by `16/15` for `d ≥ 11`. -/
def HsC.inverse : HsC d s →L[ℝ] HsC d s :=
  ((Hs.complInv hd11 hμ0 hμ2 : Hs d s →L[ℝ] Hs d s).comp (HsC d s).subtypeL).codRestrict (HsC d s)
    (Hs.complInv_mem hd11 hμ0 hμ2)

theorem HsC.inverse_val (w : HsC d s) :
    ((HsC.inverse hd11 hμ0 hμ2 w : HsC d s) : Hs d s).val =
      ((LocalEleven.continuousComplementContinuousLinearEquiv hd11 hμ0 hμ2).symm (HsC.toComplement d s w) : Space d) := by
  show complInvC hd11 hμ0 hμ2 (w : Hs d s).val = _
  show ((LocalEleven.continuousComplementContinuousLinearEquiv hd11 hμ0 hμ2).symm (complementMap d (w : Hs d s).val) : Space d) = _
  congr 2
  exact complementMap_subtype (⟨(w : Hs d s).val, w.property⟩ : complement d)

theorem HsC.coeff_inverse (w : HsC d s) (k : Frequency d) :
    coefficient k ((HsC.inverse hd11 hμ0 hμ2 w : HsC d s) : Hs d s).val =
      (complementInverseMultiplier μ k : ℂ) * coefficient k (w : Hs d s).val :=
  coefficient_complInvC hd11 hμ0 hμ2 _ k

/-- The continuous complement isomorphism `Id - P_{K^⊥} G` (`μ = 1`) of the continuous-function
development, used only to transport the inverse-multiplier identities. -/
def complEquivC : complement d ≃L[ℝ] complement d :=
  LocalEleven.continuousComplementContinuousLinearEquiv hd11 hμ0 hμ2

theorem HsC.toComplement_forward (w : HsC d s) :
    HsC.toComplement d s (w - μ • HsC.linearPart d s w) =
      complEquivC hd11 hμ0 hμ2 (HsC.toComplement d s w) := by
  have h1 := LocalEleven.continuousComplementContinuousLinearEquiv_toCLM hd11 hμ0 hμ2
  have h2 := congrArg (fun F : complement d →L[ℝ] complement d => F (HsC.toComplement d s w)) h1
  have h3 := LocalEleven.GreenLocalBranch.linearPart_eq (SobolevIndex.hd d s)
  change complEquivC hd11 hμ0 hμ2 (HsC.toComplement d s w) =
    HsC.toComplement d s w - μ • continuousComplementGreen (SobolevIndex.hd d s) (HsC.toComplement d s w)
    at h2
  rw [h2, ← h3, map_sub, map_smul, HsC.toComplement_linearPart]

omit hd11 hμ0 hμ2 in
theorem HsC.toComplement_injective : Function.Injective (HsC.toComplement d s) := by
  intro u v h
  apply Subtype.ext
  apply Hs.ext
  have h' := congrArg (fun x : complement d => (x : Space d)) h
  exact h'

/-- **`Id - P_{K^⊥} T` is a Banach-space isomorphism of `K^⊥ ⊂ H^s`**, with the explicit inverse
multiplier `HsC.inverse` of symbol `(1 - |k|^{-d})^{-1}` (`≤ 16/15` for `d ≥ 11`). -/
def HsC.equiv : HsC d s ≃L[ℝ] HsC d s where
  toLinearEquiv :=
    { toFun := fun w => w - μ • HsC.linearPart d s w
      invFun := HsC.inverse hd11 hμ0 hμ2
      left_inv := fun w => by
        apply Subtype.ext
        apply Hs.ext
        rw [HsC.inverse_val, HsC.toComplement_forward hd11 hμ0 hμ2]
        exact congrArg Subtype.val ((complEquivC hd11 hμ0 hμ2).symm_apply_apply _)
      right_inv := fun w => by
        apply HsC.toComplement_injective
        rw [HsC.toComplement_forward hd11 hμ0 hμ2]
        have : HsC.toComplement d s (HsC.inverse hd11 hμ0 hμ2 w) = (complEquivC hd11 hμ0 hμ2).symm (HsC.toComplement d s w) :=
          Subtype.ext (HsC.inverse_val hd11 hμ0 hμ2 w)
        rw [this]
        exact (complEquivC hd11 hμ0 hμ2).apply_symm_apply _
      map_add' := fun u v => by simp [sub_add_sub_comm]
      map_smul' := fun c u => by simp [smul_sub, smul_comm μ c] }
  continuous_toFun := (ContinuousLinearMap.id ℝ (HsC d s) - μ • HsC.linearPart d s).continuous
  continuous_invFun := (HsC.inverse hd11 hμ0 hμ2).continuous

@[simp] theorem HsC.equiv_apply (w : HsC d s) : HsC.equiv hd11 hμ0 hμ2 w = w - μ • HsC.linearPart d s w := rfl

end Inverse

end BecknerOnofri.V2.Reaudit.Sobolev
