module

public import BecknerOnofri.V2.Reaudit.SobolevQuartic.Expansion
public import BecknerOnofri.LocalElevenCore.FirstShellOrbits
public import BecknerOnofri.LocalElevenCore.CorrectionSymmetry

@[expose] public section

/-! # Half-period translation symmetry of the `H^s` graph

The manuscript's last paragraph of the proof of `lem:section5-quartic-reduction` uses that
`Ψ_{d,τ}` is analytic in `r` ("analyticity in `r` excludes odd degrees in `(z, z̄)`").  The
symmetry behind this is the torus action: translation of `𝕋^d` multiplies `z_j` by the character
phase and permutes nothing else.  Here it is implemented natively on `H^s` for the half-period
translation `x ↦ x + (½,…,½)` (`z ↦ -z`):

* `translH a` : translation as a bounded operator on `H^s` (restriction of the sup-norm isometry
  `ContinuousSymmetry.translation a`; it is a ring automorphism, preserves the mean, commutes with
  `exp`, the partition function and the Gibbs map);
* `translC a` : its restriction to `K^⊥`; it commutes with `P_{K^⊥} T`, hence with the complement
  equation (`complementEq_transl`);
* `graph_half` : by the *Sobolev* local uniqueness `graph_unique`,
  `w(1, -z) = translation(w(1, z))`;
* `Lfun_half` / `theta_one_even` : `Θ(1,-z) = Θ(1,z)`. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter Asymptotics
open scoped ENNReal Topology

namespace BecknerOnofri.V2.Reaudit.SobolevQuartic
open BecknerOnofri.V2.Reaudit.Sobolev BecknerOnofri.HighDim ContinuousGibbs ContinuousFirstShell
  ContinuousComplement BecknerOnofri.HighDim.ContinuousSymmetry

variable {d : ℕ} {s : ℝ} [SobolevIndex d s]

theorem translation_coeff_le (a : Torus d) (u : Space d) (k : Frequency d) :
    ‖coefficient k (translation a u)‖ ≤ 1 * ‖coefficient k u‖ := by
  rw [coefficient_translation, norm_mul, BecknerOnofri.HighDim.mFourier_norm_apply, one_mul]

/-- Translation as a bounded operator on `H^s`. -/
def translH (a : Torus d) : Hs d s →L[ℝ] Hs d s :=
  Hs.restrictCLM ((translation a).toContinuousLinearEquiv : Space d →L[ℝ] Space d) 1 zero_le_one
    (translation_coeff_le a)

@[simp] theorem translH_val (a : Torus d) (u : Hs d s) :
    (translH a u).val = translation a u.val := rfl

theorem translH_mul (a : Torus d) (u v : Hs d s) :
    translH a (u * v) = translH a u * translH a v := Hs.ext rfl

@[simp] theorem translH_one (a : Torus d) : translH a (1 : Hs d s) = 1 :=
  Hs.ext (translation_one a)

theorem translH_pow (a : Torus d) (u : Hs d s) (n : ℕ) : translH a (u ^ n) = (translH a u) ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, translH_mul, ih, pow_succ]

theorem meanCLM_translH (a : Torus d) (u : Hs d s) :
    Hs.meanCLM d s (translH a u) = Hs.meanCLM d s u := by
  rw [Hs.meanCLM_apply, Hs.meanCLM_apply, translH_val, mean_translation]

theorem translH_exp (a : Torus d) (u : Hs d s) :
    translH a (NormedSpace.exp u) = NormedSpace.exp (translH a u) := by
  apply Hs.ext
  rw [translH_val, Hs.val_exp, Hs.val_exp, translH_val, exponential_translation]

theorem partition_translH (a : Torus d) (u : Hs d s) :
    Hs.partition (translH a u) = Hs.partition u := by
  unfold Hs.partition
  rw [← translH_exp, meanCLM_translH]

theorem gibbs_translH (a : Torus d) (u : Hs d s) :
    Hs.gibbs (translH a u) = translH a (Hs.gibbs u) := by
  unfold Hs.gibbs
  rw [partition_translH, map_smul, translH_exp]

theorem logZ_translH (a : Torus d) (u : Hs d s) : logZ (translH a u) = logZ u := by
  unfold logZ
  rw [partition_translH]

theorem translH_assemblyH (a : Torus d) (z : Coordinates d) :
    translH a (Hs.assemblyH d s z) = Hs.assemblyH d s (phaseCoordinates a z) :=
  Hs.ext (translation_assembly a z)

theorem translH_mem (a : Torus d) {u : Hs d s} (hu : u ∈ HsC d s) : translH a u ∈ HsC d s := by
  rw [HsC.mem_iff] at hu ⊢
  rw [translH_val]
  exact (translation_mem_complement_iff a _).mpr hu

/-- Translation on `K^⊥ ⊂ H^s`. -/
def translC (a : Torus d) : HsC d s →L[ℝ] HsC d s :=
  ((translH a : Hs d s →L[ℝ] Hs d s).comp (HsC d s).subtypeL).codRestrict (HsC d s)
    (fun w => translH_mem a w.property)

@[simp] theorem translC_coe (a : Torus d) (w : HsC d s) :
    ((translC a w : HsC d s) : Hs d s) = translH a (w : Hs d s) := rfl

theorem cmG_translH (a : Torus d) (u : Hs d s) :
    cmG d s (translH a u) = translC a (cmG d s u) := by
  apply Subtype.ext
  apply Hs.ext
  simp only [cmG_apply, Hs.complMap_val, Hs.greenH_val, translC_coe, translH_val]
  rw [BecknerOnofri.HighDim.LocalEleven.ContinuousSymmetry.green_translation (SobolevIndex.hd d s),
    complementProjection_translation]

/-- The complement equation is covariant under translation. -/
theorem complementEq_transl (τ : ℝ) (a : Torus d) (z : Coordinates d) (w : HsC d s) :
    complementEq d s τ (phaseCoordinates a z) (translC a w) = translC a (complementEq d s τ z w) := by
  unfold complementEq
  have h1 : Hs.reconstructionH d s (phaseCoordinates a z, translC a w) =
      translH a (Hs.reconstructionH d s (z, w)) := by
    rw [Hs.reconstructionH_apply, Hs.reconstructionH_apply, map_add, translH_assemblyH, translC_coe]
  rw [h1, gibbs_translH]
  have h2 : translH a (Hs.gibbs (Hs.reconstructionH d s (z, w))) - 1 =
      translH a (Hs.gibbs (Hs.reconstructionH d s (z, w)) - 1) := by
    rw [map_sub, translH_one]
  rw [h2]
  simp only [← cmG_apply, cmG_translH, map_sub, map_smul]

/-! ## The half period -/

/-- The half-period translation `x ↦ x + (½, …, ½)`. -/
def halfT (d : ℕ) : Torus d := BecknerOnofri.HighDim.LocalEleven.ContinuousSymmetry.allHalfTranslation d

theorem phase_half (z : Coordinates d) : phaseCoordinates (halfT d) z = -z :=
  BecknerOnofri.HighDim.LocalEleven.ContinuousSymmetry.phase_allHalfTranslation z

theorem translH_half_assemblyH (z : Coordinates d) :
    translH (halfT d) (Hs.assemblyH d s z) = Hs.assemblyH d s (-z) := by
  rw [translH_assemblyH, phase_half]

/-- **Symmetry of the graph**: `w(1, -z) = T_{½} w(1, z)` near `z = 0`, by the local uniqueness
in `H^s`. -/
theorem graph_half (hd11 : 11 ≤ d) :
    ∀ᶠ z in 𝓝 (0 : Coordinates d),
      graph (s := s) hd11 (1, -z) = translC (halfT d) (graph (s := s) hd11 (1, z)) := by
  have hz : Tendsto (fun z : Coordinates d => ((1 : ℝ), z)) (𝓝 0) (𝓝 (1, 0)) :=
    (continuous_const.prodMk continuous_id).tendsto' _ _ (by simp)
  have hg : Tendsto (fun z : Coordinates d => graph (s := s) hd11 (1, z)) (𝓝 0) (𝓝 0) := by
    have := ((graph_analytic (s := s) hd11).continuousAt.tendsto).comp hz
    rw [graph_base] at this
    exact this
  have hgt : Tendsto (fun z : Coordinates d => translC (halfT d) (graph (s := s) hd11 (1, z)))
      (𝓝 0) (𝓝 0) := by
    have := ((translC (halfT d) : HsC d s →L[ℝ] HsC d s).continuous.tendsto 0).comp hg
    rw [map_zero] at this
    exact this
  have hpt : Tendsto (fun z : Coordinates d =>
      (((1 : ℝ), -z), translC (halfT d) (graph (s := s) hd11 (1, z))))
      (𝓝 0) (𝓝 (((1 : ℝ), (0 : Coordinates d)), (0 : HsC d s))) := by
    have h1 : Tendsto (fun z : Coordinates d => ((1 : ℝ), -z)) (𝓝 0) (𝓝 (1, 0)) :=
      (continuous_const.prodMk continuous_neg).tendsto' _ _ (by simp)
    exact h1.prodMk_nhds hgt
  filter_upwards [hpt.eventually (graph_unique (s := s) hd11), hz.eventually (graph_solves (s := s) hd11)]
    with z hu hs
  apply hu.mp
  have := complementEq_transl (s := s) 1 (halfT d) z (graph (s := s) hd11 (1, z))
  rw [phase_half] at this
  rw [this]
  have hs' : complementEq d s 1 z (graph (s := s) hd11 (1, z)) = 0 := hs
  rw [hs', map_zero]

theorem mass_neg (z : Coordinates d) :
    LocalReductionStatement.mass (-z) = LocalReductionStatement.mass z := by
  simp [LocalReductionStatement.mass]

/-- **Half-period invariance of the Euler-form functional**: `L_{-z}(T_{½} w) = L_z(w)`. -/
theorem Lfun_half (z : Coordinates d) (w : Hs d s) :
    Lfun (-z) (translH (halfT d) w) = Lfun z w := by
  unfold Lfun
  have h1 : Hs.assemblyH d s (-z) + translH (halfT d) w = translH (halfT d) (Hs.assemblyH d s z + w) := by
    rw [map_add, translH_half_assemblyH]
  rw [h1, logZ_translH, gibbs_translH, mass_neg, ← translH_mul, meanCLM_translH]

/-- **`Θ(1, -z) = Θ(1, z)`** near `z = 0`: the reduced functional is even on the slice `τ = 1`. -/
theorem theta_one_even (hd11 : 11 ≤ d) :
    ∀ᶠ z in 𝓝 (0 : Coordinates d),
      Lfun (-z) (wS (s := s) hd11 (-z)) = Lfun z (wS (s := s) hd11 z) := by
  filter_upwards [graph_half (s := s) hd11] with z hz
  have : wS (s := s) hd11 (-z) = translH (halfT d) (wS (s := s) hd11 z) := by
    unfold wS
    rw [hz]
    rfl
  rw [this, Lfun_half]

end BecknerOnofri.V2.Reaudit.SobolevQuartic
