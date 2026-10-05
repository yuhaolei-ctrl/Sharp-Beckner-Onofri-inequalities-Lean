import BecknerOnofri.DiagonalProfile
import BecknerOnofri.GraphAllSobolevBounds

/-! The genuine physical diagonal branch has its trusted leading profile
in every Sobolev norm, uniformly over all torus translations. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter Asymptotics
open scoped Topology BigOperators
namespace BecknerOnofri.HighDim.DiagonalScalarBranch
open ContinuousGibbs ContinuousFirstShell ContinuousComplement GreenLocalBranch ReducedEquation
open ReducedCubicExpansion GraphRegularity GraphWienerBounds GraphAllSobolevBounds
open BecknerOnofri.OnsetWienerBounds

/-- The profile error before converting normalized parameter μ to physical β. -/
def normalizedProfileRemainder {d : ℕ} (hd : 12 ≤ d) (μ : ℝ) : Space d :=
  branchPotential hd (amplitude hd μ)-assembly d (realDiagonal d (Real.sqrt (onset μ/kappa d)))

theorem normalizedProfileRemainder_split {d : ℕ} (hd : 12 ≤ d) (μ : ℝ) :
    normalizedProfileRemainder hd μ =
      assembly d (realDiagonal d (amplitude hd μ-Real.sqrt (onset μ/kappa d))) +
        (correction hd (parameter hd (amplitude hd μ),realDiagonal d (amplitude hd μ)) : Space d) := by
  simp only [normalizedProfileRemainder,branchPotential,potential,reconstruction_apply,map_sub]
  abel

theorem normalizedProfileRemainder_radial {d : ℕ} (hd : 12 ≤ d) (m : ℕ) :
    ∀ᶠ μ in 𝓝[>] (1:ℝ), Radial m (normalizedProfileRemainder hd μ) := by
  have he := (((branch_coordinates_tendsto hd).comp (amplitude_tendsto hd)).eventually (correction_solves hd))
  filter_upwards [he] with μ he
  rw [normalizedProfileRemainder_split]
  exact radial_add m _ _ (radial_assembly m _)
    (correction_radial (by omega) _ _ _ he m)

theorem normalizedProfileRemainder_wiener_bound {d : ℕ} (hd : 12 ≤ d) (m : ℕ) :
    (fun μ => wienerSize m (normalizedProfileRemainder hd μ)) =O[𝓝[>] (1:ℝ)] onset := by
  have hlin0 : (fun μ => realDiagonal d (amplitude hd μ-Real.sqrt (onset μ/kappa d)))
      =O[𝓝[>] (1:ℝ)] onset :=
    ((realDiagonal d).isBigO_comp _ _).trans (amplitude_sqrt_bound hd)
  have hlin : (fun μ => wienerSize m (assembly d
      (realDiagonal d (amplitude hd μ-Real.sqrt (onset μ/kappa d)))))
      =O[𝓝[>] (1:ℝ)] onset := by
    have hb : (fun z : Coordinates d => wienerSize m (assembly d z))
        =O[Filter.map (fun μ => realDiagonal d (amplitude hd μ-Real.sqrt (onset μ/kappa d)))
          (𝓝[>] (1:ℝ))] (fun z => ‖z‖) := by
      apply IsBigO.of_bound (2^(m+1)*d)
      exact Eventually.of_forall (fun z => by
        simpa only [Real.norm_of_nonneg (radialSize_nonneg _ _),norm_norm] using wienerSize_assembly_le m z)
    exact (hb.comp_tendsto tendsto_map).trans hlin0.norm_left
  have hdiag : (fun μ => ‖realDiagonal d (amplitude hd μ)‖^2)
      =O[𝓝[>] (1:ℝ)] onset :=
    (((realDiagonal d).isBigO_comp (amplitude hd) (𝓝[>] (1:ℝ))).norm_left.pow 2).trans
      (amplitude_square_bound hd)
  have hcor : (fun μ => wienerSize m (correction hd
      (parameter hd (amplitude hd μ),realDiagonal d (amplitude hd μ)) : Space d))
      =O[𝓝[>] (1:ℝ)] onset :=
    ((correction_wiener_quadratic hd m).comp_tendsto
      ((branch_coordinates_tendsto hd).comp (amplitude_tendsto hd))).trans hdiag
  have hb : (fun μ => wienerSize m (normalizedProfileRemainder hd μ)) =O[𝓝[>] (1:ℝ)]
      (fun μ => wienerSize m (assembly d (realDiagonal d (amplitude hd μ-Real.sqrt (onset μ/kappa d))))+
        wienerSize m (correction hd (parameter hd (amplitude hd μ),realDiagonal d (amplitude hd μ)) : Space d)) := by
    apply IsBigO.of_bound 1
    filter_upwards [((branch_coordinates_tendsto hd).comp (amplitude_tendsto hd)).eventually (correction_solves hd)] with μ he
    rw [Real.norm_of_nonneg (radialSize_nonneg _ _),Real.norm_of_nonneg
      (add_nonneg (radialSize_nonneg _ _) (radialSize_nonneg _ _)),one_mul,normalizedProfileRemainder_split]
    exact wienerSize_add_le m _ _ (radial_assembly m _) (correction_radial (by omega) _ _ _ he m)
  exact hb.trans (hlin.add hcor)

theorem normalizedProfileRemainder_sobolev_bound {d : ℕ} (hd : 12 ≤ d) (s : ℝ) :
    (fun μ => sobolevNorm s (normalizedProfileRemainder hd μ)) =O[𝓝[>] (1:ℝ)] onset := by
  obtain ⟨m, hm⟩ := exists_nat_ge s
  have hb : (fun μ => sobolevNorm s (normalizedProfileRemainder hd μ)) =O[𝓝[>] (1:ℝ)]
      (fun μ => wienerSize m (normalizedProfileRemainder hd μ)) := by
    apply IsBigO.of_bound ((1+2*Real.pi)^m)
    filter_upwards [normalizedProfileRemainder_radial hd m] with μ hμ
    rw [Real.norm_of_nonneg (show 0 ≤ sobolevNorm s (normalizedProfileRemainder hd μ) from Real.sqrt_nonneg _),
      Real.norm_of_nonneg (radialSize_nonneg _ _)]
    exact sobolevNorm_le_wiener hm _ hμ
  exact hb.trans (normalizedProfileRemainder_wiener_bound hd m)

theorem normalizedProfileRemainder_inSobolev {d : ℕ} (hd : 12 ≤ d) (s : ℝ) :
    ∀ᶠ μ in 𝓝[>] (1:ℝ), InSobolev s (normalizedProfileRemainder hd μ) := by
  obtain ⟨m, hm⟩ := exists_nat_ge s
  filter_upwards [normalizedProfileRemainder_radial hd m] with μ hμ
  exact inSobolev_of_wiener hm _ hμ

theorem normalizedProfileRemainder_physical {d : ℕ} (hd : 12 ≤ d) (β : ℝ) :
    (normalizedProfileRemainder hd (β/spectralThreshold d) : Torus d → ℝ) =
      branchRemainder β (physicalPotential hd β) 0 := by
  funext x
  simp only [normalizedProfileRemainder,physicalPotential,physical_onset_eq hd,
    ContinuousMap.sub_apply,assembly_realDiagonal_apply,branchRemainder,translate_zero]

theorem physical_profile_sobolev_bound {d : ℕ} (hd : 12 ≤ d) (s : ℝ) :
    (fun β => sobolevNorm s (branchRemainder β (physicalPotential hd β) 0))
      =O[𝓝[>] (spectralThreshold d)] (onsetDelta d) := by
  apply ((normalizedProfileRemainder_sobolev_bound hd s).comp_tendsto
    (normalized_parameter_tendsto hd)).congr
  · intro β
    dsimp only [Function.comp_apply]
    rw [normalizedProfileRemainder_physical]
  · exact physical_onset_eq hd

/-- The exact trusted remainder is controlled by one constant for every translation. -/
theorem physical_profile_sobolev_uniform {d : ℕ} (hd : 12 ≤ d) (s : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ β in 𝓝[>] (spectralThreshold d),
      ∀ a : Torus d, InSobolev s (branchRemainder β (physicalPotential hd β) a) ∧
        sobolevNorm s (branchRemainder β (physicalPotential hd β) a) ≤ C*onsetDelta d β := by
  obtain ⟨C,hC,hB⟩ := (physical_profile_sobolev_bound hd s).exists_pos
  refine ⟨C,hC,?_⟩
  filter_upwards [hB.bound,(normalized_parameter_tendsto hd).eventually
    (normalizedProfileRemainder_inSobolev hd s),
    (normalized_parameter_tendsto hd).eventually self_mem_nhdsWithin] with β hb hreg hβ
  have ho : 0 < onsetDelta d β := by
    rw [← physical_onset_eq hd]
    exact onset_pos hβ
  rw [normalizedProfileRemainder_physical] at hreg
  intro a
  refine ⟨(branchRemainder_inSobolev_iff s β _ a).mpr hreg,?_⟩
  rw [branchRemainder_sobolevNorm]
  simpa only [Real.norm_of_nonneg (show 0 ≤ sobolevNorm s (branchRemainder β (physicalPotential hd β) 0)
    from Real.sqrt_nonneg _),Real.norm_eq_abs,abs_of_pos ho] using hb

/-- Interval form matching the Sobolev-profile clause of the trusted branch statement.
The same actual branch works for all s; only the constants and radius depend on s. -/
theorem physical_profile_sobolev_interval {d : ℕ} (hd : 12 ≤ d) (s : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ η C : ℝ, 0 < η ∧ η ≤ ε ∧ 0 ≤ C ∧
      ∀ β : ℝ, spectralThreshold d < β → β < spectralThreshold d+η →
        ∀ a : Torus d, InSobolev s (branchRemainder β (physicalPotential hd β) a) ∧
          sobolevNorm s (branchRemainder β (physicalPotential hd β) a) ≤ C*onsetDelta d β := by
  obtain ⟨C,hC,hB⟩ := physical_profile_sobolev_uniform hd s
  obtain ⟨r,hr,hBall⟩ := Metric.mem_nhdsWithin_iff.mp hB
  refine ⟨min ε r,C,lt_min hε hr,min_le_left _ _,hC.le,?_⟩
  intro β hβ hupper
  apply hBall
  refine ⟨?_,hβ⟩
  rw [Metric.mem_ball,Real.dist_eq,abs_of_pos (sub_pos.mpr hβ)]
  have hm := min_le_right ε r
  linarith

#print axioms physical_profile_sobolev_interval
#print axioms physical_profile_sobolev_uniform
#print axioms physical_profile_sobolev_bound
end BecknerOnofri.HighDim.DiagonalScalarBranch
