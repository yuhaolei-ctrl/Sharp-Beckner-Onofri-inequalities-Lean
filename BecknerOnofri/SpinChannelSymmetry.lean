module

public import BecknerOnofri.BinarySpinChannel
public import BecknerOnofri.PermutationSymmetry

@[expose] public section

/-! Coordinate symmetry of a genuine Haar density implies exchangeability of
its binary channel law, by an actual measure-preserving change of variables. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped BigOperators
namespace BecknerOnofri.HighDim.Spin
open ContinuousSymmetry

theorem channel_permutation (c : Fin 12 → ℝ) (π : Equiv.Perm (Fin 12))
    (σ : Configuration) :
    channel (fun i => c (π.symm i)) (σ.map π.toEmbedding)=channel c σ := by
  classical
  have he : (σ.map π.toEmbedding)ᶜ=σᶜ.map π.toEmbedding := by
    ext i
    simp
  simp [channel,he,Finset.prod_map]

theorem channelLaw_exchangeable (ρ : ProbabilityDensity 12)
    (hρ : ∀ (π : Equiv.Perm (Fin 12)) (x : Torus 12),
      ρ.value (pointPermutation π x)=ρ.value x) : Exchangeable (channelLaw ρ) := by
  intro π σ
  unfold channelLaw
  rw [← integral_pointPermutation π]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  dsimp only
  rw [hρ]
  congr 1
  have he : torusCosines (pointPermutation π x)=(fun i => torusCosines x (π.symm i)) := by
    funext i
    simp only [torusCosines,pointPermutation_apply]
  rw [he]
  exact channel_permutation (torusCosines x) π σ

theorem channelLaw_exchangeable_coordinates (ρ : ProbabilityDensity 12)
    (hρ : ∀ (π : Equiv.Perm (Fin 12)) (x : Torus 12),
      ρ.value (fun i => x (π.symm i))=ρ.value x) : Exchangeable (channelLaw ρ) := by
  apply channelLaw_exchangeable
  intro π x
  have he : pointPermutation π x=(fun i => x (π.symm i)) := by
    funext i
    exact pointPermutation_apply π x i
  rw [he]
  exact hρ π x

#print axioms channelLaw_exchangeable
end BecknerOnofri.HighDim.Spin
