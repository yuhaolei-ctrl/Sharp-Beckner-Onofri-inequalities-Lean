import BecknerOnofri.SpinMixtureMoments
import BecknerOnofri.SpinCountMoments

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
namespace BecknerOnofri.HighDim.Spin
open Legacy.BecknerOnofri
attribute [local irreducible] RectangleLattice.box

theorem jointSpin_permutation (π : Equiv.Perm (Fin 12)) (S σ : Configuration) :
    jointSpin (S.map π.toEmbedding) (σ.map π.toEmbedding) = jointSpin S σ := by
  classical
  have he : (σ.map π.toEmbedding)ᶜ = σᶜ.map π.toEmbedding := by ext i; simp
  simp [jointSpin, he, Finset.prod_map]

theorem exchangeable_joint_permutation {ν : Configuration → ℝ} (hν : Exchangeable ν)
    (π : Equiv.Perm (Fin 12)) (S : Configuration) :
    (∑ σ : Configuration, ν σ*jointSpin (S.map π.toEmbedding) σ) =
      ∑ σ : Configuration, ν σ*jointSpin S σ := by
  rw [← Equiv.sum_comp π.finsetCongr]
  have he (σ : Configuration) : ν (σ.map π.toEmbedding)=ν σ := hν π σ
  simp only [Equiv.finsetCongr_apply, he, jointSpin_permutation]

theorem exchangeable_joint_equal_card {ν : Configuration → ℝ} (hν : Exchangeable ν)
    {S T : Configuration} (hST : S.card=T.card) :
    (∑ σ : Configuration, ν σ*jointSpin S σ) =
      ∑ σ : Configuration, ν σ*jointSpin T σ := by
  obtain ⟨π,hπ⟩ := Equiv.Perm.exists_map_finset_eq S T hST
  simpa only [hπ] using (exchangeable_joint_permutation hν π S).symm

theorem firstCoordinates_card : ∀ s : Order, (firstCoordinates s).card=s.val+1 := by
  decide +kernel

theorem cube_abs (k : Frequency 12) (hk : k ∈ RectangleLattice.box (fun _ => 1)) (i : Fin 12) :
    (k i).natAbs = if k i=0 then 0 else 1 := by
  have h := (RectangleLattice.mem_box _ _).mp hk i
  norm_num only [Nat.cast_one] at h
  have he : k i = -1 ∨ k i=0 ∨ k i=1 := by omega
  rcases he with he | he | he <;> simp [he]

theorem cube_latticeSquare (k : Frequency 12) (hk : k ∈ RectangleLattice.box (fun _ => 1)) :
    latticeSquare k = (RectangleLattice.support k).card := by
  classical
  simp_rw [latticeSquare, cube_abs k hk]
  simp [RectangleLattice.support, Finset.card_filter, ite_pow, eq_comm]

theorem cube_component_support (N : Fin 12 → ℕ) (k : Frequency 12)
    (hk : k ∈ RectangleLattice.box (fun _ => 1)) :
    RandomRectangles.componentCoeff N k =
      RandomRectangles.componentCoeff N (subsetFrequency (RectangleLattice.support k)) := by
  classical
  unfold RandomRectangles.componentCoeff Legacy.D10.binomialProduct
  apply Finset.prod_congr rfl
  intro i _
  dsimp only
  rw [cube_abs k hk]
  by_cases hi : k i=0 <;> simp [subsetFrequency, RectangleLattice.support, hi]

theorem mixture_fourier_real (ρ : ProbabilityDensity 12)
    (hρ : GenericCosineRepresentation.HasPositiveCosineMixture ρ.value) (k : Frequency 12) :
    ‖HighDim.fourierCoeff ρ.value k‖^2 = (HighDim.fourierCoeff ρ.value k).re^2 := by
  obtain ⟨w,N,hw,hm,hSup,he⟩ := hρ
  rw [he]
  change ‖Legacy.TorusEndpoint.densityFourier _ k‖^2 = (Legacy.TorusEndpoint.densityFourier _ k).re^2
  rw [CosineMixtureTransfer.rho_fourier w N hw hm.summable]
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs, Complex.ofReal_re]

theorem mixture_cube_fourier (ρ : ProbabilityDensity 12)
    (hρ : GenericCosineRepresentation.HasPositiveCosineMixture ρ.value) (k : Frequency 12)
    (hk : k ∈ RectangleLattice.box (fun _ => 1)) :
    ‖HighDim.fourierCoeff ρ.value k‖^2 =
      (∑ σ : Configuration, channelLaw ρ σ*jointSpin (RectangleLattice.support k) σ)^2 := by
  rw [mixture_channel_joint_fourier ρ hρ, mixture_fourier_real ρ hρ]
  congr 2
  obtain ⟨w,N,hw,hm,hSup,he⟩ := hρ
  rw [he]
  change Legacy.TorusEndpoint.densityFourier _ k = Legacy.TorusEndpoint.densityFourier _ _
  simp only [CosineMixtureTransfer.rho_fourier w N hw hm.summable]
  congr 1
  apply tsum_congr
  intro n
  rw [cube_component_support (N n) k hk]

#print axioms mixture_cube_fourier
end BecknerOnofri.HighDim.Spin
