import BecknerOnofri.SpinCubeFourier
import BecknerOnofri.CubeShellCounting

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
namespace BecknerOnofri.HighDim.Spin

def prefixCoordinates (r : ℕ) : Configuration := Finset.univ.filter (fun i => i.val<r)
def jointBySize (ν : Configuration → ℝ) (r : ℕ) : ℝ :=
  ∑ σ : Configuration, ν σ*jointSpin (prefixCoordinates r) σ

theorem prefixCoordinates_card_checked : ∀ r : Fin 13, (prefixCoordinates r.val).card=r.val := by
  decide +kernel

theorem prefixCoordinates_card {r : ℕ} (hr : r ≤ 12) : (prefixCoordinates r).card=r :=
  prefixCoordinates_card_checked ⟨r, by omega⟩

theorem cube_fourier_by_size (ρ : ProbabilityDensity 12)
    (hρ : GenericCosineRepresentation.HasPositiveCosineMixture ρ.value)
    (hex : Exchangeable (channelLaw ρ)) (k : Frequency 12)
    (hk : k ∈ RectangleLattice.box (fun _ => 1)) :
    ‖HighDim.fourierCoeff ρ.value k‖^2 = jointBySize (channelLaw ρ) (latticeSquare k)^2 := by
  have hcard : (RectangleLattice.support k).card ≤ 12 := by
    simpa using Finset.card_le_card (Finset.subset_univ (RectangleLattice.support k))
  rw [mixture_cube_fourier ρ hρ k hk, cube_latticeSquare k hk]
  congr 1
  exact exchangeable_joint_equal_card hex (prefixCoordinates_card hcard).symm

attribute [local irreducible] RectangleLattice.box

theorem cube_energy_by_size (ρ : ProbabilityDensity 12)
    (hρ : GenericCosineRepresentation.HasPositiveCosineMixture ρ.value)
    (hex : Exchangeable (channelLaw ρ)) :
    (∑ k ∈ RectangleLattice.box (fun _ : Fin 12 => 1),
      (frequencyLength k^12)⁻¹*‖HighDim.fourierCoeff ρ.value k‖^2) =
      ∑ r ∈ Finset.range 13, ((12 : ℕ).choose r : ℝ)*2^r*
        ((r : ℝ)^6)⁻¹*jointBySize (channelLaw ρ) r^2 := by
  calc
    _ = ∑ k ∈ RectangleLattice.box (fun _ : Fin 12 => 1),
        ((latticeSquare k : ℝ)^6)⁻¹*jointBySize (channelLaw ρ) (latticeSquare k)^2 := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [cube_fourier_by_size ρ hρ hex k hk, frequencyLength_pow_eq]
      norm_num only [Nat.cast_ofNat, show (12 : ℝ)/2=6 by norm_num, Real.rpow_ofNat]
    _ = _ := by
      have h := CubeShell.cube_sum 12 (fun r => ((r : ℝ)^6)⁻¹*jointBySize (channelLaw ρ) r^2)
      convert! h using 1
      apply Finset.sum_congr rfl
      intro r _
      ring

theorem cube_half_energy_eq_quadratic (ρ : ProbabilityDensity 12)
    (hρ : GenericCosineRepresentation.HasPositiveCosineMixture ρ.value)
    (hex : Exchangeable (channelLaw ρ)) :
    (1/2 : ℝ)*(∑ k ∈ RectangleLattice.box (fun _ : Fin 12 => 1),
      (frequencyLength k^12)⁻¹*‖HighDim.fourierCoeff ρ.value k‖^2) = quadratic (countLaw (channelLaw ρ)) := by
  rw [cube_energy_by_size ρ hρ hex, ← exchangeable_energy hex]
  rw [Finset.sum_range_succ']
  norm_num only [Nat.choose_zero_right, Nat.cast_one, pow_zero, Nat.cast_zero, zero_pow,
    inv_zero, mul_zero, zero_mul, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]
  rw [Finset.mul_sum, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro r _
  change (1/2 : ℝ)*(((12 : ℕ).choose (r.val+1) : ℝ)*2^(r.val+1)*
    (((r.val+1 : ℕ) : ℝ)^6)⁻¹*jointBySize (channelLaw ρ) (r.val+1)^2) = _
  simp only [weight, weightQ, Rat.cast_mul, Rat.cast_div, Rat.cast_inv, Rat.cast_pow, Rat.cast_natCast,
    Rat.cast_ofNat, Rat.cast_add, Rat.cast_one, Nat.cast_add, Nat.cast_one,
    pow_succ, jointBySize, prefixCoordinates, firstCoordinates, div_eq_mul_inv]
  ring

#print axioms cube_half_energy_eq_quadratic
end BecknerOnofri.HighDim.Spin
