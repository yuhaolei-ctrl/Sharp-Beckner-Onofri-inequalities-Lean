import Legacy.BecknerOnofri.WeightedWiener

/-! Exact quadratic tails in a normalized weighted Fourier Wiener algebra. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
namespace BecknerOnofri.WeightedExponentialRemainder
open Legacy.TorusEndpoint Legacy.BecknerOnofri.WienerFourier Legacy.BecknerOnofri.WeightedWiener

def tailCoefficients {d : ℕ} (a : Frequency d → ℂ) (k : Frequency d) : ℂ :=
  ∑' n : ℕ, (((n+2).factorial : ℂ)⁻¹ * convolutionPower a (n+2) k)

theorem shift_injective {d : ℕ} : Function.Injective
    (fun p : ℕ × Frequency d => (p.1+2,p.2)) := by
  intro a b h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  apply Prod.ext
  · dsimp at h1
    omega
  · exact h2

theorem convolutionPower_one {d : ℕ} (a : Frequency d → ℂ)
    (ha : Summable (fun k => ‖a k‖)) (k : Frequency d) : convolutionPower a 1 k = a k := by
  have he : absoluteFourierSeries (convolutionPower a 1) = absoluteFourierSeries a := by
    funext x
    rw [convolutionPower_series a ha, pow_one]
  rw [← absoluteFourierSeries_coefficient _ (convolutionPower_norm_summable a ha 1), he,
    absoluteFourierSeries_coefficient _ ha]

theorem tailCoefficients_eq {d : ℕ} (a : Frequency d → ℂ)
    (ha : Summable (fun k => ‖a k‖)) (k : Frequency d) :
    tailCoefficients a k = exponentialCoefficients a k - (if k=0 then 1 else 0) - a k := by
  classical
  have hs := ((exponential_joint_norm_summable a ha).prod_symm.prod_factor k).of_norm
  have hh := hs.sum_add_tsum_nat_add 2
  simp only [Prod.swap, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial_zero,
    Nat.factorial_one, Nat.cast_one, inv_one, one_mul, zero_add,
    convolutionPower_one a ha] at hh
  change (if k=0 then (1:ℂ) else 0) + a k + tailCoefficients a k = exponentialCoefficients a k at hh
  rw [← hh]
  abel

theorem tail_weighted_summable {d : ℕ} {w : Frequency d → ℝ} (hw : IsWeight w)
    (a : Frequency d → ℂ) (ha : Summable (fun k => w k * ‖a k‖)) :
    Summable (fun k => w k * ‖tailCoefficients a k‖) := by
  have hs := (exponential_joint_summable hw a ha).comp_injective (shift_injective (d := d))
  have hs0 := (exponential_joint_norm_summable a (summable_norm hw ha)).comp_injective
    (shift_injective (d := d))
  dsimp only [Function.comp_def] at hs hs0
  apply hs.prod_symm.prod.of_nonneg_of_le (fun k => mul_nonneg (hw.nonneg k) (norm_nonneg _))
  intro k
  calc
    _ ≤ w k * ∑' n : ℕ, ‖((n+2).factorial : ℂ)⁻¹ * convolutionPower a (n+2) k‖ :=
      mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm (hs0.prod_symm.prod_factor k)) (hw.nonneg k)
    _ = _ := tsum_mul_left.symm

/-- The tail mass is bounded by the exact scalar exponential Taylor tail. -/
theorem tail_weighted_sum_le {d : ℕ} {w : Frequency d → ℝ} (hw : IsWeight w)
    (a : Frequency d → ℂ) (ha : Summable (fun k => w k * ‖a k‖)) :
    (∑' k, w k * ‖tailCoefficients a k‖) ≤
      Real.exp (∑' k, w k * ‖a k‖) - 1 - ∑' k, w k * ‖a k‖ := by
  let b : Frequency d → ℝ := fun k => w k * ‖a k‖
  have hb (k) : 0 ≤ b k := mul_nonneg (hw.nonneg k) (norm_nonneg _)
  have hs := (exponential_joint_summable hw a ha).comp_injective (shift_injective (d := d))
  have hs0 := (exponential_joint_norm_summable a (summable_norm hw ha)).comp_injective
    (shift_injective (d := d))
  have hsB := (fourierExponential_joint_summable b ha hb).comp_injective (shift_injective (d := d))
  dsimp only [Function.comp_def] at hs hs0 hsB
  have hp (k : Frequency d) : w k * ‖tailCoefficients a k‖ ≤
      ∑' n : ℕ, ((n+2).factorial : ℝ)⁻¹ * fourierPower b (n+2) k := by
    calc
      _ ≤ w k * ∑' n : ℕ, ‖((n+2).factorial : ℂ)⁻¹ * convolutionPower a (n+2) k‖ :=
        mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm (hs0.prod_symm.prod_factor k)) (hw.nonneg k)
      _ = ∑' n : ℕ, w k * ‖((n+2).factorial : ℂ)⁻¹ * convolutionPower a (n+2) k‖ := tsum_mul_left.symm
      _ ≤ _ := by
        apply Summable.tsum_le_tsum _ (hs.prod_symm.prod_factor k) (hsB.prod_symm.prod_factor k)
        intro n
        simp only [Prod.swap, norm_mul, norm_inv, Complex.norm_natCast]
        calc
          _ = ((n+2).factorial : ℝ)⁻¹ * (w k * ‖convolutionPower a (n+2) k‖) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left (power_le hw a ha (n+2) k) (by positivity)
  have he : HasSum (fun n : ℕ => (n.factorial : ℝ)⁻¹ * (∑' k, b k)^n) (Real.exp (∑' k,b k)) := by
    simpa only [smul_eq_mul, ← Real.exp_eq_exp_ℝ] using
      NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (∑' k,b k)
  have ht := he.summable.sum_add_tsum_nat_add 2
  simp only [Prod.swap, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial_zero,
    Nat.factorial_one, Nat.cast_one, inv_one, one_mul, zero_add, pow_zero, pow_one] at ht
  rw [he.tsum_eq] at ht
  calc
    _ ≤ ∑' k, ∑' n : ℕ, ((n+2).factorial : ℝ)⁻¹ * fourierPower b (n+2) k :=
      Summable.tsum_le_tsum hp (tail_weighted_summable hw a ha) hsB.prod_symm.prod
    _ = ∑' n : ℕ, ∑' k, ((n+2).factorial : ℝ)⁻¹ * fourierPower b (n+2) k := hsB.tsum_comm
    _ = ∑' n : ℕ, ((n+2).factorial : ℝ)⁻¹ * (∑' k,b k)^(n+2) := by
      apply tsum_congr
      intro n
      rw [tsum_mul_left, (fourierPower_hasSum b ha hb (n+2)).tsum_eq]
    _ = _ := by dsimp only [b] at ht ⊢; linarith

#print axioms tail_weighted_sum_le
end BecknerOnofri.WeightedExponentialRemainder
