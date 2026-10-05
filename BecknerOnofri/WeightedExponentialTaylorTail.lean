module

public import BecknerOnofri.WeightedExponentialTail

@[expose] public section

/-! Arbitrary Taylor tails in the actual weighted Fourier Wiener algebra. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
namespace BecknerOnofri.WeightedExponentialTaylorTail
open Legacy.TorusEndpoint Legacy.BecknerOnofri.WienerFourier Legacy.BecknerOnofri.WeightedWiener

def tailCoefficients (N : ℕ) {d : ℕ} (a : Frequency d → ℂ) (k : Frequency d) : ℂ :=
  ∑' n : ℕ, (((n+N).factorial : ℂ)⁻¹ * convolutionPower a (n+N) k)

theorem shift_injective (N : ℕ) {d : ℕ} : Function.Injective
    (fun p : ℕ × Frequency d => (p.1+N,p.2)) := by
  intro a b h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  apply Prod.ext
  · dsimp at h1
    omega
  · exact h2

theorem tailCoefficients_eq (N : ℕ) {d : ℕ} (a : Frequency d → ℂ)
    (ha : Summable (fun k => ‖a k‖)) (k : Frequency d) :
    tailCoefficients N a k = exponentialCoefficients a k -
      ∑ n ∈ Finset.range N, (n.factorial:ℂ)⁻¹*convolutionPower a n k := by
  classical
  have hs := ((exponential_joint_norm_summable a ha).prod_symm.prod_factor k).of_norm
  have hh := hs.sum_add_tsum_nat_add N
  change (∑ n ∈ Finset.range N,(n.factorial:ℂ)⁻¹*convolutionPower a n k) +
    tailCoefficients N a k = exponentialCoefficients a k at hh
  rw [← hh]
  abel

theorem tail_weighted_summable (N : ℕ) {d : ℕ} {w : Frequency d → ℝ} (hw : IsWeight w)
    (a : Frequency d → ℂ) (ha : Summable (fun k => w k * ‖a k‖)) :
    Summable (fun k => w k * ‖tailCoefficients N a k‖) := by
  have hs := (exponential_joint_summable hw a ha).comp_injective (shift_injective N (d := d))
  have hs0 := (exponential_joint_norm_summable a (summable_norm hw ha)).comp_injective
    (shift_injective N (d := d))
  dsimp only [Function.comp_def] at hs hs0
  apply hs.prod_symm.prod.of_nonneg_of_le (fun k => mul_nonneg (hw.nonneg k) (norm_nonneg _))
  intro k
  calc
    _ ≤ w k * ∑' n : ℕ, ‖((n+N).factorial : ℂ)⁻¹ * convolutionPower a (n+N) k‖ :=
      mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm (hs0.prod_symm.prod_factor k)) (hw.nonneg k)
    _ = _ := tsum_mul_left.symm

/-- The tail mass is bounded by the exact scalar exponential Taylor tail. -/
theorem tail_weighted_sum_le (N : ℕ) {d : ℕ} {w : Frequency d → ℝ} (hw : IsWeight w)
    (a : Frequency d → ℂ) (ha : Summable (fun k => w k * ‖a k‖)) :
    (∑' k, w k * ‖tailCoefficients N a k‖) ≤
      Real.exp (∑' k, w k * ‖a k‖) -
        ∑ n ∈ Finset.range N,(n.factorial:ℝ)⁻¹*(∑' k,w k*‖a k‖)^n := by
  let b : Frequency d → ℝ := fun k => w k * ‖a k‖
  have hb (k) : 0 ≤ b k := mul_nonneg (hw.nonneg k) (norm_nonneg _)
  have hs := (exponential_joint_summable hw a ha).comp_injective (shift_injective N (d := d))
  have hs0 := (exponential_joint_norm_summable a (summable_norm hw ha)).comp_injective
    (shift_injective N (d := d))
  have hsB := (fourierExponential_joint_summable b ha hb).comp_injective (shift_injective N (d := d))
  dsimp only [Function.comp_def] at hs hs0 hsB
  have hp (k : Frequency d) : w k * ‖tailCoefficients N a k‖ ≤
      ∑' n : ℕ, ((n+N).factorial : ℝ)⁻¹ * fourierPower b (n+N) k := by
    calc
      _ ≤ w k * ∑' n : ℕ, ‖((n+N).factorial : ℂ)⁻¹ * convolutionPower a (n+N) k‖ :=
        mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm (hs0.prod_symm.prod_factor k)) (hw.nonneg k)
      _ = ∑' n : ℕ, w k * ‖((n+N).factorial : ℂ)⁻¹ * convolutionPower a (n+N) k‖ := tsum_mul_left.symm
      _ ≤ _ := by
        apply Summable.tsum_le_tsum _ (hs.prod_symm.prod_factor k) (hsB.prod_symm.prod_factor k)
        intro n
        simp only [Prod.swap, norm_mul, norm_inv, Complex.norm_natCast]
        calc
          _ = ((n+N).factorial : ℝ)⁻¹ * (w k * ‖convolutionPower a (n+N) k‖) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left (power_le hw a ha (n+N) k) (by positivity)
  have he : HasSum (fun n : ℕ => (n.factorial : ℝ)⁻¹ * (∑' k, b k)^n) (Real.exp (∑' k,b k)) := by
    simpa only [smul_eq_mul, ← Real.exp_eq_exp_ℝ] using
      NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (∑' k,b k)
  have ht := he.summable.sum_add_tsum_nat_add N
  rw [he.tsum_eq] at ht
  calc
    _ ≤ ∑' k, ∑' n : ℕ, ((n+N).factorial : ℝ)⁻¹ * fourierPower b (n+N) k :=
      Summable.tsum_le_tsum hp (tail_weighted_summable N hw a ha) hsB.prod_symm.prod
    _ = ∑' n : ℕ, ∑' k, ((n+N).factorial : ℝ)⁻¹ * fourierPower b (n+N) k := hsB.tsum_comm
    _ = ∑' n : ℕ, ((n+N).factorial : ℝ)⁻¹ * (∑' k,b k)^(n+N) := by
      apply tsum_congr
      intro n
      rw [tsum_mul_left, (fourierPower_hasSum b ha hb (n+N)).tsum_eq]
    _ = _ := by dsimp only [b] at ht ⊢; linarith

#print axioms tail_weighted_sum_le
end BecknerOnofri.WeightedExponentialTaylorTail
