import BecknerOnofri.EntropyTailMixture

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
namespace BecknerOnofri.HighDim.EntropyTail
open Legacy.TorusEndpoint Legacy.BecknerOnofri Legacy.D10 Finset

theorem latentAverage_tsum {α : Type*} (s : Finset α) (w : α → ℝ) (N : α → Fin 12 → ℕ)
    (F : ℕ → (Fin 12 → ℕ) → ℝ) (hF : ∀ L, Summable (fun j => F j L)) :
    (∑' j, latentAverage s w N (F j)) = latentAverage s w N (fun L => ∑' j, F j L) := by
  unfold latentAverage
  rw [Summable.tsum_finsetSum]
  · apply sum_congr rfl
    intro a _
    rw [Summable.tsum_finsetSum]
    · apply sum_congr rfl
      intro b _
      rw [Summable.tsum_finsetSum]
      · simp_rw [tsum_mul_left]
      · intro L _
        exact (hF L).mul_left _
    · intro b _
      exact summable_sum (fun L _ => (hF L).mul_left _)
  · intro a _
    exact summable_sum (fun b _ => summable_sum (fun L _ => (hF L).mul_left _))

theorem latentAverage_axis_tail {α : Type*} (s : Finset α) (w : α → ℝ) (N : α → Fin 12 → ℕ)
    (i : Fin 12) :
    latentAverage s w N (fun L => ∑' j : ℕ, scalarCoefficient (L i) (j+3)/(j+3 : ℝ)) =
      ∑' j : ℕ, ‖densityFourier (CosineMixture.mixture s w N) (Pi.single i (j+3 : ℤ))‖^2/(j+3 : ℝ) := by
  have hs (L : Fin 12 → ℕ) : Summable (fun j : ℕ => scalarCoefficient (L i) (j+3)/(j+3 : ℝ)) := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_ofNat] using
      (scalarHarmonic_summable (L i)).comp_injective
        (show Function.Injective (fun j : ℕ => j+3) from fun a b h => by dsimp at h; omega)
  rw [← latentAverage_tsum s w N _ hs]
  apply tsum_congr
  intro j
  simp_rw [div_eq_mul_inv, mul_comm _ ((j+3 : ℝ)⁻¹)]
  rw [latentAverage_mul, latentAverage_axis]
  norm_num only [Nat.cast_add, Nat.cast_ofNat]

theorem latentAverage_budget {α : Type*} (s : Finset α) (w : α → ℝ) (N : α → Fin 12 → ℕ) :
    latentAverage s w N (fun L => (1/12 : ℝ)*∑ i : Fin 12, scalarBudget (L i)) =
      ∑ i : Fin 12, ((21/500)*‖densityFourier (CosineMixture.mixture s w N) (Pi.single i (2 : ℤ))‖^2+
        (27/20)*∑' j : ℕ, ‖densityFourier (CosineMixture.mixture s w N) (Pi.single i (j+3 : ℤ))‖^2/(j+3 : ℝ)) := by
  simp_rw [scalarBudget_eq_axis_tail, ← mul_sum]
  norm_num only [show (1/12 : ℝ)*12=1 by norm_num, ← mul_assoc, one_mul]
  rw [latentAverage_sum]
  apply sum_congr rfl
  intro i _
  rw [latentAverage_add, latentAverage_mul, latentAverage_mul, latentAverage_axis, latentAverage_axis_tail]
  norm_num only [Nat.cast_ofNat]

/-- The scalar-to-mixture transfer. The scalar estimate is an explicit input here;
the independent numerical certificate is required to discharge it. -/
theorem finite_mixture_tail_of_scalar {α : Type*}
    (hscalar : ∀ n : ℕ, scalarTail n ≤ scalarBudget n)
    (s : Finset α) (w : α → ℝ) (N : α → Fin 12 → ℕ) (hw : ∀ a ∈ s, 0 ≤ w a) :
    (1/2 : ℝ)*(∑' k : Frequency 12, scalarTailWeight k*‖densityFourier (CosineMixture.mixture s w N) k‖^2) ≤
      ∑ i : Fin 12, ((21/1000)*‖densityFourier (CosineMixture.mixture s w N) (Pi.single i (2 : ℤ))‖^2+
        (27/40)*∑' j : ℕ, ‖densityFourier (CosineMixture.mixture s w N) (Pi.single i (j+3 : ℤ))‖^2/(j+3 : ℝ)) := by
  have h := (finite_mixture_tail_comparison s w N hw).trans
    (latentAverage_mono s w N hw (fun L => mul_le_mul_of_nonneg_left
      (sum_le_sum (fun i _ => hscalar (L i))) (by norm_num : (0 : ℝ) ≤ 1/12)))
  rw [latentAverage_budget] at h
  have hh := mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 1/2)
  convert! hh using 1
  rw [mul_sum]
  apply sum_congr rfl
  intro i _
  ring

#print axioms finite_mixture_tail_of_scalar
end BecknerOnofri.HighDim.EntropyTail
