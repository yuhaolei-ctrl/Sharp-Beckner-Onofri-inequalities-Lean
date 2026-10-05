import BecknerOnofri.EntropyTailMixedMellin
import BecknerOnofri.EntropyTailHarmonic
import BecknerOnofri.CosineMixtureTransfer

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
namespace BecknerOnofri.HighDim.EntropyTail
open Legacy.TorusEndpoint Legacy.BecknerOnofri Legacy.D10
open RandomRectangles Finset

def latentAverage {α : Type*} (s : Finset α) (w : α → ℝ) (N : α → Fin 12 → ℕ)
    (F : (Fin 12 → ℕ) → ℝ) : ℝ :=
  ∑ a ∈ s, ∑ b ∈ s, ∑ L ∈ latentBox (N a), w a*w b*latentWeight (N a) (N b) L*F L

theorem latentAverage_mono {α : Type*} (s : Finset α) (w : α → ℝ) (N : α → Fin 12 → ℕ)
    (hw : ∀ a ∈ s, 0 ≤ w a) {F G : (Fin 12 → ℕ) → ℝ} (h : ∀ L, F L ≤ G L) :
    latentAverage s w N F ≤ latentAverage s w N G := by
  apply sum_le_sum
  intro a ha
  apply sum_le_sum
  intro b hb
  apply sum_le_sum
  intro L _
  exact mul_le_mul_of_nonneg_left (h L)
    (mul_nonneg (mul_nonneg (hw a ha) (hw b hb)) (latentWeight_nonneg _ _ _))

theorem latentAverage_add {α : Type*} (s : Finset α) (w : α → ℝ) (N : α → Fin 12 → ℕ)
    (F G : (Fin 12 → ℕ) → ℝ) :
    latentAverage s w N (fun L => F L+G L) = latentAverage s w N F+latentAverage s w N G := by
  simp only [latentAverage, mul_add, sum_add_distrib]

theorem latentAverage_mul {α : Type*} (s : Finset α) (w : α → ℝ) (N : α → Fin 12 → ℕ)
    (c : ℝ) (F : (Fin 12 → ℕ) → ℝ) :
    latentAverage s w N (fun L => c*F L) = c*latentAverage s w N F := by
  simp only [latentAverage, mul_sum]
  apply sum_congr rfl
  intro a _
  apply sum_congr rfl
  intro b _
  apply sum_congr rfl
  intro L _
  ring

theorem latentAverage_sum {α ι : Type*} (s : Finset α) (w : α → ℝ) (N : α → Fin 12 → ℕ)
    (t : Finset ι) (F : ι → (Fin 12 → ℕ) → ℝ) :
    latentAverage s w N (fun L => ∑ i ∈ t, F i L) = ∑ i ∈ t, latentAverage s w N (F i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [latentAverage]
  | @insert i t hi ih =>
    simp only [sum_insert hi]
    rw [latentAverage_add, ih]

theorem mixedCoefficient_axis (L : Fin 12 → ℕ) (i : Fin 12) (j : ℕ) :
    mixedCoefficient L (Pi.single i (j : ℤ)) = scalarCoefficient (L i) j := by
  classical
  unfold mixedCoefficient
  have he (r : Fin 12) : scalarCoefficient (L r) ((Pi.single i (j : ℤ) : Frequency 12) r).natAbs =
      if r=i then scalarCoefficient (L i) j else 1 := by
    by_cases h : r=i
    · subst r
      simp
    · simp [Pi.single_apply, h, Ne.symm h, scalarCoefficient_eq, RandomRectangles.coeff_zero]
  simp_rw [he]
  simp

theorem latentAverage_axis {α : Type*} (s : Finset α) (w : α → ℝ) (N : α → Fin 12 → ℕ)
    (i : Fin 12) (j : ℕ) :
    latentAverage s w N (fun L => scalarCoefficient (L i) j) =
      ‖densityFourier (CosineMixture.mixture s w N) (Pi.single i (j : ℤ))‖^2 := by
  have h := CosineMixtureTransfer.weighted_mixture_eq_latent s w N
    (fun _ => (1 : ℝ)) (Pi.single i (j : ℤ))
  simpa only [one_mul, CosineMixtureTransfer.latentTerm, latentAverage,
    ← mixedCoefficient_component, mixedCoefficient_axis] using h.symm

theorem finite_mixture_tail_comparison {α : Type*} (s : Finset α) (w : α → ℝ)
    (N : α → Fin 12 → ℕ) (hw : ∀ a ∈ s, 0 ≤ w a) :
    (∑' k : Frequency 12, scalarTailWeight k*‖densityFourier (CosineMixture.mixture s w N) k‖^2) ≤
      latentAverage s w N (fun L => (1/12 : ℝ)*∑ i : Fin 12, scalarTail (L i)) := by
  rw [CosineMixtureTransfer.weighted_mixture_tsum]
  change latentAverage s w N (fun L => ∑' k, scalarTailWeight k*componentCoeff L k) ≤ _
  simp_rw [← mixedCoefficient_component]
  exact latentAverage_mono s w N hw mixedTail_le_diagonal

#print axioms finite_mixture_tail_comparison
end BecknerOnofri.HighDim.EntropyTail
