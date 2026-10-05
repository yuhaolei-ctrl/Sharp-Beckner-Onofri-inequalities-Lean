import BecknerOnofri.RandomRectangles
import Legacy.BecknerOnofri.CountableCosineMixture

/-! Dimension transfer for the actual Fourier energies of correlated cosine mixtures. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators Topology
open Finset MeasureTheory

namespace BecknerOnofri.CosineMixtureTransfer
open RectangleLattice RandomRectangles Legacy.TorusEndpoint
open Legacy.BecknerOnofri Legacy.D10

/-- Inverse-power Fourier energy, with the zero frequency omitted by the weight. -/
def energy {d : ℕ} (p : ℝ) (f : Torus d → ℝ) : ℝ :=
  ∑' k : Frequency d, weight p k * ‖densityFourier f k‖^2

/-- The Fourier energy retained after integrating out coordinate i. -/
def deletionEnergy {d : ℕ} (p : ℝ) (f : Torus d → ℝ) (i : Fin d) : ℝ :=
  ∑' k : Frequency d, (if k i = 0 then weight p k else 0) * ‖densityFourier f k‖^2

def latentTerm {α : Type*} {d : ℕ} (s : Finset α) (w : α → ℝ)
    (N : α → Fin d → ℕ) (f : Frequency d → ℝ) (k : Frequency d) : ℝ :=
  ∑ a ∈ s, ∑ b ∈ s, ∑ L ∈ latentBox (N a),
    w a * w b * latentWeight (N a) (N b) L * (f k * componentCoeff L k)

theorem weighted_mixture_eq_latent {α : Type*} {d : ℕ} (s : Finset α) (w : α → ℝ)
    (N : α → Fin d → ℕ) (f : Frequency d → ℝ) (k : Frequency d) :
    f k * ‖densityFourier (CosineMixture.mixture s w N) k‖^2 = latentTerm s w N f k := by
  rw [CosineMixture.mixture_fourier_norm_sq]
  unfold latentTerm componentCoeff
  simp only [mul_sum]
  apply sum_congr rfl
  intro a ha
  apply sum_congr rfl
  intro b hb
  apply sum_congr rfl
  intro L hL
  ring

theorem summable_latentTerm {α : Type*} {d : ℕ} (s : Finset α) (w : α → ℝ)
    (N : α → Fin d → ℕ) (f : Frequency d → ℝ) : Summable (latentTerm s w N f) := by
  unfold latentTerm
  exact summable_sum (fun a _ => summable_sum (fun b _ => summable_sum (fun L _ =>
    (summable_weighted_component L f).mul_left _)))

theorem tsum_latentTerm {α : Type*} {d : ℕ} (s : Finset α) (w : α → ℝ)
    (N : α → Fin d → ℕ) (f : Frequency d → ℝ) :
    (∑' k, latentTerm s w N f k) =
      ∑ a ∈ s, ∑ b ∈ s, ∑ L ∈ latentBox (N a),
        w a * w b * latentWeight (N a) (N b) L * (∑' k, f k * componentCoeff L k) := by
  unfold latentTerm
  rw [Summable.tsum_finsetSum]
  · apply sum_congr rfl
    intro a ha
    rw [Summable.tsum_finsetSum]
    · apply sum_congr rfl
      intro b hb
      rw [Summable.tsum_finsetSum]
      · simp_rw [tsum_mul_left]
      · intro L hL
        exact (summable_weighted_component L f).mul_left _
    · intro b hb
      exact summable_sum (fun L _ => (summable_weighted_component L f).mul_left _)
  · intro a ha
    exact summable_sum (fun b _ => summable_sum (fun L _ =>
      (summable_weighted_component L f).mul_left _))

theorem weighted_mixture_tsum {α : Type*} {d : ℕ} (s : Finset α) (w : α → ℝ)
    (N : α → Fin d → ℕ) (f : Frequency d → ℝ) :
    (∑' k, f k * ‖densityFourier (CosineMixture.mixture s w N) k‖^2) =
      ∑ a ∈ s, ∑ b ∈ s, ∑ L ∈ latentBox (N a),
        w a * w b * latentWeight (N a) (N b) L * (∑' k, f k * componentCoeff L k) := by
  simp_rw [weighted_mixture_eq_latent]
  exact tsum_latentTerm s w N f

/-- Genuine finite correlated-mixture dimension transfer. The entire mixture
index can correlate all coordinates; only its weights must be nonnegative. -/
theorem finite_mixture_comparison {α : Type*} {d : ℕ} (hd : 13 ≤ d)
    (s : Finset α) (w : α → ℝ) (N : α → Fin d → ℕ) (hw : ∀ a ∈ s, 0 ≤ w a) :
    energy (d : ℝ) (CosineMixture.mixture s w N) ≤ (1 / ((d : ℝ)-1)) *
      ∑ i : Fin d, deletionEnergy ((d : ℝ)-1) (CosineMixture.mixture s w N) i := by
  unfold energy deletionEnergy
  simp_rw [weighted_mixture_tsum]
  rw [sum_comm (s := univ) (t := s)]
  simp_rw [sum_comm (s := univ) (t := s)]
  simp_rw [sum_comm (s := univ) (t := latentBox _)]
  simp_rw [← mul_sum]
  rw [mul_sum]
  apply sum_le_sum
  intro a ha
  rw [mul_sum]
  apply sum_le_sum
  intro b hb
  rw [mul_sum]
  apply sum_le_sum
  intro L hL
  have hn : 0 ≤ w a * w b * latentWeight (N a) (N b) L :=
    mul_nonneg (mul_nonneg (hw a ha) (hw b hb)) (latentWeight_nonneg _ _ _)
  have h := mul_le_mul_of_nonneg_left (component_comparison hd L) hn
  simpa only [componentEnergy, componentDeletion, mul_left_comm] using h

#print axioms finite_mixture_comparison

end BecknerOnofri.CosineMixtureTransfer
