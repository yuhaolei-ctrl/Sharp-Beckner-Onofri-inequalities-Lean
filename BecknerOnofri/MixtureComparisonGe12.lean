module

public import BecknerOnofri.CountableMixtureTransfer
public import BecknerOnofri.RectangleTwelve

@[expose] public section

/-! Include the manuscript's new d=12 rectangle case in the actual cosine-mixture
energy transfer. The countable result here still assumes a summable uniform
majorant; removing it and proving the general r-subset formula are separate work. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators Topology
open Finset MeasureTheory Filter
namespace BecknerOnofri.RandomRectangles
open RectangleLattice Legacy.D10
theorem component_comparison_ge12 {d : ℕ} (hd : 12 ≤ d) (N : Fin d → ℕ) :
    componentEnergy (d : ℝ) N ≤ (1 / ((d : ℝ)-1)) *
      ∑ i : Fin d, componentDeletion ((d : ℝ)-1) N i := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hdm : (0 : ℝ) < (d : ℝ)-1 := by
    have : (12 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  rw [componentEnergy_rectangles hdpos]
  simp_rw [componentDeletion_rectangles hdm]
  rw [sum_comm]
  rw [mul_sum]
  apply sum_le_sum
  intro R hR
  calc
    _ ≤ rectangleLaw N R * ((1 / ((d : ℝ)-1)) *
        ∑ i : Fin d, latticeSum ((d : ℝ)-1) (Function.update R i 0)) :=
      mul_le_mul_of_nonneg_left (rectangle_comparison_ge12 hd R) (rectangleLaw_nonneg N R)
    _ = _ := by rw [← mul_sum]; ring

#print axioms component_comparison_ge12
end BecknerOnofri.RandomRectangles
namespace BecknerOnofri.CosineMixtureTransfer
open RectangleLattice RandomRectangles Legacy.TorusEndpoint
open Legacy.BecknerOnofri Legacy.D10
theorem finite_mixture_comparison_ge12 {α : Type*} {d : ℕ} (hd : 12 ≤ d)
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
  have h := mul_le_mul_of_nonneg_left (component_comparison_ge12 hd L) hn
  simpa only [componentEnergy, componentDeletion, mul_left_comm] using h

theorem countable_mixture_comparison_ge12 {d : ℕ} (hd : 12 ≤ d) (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ)
    (hw : ∀ n, 0 ≤ w n) (hs : Summable w)
    (hSup : Summable (fun n => w n * CosineMixture.tensor (N n) 0)) :
    energy (d:ℝ) (CosineMixtureApproximation.rho w N) ≤ (1 / ((d:ℝ)-1)) *
      ∑ i : Fin d, deletionEnergy ((d:ℝ)-1) (CosineMixtureApproximation.rho w N) i := by
  have hd0 : (0:ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hdm : (0:ℝ) < (d:ℝ)-1 := by
    have : (12:ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hleft := partial_weighted_energy_tendsto w N hw hs hSup (weight (d:ℝ))
    (fun k => ⟨weight_nonneg _ _, weight_le_one hd0 k⟩)
  have hright (i : Fin d) := partial_weighted_energy_tendsto w N hw hs hSup
    (fun k => if k i = 0 then weight ((d:ℝ)-1) k else 0)
    (fun k => by split_ifs; exact ⟨weight_nonneg _ _, weight_le_one hdm k⟩; norm_num)
  have hr := (tendsto_finsetSum univ (fun i _ => hright i)).const_mul (1/((d:ℝ)-1))
  exact le_of_tendsto_of_tendsto hleft hr (Eventually.of_forall fun m =>
    finite_mixture_comparison_ge12 hd (range m) w N (fun n _ => hw n))

#print axioms finite_mixture_comparison_ge12
#print axioms countable_mixture_comparison_ge12
end BecknerOnofri.CosineMixtureTransfer
