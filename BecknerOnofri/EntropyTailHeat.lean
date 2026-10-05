import BecknerOnofri.EntropyTailGaussian
import BecknerOnofri.EntropyTailTwo

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open Classical
namespace BecknerOnofri.HighDim.EntropyTail
open Legacy.BecknerOnofri.GaussianLattice

/-- The positive summands of the cube-complement heat series. -/
def heatTerm (s : ℝ) (k : Frequency 12) : ℝ :=
  if outsideCube k then gaussian s k else 0

theorem heatTerm_nonneg (s : ℝ) (k : Frequency 12) : 0 ≤ heatTerm s k := by
  unfold heatTerm gaussian
  split_ifs <;> positivity

theorem heatTerm_summable {s : ℝ} (hs : 0 < s) : Summable (heatTerm s) := by
  apply Summable.of_nonneg_of_le (heatTerm_nonneg s) _ (summable_gaussian hs)
  intro k
  unfold heatTerm
  split_ifs
  · exact le_rfl
  · exact (Real.exp_pos _).le

theorem gaussian_cube_sum (s : ℝ) :
    (∑ k ∈ RectangleLattice.box (fun _ : Fin 12 => 1), gaussian s k) =
      (1+2*Real.exp (-s))^12 := by
  simp_rw [gaussian_eq_product]
  change (∑ k ∈ Fintype.piFinset (fun _ : Fin 12 => Finset.Icc (-1 : ℤ) 1),
    ∏ i : Fin 12, Real.exp (-s * (k i : ℝ)^2)) = _
  rw [← Finset.sum_pow' (Finset.Icc (-1 : ℤ) 1) (fun j : ℤ => Real.exp (-s*(j : ℝ)^2)) 12]
  have he : Finset.Icc (-1 : ℤ) 1 = {-1,0,1} := by decide +kernel
  rw [he]
  norm_num
  ring

attribute [local irreducible] RectangleLattice.box

theorem finite_complement_tsum {α : Type*} (f : α → ℝ) (hf : Summable f)
    (c : Finset α) :
    (∑' k, if k ∉ c then f k else 0) = (∑' k, f k) - ∑ k ∈ c, f k := by
  classical
  have hi : Summable (fun k => if k ∈ c then f k else 0) := by
    apply (hf.indicator (c : Set α)).congr
    intro k
    by_cases hk : k ∈ c
    · rw [Set.indicator_of_mem hk, if_pos hk]
    · rw [Set.indicator_of_notMem hk, if_neg hk]
  have ho : Summable (fun k => if k ∉ c then f k else 0) := by
    apply (hf.indicator ((c : Set α)ᶜ)).congr
    intro k
    by_cases hk : k ∉ c
    · rw [Set.indicator_of_mem hk, if_pos hk]
    · rw [Set.indicator_of_notMem hk, if_neg hk]
  have hiSum : (∑' k, if k ∈ c then f k else 0) = ∑ k ∈ c, f k := by
    rw [tsum_eq_sum (s := c) (fun k hk => if_neg hk)]
    exact Finset.sum_congr rfl (fun k hk => if_pos hk)
  have he : (fun k => (if k ∈ c then f k else 0) + (if k ∉ c then f k else 0)) = f := by
    funext k
    by_cases hk : k ∈ c <;> simp [hk]
  have hsum := hi.tsum_add ho
  rw [he, hiSum] at hsum
  linarith

theorem heatComplement_eq_tsum {s : ℝ} (hs : 0 < s) :
    heatComplement s = ∑' k : Frequency 12, heatTerm s k := by
  have h := finite_complement_tsum (gaussian s) (summable_gaussian hs)
    (RectangleLattice.box (fun _ : Fin 12 => 1))
  rw [tsum_gaussian_eq_theta_pow 12 hs, gaussian_cube_sum] at h
  change _ = heatComplement s at h
  rw [← h]
  apply tsum_congr
  intro k
  simp only [heatTerm, outsideCube_iff_not_mem]
  split_ifs <;> rfl

theorem heatComplement_nonneg {s : ℝ} (hs : 0 < s) : 0 ≤ heatComplement s := by
  rw [heatComplement_eq_tsum hs]
  exact tsum_nonneg (heatTerm_nonneg s)

theorem heatComplement_antitone : AntitoneOn heatComplement (Set.Ioi (0 : ℝ)) := by
  intro s hs t ht hst
  rw [heatComplement_eq_tsum hs, heatComplement_eq_tsum ht]
  apply (heatTerm_summable ht).tsum_le_tsum _ (heatTerm_summable hs)
  intro k
  unfold heatTerm gaussian Legacy.TorusEndpoint.GreenMultiplierSummability.radiusSq
  split_ifs
  · apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right (neg_le_neg hst) (Finset.sum_nonneg (fun i _ => sq_nonneg _))
  · exact le_rfl

#print axioms heatComplement_eq_tsum
#print axioms heatComplement_antitone
end BecknerOnofri.HighDim.EntropyTail
