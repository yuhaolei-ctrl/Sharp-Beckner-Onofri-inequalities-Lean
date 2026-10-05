import BecknerOnofri.EntropyTailAxisHeat
import BecknerOnofri.EntropyTailProductDeficit

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
namespace BecknerOnofri.HighDim.EntropyTail
open Legacy.BecknerOnofri.GaussianLattice

def mixedCoefficient (L : Fin 12 → ℕ) (k : Frequency 12) : ℝ :=
  ∏ i : Fin 12, scalarCoefficient (L i) (k i).natAbs

def mixedTail (L : Fin 12 → ℕ) : ℝ := ∑' k, scalarTailWeight k*mixedCoefficient L k

def mixedHeat (s : ℝ) (L : Fin 12 → ℕ) : ℝ := ∑' k, mixedCoefficient L k*heatTerm s k

theorem mixedCoefficient_component (L : Fin 12 → ℕ) (k : Frequency 12) :
    mixedCoefficient L k = RandomRectangles.componentCoeff L k := by
  simp only [mixedCoefficient, RandomRectangles.componentCoeff, Legacy.D10.binomialProduct, scalarCoefficient_eq]

theorem mixedCoefficient_nonneg (L : Fin 12 → ℕ) (k : Frequency 12) : 0 ≤ mixedCoefficient L k :=
  Finset.prod_nonneg (fun _ _ => scalarCoefficient_nonneg _ _)

theorem mixedTail_summable (L : Fin 12 → ℕ) :
    Summable (fun k => scalarTailWeight k*mixedCoefficient L k) := by
  simpa only [mixedCoefficient_component] using RandomRectangles.summable_weighted_component L scalarTailWeight

theorem mixedHeat_summable (s : ℝ) (L : Fin 12 → ℕ) :
    Summable (fun k => mixedCoefficient L k*heatTerm s k) := by
  simpa only [mixedCoefficient_component, mul_comm] using
    RandomRectangles.summable_weighted_component L (heatTerm s)

theorem mixedGaussian_summable (s : ℝ) (L : Fin 12 → ℕ) :
    Summable (fun k => mixedCoefficient L k*gaussian s k) := by
  simpa only [mixedCoefficient_component, mul_comm] using
    RandomRectangles.summable_weighted_component L (gaussian s)

theorem mixedGaussian_product (s : ℝ) (L : Fin 12 → ℕ) (k : Frequency 12) :
    mixedCoefficient L k*gaussian s k = ∏ i : Fin 12, axisTerm s (L i) (k i) := by
  rw [gaussian_eq_product, mixedCoefficient, ← Finset.prod_mul_distrib]
  rfl

theorem mixedGaussian_sum {s : ℝ} (hs : 0 < s) (L : Fin 12 → ℕ) :
    (∑' k, mixedCoefficient L k*gaussian s k) = ∏ i : Fin 12, (axisLow s (L i)+axisHigh s (L i)) := by
  have hn (i : Fin 12) : Summable (fun j : ℤ => ‖(axisTerm s (L i) j : ℂ)‖) := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (axisTerm_nonneg s (L i) _)] using
      axisTerm_summable hs (L i)
  have h := Legacy.TorusEndpoint.TorusHeatPositivity.finite_product_tsum 12
    (fun i j => (axisTerm s (L i) j : ℂ)) hn
  simp only [← Complex.ofReal_prod, ← Complex.ofReal_tsum] at h
  have hr := congrArg Complex.re h
  simp only [Complex.ofReal_re] at hr
  simp_rw [mixedGaussian_product, axisTerm_tsum hs] at hr ⊢
  exact hr

theorem mixedGaussian_cube (s : ℝ) (L : Fin 12 → ℕ) :
    (∑ k ∈ RectangleLattice.box (fun _ : Fin 12 => 1), mixedCoefficient L k*gaussian s k) =
      ∏ i : Fin 12, axisLow s (L i) := by
  simp_rw [mixedGaussian_product]
  change (∑ k ∈ Fintype.piFinset (fun _ : Fin 12 => Finset.Icc (-1 : ℤ) 1),
    ∏ i : Fin 12, axisTerm s (L i) (k i)) = _
  rw [← Finset.prod_univ_sum]
  apply Finset.prod_congr rfl
  intro i _
  have he : Finset.Icc (-1 : ℤ) 1 = {-1,0,1} := by decide +kernel
  rw [he]
  have hz : scalarCoefficient (L i) 0 = 1 := by
    simp [scalarCoefficient_eq, Legacy.D10.binomialCoeffReal]
  norm_num [axisTerm, axisLow, hz]
  ring

attribute [local irreducible] RectangleLattice.box

theorem mixedHeat_product {s : ℝ} (hs : 0 < s) (L : Fin 12 → ℕ) :
    mixedHeat s L = (∏ i : Fin 12, (axisLow s (L i)+axisHigh s (L i)))-
      (∏ i : Fin 12, axisLow s (L i)) := by
  have h := finite_complement_tsum (fun k => mixedCoefficient L k*gaussian s k)
    (mixedGaussian_summable s L) (RectangleLattice.box (fun _ : Fin 12 => 1))
  rw [mixedGaussian_sum hs, mixedGaussian_cube] at h
  rw [← h]
  unfold mixedHeat
  apply tsum_congr
  intro k
  simp only [heatTerm, outsideCube_iff_not_mem]
  split_ifs <;> simp only [mul_zero]

theorem mixedHeat_diagonal {s : ℝ} (hs : 0 < s) (n : ℕ) :
    mixedHeat s (fun _ => n) = (axisLow s n+axisHigh s n)^12-(axisLow s n)^12 := by
  rw [mixedHeat_product hs]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem mixedHeat_le_diagonal {s : ℝ} (hs : 0 < s) (L : Fin 12 → ℕ) :
    mixedHeat s L ≤ (1/12 : ℝ)*∑ i : Fin 12, mixedHeat s (fun _ => L i) := by
  rw [mixedHeat_product hs]
  simp_rw [mixedHeat_diagonal hs]
  simpa only [Nat.cast_ofNat, one_div] using
    DiscreteLayers.product_deficit_comparison (by norm_num : 0 < 12)
      (axisLow s) (axisHigh s) (axisLow_nonneg s) (axisHigh_nonneg s)
      (axisLow_monotone s) (axisHigh_monotone s) L

#print axioms mixedHeat_le_diagonal
end BecknerOnofri.HighDim.EntropyTail
