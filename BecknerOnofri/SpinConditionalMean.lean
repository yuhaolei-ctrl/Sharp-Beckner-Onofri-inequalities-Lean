import BecknerOnofri.SpinPrefixDefinitions
import BecknerOnofri.BinarySpinChannel
import BecknerOnofri.ConditionalWeightedTower

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace BecknerOnofri.HighDim.Spin
open EntropyShearer ConditionalEntropy

theorem prefixLikelihood_continuous (k : ℕ) (σ : Configuration) :
    Continuous (prefixLikelihood k σ) := by
  unfold prefixLikelihood torusCosines
  apply continuous_finset_prod
  intro j hj
  split_ifs <;> fun_prop

theorem prefixLikelihood_bounds (k : ℕ) (σ : Configuration) (x : Torus 12) :
    0 ≤ prefixLikelihood k σ x ∧ prefixLikelihood k σ x ≤ 1 := by
  have hfactor (j : Fin 12) :
      0 ≤ (if j ∈ σ then (1 + torusCosines x j) / 2 else (1 - torusCosines x j) / 2) ∧
      (if j ∈ σ then (1 + torusCosines x j) / 2 else (1 - torusCosines x j) / 2) ≤ 1 := by
    have hj := abs_le.mp (torusCosines_bound x j)
    split_ifs <;> constructor <;> linarith
  exact ⟨Finset.prod_nonneg (fun j _ => (hfactor j).1),
    Finset.prod_le_one (fun j _ => (hfactor j).1) (fun j _ => (hfactor j).2)⟩

theorem prefixLikelihood_bounded (k : ℕ) (σ : Configuration) :
    BoundedMeasurable (prefixLikelihood k σ) := by
  refine ⟨(prefixLikelihood_continuous k σ).measurable, 1, fun x => ?_⟩
  rw [Real.norm_eq_abs, abs_of_nonneg (prefixLikelihood_bounds k σ x).1]
  exact (prefixLikelihood_bounds k σ x).2

theorem prefixLikelihood_depends (k : ℕ) (σ : Configuration) (x y : Torus 12)
    (hxy : ∀ j : Fin 12, j.val < k → x j = y j) :
    prefixLikelihood k σ x = prefixLikelihood k σ y := by
  apply Finset.prod_congr rfl
  intro j hj
  have he := hxy j (Finset.mem_filter.mp hj).2
  simp only [torusCosines, he]

theorem conditional_spin_mean {f : Torus 12 → ℝ} (hf : PositiveBounded f)
    (i : Fin 12) (σ : Configuration) :
    (∫ x, f x * (prefixLikelihood i.val σ x * torusCosines x i) ∂torusMeasure 12) =
      ∫ x, f x * (prefixLikelihood i.val σ x * conditionalCosineMoment f i 1 x)
        ∂torusMeasure 12 := by
  simpa only [Nat.cast_one, torusCosines] using
    (conditional_moment_weighted_tower hf (prefixLikelihood_bounded i.val σ) i 1
      (prefixLikelihood_depends i.val σ)).symm

#print axioms conditional_spin_mean

end BecknerOnofri.HighDim.Spin
