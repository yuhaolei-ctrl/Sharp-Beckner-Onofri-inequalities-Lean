module

public import BecknerOnofri.SpinPrefixTree
public import BecknerOnofri.SpinEntropyChainScalar

@[expose] public section

/-! The finite spin entropy chain and its comparison with the actual
conditional angle means. Prefix events are counted exactly once. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace BecknerOnofri.HighDim.Spin
open EntropyShearer ConditionalEntropy

def prefixEntropy (f : Torus 12 → ℝ) (k : ℕ) : ℝ :=
  ∑ σ ∈ (prefixSet k).powerset, prefixMass f k σ * Real.log (2 ^ k * prefixMass f k σ)

theorem prefixEntropy_zero {f : Torus 12 → ℝ} (hm : (∫ x, f x ∂torusMeasure 12) = 1) :
    prefixEntropy f 0 = 0 := by
  simp [prefixEntropy, prefixMass, prefixLikelihood, hm]

theorem prefix_entropy_children {f : Torus 12 → ℝ} (hf : PositiveBounded f)
    (i : Fin 12) {σ : Configuration} (hσ : σ ⊆ prefixSet i.val) :
    prefixMass f (i.val + 1) σ * Real.log (2 ^ (i.val + 1) * prefixMass f (i.val + 1) σ) +
      prefixMass f (i.val + 1) (insert i σ) *
        Real.log (2 ^ (i.val + 1) * prefixMass f (i.val + 1) (insert i σ)) =
    prefixMass f i.val σ * Real.log (2 ^ i.val * prefixMass f i.val σ) +
      prefixMass f i.val σ * binaryCost
        ((∫ x, f x * (prefixLikelihood i.val σ x * torusCosines x i) ∂torusMeasure 12) /
          prefixMass f i.val σ) := by
  have h := binary_entropy_split (prefixMass_positive hf (i.val + 1) (insert i σ))
    (prefixMass_positive hf (i.val + 1) σ) (show (0 : ℝ) < 2 ^ i.val by positivity)
  rw [(prefixMass_children hf i hσ).1, (prefixMass_children hf i hσ).2] at h
  have he : (2 : ℝ) * 2 ^ i.val = 2 ^ (i.val + 1) := by rw [pow_succ]; ring
  rw [he] at h
  simpa only [add_comm] using h

theorem prefixEntropy_step {f : Torus 12 → ℝ} (hf : PositiveBounded f) (i : Fin 12) :
    prefixEntropy f (i.val + 1) = prefixEntropy f i.val +
      ∑ σ ∈ (prefixSet i.val).powerset, prefixMass f i.val σ * binaryCost
        ((∫ x, f x * (prefixLikelihood i.val σ x * torusCosines x i) ∂torusMeasure 12) /
          prefixMass f i.val σ) := by
  unfold prefixEntropy
  rw [prefixSet_step, Finset.sum_powerset_insert (by simp : i ∉ prefixSet i.val),
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro σ hσ
  exact prefix_entropy_children hf i (Finset.mem_powerset.mp hσ)

theorem conditional_binaryCost_bounded {f : Torus 12 → ℝ} (hf : PositiveBounded f)
    (i : Fin 12) : BoundedMeasurable (fun x => binaryCost (conditionalCosineMoment f i 1 x)) := by
  have hu := conditional_moment_bounded hf i 1
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image
    (binaryCost_continuous.norm.continuousOn :
      ContinuousOn (fun t => ‖binaryCost t‖) (Set.Icc (-1 : ℝ) 1))
  refine ⟨binaryCost_continuous.measurable.comp hu.1, C, fun x => ?_⟩
  exact hC (Set.mem_image_of_mem (fun t => ‖binaryCost t‖)
    (abs_le.mp (conditional_moment_abs_le_one hf i 1 x)))

theorem sum_prefix_posterior_bound {f : Torus 12 → ℝ} (hf : PositiveBounded f) (i : Fin 12) :
    (∑ σ ∈ (prefixSet i.val).powerset, prefixMass f i.val σ * binaryCost
        ((∫ x, f x * (prefixLikelihood i.val σ x * torusCosines x i) ∂torusMeasure 12) /
          prefixMass f i.val σ)) ≤
      ∫ x, f x * binaryCost (conditionalCosineMoment f i 1 x) ∂torusMeasure 12 := by
  have hb := conditional_binaryCost_bounded hf i
  calc
    _ ≤ ∑ σ ∈ (prefixSet i.val).powerset,
        ∫ x, f x * (prefixLikelihood i.val σ x * binaryCost (conditionalCosineMoment f i 1 x))
          ∂torusMeasure 12 := by
      apply Finset.sum_le_sum
      intro σ hσ
      exact (posterior_binary_entropy hf i σ).2
    _ = ∫ x, ∑ σ ∈ (prefixSet i.val).powerset,
        f x * (prefixLikelihood i.val σ x * binaryCost (conditionalCosineMoment f i 1 x))
          ∂torusMeasure 12 := by
      rw [integral_finsetSum]
      intro σ hσ
      exact (hf.bounded.mul ((prefixLikelihood_bounded i.val σ).mul hb)).integrable
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [← Finset.mul_sum, ← Finset.sum_mul, prefixLikelihood_sum i.val i.isLt.le]
      simp

theorem prefixEntropy_step_le {f : Torus 12 → ℝ} (hf : PositiveBounded f) (i : Fin 12) :
    prefixEntropy f (i.val + 1) ≤ prefixEntropy f i.val +
      ∫ x, f x * binaryCost (conditionalCosineMoment f i 1 x) ∂torusMeasure 12 := by
  rw [prefixEntropy_step hf]
  exact add_le_add le_rfl (sum_prefix_posterior_bound hf i)

theorem prefixEntropy_le {f : Torus 12 → ℝ} (hf : PositiveBounded f)
    (hm : (∫ x, f x ∂torusMeasure 12) = 1) (k : ℕ) (hk : k ≤ 12) :
    prefixEntropy f k ≤ ∑ i ∈ prefixSet k,
      ∫ x, f x * binaryCost (conditionalCosineMoment f i 1 x) ∂torusMeasure 12 := by
  induction k with
  | zero => simp [prefixEntropy_zero hm]
  | succ k ih =>
    let i : Fin 12 := ⟨k, by omega⟩
    change prefixEntropy f (i.val + 1) ≤ _
    calc
      _ ≤ prefixEntropy f i.val +
          ∫ x, f x * binaryCost (conditionalCosineMoment f i 1 x) ∂torusMeasure 12 :=
        prefixEntropy_step_le hf i
      _ ≤ (∑ j ∈ prefixSet i.val,
          ∫ x, f x * binaryCost (conditionalCosineMoment f j 1 x) ∂torusMeasure 12) +
          ∫ x, f x * binaryCost (conditionalCosineMoment f i 1 x) ∂torusMeasure 12 :=
        add_le_add (ih (by omega)) le_rfl
      _ = _ := by
        change _ = ∑ j ∈ prefixSet (i.val + 1), _
        rw [prefixSet_step, Finset.sum_insert (by simp)]
        ring

theorem channel_entropy_le_conditional (ρ : ProbabilityDensity 12)
    (hρ : PositiveBounded ρ.value) :
    (∑ σ : Configuration, channelLaw ρ σ * Real.log (channelLaw ρ σ / (1 / 4096))) ≤
      ∑ i : Fin 12, ∫ x, ρ.value x * binaryCost (conditionalCosineMoment ρ.value i 1 x)
        ∂torusMeasure 12 := by
  have h := prefixEntropy_le hρ ρ.mass 12 le_rfl
  have he : prefixEntropy ρ.value 12 =
      ∑ σ : Configuration, channelLaw ρ σ * Real.log (channelLaw ρ σ / (1 / 4096)) := by
    unfold prefixEntropy
    rw [prefixSet_twelve]
    simp only [Finset.powerset_univ]
    apply Finset.sum_congr rfl
    intro σ hσ
    have hm : prefixMass ρ.value 12 σ = channelLaw ρ σ := by
      unfold prefixMass channelLaw
      simp only [prefixLikelihood_full]
    rw [hm]
    congr 2
    norm_num
    ring
  rw [he, prefixSet_twelve] at h
  exact h

#print axioms prefixEntropy_step
#print axioms channel_entropy_le_conditional
end BecknerOnofri.HighDim.Spin
