module

public import BecknerOnofri.SpinMixtureCap

@[expose] public section

/-! The actual positive-mixture spin law belongs to the full thirteen-state
feasible domain, including its all-minus probability cap. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped BigOperators
namespace BecknerOnofri.HighDim.Spin
open Legacy.BecknerOnofri

theorem mixture_minus_spin_bound (w : ℕ → ℝ) (N : ℕ → Fin 12 → ℕ)
    (hw : ∀ n,0≤w n) (hm : HasSum w 1)
    (hSup : Summable (fun n => w n*CosineMixture.tensor (N n) 0)) :
    (∫ x : Torus 12,CosineMixtureApproximation.rho w N x*channel (torusCosines x) ∅
      ∂torusMeasure 12)≤1/4096 := by
  let F : ℕ → Torus 12 → ℝ := fun n x => w n*CosineMixture.tensor (N n) x*channel (torusCosines x) ∅
  have hi (n : ℕ) : Integrable (F n) (torusMeasure 12) := by
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    exact ((CosineMixture.tensor_continuous (N n)).const_mul (w n)).mul (channel_continuous ∅)
  have hpoint (n : ℕ) (x : Torus 12) : ‖F n x‖≤w n*CosineMixture.tensor (N n) 0 := by
    have hnon := channel_nonneg (torusCosines_bound x) ∅
    have hone := channel_le_one (torusCosines_bound x) ∅
    dsimp [F]
    rw [abs_mul,abs_of_nonneg hnon]
    calc
      ‖w n*CosineMixture.tensor (N n) x‖*channel (torusCosines x) ∅≤
          ‖w n*CosineMixture.tensor (N n) x‖*1 := mul_le_mul_of_nonneg_left hone (norm_nonneg _)
      _ ≤w n*CosineMixture.tensor (N n) 0 := by
        simpa using CosineMixtureApproximation.term_norm_le w N hw n x
  have hnorm (n : ℕ) : (∫ x, ‖F n x‖ ∂torusMeasure 12)≤w n*CosineMixture.tensor (N n) 0 := by
    have h := integral_mono (hi n).norm (integrable_const (w n*CosineMixture.tensor (N n) 0)) (hpoint n)
    simpa using h
  have hsumNorm : Summable (fun n => ∫ x,‖F n x‖ ∂torusMeasure 12) :=
    hSup.of_nonneg_of_le (fun n => integral_nonneg (fun _ => norm_nonneg _)) hnorm
  have hswap := integral_tsum_of_summable_integral_norm hi hsumNorm
  have hsum : Summable (fun n => ∫ x,F n x ∂torusMeasure 12) := by
    apply hsumNorm.of_nonneg_of_le
    · intro n
      exact integral_nonneg (fun x => mul_nonneg (mul_nonneg (hw n) (CosineMixture.tensor_nonneg _ _))
        (channel_nonneg (torusCosines_bound x) ∅))
    · intro n
      exact integral_mono (hi n) (hi n).norm (fun _ => le_abs_self _)
  have hterm (n : ℕ) : (∫ x,F n x ∂torusMeasure 12)≤w n*(1/4096) := by
    dsimp [F]
    simp_rw [mul_assoc]
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (tensor_minus_spin_bound (N n)) (hw n)
  have hbound := Summable.tsum_le_tsum hterm hsum (hm.summable.mul_right (1/4096))
  rw [tsum_mul_right,hm.tsum_eq,one_mul] at hbound
  have he : (fun x : Torus 12 => CosineMixtureApproximation.rho w N x*channel (torusCosines x) ∅)=
      (fun x => ∑' n,F n x) := by
    funext x
    dsimp [CosineMixtureApproximation.rho,F]
    rw [tsum_mul_right]
  rw [he,← hswap]
  exact hbound

theorem channel_count_feasible (ρ : ProbabilityDensity 12)
    (hρ : GenericCosineRepresentation.HasPositiveCosineMixture ρ.value) :
    Feasible (countLaw (channelLaw ρ)) := by
  refine ⟨countLaw_nonneg (channelLaw_nonneg ρ),?_,?_⟩
  · rw [countLaw_mass,channelLaw_mass]
  · have hzero : countLaw (channelLaw ρ) 0=channelLaw ρ ∅ := by
      simp [countLaw,countClass]
    rw [hzero,channelLaw]
    obtain ⟨w,N,hw,hm,hSup,he⟩ := hρ
    rw [he]
    exact mixture_minus_spin_bound w N hw hm hSup

#print axioms channel_count_feasible
end BecknerOnofri.HighDim.Spin
