module

public import BecknerOnofri.ElevenTransitionZeroSet
public import BecknerOnofri.SubcriticalOptimizerCompactness
public import BecknerOnofri.SubcriticalOptimizerConvergence

@[expose] public section

/-! An explicit sequence of positive-pressure subcritical couplings decreasing
to the global transition, with a uniform genuine coercivity gap. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace BecknerOnofri.HighDim.Eleven
open ContinuousGibbs ContinuousFirstShell ContinuousOptimizers
open Legacy.BecknerOnofri.TorusSobolev Legacy.BecknerOnofri.SubcriticalAttainment

def transitionCoupling (n : ℕ) : ℝ :=
  globalTransition+(spectralThreshold 11-globalTransition)/2*(1/((n:ℝ)+1))

lemma transitionCoupling_bounds (n : ℕ) :
    globalTransition < transitionCoupling n ∧ transitionCoupling n < spectralThreshold 11 := by
  have hgap : 0 < spectralThreshold 11-globalTransition :=
    sub_pos.mpr (transition_upper.trans spectralThreshold_bounds.1)
  have hn : (1:ℝ) ≤ (n:ℝ)+1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have hi : 0 < 1/((n:ℝ)+1) := by positivity
  have hi1 : 1/((n:ℝ)+1) ≤ 1 := (div_le_one (by positivity)).mpr hn
  unfold transitionCoupling
  constructor
  · exact lt_add_of_pos_right _ (mul_pos (by linarith) hi)
  · nlinarith

lemma transitionCoupling_pos (n : ℕ) : 0 < transitionCoupling n :=
  transition_pos.trans (transitionCoupling_bounds n).1

lemma transitionCoupling_limit : Tendsto transitionCoupling atTop (𝓝 globalTransition) := by
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul
    ((spectralThreshold 11-globalTransition)/2)
  convert! h.const_add globalTransition using 1 <;> simp only [mul_zero, add_zero]

lemma transitionCoupling_pressure_pos (n : ℕ) : 0 < pressure 11 (transitionCoupling n) := by
  apply lt_of_le_of_ne (pressure_nonneg _ _)
  intro hz
  exact (transitionCoupling_bounds n).1.not_ge
    ((pressure_zero_iff (transitionCoupling_pos n).le).mp hz.symm)

lemma eleven_rough_gap :
    ∃ b Ab : ℝ, 0 < b ∧ RoughExponentialBound 11 b Ab ∧ 1/(4*b) < (1/2:ℝ) := by
  have hC : (1/2:ℝ) < Legacy.BecknerOnofri.endpointConstant 11 := by
    unfold Legacy.BecknerOnofri.endpointConstant
    change (1/2:ℝ) < (11:ℝ)/spectralThreshold 11
    apply (lt_div_iff₀ (spectralThreshold_pos (d := 11) (by norm_num))).mpr
    linarith [spectralThreshold_bounds.2]
  let b := ((1/2:ℝ)+Legacy.BecknerOnofri.endpointConstant 11)/2
  have hb : 0 < b := by dsimp [b]; linarith
  have hbd : b < Legacy.BecknerOnofri.endpointConstant 11 := by dsimp [b]; linarith
  have hg : 1/(4*b) < (1/2:ℝ) := by
    apply (div_lt_iff₀ (by positivity : 0 < 4*b)).mpr
    dsimp [b]
    linarith
  exact ⟨b, Legacy.BecknerOnofri.GreenRoughEnergy.partition 11 b, hb,
    GenericAttainment.rough_bound (by norm_num) hb hbd, hg⟩

lemma normalized_coefficient_gt_half {β : ℝ} (hβ : 0 < β) (hb : β < spectralThreshold 11) :
    (1/2:ℝ) < spectralThreshold 11/(2*β) := by
  apply (lt_div_iff₀ (by positivity : 0 < 2*β)).mpr
  linarith

lemma exists_nonzero_optimizer (n : ℕ) :
    ∃ u : Space 11, InCriticalSobolev u ∧ MeanZero u ∧
      (∀ v : Torus 11 → ℝ, InCriticalSobolev v →
        dualFunctional (transitionCoupling n) v ≤ dualFunctional (transitionCoupling n) u) ∧
      ReducedEquation.full 11 (transitionCoupling n/spectralThreshold 11) u = 0 ∧ u ≠ 0 := by
  have hb : transitionCoupling n < 2*(11:ℝ) := by
    have hh := (transitionCoupling_bounds n).2.trans spectralThreshold_bounds.2
    norm_num at *
    exact hh
  obtain ⟨u,hu,hm,_,_,_,hmax,hfull⟩ := exists_continuous_optimizer (d := 11) (by norm_num)
    (transitionCoupling_pos n) hb
  refine ⟨u,hu,hm,hmax,hfull,?_⟩
  intro he
  have hp := transitionCoupling_pressure_pos n
  rw [OptimizerDuality.pressure_eq_dual (by norm_num) (transitionCoupling_pos n) u hu hmax] at hp
  rw [dualFunctional_eq_toL2 (by norm_num) _ u hu hm, he, map_zero] at hp
  simpa using hp

#print axioms exists_nonzero_optimizer
end BecknerOnofri.HighDim.Eleven
