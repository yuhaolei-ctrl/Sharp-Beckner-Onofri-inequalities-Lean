import BecknerOnofri.SpinCountLaw
import BecknerOnofri.SpinChannelDefinitions
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! The genuine binary-spin channel (5.48), for every Haar probability
density. Its normalization and joint cosine moments follow from finite product
identities and actual integrals, with no assumed channel comparison. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped BigOperators
namespace BecknerOnofri.HighDim.Spin

theorem channel_mass (c : Fin 12 → ℝ) : (∑ σ : Configuration,channel c σ)=1 := by
  simp only [channel]
  rw [← Fintype.prod_add]
  have he (i : Fin 12) : (1+c i)/2+(1-c i)/2=1 := by ring
  simp_rw [he]
  simp

theorem channel_nonneg {c : Fin 12 → ℝ} (hc : ∀ i,|c i|≤1) (σ : Configuration) :
    0≤channel c σ := by
  apply mul_nonneg
  · exact Finset.prod_nonneg (fun i _ => by have h := (abs_le.mp (hc i)).1; linarith)
  · exact Finset.prod_nonneg (fun i _ => by have h := (abs_le.mp (hc i)).2; linarith)

theorem channel_le_one {c : Fin 12 → ℝ} (hc : ∀ i,|c i|≤1) (σ : Configuration) :
    channel c σ≤1 := by
  rw [← channel_mass c]
  exact Finset.single_le_sum (fun τ _ => channel_nonneg hc τ) (Finset.mem_univ σ)

theorem channel_jointSpin (c : Fin 12 → ℝ) (S : Finset (Fin 12)) :
    (∑ σ : Configuration,channel c σ*jointSpin S σ)=∏ i ∈ S,c i := by
  have he : (∑ σ : Configuration,channel c σ*jointSpin S σ)=
      ∏ i : Fin 12,((1+c i)/2+(1-c i)/2*(if i∈S then (-1:ℝ) else 1)) := by
    rw [Fintype.prod_add]
    apply Finset.sum_congr rfl
    intro σ _
    simp only [channel,jointSpin,Finset.prod_mul_distrib]
    ring
  rw [he]
  have hi (i : Fin 12) : (1+c i)/2+(1-c i)/2*(if i∈S then (-1:ℝ) else 1)=
      if i∈S then c i else 1 := by split_ifs <;> ring
  simp_rw [hi]
  simp [Finset.prod_ite]

theorem torusCosines_bound (x : Torus 12) (i : Fin 12) : |torusCosines x i|≤1 := by
  calc
    _ ≤ ‖fourier 1 (x i)‖ := Complex.abs_re_le_norm _
    _ = 1 := by simp [fourier_apply]

theorem channel_continuous (σ : Configuration) :
    Continuous (fun x : Torus 12 => channel (torusCosines x) σ) := by
  unfold channel torusCosines
  fun_prop

theorem channel_integrable (ρ : ProbabilityDensity 12) (σ : Configuration) :
    Integrable (fun x => ρ.value x*channel (torusCosines x) σ) (torusMeasure 12) := by
  apply ρ.integrable.mul_bdd (channel_continuous σ).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro x
  rw [Real.norm_eq_abs,abs_of_nonneg (channel_nonneg (torusCosines_bound x) σ)]
  exact channel_le_one (torusCosines_bound x) σ

theorem channelLaw_nonneg (ρ : ProbabilityDensity 12) (σ : Configuration) :
    0≤channelLaw ρ σ := by
  apply integral_nonneg_of_ae
  filter_upwards [ρ.nonneg] with x hx
  exact mul_nonneg hx (channel_nonneg (torusCosines_bound x) σ)

theorem channelLaw_mass (ρ : ProbabilityDensity 12) :
    (∑ σ : Configuration,channelLaw ρ σ)=1 := by
  simp only [channelLaw]
  rw [← integral_finset_sum _ (fun σ _ => channel_integrable ρ σ)]
  simp_rw [← Finset.mul_sum,channel_mass,mul_one]
  exact ρ.mass

/-- Exact joint-moment identity, before Fourier symmetry or entropy estimates. -/
theorem channelLaw_joint_moment (ρ : ProbabilityDensity 12) (S : Finset (Fin 12)) :
    (∑ σ : Configuration,channelLaw ρ σ*jointSpin S σ)=
      ∫ x,ρ.value x*(∏ i ∈ S,(fourier 1 (x i)).re) ∂torusMeasure 12 := by
  simp only [channelLaw,← integral_mul_const]
  rw [← integral_finset_sum _ (fun σ _ => (channel_integrable ρ σ).mul_const _)]
  congr 1
  funext x
  simp only [mul_assoc,← Finset.mul_sum,channel_jointSpin,torusCosines]

#print axioms channelLaw_mass
#print axioms channelLaw_joint_moment
end BecknerOnofri.HighDim.Spin
