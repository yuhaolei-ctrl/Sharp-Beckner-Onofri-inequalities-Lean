module

public import BecknerOnofri.CountableMixtureHaarMarginal

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Topology
open Finset MeasureTheory Filter
namespace BecknerOnofri.CosineMixtureTransfer
open Legacy.TorusEndpoint Legacy.BecknerOnofri Legacy.D10
open HighDim.EntropyShearer

/-- Zeroing an index integrates out that coordinate's normalized cosine power. -/
def maskIndex {d : ℕ} (I : Finset (Fin d)) (N : Fin d → ℕ) : Fin d → ℕ :=
  fun i => if i ∈ I then N i else 0

lemma fullAvg_tensor {d : ℕ} (I : Finset (Fin d)) (N : Fin d → ℕ) :
    fullAvg Iᶜ (CosineMixture.tensor N) = CosineMixture.tensor (maskIndex I N) := by
  funext x
  change (∫ y, ∏ i, cosinePower (N i) (if i ∈ Iᶜ then y i else x i)
    ∂torusMeasure d) = ∏ i, cosinePower (maskIndex I N i) (x i)
  rw [torusMeasure_explicit, integral_fintype_prod_eq_prod
    (fun i y => cosinePower (N i) (if i ∈ Iᶜ then y else x i))]
  apply prod_congr rfl
  intro i hi
  by_cases hI : i ∈ I
  · simp [hI, maskIndex]
  · simp only [mem_compl, hI, not_false_eq_true, if_true, maskIndex, if_false]
    rw [CosineFourier.mass]
    simp [cosinePower]

lemma fullAvg_finite_mixture_subset {d : ℕ} (I : Finset (Fin d)) (s : Finset ℕ)
    (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ) :
    fullAvg Iᶜ (CosineMixture.mixture s w N) =
      CosineMixture.mixture s w (fun n => maskIndex I (N n)) := by
  funext x
  change (∫ y, ∑ n ∈ s, w n * CosineMixture.tensor (N n) (mix Iᶜ (x,y))
    ∂torusMeasure d) = _
  rw [integral_finsetSum]
  · unfold CosineMixture.mixture
    apply sum_congr rfl
    intro n hn
    rw [integral_const_mul]
    exact congrArg (fun v => w n*v x) (fullAvg_tensor I (N n))
  · intro n hn
    have hc : Continuous (fun y => w n * CosineMixture.tensor (N n) (mix Iᶜ (x,y))) := by
      apply Continuous.const_mul
      apply (CosineMixture.tensor_continuous _).comp
      unfold mix
      apply continuous_pi
      intro i
      by_cases hi : i ∈ Iᶜ
      · simp only [hi, if_true]; exact continuous_apply i
      · simp only [hi, if_false]; exact continuous_const
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- Every coordinate marginal is again a countable probability mixture,
with no extra boundedness, smoothness, or entropy assumption. -/
theorem fullAvg_countable_mixture_subset {d : ℕ} (I : Finset (Fin d))
    (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ) (hw : ∀ n, 0 ≤ w n) (hm : HasSum w 1) :
    fullAvg Iᶜ (CosineMixtureApproximation.rho w N) =ᵐ[torusMeasure d]
      CosineMixtureApproximation.rho w (fun n => maskIndex I (N n)) := by
  let F := fullAvg Iᶜ (CosineMixtureApproximation.rho w N)
  let G := CosineMixtureApproximation.rho w (fun n => maskIndex I (N n))
  have hρ := rho_integrable_mass_one w N hw hm
  have hF : Integrable F (torusMeasure d) := fullAvg_integrable Iᶜ hρ
  have hG : Integrable G (torusMeasure d) := rho_integrable_mass_one w _ hw hm
  have hb (m : ℕ) : (∫ x, ‖F x-G x‖ ∂torusMeasure d) ≤ 2*(1-∑ n ∈ range m, w n) := by
    let M := fullAvg Iᶜ (CosineMixture.mixture (range m) w N)
    have hM : Integrable M (torusMeasure d) := fullAvg_integrable Iᶜ
      (CosineMixture.mixture_integrable _ _ _)
    have h1 := fullAvg_l1_contraction Iᶜ hρ (CosineMixture.mixture_integrable (range m) w N)
    have h2 : (∫ x, ‖M x-G x‖ ∂torusMeasure d) = 1-∑ n ∈ range m, w n := by
      dsimp only [M, G]
      rw [fullAvg_finite_mixture_subset]
      rw [show (fun x => ‖CosineMixture.mixture (range m) w _ x - CosineMixtureApproximation.rho w _ x‖) =
        (fun x => ‖CosineMixtureApproximation.rho w _ x - CosineMixture.mixture (range m) w _ x‖) from
          funext (fun x => norm_sub_rev _ _)]
      exact mixture_partial_l1_exact w _ hw hm m
    calc
      _ ≤ ∫ x, (‖F x-M x‖+‖M x-G x‖) ∂torusMeasure d := by
        apply integral_mono (hF.sub hG).norm ((hF.sub hM).norm.add (hM.sub hG).norm)
        intro x
        simpa only [dist_eq_norm, Pi.sub_apply, Pi.add_apply] using! dist_triangle (F x) (M x) (G x)
      _ = (∫ x, ‖F x-M x‖ ∂torusMeasure d)+(1-∑ n ∈ range m, w n) := by
        rw [integral_add (f := fun x => ‖F x-M x‖) (g := fun x => ‖M x-G x‖)
          (hF.sub hM).norm (hM.sub hG).norm, h2]
      _ ≤ (1-∑ n ∈ range m, w n)+(1-∑ n ∈ range m, w n) :=
        add_le_add (h1.trans_eq (mixture_partial_l1_exact w N hw hm m)) le_rfl
      _ = _ := by ring
  have hlim : Tendsto (fun m => 2*(1-∑ n ∈ range m, w n)) atTop (𝓝 (0:ℝ)) := by
    simpa using ((tendsto_const_nhds (x := (1:ℝ))).sub hm.tendsto_sum_nat).const_mul (2:ℝ)
  have hz : (∫ x, ‖F x-G x‖ ∂torusMeasure d) = 0 :=
    le_antisymm (ge_of_tendsto hlim (Eventually.of_forall hb))
      (integral_nonneg (fun _ => norm_nonneg _))
  have hae := (integral_eq_zero_iff_of_nonneg_ae
    (ae_of_all _ (fun x => norm_nonneg (F x-G x))) (hF.sub hG).norm).mp hz
  filter_upwards [hae] with x hx
  exact sub_eq_zero.mp (norm_eq_zero.mp hx)

#print axioms fullAvg_countable_mixture_subset
end BecknerOnofri.CosineMixtureTransfer
