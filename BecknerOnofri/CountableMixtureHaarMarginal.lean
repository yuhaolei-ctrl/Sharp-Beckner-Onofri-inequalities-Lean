import BecknerOnofri.CountableMixtureL1
import BecknerOnofri.EntropyShearer.L1Contraction

/-! Actual Haar marginalization of unrestricted countable probability mixtures.
The equality is almost everywhere, as is appropriate on the full L1 domain. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Topology ENNReal
open Finset MeasureTheory Filter
namespace BecknerOnofri.CosineMixtureTransfer
open Legacy.TorusEndpoint Legacy.BecknerOnofri
open HighDim.EntropyShearer

lemma drop_measurePreserving {d : ℕ} (i : Fin (d+1)) :
    MeasurePreserving (drop i) (torusMeasure (d+1)) (torusMeasure d) := by
  exact (measurePreserving_snd (μ := AddCircle.haarAddCircle) (ν := torusMeasure d)).comp
    (measurePreserving_piFinSuccAbove (fun _ : Fin (d+1) => AddCircle.haarAddCircle) i)

lemma fullAvg_finite_mixture {d : ℕ} (i : Fin (d+1)) (s : Finset ℕ)
    (w : ℕ → ℝ) (N : ℕ → Fin (d+1) → ℕ) (hw : ∀ n, 0 ≤ w n) :
    fullAvg {i} (CosineMixture.mixture s w N) =
      fun x => CosineMixture.mixture s w (fun n => drop i (N n)) (drop i x) := by
  have hb : BoundedMeasurable (CosineMixture.mixture s w N) := by
    refine ⟨(CosineMixture.mixture_continuous _ _ _).measurable,
      ∑ n ∈ s, w n * CosineMixture.tensor (N n) 0, ?_⟩
    intro x
    exact (norm_sum_le _ _).trans (sum_le_sum (fun n _ =>
      CosineMixtureApproximation.term_norm_le w N hw n x))
  rw [fullAvg_eq_avg _ hb, avg_singleton]
  funext x
  unfold CosineMixture.mixture
  rw [integral_finsetSum]
  · apply sum_congr rfl
    intro n hn
    rw [integral_const_mul, tensor_marginal]
  · intro n hn
    exact (((CosineMixture.tensor_continuous _).comp
      (continuous_const.update i continuous_id)).const_mul _).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)

theorem fullAvg_countable_mixture {d : ℕ} (i : Fin (d+1)) (w : ℕ → ℝ)
    (N : ℕ → Fin (d+1) → ℕ) (hw : ∀ n, 0 ≤ w n) (hm : HasSum w 1) :
    fullAvg {i} (CosineMixtureApproximation.rho w N) =ᵐ[torusMeasure (d+1)]
      (fun x => CosineMixtureApproximation.rho w (fun n => drop i (N n)) (drop i x)) := by
  let F := fullAvg {i} (CosineMixtureApproximation.rho w N)
  let G := fun x => CosineMixtureApproximation.rho w (fun n => drop i (N n)) (drop i x)
  have hρ := rho_integrable_mass_one w N hw hm
  have hF : Integrable F (torusMeasure (d+1)) := fullAvg_integrable {i} hρ
  have hG : Integrable G (torusMeasure (d+1)) :=
    (drop_measurePreserving i).integrable_comp_of_integrable (rho_integrable_mass_one w _ hw hm)
  have hb (m : ℕ) : (∫ x, ‖F x-G x‖ ∂torusMeasure (d+1)) ≤
      2*(1-∑ n ∈ range m, w n) := by
    let M := fullAvg {i} (CosineMixture.mixture (range m) w N)
    have hM : Integrable M (torusMeasure (d+1)) :=
      fullAvg_integrable {i} (CosineMixture.mixture_integrable _ _ _)
    have h1 := fullAvg_l1_contraction {i} hρ (CosineMixture.mixture_integrable (range m) w N)
    have h2 : (∫ x, ‖M x-G x‖ ∂torusMeasure (d+1)) = 1-∑ n ∈ range m, w n := by
      dsimp only [M, G]
      rw [fullAvg_finite_mixture i (range m) w N hw]
      simp only [Pi.sub_apply]
      rw [integral_drop i (fun x => ‖CosineMixture.mixture (range m) w (fun n => drop i (N n)) x -
        CosineMixtureApproximation.rho w (fun n => drop i (N n)) x‖)]
      rw [show (fun x => ‖CosineMixture.mixture (range m) w _ x - CosineMixtureApproximation.rho w _ x‖) =
        (fun x => ‖CosineMixtureApproximation.rho w _ x - CosineMixture.mixture (range m) w _ x‖) from
          funext (fun x => norm_sub_rev _ _)]
      exact mixture_partial_l1_exact w _ hw hm m
    calc
      _ ≤ ∫ x, (‖F x-M x‖ + ‖M x-G x‖) ∂torusMeasure (d+1) := by
        apply integral_mono (hF.sub hG).norm ((hF.sub hM).norm.add (hM.sub hG).norm)
        intro x
        simpa only [dist_eq_norm, Pi.sub_apply, Pi.add_apply] using! dist_triangle (F x) (M x) (G x)
      _ = (∫ x, ‖F x-M x‖ ∂torusMeasure (d+1)) + (1-∑ n ∈ range m, w n) := by
        rw [integral_add (f := fun x => ‖F x-M x‖) (g := fun x => ‖M x-G x‖)
          (hF.sub hM).norm (hM.sub hG).norm, h2]
      _ ≤ (1-∑ n ∈ range m, w n) + (1-∑ n ∈ range m, w n) := by
        exact add_le_add (h1.trans_eq (mixture_partial_l1_exact w N hw hm m)) le_rfl
      _ = _ := by ring
  have hlim : Tendsto (fun m => 2*(1-∑ n ∈ range m, w n)) atTop (𝓝 (0:ℝ)) := by
    simpa using ((tendsto_const_nhds (x := (1:ℝ))).sub hm.tendsto_sum_nat).const_mul (2:ℝ)
  have hz : (∫ x, ‖F x-G x‖ ∂torusMeasure (d+1)) = 0 :=
    le_antisymm (ge_of_tendsto hlim (Eventually.of_forall hb))
      (integral_nonneg (fun _ => norm_nonneg _))
  have hae := (integral_eq_zero_iff_of_nonneg_ae
    (ae_of_all _ (fun x => norm_nonneg (F x-G x))) (hF.sub hG).norm).mp hz
  filter_upwards [hae] with x hx
  exact sub_eq_zero.mp (norm_eq_zero.mp hx)

#print axioms fullAvg_finite_mixture
#print axioms fullAvg_countable_mixture
end BecknerOnofri.CosineMixtureTransfer
