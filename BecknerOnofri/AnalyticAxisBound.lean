import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-! An analytic map with zero first derivative and vanishing on a parameter
axis has the mixed quadratic bound needed in complement reduction. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter Asymptotics
open scoped Topology
namespace BecknerOnofri

variable {E K W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup K] [NormedSpace ℝ K]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem analytic_axis_bound {f : E × K → W} {a : E}
    (hf : AnalyticAt ℝ f (a, 0)) (hf' : HasFDerivAt (𝕜 := ℝ) f 0 (a, 0))
    (haxis : ∀ᶠ t in 𝓝 a, f (t, 0) = 0) :
    f =O[𝓝 (a, (0 : K))] (fun x => ‖x.2‖^2 + ‖x.1-a‖ * ‖x.2‖) := by
  obtain ⟨p, hp⟩ := hf
  have h1 : continuousMultilinearCurryFin1 ℝ (E × K) W (p 1) = 0 :=
    hp.hasFDerivAt.unique hf'
  have h1' (v : E × K) : p 1 (fun _ => v) = 0 := by
    exact congrArg (fun g : (E × K) →L[ℝ] W => g v) h1
  have ht : Tendsto (fun x : E × K => (x, (x.1, (0 : K))))
      (𝓝 (a, (0 : K))) (𝓝 ((a, (0 : K)), (a, (0 : K)))) :=
    (continuous_id.prodMk (continuous_fst.prodMk continuous_const)).continuousAt
  have hb := hp.isBigO_image_sub_norm_mul_norm_sub.comp_tendsto ht
  have hn (x : E × K) :
      ‖(x, (x.1, (0 : K))) - ((a, (0 : K)), (a, (0 : K)))‖ *
        ‖x - (x.1, (0 : K))‖ = max ‖x.1-a‖ ‖x.2‖ * ‖x.2‖ := by
    simp [Prod.norm_def, max_assoc, max_left_comm, max_comm, norm_nonneg]
  have hb' : (fun x : E × K => f x - f (x.1, 0)) =O[𝓝 (a, (0 : K))]
      (fun x => max ‖x.1-a‖ ‖x.2‖ * ‖x.2‖) := by
    convert hb using 1
    · funext x
      simp [h1']
    · funext x
      exact (hn x).symm
  have ha : ∀ᶠ x : E × K in 𝓝 (a, (0 : K)), f (x.1, 0) = 0 :=
    (continuous_fst.continuousAt : Tendsto (Prod.fst : E × K → E)
      (𝓝 (a, (0 : K))) (𝓝 a)).eventually haxis
  have hb'' : f =O[𝓝 (a, (0 : K))]
      (fun x => max ‖x.1-a‖ ‖x.2‖ * ‖x.2‖) :=
    hb'.congr' (ha.mono (fun x hx => by simp [hx])) (Eventually.of_forall (fun _ => rfl))
  apply hb''.trans
  apply IsBigO.of_bound 1
  apply Eventually.of_forall
  intro x
  have hm : max ‖x.1-a‖ ‖x.2‖ ≤ ‖x.1-a‖ + ‖x.2‖ :=
    max_le (le_add_of_nonneg_right (norm_nonneg _)) (le_add_of_nonneg_left (norm_nonneg _))
  simp only [norm_mul, norm_norm, Real.norm_eq_abs, abs_norm, abs_of_nonneg (by positivity :
    0 ≤ max ‖x.1-a‖ ‖x.2‖), abs_of_nonneg (by positivity :
    0 ≤ ‖x.2‖^2 + ‖x.1-a‖ * ‖x.2‖), one_mul]
  nlinarith [mul_le_mul_of_nonneg_right hm (norm_nonneg x.2)]

#print axioms analytic_axis_bound
end BecknerOnofri
