import Legacy.BecknerOnofri.EndpointClosure
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Bounded continuous density approximations converge in L1 and entropy.
These lemmas require no positivity lower bound. -/

noncomputable section
open MeasureTheory Filter Legacy.TorusEndpoint
open scoped Topology

namespace Legacy.BecknerOnofri.UniformDensityLimits

theorem L1_tendsto_of_bounded_pointwise {d : ℕ} (f : ℕ → Torus d → ℝ)
    (g : Torus d → ℝ) (hf : ∀ n, Continuous (f n)) (hg : Continuous g)
    (B : ℝ) (hB : ∀ n x, ‖f n x‖ ≤ B)
    (hlim : ∀ x, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    Tendsto (fun n => ∫ x, ‖f n x - g x‖ ∂torusMeasure d) atTop (𝓝 0) := by
  have hgB (x : Torus d) : ‖g x‖ ≤ B :=
    le_of_tendsto (hlim x).norm (Eventually.of_forall (fun n => hB n x))
  have h := tendsto_integral_filter_of_norm_le_const
    (μ := torusMeasure d) (F := fun n x => ‖f n x - g x‖) (f := fun _ => (0 : ℝ))
    (Eventually.of_forall (fun n => ((hf n).sub hg).norm.aestronglyMeasurable))
    ⟨2 * B, Eventually.of_forall (fun n => ae_of_all _ (fun x => by
      rw [norm_norm]
      exact (norm_sub_le _ _).trans (by linarith [hB n x, hgB x])))⟩
    (ae_of_all _ (fun x => by simpa using ((hlim x).sub_const (g x)).norm))
  simpa using h

theorem entropy_tendsto_of_bounded_pointwise {d : ℕ} (f : ℕ → Torus d → ℝ)
    (g : Torus d → ℝ) (hf : ∀ n, Continuous (f n))
    (B : ℝ) (hB : ∀ n x, ‖f n x‖ ≤ B)
    (hlim : ∀ x, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    Tendsto (fun n => densityEntropy (f n)) atTop (𝓝 (densityEntropy g)) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Set.Icc (-B) B) Real.continuous_mul_log.continuousOn
  apply tendsto_integral_filter_of_norm_le_const
    (Eventually.of_forall (fun n =>
      (Real.continuous_mul_log.comp (hf n)).aestronglyMeasurable))
    ⟨C, Eventually.of_forall (fun n => ae_of_all _ (fun x =>
      hC (f n x) (abs_le.mp (by simpa [Real.norm_eq_abs] using hB n x))))⟩
  exact ae_of_all _ (fun x => Real.continuous_mul_log.continuousAt.tendsto.comp (hlim x))

theorem L1_tendsto_of_uniform {d : ℕ} (f : ℕ → Torus d → ℝ)
    (g : Torus d → ℝ) (hf : ∀ n, Continuous (f n)) (hg : Continuous g)
    (B : ℝ) (hB : ∀ n x, ‖f n x‖ ≤ B)
    (hlim : TendstoUniformly f g atTop) :
    Tendsto (fun n => ∫ x, ‖f n x - g x‖ ∂torusMeasure d) atTop (𝓝 0) :=
  L1_tendsto_of_bounded_pointwise f g hf hg B hB hlim.tendsto_at

theorem entropy_tendsto_of_uniform {d : ℕ} (f : ℕ → Torus d → ℝ)
    (g : Torus d → ℝ) (hf : ∀ n, Continuous (f n))
    (B : ℝ) (hB : ∀ n x, ‖f n x‖ ≤ B)
    (hlim : TendstoUniformly f g atTop) :
    Tendsto (fun n => densityEntropy (f n)) atTop (𝓝 (densityEntropy g)) :=
  entropy_tendsto_of_bounded_pointwise f g hf B hB hlim.tendsto_at

end Legacy.BecknerOnofri.UniformDensityLimits
