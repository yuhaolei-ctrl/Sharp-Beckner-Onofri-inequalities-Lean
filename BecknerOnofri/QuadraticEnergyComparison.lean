import BecknerOnofri.AnalyticEvenOrder

noncomputable section
open Filter Asymptotics
open scoped Topology
namespace BecknerOnofri

theorem quadratic_energy_compare {f g : ℝ → ℝ} {a b : ℝ} (hab : a<b)
    (hf : (fun δ => f δ-a*δ^2) =O[𝓝[>] (0:ℝ)] (fun δ => ‖δ‖^3))
    (hg : (fun δ => g δ-b*δ^2) =O[𝓝[>] (0:ℝ)] (fun δ => ‖δ‖^3)) :
    ∀ᶠ δ in 𝓝[>] (0:ℝ), f δ<g δ := by
  obtain ⟨C,hC⟩ := hf.exists_pos
  obtain ⟨D,hD⟩ := hg.exists_pos
  have ht : Tendsto (fun δ : ℝ => (C+D)*δ) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have hc : Continuous (fun δ : ℝ => (C+D)*δ) := continuous_const.mul continuous_id
    simpa only [mul_zero] using
      (hc.tendsto (0:ℝ)).mono_left
        (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
  filter_upwards [hC.2.bound,hD.2.bound,ht.eventually (gt_mem_nhds (sub_pos.mpr hab)),
    self_mem_nhdsWithin] with δ hf hg hs hδ
  change 0<δ at hδ
  simp only [Real.norm_eq_abs,abs_pow,abs_abs,abs_of_pos hδ] at hf hg
  have hfu := (abs_le.mp hf).2
  have hgl := (abs_le.mp hg).1
  have hm := mul_lt_mul_of_pos_right hs (sq_pos_of_pos hδ)
  nlinarith

#print axioms quadratic_energy_compare
end BecknerOnofri
