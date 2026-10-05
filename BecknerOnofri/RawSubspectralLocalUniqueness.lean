import BecknerOnofri.FullSobolevEmbedding
import BecknerOnofri.SubspectralLocalUniqueness
import BecknerOnofri.EulerEquation
import BecknerOnofri.PotentialRigidity

/-! Local uniqueness on the full raw H^d domain, using its continuous
representative and the exact Fourier form of the Euler equation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter Set
open scoped Topology
namespace BecknerOnofri.HighDim.RawSubspectralLocalUniqueness
open ContinuousGibbs ContinuousFirstShell FullSobolevEmbedding
open Legacy.BecknerOnofri.TorusSobolev

lemma exists_continuous_representative {d : ℕ} (hd : 0 < d) (u : Torus d → ℝ)
    (hu : InSobolev (d:ℝ) u) : ∃ v : Space d,
      (v : Torus d → ℝ) =ᵐ[torusMeasure d] u ∧ InSobolev (d:ℝ) v ∧
      ‖v‖ ≤ ‖inverseScaleLp hd‖*sobolevNorm (d:ℝ) u := by
  let U := Bridge.potentialLp u hu.1
  have hs : Summable (fun k => ‖fourierIsometry d U k‖) := by
    simpa only [U,Bridge.potentialLp_fourier] using fourier_summable hd u hu
  let v := ContinuousOptimizers.realRepresentative U hs
  have he : (v : Torus d → ℝ) =ᵐ[torusMeasure d] u := by
    filter_upwards [ContinuousOptimizers.realRepresentative_ae U hs,Bridge.potentialLp_ae u hu.1]
      with x hx hu'
    exact hx.trans (congrArg Complex.re hu')
  have hv : InSobolev (d:ℝ) v := (OnsetRaw.inSobolev_congr_ae he).mpr hu
  refine ⟨v,he,hv,?_⟩
  simpa only [OnsetRaw.sobolevNorm_congr_ae he] using continuous_norm_bound hd v hv

lemma gibbs_congr_ae {d : ℕ} {u v : Torus d → ℝ}
    (he : u =ᵐ[torusMeasure d] v) : normalizedGibbs u =ᵐ[torusMeasure d] normalizedGibbs v := by
  have hi : (∫ x, Real.exp (u x) ∂torusMeasure d) = ∫ x, Real.exp (v x) ∂torusMeasure d :=
    integral_congr_ae (he.fun_comp Real.exp)
  filter_upwards [he] with x hx
  simp only [normalizedGibbs,hi,hx]

lemma continuous_local_unique {d : ℕ} (hd : 0 < d) {β₀ : ℝ}
    (hβ : 0 < β₀) (hβσ : β₀ < spectralThreshold d) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (β : ℝ) (u : Space d),
      |β-β₀| < δ → ‖u‖ < δ → ReducedEquation.full d (β/spectralThreshold d) u = 0 → u=0 := by
  have hσ := spectralThreshold_pos hd
  have hlocal := SubspectralLocalUniqueness.local_unique hd
    (div_pos hβ hσ).le ((div_lt_one hσ).mpr hβσ)
  have hc : Tendsto (fun x : ℝ × Space d => (x.1/spectralThreshold d,x.2))
      (𝓝 (β₀,0)) (𝓝 (β₀/spectralThreshold d,0)) := by
    exact ((continuous_fst.div_const (spectralThreshold d)).prodMk continuous_snd).tendsto (β₀,(0:Space d))
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp (hc.eventually hlocal)
  refine ⟨δ,hδ,fun β u hb hu he => ?_⟩
  apply hball (a := (β,u)) ?_ he
  change dist (β,u) (β₀,(0:Space d)) < δ
  simpa only [Prod.dist_eq,Real.dist_eq,dist_zero_right,max_lt_iff] using And.intro hb hu

theorem local_unique {d : ℕ} (hd : 0 < d) {β₀ : ℝ}
    (hβ : 0 < β₀) (hβσ : β₀ < spectralThreshold d) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (β : ℝ) (u : Torus d → ℝ),
      |β-β₀| < ε → InSobolev (d:ℝ) u → MeanZero u → sobolevNorm (d:ℝ) u < ε →
      (∀ k : NonzeroFrequency d,
        ((frequencyLength k.val^d:ℝ):ℂ)*fourierCoeff u k.val =
          (β/spectralThreshold d:ℝ)*fourierCoeff (normalizedGibbs u) k.val) →
      u =ᵐ[torusMeasure d] (fun _ => 0) := by
  obtain ⟨δ,hδ,hlocal⟩ := continuous_local_unique hd hβ hβσ
  let C := ‖inverseScaleLp hd‖
  have hC : 0 ≤ C := norm_nonneg _
  let ε := min δ (δ/(C+1))
  have hε : 0 < ε := lt_min hδ (div_pos hδ (by positivity))
  refine ⟨ε,hε,fun β u hb hu hm hn hEuler => ?_⟩
  obtain ⟨v,hvu,hv,hbound⟩ := exists_continuous_representative hd u hu
  have hvn : ‖v‖ < δ := by
    have hsmall : sobolevNorm (d:ℝ) u < δ/(C+1) := hn.trans_le (min_le_right _ _)
    have hs := (lt_div_iff₀ (by positivity : 0 < C+1)).mp hsmall
    have hN : 0 ≤ sobolevNorm (d:ℝ) u := Real.sqrt_nonneg _
    change ‖v‖ ≤ C*sobolevNorm (d:ℝ) u at hbound
    nlinarith
  have hmv : MeanZero v := (integral_congr_ae hvu).trans hm
  have heq : ReducedEquation.full d (β/spectralThreshold d) v = 0 := by
    apply (ReducedEquation.full_zero_iff_stationary hd _ v).mpr
    refine ⟨hmv,fun k => ?_⟩
    rw [fourierCoeff_congr_ae hvu,fourierCoeff_congr_ae (gibbs_congr_ae hvu)]
    exact hEuler k
  have hv0 := hlocal β v (hb.trans_le (min_le_left _ _)) hvn heq
  rw [hv0] at hvu
  exact hvu.symm

#print axioms exists_continuous_representative
#print axioms local_unique
end BecknerOnofri.HighDim.RawSubspectralLocalUniqueness
