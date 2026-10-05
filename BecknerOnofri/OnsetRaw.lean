import BecknerOnofri.OnsetSobolev

/-! The onset compactness theorem in the manuscript's actual raw-function,
β-normalized variational problem. Centering is explicit and no smoothness or
higher Sobolev membership is assumed. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace BecknerOnofri.HighDim.OnsetRaw
open Legacy.BecknerOnofri Legacy.TorusEndpoint
open TorusSobolev SubcriticalAttainment SobolevCentering
open RawAttainment

theorem dualFunctional_eq_normalized {d : ℕ} (hd : 0 < d) (β : ℝ)
    (u : HighDim.Torus d → ℝ) (hu : InCriticalSobolev u) :
    dualFunctional β u =
      (functional (spectralThreshold d/(2*β)) (center (Bridge.potentialLp u hu.1)) : EReal) := by
  rw [dualFunctional_eq_raw, rawFunctional_eq_legacy hd _ u hu]
  have hp : (2*Real.pi)^d ≠ 0 := (pow_pos (by positivity : (0:ℝ)<2*Real.pi) d).ne'
  have hc : spectralThreshold d/(2*β*(2*Real.pi)^d)*(2*Real.pi)^d =
      spectralThreshold d/(2*β) := by
    rw [div_mul_eq_div_div, div_mul_cancel₀ _ hp]
  rw [hc]

theorem sobolevTerm_congr_ae {d : ℕ} {u v : HighDim.Torus d → ℝ}
    (huv : u =ᵐ[HighDim.torusMeasure d] v) (s : ℝ) : sobolevTerm s u = sobolevTerm s v := by
  funext k
  unfold sobolevTerm
  congr 2
  apply congrArg norm
  apply integral_congr_ae
  filter_upwards [huv] with x hx
  rw [hx]

theorem inSobolev_congr_ae {d : ℕ} {u v : HighDim.Torus d → ℝ}
    (huv : u =ᵐ[HighDim.torusMeasure d] v) {s : ℝ} : InSobolev s u ↔ InSobolev s v := by
  simp only [InSobolev, memLp_congr_ae huv, sobolevTerm_congr_ae huv s]

theorem sobolevNorm_congr_ae {d : ℕ} {u v : HighDim.Torus d → ℝ}
    (huv : u =ᵐ[HighDim.torusMeasure d] v) (s : ℝ) : sobolevNorm s u = sobolevNorm s v := by
  simp only [sobolevNorm, sobolevTerm_congr_ae huv s]

/-- Every sequence of genuine global dual optimizers approaching β=σ_d
converges, after subtracting its actual Haar mean, in every fixed H^s norm. -/
theorem centered_optimizers_sobolev_tendsto_zero {d : ℕ} (hd : 12 ≤ d)
    (hEndpoint : EndpointRigidity.CoefficientEndpoint d (1/2))
    (hRigidity : OnsetCompactness.DensityRigidity d)
    {β : ℕ → ℝ} (hβ : Tendsto β atTop (𝓝 (spectralThreshold d)))
    (u : ℕ → HighDim.Torus d → ℝ) (hu : ∀ n, InCriticalSobolev (u n))
    (hmax : ∀ n (v : HighDim.Torus d → ℝ), InCriticalSobolev v →
      dualFunctional (β n) v ≤ dualFunctional (β n) (u n)) (s : ℝ) :
    (∀ᶠ n in atTop, InSobolev s (centered (u n))) ∧
      Tendsto (fun n => sobolevNorm s (centered (u n))) atTop (𝓝 0) := by
  have hd0 : 0 < d := by omega
  let U : ℕ → TorusL2 d := fun n => center (Bridge.potentialLp (u n) (hu n).1)
  have hU (n : ℕ) : Admissible (U n) := center_admissible hd0
    (Bridge.potentialLp_real (u n) (hu n).1) (Bridge.potentialLp_summable hd0 (u n) (hu n))
  have hmaxU (n : ℕ) (v : TorusL2 d) (hv : Admissible v) :
      functional (spectralThreshold d/(2*β n)) v ≤
        functional (spectralThreshold d/(2*β n)) (U n) := by
    have hh := hmax n (realValue v) (realValue_sobolev v hv)
    rw [dualFunctional_eq_normalized hd0 _ _ (realValue_sobolev v hv),
      dualFunctional_eq_normalized hd0 _ _ (hu n), center_potentialLp_realValue v hv] at hh
    exact_mod_cast hh
  have hSigma : spectralThreshold d ≠ 0 := (endpointSigma_pos hd0).ne'
  have hA : Tendsto (fun n => spectralThreshold d/(2*β n)) atTop (𝓝 (1/2)) := by
    have hh := (tendsto_const_nhds (x := spectralThreshold d)).div
      (hβ.const_mul 2) (mul_ne_zero (by norm_num) hSigma)
    convert hh using 1
    congr 1
    field_simp
  have h := OnsetSobolev.maximizers_sobolev_tendsto_zero hd hEndpoint hRigidity hA U hU hmaxU s
  have hae (n : ℕ) : realValue (U n) =ᵐ[HighDim.torusMeasure d] centered (u n) :=
    Bridge.centeredLp_ae (u n) (hu n).1
  refine ⟨h.1.mono (fun n hn => (inSobolev_congr_ae (hae n)).mp hn), ?_⟩
  exact h.2.congr' (Eventually.of_forall (fun n => sobolevNorm_congr_ae (hae n) s))

/-- For mean-zero representatives, no recentering appears in the conclusion. -/
theorem meanZero_optimizers_sobolev_tendsto_zero {d : ℕ} (hd : 12 ≤ d)
    (hEndpoint : EndpointRigidity.CoefficientEndpoint d (1/2))
    (hRigidity : OnsetCompactness.DensityRigidity d)
    {β : ℕ → ℝ} (hβ : Tendsto β atTop (𝓝 (spectralThreshold d)))
    (u : ℕ → HighDim.Torus d → ℝ) (hu : ∀ n, InCriticalSobolev (u n))
    (hmean : ∀ n, MeanZero (u n))
    (hmax : ∀ n (v : HighDim.Torus d → ℝ), InCriticalSobolev v →
      dualFunctional (β n) v ≤ dualFunctional (β n) (u n)) (s : ℝ) :
    (∀ᶠ n in atTop, InSobolev s (u n)) ∧
      Tendsto (fun n => sobolevNorm s (u n)) atTop (𝓝 0) := by
  have he (n : ℕ) : centered (u n) = u n := by
    have hm : (∫ y, u n y ∂HighDim.torusMeasure d) = 0 := hmean n
    funext x
    simp only [centered, hm, sub_zero]
  simpa only [he] using centered_optimizers_sobolev_tendsto_zero hd hEndpoint hRigidity hβ u hu hmax s

#print axioms centered_optimizers_sobolev_tendsto_zero
#print axioms meanZero_optimizers_sobolev_tendsto_zero
end BecknerOnofri.HighDim.OnsetRaw
