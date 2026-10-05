module

public import BecknerOnofri.GraphHessian

@[expose] public section

/-! The mixed graph/complement Hessian vanishes on the full raw L² domain,
so in particular on every trusted critical-Sobolev complementary direction. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators ComplexConjugate
namespace BecknerOnofri.HighDim.GraphHessian
open ContinuousGibbs ContinuousFirstShell ContinuousComplement GreenLocalBranch ReducedEquation
open GreenPairing GraphEnergy
open Legacy.BecknerOnofri.TorusSobolev

theorem raw_pairing_hasSum {d : ℕ} (a : Space d) (q : Torus d → ℝ)
    (hq : MemLp q 2 (torusMeasure d)) :
    HasSum (fun k : Frequency d => (conj (coefficient k a)*fourierCoeff q k).re)
      (∫ x, a x*q x ∂torusMeasure d) := by
  let v := Bridge.potentialLp q hq
  have hs := Complex.hasSum_re (UnitAddTorus.hasSum_prod_mFourierCoeff (toL2 d a) v)
  have hi : Integrable (fun x => conj (toL2 d a x)*v x) (torusMeasure d) :=
    (Lp.memLp (toL2 d a)).star.integrable_mul (Lp.memLp v)
  have he : (∫ x, conj (toL2 d a x)*v x ∂torusMeasure d).re =
      ∫ x, a x*q x ∂torusMeasure d := by
    calc
      _ = ∫ x, (conj (toL2 d a x)*v x).re ∂torusMeasure d := (integral_re hi).symm
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [toL2_ae a,Bridge.potentialLp_ae q hq] with x ha hx
        change v x=(q x:ℂ) at hx
        simp only [ha,hx,Complex.conj_ofReal,← Complex.ofReal_mul,Complex.ofReal_re]
  change HasSum (fun k : Frequency d =>
    (conj (UnitAddTorus.mFourierCoeff (toL2 d a) k)*UnitAddTorus.mFourierCoeff v k).re)
      ((∫ x, conj (toL2 d a x)*v x ∂torusMeasure d).re) at hs
  rw [he] at hs
  simpa only [coefficient_apply,← fourierIsometry_apply,v,Bridge.potentialLp_fourier] using hs

theorem linearized_pairing_raw_complement {d : ℕ} (hd : 0<d) (μ : ℝ)
    (z : Coordinates d) (w : complement d) (a : Space d)
    (hw : (w : Space d)=μ • projectedGreen d a) (q : Torus d → ℝ)
    (hq : MemLp q 2 (torusMeasure d)) (hc : ComplementSupported (fourierCoeff q)) :
    normalizedEnergyPairing (reconstruction d (z,w)) q=μ*(∫ x, a x*q x ∂torusMeasure d) := by
  have he (k : Frequency d) :
      frequencyLength k^d*(conj (coefficient k (reconstruction d (z,w)))*fourierCoeff q k).re =
        μ*(conj (coefficient k a)*fourierCoeff q k).re := by
    by_cases hk : ComplementFrequency k
    · have hz : coefficient k (assembly d z)=0 := by
        rw [← projection_assembly z]
        exact coefficient_projection_off_shell _ _ hk.2
      have hh := congrArg (fun v : ℂ => (conj v*fourierCoeff q k).re)
        (linearized_fourier_euler hd μ w a hw k hk)
      simp only [reconstruction_apply,map_add,hz,zero_add]
      simpa only [map_mul,Complex.conj_ofReal,Complex.mul_re,Complex.mul_im,
        Complex.ofReal_re,Complex.ofReal_im,zero_mul,mul_zero,sub_zero,zero_add,mul_assoc] using hh
    · rw [hc k hk]
      simp
  have hh := ((raw_pairing_hasSum a q hq).mul_left μ).congr_fun he
  simpa only [normalizedEnergyPairing,coefficient_eq_fourierCoeff] using hh.tsum_eq

theorem continuous_mul_raw_integrable {d : ℕ} (a : Space d) (q : Torus d → ℝ)
    (hq : MemLp q 2 (torusMeasure d)) : Integrable (fun x => a x*q x) (torusMeasure d) :=
  (hq.integrable (by norm_num)).bdd_mul a.continuous.aestronglyMeasurable
    (Eventually.of_forall (fun x => a.norm_coe_le_norm x))

theorem hessianPairing_raw {d : ℕ} (β : ℝ) (u v : Space d) (q : Torus d → ℝ)
    (hq : MemLp q 2 (torusMeasure d)) :
    hessianPairing β u v q=(∫ x, normalizedDerivative u v x*q x ∂torusMeasure d)-
      spectralThreshold d/β*normalizedEnergyPairing v q := by
  have he : (fun x => normalizedDerivative u v x*q x) =
      (fun x => (normalized u*v) x*q x-(weightedMean u v)*((normalized u) x*q x)) := by
    funext x
    simp only [normalizedDerivative_apply,ContinuousMap.sub_apply,ContinuousMap.mul_apply,
      ContinuousMap.smul_apply,smul_eq_mul]
    ring
  rw [he,integral_sub (continuous_mul_raw_integrable (normalized u*v) q hq)
    ((continuous_mul_raw_integrable (normalized u) q hq).const_mul _),integral_const_mul]
  simp only [hessianPairing,weightedMean_apply,mean_apply,ContinuousMap.mul_apply,normalized_apply]

/-- Exact mixed orthogonality on the full actual raw complementary L² domain. -/
theorem hessianPairing_linearized_raw_complement {d : ℕ} (hd : 0<d) {μ : ℝ} (hμ : μ≠0)
    (u : Space d) (h : Coordinates d) (w : complement d)
    (hw : (w : Space d)=μ • projectedGreen d
      (normalizedDerivative u (reconstruction d (h,w))))
    (q : Torus d → ℝ) (hq : MemLp q 2 (torusMeasure d))
    (hc : ComplementSupported (fourierCoeff q)) :
    hessianPairing (μ*spectralThreshold d) u (reconstruction d (h,w)) q=0 := by
  rw [hessianPairing_raw _ _ _ _ hq,physical_factor hd,
    linearized_pairing_raw_complement hd μ h w _ hw q hq hc]
  field_simp
  ring

theorem hessianPairing_tangentMap_raw_complement {d : ℕ} (hd : 12≤d) :
    ∀ᶠ x in 𝓝 (1,(0 : Coordinates d)), ∀ (h : Coordinates d) (q : Torus d → ℝ),
      MemLp q 2 (torusMeasure d) → ComplementSupported (fourierCoeff q) →
      hessianPairing (x.1*spectralThreshold d) (potential hd x) (tangentMap hd x h) q=0 := by
  have hpos : ∀ᶠ x : ℝ × Coordinates d in 𝓝 (1,0), 0<x.1 :=
    continuous_fst.continuousAt.preimage_mem_nhds (Ioi_mem_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [tangentMap_equation hd,hpos] with x hx hμ h q hq hc
  obtain ⟨w,hv,hw,hreg⟩ := hx h
  rw [hv] at hw ⊢
  exact hessianPairing_linearized_raw_complement (by omega) hμ.ne' _ h w hw q hq hc

#print axioms hessianPairing_tangentMap_raw_complement
end BecknerOnofri.HighDim.GraphHessian
