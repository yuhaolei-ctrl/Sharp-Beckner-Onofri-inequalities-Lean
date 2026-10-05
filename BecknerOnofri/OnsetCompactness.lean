import BecknerOnofri.EndpointRigidity.MixtureInduction
import Legacy.BecknerOnofri.SobolevCentering

/-! Actual global maximizers at coefficients approaching the spectral threshold
converge to the zero potential in L². Uniform coercivity comes from the proved
strict concentration gap, and the limit is identified by density rigidity. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace BecknerOnofri.OnsetCompactness
open Legacy.TorusEndpoint Legacy.BecknerOnofri
open TorusSobolev SubcriticalAttainment SubcriticalEuler SubcriticalPrimalDual SobolevCentering
open EndpointRigidity

/-- Only the actual finite-entropy density equality classification is assumed. -/
def DensityRigidity (d : ℕ) : Prop :=
  ∀ r : ProbabilityDensity d, r.FiniteEntropy →
    (1/2:ℝ) * fourierEnergy r = densityEntropy r.value →
    r.value =ᵐ[torusMeasure d] (fun _ => 1)

theorem zero_of_endpoint_nonneg {d : ℕ} (hd : 0 < d)
    (hEndpoint : CoefficientEndpoint d (1/2)) (hRigidity : DensityRigidity d)
    {u : TorusL2 d} (hu : Admissible u) (hf : 0 ≤ functional (1/2) u) : u = 0 := by
  have hR := AnalyticEndpoint.rough_of_endpoint hd (by norm_num : (0:ℝ)<1/2) hEndpoint
  have hlo := dual_le_gibbs hd hR (by norm_num : (0:ℝ)<1/2) hu
  have hhi := (hEndpoint (gibbsDensity hR hu) (gibbsDensity_finiteEntropy hR hu)).2
  unfold densityFunctional at hlo
  norm_num at hlo
  change functional (1/2) u ≤ (1/2:ℝ) * fourierEnergy (gibbsDensity hR hu) -
    densityEntropy (gibbsValue u) at hlo
  change (1/2:ℝ) * fourierEnergy (gibbsDensity hR hu) ≤ densityEntropy (gibbsValue u) at hhi
  have he : (1/2:ℝ) * fourierEnergy (gibbsDensity hR hu) = densityEntropy (gibbsValue u) := by
    linarith
  have hg := hRigidity (gibbsDensity hR hu) (gibbsDensity_finiteEntropy hR hu) he
  have heq : u =ᵐ[torusMeasure d] (fun _ => ((Real.log (partition u) : ℝ) : ℂ)) := by
    filter_upwards [hg, hu.1] with x hx hi
    have hl := log_gibbsValue hR hu x
    change gibbsValue u x = 1 at hx
    rw [hx, Real.log_one] at hl
    apply Complex.ext
    · change (u x).re = Real.log (partition u)
      linarith
    · exact hi
  have huconst : u = constant d (Real.log (partition u) : ℂ) :=
    Lp.ext (heq.trans (constant_ae d _).symm)
  have hzero := hu.2.1
  rw [huconst, constant_fourier] at hzero
  simp only [ite_true] at hzero
  rw [huconst, hzero]
  exact map_zero (Lp.const 2 (torusMeasure d))

theorem eventual_energy_bound {d : ℕ} {b Ab : ℝ}
    (hR : RoughExponentialBound d b Ab) (hgap : 1/(4*b) < (1/2:ℝ))
    {A : ℕ → ℝ} (hA : Tendsto A atTop (𝓝 (1/2)))
    (u : ℕ → TorusL2 d) (hu : ∀ n, Admissible (u n))
    (hmax : ∀ n (v : TorusL2 d), Admissible v → functional (A n) v ≤ functional (A n) (u n)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ n in atTop, u n ∈ realSobolevBall d B := by
  let a : ℝ := (1/(4*b)+(1/2:ℝ))/2
  have ha : 1/(4*b) < a := by dsimp [a]; linarith
  have ha' : a < (1/2:ℝ) := by dsimp [a]; linarith
  let B := (Real.log Ab + 1)/(a-1/(4*b))
  have hB : 0 ≤ B := div_nonneg (by linarith [rough_log_nonneg hR]) (sub_pos.mpr ha).le
  refine ⟨B, hB, ?_⟩
  filter_upwards [hA.eventually (lt_mem_nhds ha')] with n hn
  have hz : 0 ≤ functional (A n) (u n) := by simpa using hmax n 0 (admissible_zero d)
  have hc := coercivity hR (A n) (hu n)
  refine ⟨⟨(hu n).2, ?_⟩, (hu n).1⟩
  apply (le_div_iff₀ (sub_pos.mpr ha)).mpr
  nlinarith [energy_nonneg (u n)]

theorem limit_zero_of_bounded {d : ℕ} (hd : 0 < d)
    (hEndpoint : CoefficientEndpoint d (1/2)) (hRigidity : DensityRigidity d)
    {b Ab B : ℝ} (hb : 0 < b) (hR : RoughExponentialBound d b Ab) (_hB : 0 ≤ B)
    {A : ℕ → ℝ} (hA : Tendsto A atTop (𝓝 (1/2)))
    {u : ℕ → TorusL2 d} (_hu : ∀ n, Admissible (u n))
    (hmax : ∀ n (v : TorusL2 d), Admissible v → functional (A n) v ≤ functional (A n) (u n))
    (hbound : ∀ᶠ n in atTop, u n ∈ realSobolevBall d B)
    {v : TorusL2 d} (hv : v ∈ realSobolevBall d B)
    (hlim : Tendsto u atTop (𝓝 v)) : v = 0 := by
  apply zero_of_endpoint_nonneg hd hEndpoint hRigidity ⟨hv.2, hv.1.1⟩
  have hErr : Tendsto (fun n => |A n-(1/2:ℝ)| * B) atTop (𝓝 0) := by
    simpa using ((hA.sub (tendsto_const_nhds (x := (1/2:ℝ)))).abs.mul_const B)
  have hLower : ∀ᶠ n in atTop, -(|A n-(1/2:ℝ)| * B) ≤ functional (1/2) (u n) := by
    filter_upwards [hbound] with n hn
    have hz : 0 ≤ functional (A n) (u n) := by simpa using hmax n 0 (admissible_zero d)
    have h1 := mul_le_mul_of_nonneg_right (neg_abs_le (A n-(1/2:ℝ))) (energy_nonneg (u n))
    have h2 := mul_le_mul_of_nonneg_left hn.1.2 (abs_nonneg (A n-(1/2:ℝ)))
    unfold functional at hz ⊢
    nlinarith
  by_contra hn
  have hneg : functional (1/2) v < 0 := lt_of_not_ge hn
  have hw : Tendsto u atTop (𝓝[realSobolevBall d B] v) :=
    tendsto_nhdsWithin_iff.mpr ⟨hlim, hbound⟩
  have hUpper := hw.eventually
    ((functional_upperSemicontinuousOn_ball hb (by norm_num : (0:ℝ)≤1/2) hR) v hv
      (functional (1/2) v / 2) (by linarith))
  have hSmall := hErr.eventually (gt_mem_nhds (by linarith : (0:ℝ) < -functional (1/2) v / 2))
  have hfalse : ∀ᶠ n : ℕ in atTop, False := by
    filter_upwards [hLower, hUpper, hSmall] with n hn hu hs
    linarith
  exact hfalse.exists.elim (fun _ hn => hn)

theorem maximizers_tendsto_zero_of_rough {d : ℕ} (hd : 0 < d)
    (hEndpoint : CoefficientEndpoint d (1/2)) (hRigidity : DensityRigidity d)
    {b Ab : ℝ} (hb : 0 < b) (hR : RoughExponentialBound d b Ab)
    (hgap : 1/(4*b) < (1/2:ℝ)) {A : ℕ → ℝ} (hA : Tendsto A atTop (𝓝 (1/2)))
    (u : ℕ → TorusL2 d) (hu : ∀ n, Admissible (u n))
    (hmax : ∀ n (v : TorusL2 d), Admissible v → functional (A n) v ≤ functional (A n) (u n)) :
    Tendsto u atTop (𝓝 0) := by
  obtain ⟨B, hB, hbound⟩ := eventual_energy_bound hR hgap hA u hu hmax
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  by_contra hn
  have hfreq : ∃ᶠ n in atTop, u n ∈ realSobolevBall d B ∩ {x | ε ≤ dist x 0} := by
    have hbad : ∃ᶠ n in atTop, ε ≤ dist (u n) 0 := by
      simpa only [Filter.Frequently, not_le] using hn
    exact hbad.and_eventually hbound |>.mono (fun _ hn => ⟨hn.2, hn.1⟩)
  have hc : IsCompact (realSobolevBall d B ∩ {x : TorusL2 d | ε ≤ dist x 0}) :=
    (realSobolevBall_isCompact hd hB).inter_right (isClosed_le continuous_const (by fun_prop))
  obtain ⟨v, hv, φ, hφ, hlim⟩ := hc.tendsto_subseq' hfreq
  have hv0 := limit_zero_of_bounded hd hEndpoint hRigidity hb hR hB
    (hA.comp hφ.tendsto_atTop) (fun n => hu (φ n)) (fun n => hmax (φ n))
    (hφ.tendsto_atTop.eventually hbound) hv.1 hlim
  exact hε.not_ge (by simpa [hv0] using hv.2)

/-- There is a genuine rough estimate whose quadratic coefficient stays
strictly below the spectral threshold. -/
theorem exists_rough_gap {d : ℕ} (hd : 12 ≤ d) :
    ∃ b Ab : ℝ, 0 < b ∧ RoughExponentialBound d b Ab ∧ 1/(4*b) < (1/2:ℝ) := by
  have hd0 : 0 < d := by omega
  have hC : (1/2:ℝ) < endpointConstant d := by
    unfold endpointConstant
    apply (lt_div_iff₀ (endpointSigma_pos hd0)).mpr
    have := HighDim.spectral_subcritical_gap hd
    change endpointSigma d < 2*(d:ℝ) at this
    linarith
  let b := ((1/2:ℝ)+endpointConstant d)/2
  have hb : 0 < b := by dsimp [b]; linarith
  have hbd : b < endpointConstant d := by dsimp [b]; linarith
  have hgap : 1/(4*b) < (1/2:ℝ) := by
    apply (div_lt_iff₀ (by positivity : 0 < 4*b)).mpr
    dsimp [b]
    linarith
  exact ⟨b, GreenRoughEnergy.partition d b, hb,
    GenericAttainment.rough_bound hd0 hb hbd, hgap⟩

/-- Actual maximizing potentials converge in L²; the genuine concentration
estimate discharges all uniform-coercivity hypotheses. -/
theorem maximizers_tendsto_zero {d : ℕ} (hd : 12 ≤ d)
    (hEndpoint : CoefficientEndpoint d (1/2)) (hRigidity : DensityRigidity d)
    {A : ℕ → ℝ} (hA : Tendsto A atTop (𝓝 (1/2)))
    (u : ℕ → TorusL2 d) (hu : ∀ n, Admissible (u n))
    (hmax : ∀ n (v : TorusL2 d), Admissible v → functional (A n) v ≤ functional (A n) (u n)) :
    Tendsto u atTop (𝓝 0) := by
  obtain ⟨b, Ab, hb, hR, hgap⟩ := exists_rough_gap hd
  exact maximizers_tendsto_zero_of_rough (by omega) hEndpoint hRigidity hb hR hgap hA u hu hmax

/-- The actual critical Fourier energy also tends to zero, giving strong
convergence at the critical Sobolev order, not merely L² convergence. -/
theorem maximizers_energy_tendsto_zero {d : ℕ} (hd : 12 ≤ d)
    (hEndpoint : CoefficientEndpoint d (1/2)) (hRigidity : DensityRigidity d)
    {A : ℕ → ℝ} (hA : Tendsto A atTop (𝓝 (1/2)))
    (u : ℕ → TorusL2 d) (hu : ∀ n, Admissible (u n))
    (hmax : ∀ n (v : TorusL2 d), Admissible v → functional (A n) v ≤ functional (A n) (u n)) :
    Tendsto (fun n => criticalEnergy (u n)) atTop (𝓝 0) := by
  obtain ⟨b, Ab, hb, hR, hgap⟩ := exists_rough_gap hd
  obtain ⟨B, hB, hbound⟩ := eventual_energy_bound hR hgap hA u hu hmax
  have hlim := maximizers_tendsto_zero hd hEndpoint hRigidity hA u hu hmax
  have hlog : Tendsto (fun n => Real.log (partition (u n))) atTop (𝓝 0) := by
    have hw : Tendsto u atTop (𝓝[realSobolevBall d B] (0 : TorusL2 d)) :=
      tendsto_nhdsWithin_iff.mpr ⟨hlim, hbound⟩
    have hh : Tendsto (fun n => Real.log (partition (u n))) atTop
        (𝓝 (Real.log (partition (0 : TorusL2 d)))) :=
      ((log_partition_continuousOn_ball (d := d) (B := B) hb hR)
        (0 : TorusL2 d) (zero_mem_realSobolevBall hB)).tendsto.comp hw
    simpa only [partition_zero, Real.log_one] using hh
  apply squeeze_zero' (Eventually.of_forall (fun n => energy_nonneg (u n)))
    (g := fun n => 4 * Real.log (partition (u n)))
  · filter_upwards [hA.eventually (lt_mem_nhds (by norm_num : (1/4:ℝ)<1/2))] with n hn
    have hz : 0 ≤ functional (A n) (u n) := by simpa using hmax n 0 (admissible_zero d)
    unfold functional at hz
    nlinarith [energy_nonneg (u n)]
  · simpa using hlog.const_mul 4

/-- The paper's β normalization gives exactly the same compactness conclusion. -/
theorem beta_maximizers_tendsto_zero {d : ℕ} (hd : 12 ≤ d)
    (hEndpoint : CoefficientEndpoint d (1/2)) (hRigidity : DensityRigidity d)
    {β : ℕ → ℝ} (hβ : Tendsto β atTop (𝓝 (HighDim.spectralThreshold d)))
    (u : ℕ → TorusL2 d) (hu : ∀ n, Admissible (u n))
    (hmax : ∀ n (v : TorusL2 d), Admissible v →
      functional (HighDim.spectralThreshold d/(2*β n)) v ≤
        functional (HighDim.spectralThreshold d/(2*β n)) (u n)) :
    Tendsto u atTop (𝓝 0) ∧ Tendsto (fun n => criticalEnergy (u n)) atTop (𝓝 0) := by
  have hσ : HighDim.spectralThreshold d ≠ 0 := (endpointSigma_pos (by omega : 0 < d)).ne'
  have hA : Tendsto (fun n => HighDim.spectralThreshold d/(2*β n)) atTop (𝓝 (1/2)) := by
    have hh := (tendsto_const_nhds (x := HighDim.spectralThreshold d)).div
      (hβ.const_mul 2) (mul_ne_zero (by norm_num) hσ)
    convert hh using 1
    congr 1
    field_simp
  exact ⟨maximizers_tendsto_zero hd hEndpoint hRigidity hA u hu hmax,
    maximizers_energy_tendsto_zero hd hEndpoint hRigidity hA u hu hmax⟩

#print axioms maximizers_tendsto_zero
#print axioms maximizers_energy_tendsto_zero
#print axioms beta_maximizers_tendsto_zero
end BecknerOnofri.OnsetCompactness
