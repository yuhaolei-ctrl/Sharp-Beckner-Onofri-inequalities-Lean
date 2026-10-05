module

public import BecknerOnofri.OnsetContinuous

@[expose] public section

/-! Actual continuous global dual optimizers: full Euler equation and subcritical attainment. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped Topology BigOperators
namespace BecknerOnofri.HighDim.ContinuousOptimizers
open ContinuousGibbs ContinuousFirstShell GraphRegularity ReducedEquation OnsetContinuous
open Legacy.BecknerOnofri.TorusSobolev
open Legacy.BecknerOnofri.SubcriticalAttainment Legacy.BecknerOnofri.SubcriticalEuler
open Legacy.BecknerOnofri.WienerFourier

/-- The actual real continuous Fourier representative of a Wiener L² potential. -/
def realRepresentative {d : ℕ} (u : TorusL2 d)
    (hs : Summable (fun k => ‖fourierIsometry d u k‖)) : Space d :=
  ⟨fun x => (representative u x).re, Complex.continuous_re.comp (representative_continuous u hs)⟩

theorem realRepresentative_ae {d : ℕ} (u : TorusL2 d)
    (hs : Summable (fun k => ‖fourierIsometry d u k‖)) :
    (realRepresentative u hs : Torus d → ℝ) =ᵐ[torusMeasure d] RawAttainment.realValue u := by
  filter_upwards [representative_ae_eq u hs] with x hx
  exact congrArg Complex.re hx

theorem toL2_realRepresentative {d : ℕ} (u : TorusL2 d)
    (hs : Summable (fun k => ‖fourierIsometry d u k‖)) (hr : RealPotential u) :
    toL2 d (realRepresentative u hs) = u := by
  apply Lp.ext
  filter_upwards [toL2_ae (realRepresentative u hs), realRepresentative_ae u hs, hr] with x hx he hi
  rw [hx, he]
  apply Complex.ext
  · rfl
  · simpa only [Complex.ofReal_im] using hi.symm

theorem inCriticalSobolev_of_toL2 {d : ℕ} (u : Space d) (hu : Admissible (toL2 d u)) :
    InCriticalSobolev u := by
  refine ⟨u.continuous.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _), ?_⟩
  have hs := hu.2.2.subtype {k : Frequency d | k ≠ 0}
  apply (hs.mul_left ((2*Real.pi)^d)).congr
  intro k
  simp only [Function.comp_apply, weightedSquare, potentialTerm, ← coefficient_eq_fourierCoeff, coefficient_apply,
    Bridge.frequencyLength_eq, mul_pow]
  ring

theorem meanZero_of_toL2 {d : ℕ} (u : Space d) (hu : Admissible (toL2 d u)) : MeanZero u := by
  have hz : coefficient 0 u = 0 := hu.2.1
  rw [coefficient_zero] at hz
  exact Complex.ofReal_eq_zero.mp hz

theorem dualFunctional_eq_toL2 {d : ℕ} (hd : 0 < d) (β : ℝ) (u : Space d)
    (hu : InCriticalSobolev u) (hm : MeanZero u) :
    dualFunctional β u = (functional (spectralThreshold d/(2*β)) (toL2 d u) : EReal) := by
  rw [OnsetRaw.dualFunctional_eq_normalized hd β u hu, ← toL2_eq_potentialLp u hu, center_toL2 u hm]

theorem toL2_optimizer {d : ℕ} (hd : 0 < d) (β : ℝ) (u : Space d)
    (hu : InCriticalSobolev u) (hm : MeanZero u)
    (hmax : ∀ v : Torus d → ℝ, InCriticalSobolev v → dualFunctional β v ≤ dualFunctional β u) :
    ∀ v : TorusL2 d, Admissible v →
      functional (spectralThreshold d/(2*β)) v ≤ functional (spectralThreshold d/(2*β)) (toL2 d u) := by
  intro v hv
  have hh := hmax (RawAttainment.realValue v) (RawAttainment.realValue_sobolev v hv)
  rw [OnsetRaw.dualFunctional_eq_normalized hd _ _ (RawAttainment.realValue_sobolev v hv),
    RawAttainment.center_potentialLp_realValue v hv, dualFunctional_eq_toL2 hd β u hu hm] at hh
  exact_mod_cast hh

theorem partition_toL2 {d : ℕ} (u : Space d) :
    Legacy.BecknerOnofri.SubcriticalAttainment.partition (toL2 d u) = ContinuousGibbs.partition u := by
  apply integral_congr_ae
  filter_upwards [toL2_ae u] with x hx
  rw [hx]
  simp only [Complex.ofReal_re, exponential_apply]

theorem normalized_coefficient_toL2 {d : ℕ} (u : Space d) (k : Frequency d) :
    coefficient k (normalized u) = Legacy.TorusEndpoint.densityFourier (gibbsValue (toL2 d u)) k := by
  rw [normalized_coefficient_legacy, ← partition_toL2]
  rfl

/-- A genuine global maximizer satisfies the complete Fourier Euler equation. -/
theorem continuous_optimizer_full {d : ℕ} (hd : 0 < d) {μ : ℝ} (hμ : 0 < μ)
    (u : Space d) (hu : InCriticalSobolev u) (hm : MeanZero u)
    (hmax : ∀ v : Torus d → ℝ, InCriticalSobolev v →
      dualFunctional (μ*spectralThreshold d) v ≤ dualFunctional (μ*spectralThreshold d) u) :
    full d μ u = 0 := by
  have hσ := Legacy.TorusEndpoint.endpointSigma_pos hd
  have hcoef : spectralThreshold d/(2*(μ*spectralThreshold d)) = 1/(2*μ) := by
    have hz : spectralThreshold d ≠ 0 := hσ.ne'
    field_simp
  have hmaxL := toL2_optimizer hd (μ*spectralThreshold d) u hu hm hmax
  rw [hcoef] at hmaxL
  have hadm := toL2_admissible hd u hu hm
  have hC : 0 < Legacy.BecknerOnofri.endpointConstant d := div_pos (Nat.cast_pos.mpr hd) hσ
  have hR := GenericAttainment.rough_bound hd
    (by positivity : 0 < Legacy.BecknerOnofri.endpointConstant d/2)
    (by linarith : Legacy.BecknerOnofri.endpointConstant d/2 < Legacy.BecknerOnofri.endpointConstant d)
  have hA : 0 < 1/(2*μ) := by positivity
  have hInv : 1/(2*(1/(2*μ))) = μ := by field_simp
  apply coefficient_ext
  intro k
  simp only [full, map_sub, map_smul, map_zero, coefficient_green hd]
  by_cases hk : k=0
  · subst k
    rw [coefficient_zero, show mean d u=0 from hm]
    simp
  · have h1 : coefficient k (1 : Space d) = 0 := by
      change coefficient k (ContinuousMap.const (Torus d) 1) = 0
      rw [coefficient_const, if_neg hk]
    rw [if_neg hk, h1, mul_zero, sub_zero]
    have hf := maximizer_fourier_formula hR hA hadm hmaxL hk
    rw [hInv, ← normalized_coefficient_toL2, ← Bridge.frequencyLength_eq] at hf
    change coefficient k u = _ at hf
    rw [hf]
    simp only [Complex.real_smul]
    push_cast
    ring

/-- The physical subcritical interval is exactly the strict concentration range
for the normalized Hilbert-space functional. -/
theorem concentration_coefficient_lt {d : ℕ} (hd : 0 < d) {β : ℝ}
    (hβ : 0 < β) (hβd : β < 2*(d:ℝ)) :
    1/(4*Legacy.BecknerOnofri.endpointConstant d) < spectralThreshold d/(2*β) := by
  have hσ : 0 < spectralThreshold d := Legacy.TorusEndpoint.endpointSigma_pos hd
  have he : 1/(4*Legacy.BecknerOnofri.endpointConstant d) = spectralThreshold d/(4*(d:ℝ)) := by
    unfold Legacy.BecknerOnofri.endpointConstant
    rw [← Bridge.spectralThreshold_eq]
    field_simp
  rw [he]
  exact div_lt_div_of_pos_left hσ (by positivity) (by linarith)

/-- Every physical subcritical problem has a continuous, smooth, mean-zero optimizer,
with comparison against the full raw critical-Sobolev domain. -/
theorem exists_continuous_optimizer {d : ℕ} (hd : 0 < d) {β : ℝ}
    (hβ : 0 < β) (hβd : β < 2*(d:ℝ)) :
    ∃ u : Space d, InCriticalSobolev u ∧ MeanZero u ∧ SmoothOnTorus u ∧
      (∀ s : ℝ, InSobolev s u) ∧ 0 ≤ dualFunctional β u ∧
      (∀ v : Torus d → ℝ, InCriticalSobolev v → dualFunctional β v ≤ dualFunctional β u) ∧
      full d (β/spectralThreshold d) u = 0 := by
  obtain ⟨U,hU,hzero,hmax⟩ := GenericAttainment.exists_subcritical_optimizer hd
    (concentration_coefficient_lt hd hβ hβd)
  have hσ : 0 < spectralThreshold d := Legacy.TorusEndpoint.endpointSigma_pos hd
  have hA : 0 < spectralThreshold d/(2*β) := by positivity
  have hC : 0 < Legacy.BecknerOnofri.endpointConstant d := div_pos (Nat.cast_pos.mpr hd) hσ
  have hR := GenericAttainment.rough_bound hd
    (by positivity : 0 < Legacy.BecknerOnofri.endpointConstant d/2)
    (by linarith : Legacy.BecknerOnofri.endpointConstant d/2 < Legacy.BecknerOnofri.endpointConstant d)
  have hs := maximizer_fourier_summable hd hR hA hU hmax
  let u := realRepresentative U hs
  have huL : toL2 d u = U := toL2_realRepresentative U hs hU.1
  have huadm : Admissible (toL2 d u) := by rw [huL]; exact hU
  have hu := inCriticalSobolev_of_toL2 u huadm
  have hm := meanZero_of_toL2 u huadm
  have huradial (m : ℕ) : Radial m u := by
    have hh := maximizer_radialSummable hd hR hA hU hmax m
    simpa only [Radial, Legacy.BecknerOnofri.RadialWiener.RadialSummable, coefficient_apply, huL] using hh
  have hraw : ∀ v : Torus d → ℝ, InCriticalSobolev v → dualFunctional β v ≤ dualFunctional β u := by
    intro v hv
    rw [OnsetRaw.dualFunctional_eq_normalized hd β v hv, dualFunctional_eq_toL2 hd β u hu hm, huL]
    have hadm := Legacy.BecknerOnofri.SobolevCentering.center_admissible hd
      (Bridge.potentialLp_real v hv.1) (Bridge.potentialLp_summable hd v hv)
    exact_mod_cast hmax _ hadm
  refine ⟨u,hu,hm,smooth_of_radial u huradial,inSobolev_of_radial u huradial,?_,hraw,?_⟩
  · rw [dualFunctional_eq_toL2 hd β u hu hm, huL]
    exact_mod_cast hzero
  · apply continuous_optimizer_full hd (div_pos hβ hσ) u hu hm
    simpa only [div_mul_cancel₀ β hσ.ne'] using hraw

#print axioms continuous_optimizer_full
#print axioms exists_continuous_optimizer
end BecknerOnofri.HighDim.ContinuousOptimizers
