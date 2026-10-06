module

public import BecknerOnofri.LocalElevenContinuousInverse
public import BecknerOnofri.QuarticSignsEleven
public import BecknerOnofri.NormalHessianCoercivity
public import BecknerOnofri.LocalElevenCore.NormalHessianL2
public import BecknerOnofri.LocalElevenCore.MeanZeroSobolevCoercivity

@[expose] public section

/-! Compact critical Sobolev balls turn the exact Hessian nullspace theorem
into a strict uniform gap on the actual L²-orthogonal normal domain. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Filter Set
open scoped Topology BigOperators
namespace BecknerOnofri.HighDim.LocalEleven.NormalHessianCoercivity

open BecknerOnofri.HighDim.NormalHessianCoercivity hiding RealL2 covariance covariance_continuous covariance_eq_integrals covariance_smul covariance_zero covariance_zero_of_tangent_orthogonal gibbsL2 gibbsL2_ae gibbsWeight l2_normal_energy_gap normal_energy_coercivity normal_sobolev_coercivity pairing pairing_continuous pairing_eq_integral pairing_smul pairing_zero potentialLp_admissible potentialLp_normalizedEnergy potentialLp_secondVariation realPart realPart_ae realValue_normalizedEnergy realValue_potentialLp_ae secondVariation_realValue

open ContinuousGibbs RawAttainment

open Legacy.BecknerOnofri.TorusSobolev Legacy.BecknerOnofri.SubcriticalAttainment

/-- Compactness is used only for the genuine bounded Gibbs covariance. -/
theorem l2_normal_energy_gap {d : ℕ} (hd : 0<d) {β : ℝ} (hβ : 0<β) (u : Space d)
    (ht : ∀ j : Fin d, MemLp (coordinateDerivative u j) 2 (torusMeasure d))
    (hQ : ∀ h : Torus d → ℝ, InCriticalSobolev h → MeanZero h → secondVariation β u h≤0)
    (hker : ∀ h : Torus d → ℝ, InCriticalSobolev h → MeanZero h →
      secondVariation β u h=0 → ∃ a : Fin d → ℝ, h =ᵐ[torusMeasure d] tangentCombination u a) :
    ∃ c : ℝ, 0<c ∧ ∀ v : TorusL2 d, Admissible v →
      (∀ j, pairing (coordinateDerivative u j) (ht j) v=0) →
      covariance u v-spectralThreshold d/β*criticalEnergy v ≤ -c*criticalEnergy v := by
  let a := spectralThreshold d/β
  have ha : 0<a := div_pos (Legacy.TorusEndpoint.endpointSigma_pos hd) hβ
  let S : Set (TorusL2 d) := realSobolevBall d 1 ∩
    {v | ∀ j : Fin d, pairing (coordinateDerivative u j) (ht j) v=0}
  have hc : IsCompact S := by
    apply (realSobolevBall_isCompact hd (by norm_num : (0:ℝ)≤1)).inter_right
    have he : {v : TorusL2 d | ∀ j : Fin d, pairing (coordinateDerivative u j) (ht j) v=0} =
        ⋂ j : Fin d, {v | pairing (coordinateDerivative u j) (ht j) v=0} := by ext v; simp
    rw [he]
    exact isClosed_iInter (fun j => isClosed_eq (pairing_continuous _ _) continuous_const)
  have hz : (0 : TorusL2 d) ∈ S := ⟨zero_mem_realSobolevBall (by norm_num),by simp⟩
  obtain ⟨v₀,hv₀,hmax⟩ := hc.exists_isMaxOn ⟨0,hz⟩ (covariance_continuous u).continuousOn
  have hadm : Admissible v₀ := ⟨hv₀.1.2,hv₀.1.1.1⟩
  have hstrict : covariance u v₀<a := by
    by_contra hn
    have hcov : a≤covariance u v₀ := le_of_not_gt hn
    have hE : criticalEnergy v₀≤1 := hv₀.1.1.2
    have hraw := hQ (realValue v₀) (realValue_sobolev v₀ hadm) (realValue_meanZero v₀ hadm)
    rw [secondVariation_realValue hd β u v₀ hadm] at hraw
    change covariance u v₀-a*criticalEnergy v₀≤0 at hraw
    have hmul : a*criticalEnergy v₀≤a := by nlinarith
    have heq : secondVariation β u (realValue v₀)=0 := by
      rw [secondVariation_realValue hd β u v₀ hadm]
      change covariance u v₀-a*criticalEnergy v₀=0
      linarith
    have hspan := hker (realValue v₀) (realValue_sobolev v₀ hadm) (realValue_meanZero v₀ hadm) heq
    have hzero := covariance_zero_of_tangent_orthogonal u ht v₀ hv₀.2 hspan
    linarith
  refine ⟨a-covariance u v₀,sub_pos.mpr hstrict,?_⟩
  intro v hv horth
  by_cases hzero : criticalEnergy v=0
  · have hh := hQ (realValue v) (realValue_sobolev v hv) (realValue_meanZero v hv)
    rw [secondVariation_realValue hd β u v hv] at hh
    simpa only [hzero,mul_zero,sub_zero] using hh
  have hE : 0<criticalEnergy v := lt_of_le_of_ne (energy_nonneg v) (Ne.symm hzero)
  let t : ℝ := (Real.sqrt (criticalEnergy v))⁻¹
  have hscale : t^2*criticalEnergy v=1 := by
    dsimp [t]
    rw [inv_pow,Real.sq_sqrt hE.le,inv_mul_cancel₀ hE.ne']
  have hwE : criticalEnergy ((t:ℂ) • v)=1 := by rw [criticalEnergy_smul_real,hscale]
  have hw : (t:ℂ) • v ∈ S := by
    have hwadm := admissible_smul_real hv t
    exact ⟨⟨⟨hwadm.2,hwE.le⟩,hwadm.1⟩,fun j => by rw [pairing_smul,horth j,mul_zero]⟩
  have hbound : covariance u v≤covariance u v₀*criticalEnergy v := by
    have hh := mul_le_mul_of_nonneg_right (hmax hw) hE.le
    rw [covariance_smul] at hh
    calc
      covariance u v=(t^2*covariance u v)*criticalEnergy v := by
        calc
          covariance u v=covariance u v*(t^2*criticalEnergy v) := by rw [hscale,mul_one]
          _ = _ := by ring
      _ ≤ _ := hh
  change covariance u v-a*criticalEnergy v≤-(a-covariance u v₀)*criticalEnergy v
  nlinarith

theorem potentialLp_admissible {d : ℕ} (hd : 0<d) (h : Torus d → ℝ)
    (hh : InCriticalSobolev h) (hm : MeanZero h) : Admissible (Bridge.potentialLp h hh.1) := by
  refine ⟨Bridge.potentialLp_real h hh.1,?_,Bridge.potentialLp_summable hd h hh⟩
  rw [Bridge.potentialLp_fourier]
  simp only [fourierCoeff,neg_zero,UnitAddTorus.mFourier_zero,ContinuousMap.one_apply,one_mul]
  rw [integral_complex_ofReal,show (∫ x, h x ∂torusMeasure d)=0 from hm]
  rfl

theorem realValue_potentialLp_ae {d : ℕ} (h : Torus d → ℝ)
    (hh : MemLp h 2 (torusMeasure d)) :
    realValue (Bridge.potentialLp h hh) =ᵐ[torusMeasure d] h := by
  filter_upwards [Bridge.potentialLp_ae h hh] with x hx
  change (Bridge.potentialLp h hh x).re=h x
  rw [hx,Complex.ofReal_re]

theorem potentialLp_normalizedEnergy {d : ℕ} (hd : 0<d) (h : Torus d → ℝ)
    (hh : InCriticalSobolev h) :
    criticalEnergy (Bridge.potentialLp h hh.1)=normalizedPotentialEnergy h := by
  rw [normalizedPotentialEnergy,Bridge.potentialLp_energy hd h hh]
  exact (mul_div_cancel_left₀ _ (pow_ne_zero _ (by positivity : (2*Real.pi:ℝ)≠0))).symm

theorem potentialLp_secondVariation {d : ℕ} (hd : 0<d) (β : ℝ) (u : Space d)
    (h : Torus d → ℝ) (hh : InCriticalSobolev h) :
    covariance u (Bridge.potentialLp h hh.1)-spectralThreshold d/β*criticalEnergy (Bridge.potentialLp h hh.1)=
      secondVariation β u h := by
  rw [covariance_eq_integrals,potentialLp_normalizedEnergy hd h hh,secondVariation]
  congr 2
  · apply integral_congr_ae
    filter_upwards [realValue_potentialLp_ae h hh.1] with x hx
    rw [hx]
  · congr 1
    apply integral_congr_ae
    filter_upwards [realValue_potentialLp_ae h hh.1] with x hx
    rw [hx]

/-- The full raw critical Sobolev domain inherits a strict energy gap, from
Hessian nonpositivity and its exact actual translation kernel. -/
theorem normal_energy_coercivity {d : ℕ} (hd : 0<d) {β : ℝ} (hβ : 0<β) (u : Space d)
    (ht : ∀ j : Fin d, MemLp (coordinateDerivative u j) 2 (torusMeasure d))
    (hQ : ∀ h : Torus d → ℝ, InCriticalSobolev h → MeanZero h → secondVariation β u h≤0)
    (hker : ∀ h : Torus d → ℝ, InCriticalSobolev h → MeanZero h →
      secondVariation β u h=0 → ∃ a : Fin d → ℝ, h =ᵐ[torusMeasure d] tangentCombination u a) :
    ∃ c : ℝ, 0<c ∧ ∀ h : Torus d → ℝ, InCriticalSobolev h → MeanZero h →
      (∀ j, (∫ x, h x*coordinateDerivative u j x ∂torusMeasure d)=0) →
      secondVariation β u h≤-c*normalizedPotentialEnergy h := by
  obtain ⟨c,hc,hgap⟩ := l2_normal_energy_gap hd hβ u ht hQ hker
  refine ⟨c,hc,?_⟩
  intro h hh hm horth
  have hp (j : Fin d) : pairing (coordinateDerivative u j) (ht j) (Bridge.potentialLp h hh.1)=0 := by
    rw [pairing_eq_integral,← horth j]
    apply integral_congr_ae
    filter_upwards [realValue_potentialLp_ae h hh.1] with x hx
    rw [hx]
  have hg := hgap (Bridge.potentialLp h hh.1) (potentialLp_admissible hd h hh hm) hp
  rwa [potentialLp_secondVariation hd β u h hh,potentialLp_normalizedEnergy hd h hh] at hg

/-- The exact physical H^(d/2) normal coercivity required by
`FullModeMorseBott`, on every raw critical Sobolev variation. -/
theorem normal_sobolev_coercivity {d : ℕ} (hd : 0<d) {β : ℝ} (hβ : 0<β) (u : Space d)
    (ht : ∀ j : Fin d, MemLp (coordinateDerivative u j) 2 (torusMeasure d))
    (hQ : ∀ h : Torus d → ℝ, InCriticalSobolev h → MeanZero h → secondVariation β u h≤0)
    (hker : ∀ h : Torus d → ℝ, InCriticalSobolev h → MeanZero h →
      secondVariation β u h=0 → ∃ a : Fin d → ℝ, h =ᵐ[torusMeasure d] tangentCombination u a) :
    ∃ c : ℝ, 0<c ∧ ∀ h : Torus d → ℝ, InCriticalSobolev h → InSobolev ((d:ℝ)/2) h →
      MeanZero h → (∀ j, (∫ x, h x*coordinateDerivative u j x ∂torusMeasure d)=0) →
      secondVariation β u h≤-c*sobolevNorm ((d:ℝ)/2) h^2 := by
  obtain ⟨c,hc,hgap⟩ := normal_energy_coercivity hd hβ u ht hQ hker
  let C := ComplementHessian.criticalWeightConstant d
  have hC : 0<C := ComplementHessian.criticalWeightConstant_pos d
  refine ⟨c/C,div_pos hc hC,?_⟩
  intro h hh hs hm horth
  have hE := hgap h hh hm horth
  have hn := MeanZeroSobolevCoercivity.sobolevNorm_sq_le_normalizedEnergy hd h hh hs hm
  have hbound : sobolevNorm ((d:ℝ)/2) h^2/C≤normalizedPotentialEnergy h := by
    exact (div_le_iff₀ hC).mpr (by simpa only [mul_comm] using hn)
  have hneg := mul_le_mul_of_nonpos_left hbound (neg_nonpos.mpr hc.le)
  apply hE.trans
  convert! hneg using 1 <;> ring

#print axioms normal_sobolev_coercivity
#print axioms l2_normal_energy_gap
#print axioms normal_energy_coercivity
end BecknerOnofri.HighDim.LocalEleven.NormalHessianCoercivity
