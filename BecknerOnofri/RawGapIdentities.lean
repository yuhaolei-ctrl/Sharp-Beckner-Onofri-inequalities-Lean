import BecknerOnofri.RawGapBridges
import BecknerOnofri.FiniteEntropyPrimalGap

/-! The two manuscript gap identities, on the full raw-function domains and
with the literal physical Green integral and relative entropy remainder. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
namespace BecknerOnofri.HighDim.Gap
open Legacy.BecknerOnofri TorusSobolev SubcriticalAttainment SubcriticalEuler SubcriticalPrimalDual
open RawAttainment

lemma admissible_sub {d : ℕ} {u v : TorusL2 d} (hu : Admissible u) (hv : Admissible v) :
    Admissible (u-v) := by
  refine ⟨?_,?_,?_⟩
  · filter_upwards [Lp.coeFn_sub u v,hu.1,hv.1] with x hx hi hj
    change ((u-v) x).im = 0
    rw [hx]
    simp only [Pi.sub_apply,Complex.sub_im,hi,hj,sub_self]
  · simp [map_sub,lp.coeFn_sub,hu.2.1,hv.2.1]
  · have hs := (hu.2.2.add hv.2.2).mul_left 2
    apply Summable.of_nonneg_of_le (weightedSquare_nonneg _) _ hs
    intro k
    simp only [weightedSquare,map_sub,lp.coeFn_sub,Pi.sub_apply,Pi.add_apply]
    have hn := norm_sub_le (fourierIsometry d u k) (fourierIsometry d v k)
    have hb : ‖fourierIsometry d u k-fourierIsometry d v k‖^2 ≤
        2*(‖fourierIsometry d u k‖^2+‖fourierIsometry d v k‖^2) := by
      nlinarith [norm_nonneg (fourierIsometry d u k-fourierIsometry d v k),
        norm_nonneg (fourierIsometry d u k),norm_nonneg (fourierIsometry d v k),
        sq_nonneg (‖fourierIsometry d u k‖-‖fourierIsometry d v k‖)]
    have hw : 0 ≤ Legacy.TorusEndpoint.frequencyRadius k^d :=
      pow_nonneg (Real.sqrt_nonneg _) _
    nlinarith [mul_le_mul_of_nonneg_left hb hw]

lemma inCriticalSobolev_congr {d : ℕ} {u v : Torus d → ℝ}
    (he : u =ᵐ[torusMeasure d] v) : InCriticalSobolev u ↔ InCriticalSobolev v := by
  have ht : potentialTerm u = potentialTerm v := by
    funext k
    simp only [potentialTerm,HighDim.fourierCoeff_congr_ae he]
  simp only [InCriticalSobolev,memLp_congr_ae he,ht]

/-- Actual Green potentials of every finite-entropy density lie in the critical
Sobolev space and have zero mean. No L2 assumption on the density is used. -/
theorem densityPotential_regular {d : ℕ} (hd : 0 < d) {β : ℝ} (hβ : 0 < β)
    (ρ : ProbabilityDensity d) (hρ : ρ.FiniteEntropy) :
    InCriticalSobolev (densityPotential β ρ.value) ∧ MeanZero (densityPotential β ρ.value) := by
  let v := FiniteEntropyGreen.dualPotential hd (spectralThreshold d/(2*β)) (Bridge.density ρ) hρ
  have hv := FiniteEntropyGreen.dualPotential_admissible hd (spectralThreshold d/(2*β))
    (Bridge.density ρ) hρ
  have he := potential_ae hd hβ (Bridge.density ρ) hρ
  refine ⟨(inCriticalSobolev_congr he).mp (realValue_sobolev v hv),?_⟩
  exact (integral_congr_ae he).symm.trans (realValue_meanZero v hv)

/-- Equation (2. dual gap), with the full finite-entropy probability domain. -/
theorem dual_gap {d : ℕ} (hd : 0 < d) {β : ℝ} (hβ : 0 < β)
    (ρ : ProbabilityDensity d) (hρ : ρ.FiniteEntropy) :
    densityValue β ρ.value = potentialValue β (densityPotential β ρ.value) -
      relativeEntropy ρ.value (normalizedGibbs (densityPotential β ρ.value)) := by
  have hσ : 0 < spectralThreshold d := Legacy.TorusEndpoint.endpointSigma_pos hd
  have hA : 0 < spectralThreshold d/(2*β) := by positivity
  let r := Bridge.density ρ
  let v := FiniteEntropyGreen.dualPotential hd (spectralThreshold d/(2*β)) r hρ
  have hv := FiniteEntropyGreen.dualPotential_admissible hd (spectralThreshold d/(2*β)) r hρ
  have he := potential_ae hd hβ r hρ
  have hg : gibbsValue v =ᵐ[torusMeasure d] normalizedGibbs (densityPotential β ρ.value) :=
    gibbs_congr he
  have hid := FiniteEntropyGreen.dual_gap_identity hd hA r hρ
  change densityValue β r.value = potentialValue β (densityPotential β r.value)-
    relativeEntropy r.value (normalizedGibbs (densityPotential β r.value))
  change realValue v =ᵐ[torusMeasure d] densityPotential β r.value at he
  rw [densityValue_eq_legacy hd hβ r hρ]
  rw [← potentialValue_congr β he, potentialValue_realValue hd hβ v hv]
  change gibbsValue v =ᵐ[torusMeasure d] normalizedGibbs (densityPotential β r.value) at hg
  have hr := relativeEntropy_congr (f := r.value) (f' := r.value) EventuallyEq.rfl hg
  rw [← hr]
  exact hid

/-- Equation (2. primal gap), for every real mean-zero critical Sobolev potential. -/
theorem primal_gap {d : ℕ} (hd : 0 < d) {β : ℝ} (hβ : 0 < β)
    (u : Torus d → ℝ) (hu : InCriticalSobolev u) (hm : MeanZero u) :
    potentialValue β u = densityValue β (normalizedGibbs u) -
      coefficient d β*potentialEnergy (u-densityPotential β (normalizedGibbs u)) := by
  have hσ : 0 < spectralThreshold d := Legacy.TorusEndpoint.endpointSigma_pos hd
  have hA : 0 < spectralThreshold d/(2*β) := by positivity
  have hC : 0 < endpointConstant d := div_pos (Nat.cast_pos.mpr hd) hσ
  have hR := GenericAttainment.rough_bound hd (by positivity : 0 < endpointConstant d/2)
    (by linarith : endpointConstant d/2 < endpointConstant d)
  let U := Bridge.potentialLp u hu.1
  have hU : Admissible U := by
    refine ⟨Bridge.potentialLp_real u hu.1,?_,Bridge.potentialLp_summable hd u hu⟩
    rw [SobolevCentering.fourier_zero]
    calc
      _ = ∫ x,(u x : ℂ) ∂torusMeasure d := integral_congr_ae (Bridge.potentialLp_ae u hu.1)
      _ = 0 := by
        rw [integral_complex_ofReal]
        exact congrArg Complex.ofReal hm
  have hUu : realValue U =ᵐ[torusMeasure d] u := by
    filter_upwards [Bridge.potentialLp_ae u hu.1] with x hx
    exact congrArg Complex.re hx
  let r := gibbsDensity hR hU
  have hr := gibbsDensity_finiteEntropy hR hU
  let v := FiniteEntropyGreen.dualPotential hd (spectralThreshold d/(2*β)) r hr
  have hv := FiniteEntropyGreen.dualPotential_admissible hd (spectralThreshold d/(2*β)) r hr
  have hru : r.value =ᵐ[torusMeasure d] normalizedGibbs u := gibbs_congr hUu
  have he := potential_ae hd hβ r hr
  have hdiff : realValue (U-v) =ᵐ[torusMeasure d]
      u-densityPotential β (normalizedGibbs u) := by
    rw [← densityPotential_congr β hru]
    filter_upwards [Lp.coeFn_sub U v,hUu,he] with x hx hu' hv'
    change ((U-v) x).re = _
    rw [hx]
    change (U x).re = u x at hu'
    change (v x).re = densityPotential β r.value x at hv'
    simp only [Pi.sub_apply,Complex.sub_re,hu',hv']
  have henergy := realValue_energy hd (U-v) (admissible_sub hU hv)
  rw [potentialEnergy_congr hdiff] at henergy
  rw [← potentialValue_congr β hUu,potentialValue_realValue hd hβ U hU,
    ← densityValue_congr β hru,densityValue_eq_legacy hd hβ r hr,henergy]
  have hid := FiniteEntropyGreen.primal_gap_identity hd hR hA U hU
  change functional _ U = densityFunctional _ r-coefficient d β*((2*Real.pi)^d*criticalEnergy (U-v))
  rw [hid]
  congr 1
  unfold coefficient
  have hc : (2*Real.pi)^d ≠ 0 := (pow_pos (by positivity : 0 < 2*Real.pi) d).ne'
  field_simp
  rfl

#print axioms densityPotential_regular
#print axioms dual_gap
#print axioms primal_gap
end BecknerOnofri.HighDim.Gap
