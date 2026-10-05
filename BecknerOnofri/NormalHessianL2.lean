import BecknerOnofri.ComplementSobolevCoercivity
import BecknerOnofri.RawAttainment
import Legacy.BecknerOnofri.BoundedL2Multiplier
import Legacy.BecknerOnofri.SobolevScalar

/-! Continuous Gibbs covariance and tangent orthogonality on the actual L²
space used by compact critical Sobolev balls. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter Set
open scoped Topology BigOperators
namespace BecknerOnofri.HighDim.NormalHessianCoercivity
open ContinuousGibbs RawAttainment
open Legacy.BecknerOnofri.TorusSobolev Legacy.BecknerOnofri.SubcriticalAttainment
open Legacy.BecknerOnofri.BoundedL2Multiplier

abbrev RealL2 (d : ℕ) := Lp ℝ 2 (torusMeasure d)

def realPart (d : ℕ) : TorusL2 d →L[ℝ] RealL2 d :=
  Complex.reCLM.compLpL 2 (torusMeasure d)

theorem realPart_ae {d : ℕ} (v : TorusL2 d) :
    realPart d v =ᵐ[torusMeasure d] realValue v :=
  Complex.reCLM.coeFn_compLpL v

def gibbsWeight {d : ℕ} (u : Space d) : Weight (torusMeasure d) where
  value := normalizedGibbs u
  measurable := by
    have he : (fun x => normalized u x)=normalizedGibbs u := funext (normalized_apply u)
    rw [← he]
    exact (normalized u).continuous.aestronglyMeasurable
  bound := ‖normalized u‖
  nonneg_bound := norm_nonneg _
  bounded := Eventually.of_forall (fun x => by simpa only [normalized_apply] using (normalized u).norm_coe_le_norm x)

def gibbsL2 {d : ℕ} (u : Space d) : RealL2 d :=
  ((normalized u).continuous.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).toLp (normalized u)

theorem gibbsL2_ae {d : ℕ} (u : Space d) :
    gibbsL2 u =ᵐ[torusMeasure d] normalizedGibbs u := by
  have he : (fun x => normalized u x)=normalizedGibbs u := funext (normalized_apply u)
  rw [← he]
  exact ((normalized u).continuous.memLp_of_hasCompactSupport
    (μ := torusMeasure d) (p := 2) (HasCompactSupport.of_compactSpace _)).coeFn_toLp

/-- Actual Gibbs covariance, expressed as a continuous quadratic map on L². -/
def covariance {d : ℕ} (u : Space d) (v : TorusL2 d) : ℝ :=
  inner ℝ ((gibbsWeight u).operator (realPart d v)) (realPart d v) -
    (inner ℝ (gibbsL2 u) (realPart d v))^2

theorem covariance_continuous {d : ℕ} (u : Space d) : Continuous (covariance u) := by
  exact (((gibbsWeight u).operator.continuous.comp (realPart d).continuous).inner
    (realPart d).continuous).sub (((continuous_const.inner (realPart d).continuous)).pow 2)

theorem covariance_eq_integrals {d : ℕ} (u : Space d) (v : TorusL2 d) :
    covariance u v = (∫ x, normalizedGibbs u x*(realValue v x)^2 ∂torusMeasure d) -
      (∫ x, normalizedGibbs u x*realValue v x ∂torusMeasure d)^2 := by
  unfold covariance
  rw [L2.inner_def,L2.inner_def]
  congr 1
  · apply integral_congr_ae
    filter_upwards [(gibbsWeight u).operator_ae (realPart d v),realPart_ae v] with x hw hr
    change (realPart d v x)*((gibbsWeight u).operator (realPart d v) x)=_
    rw [hw,hr]
    change realValue v x*(normalizedGibbs u x*realValue v x)=_
    ring
  · congr 1
    apply integral_congr_ae
    filter_upwards [gibbsL2_ae u,realPart_ae v] with x hw hr
    simp only [hw,hr,RCLike.inner_apply,conj_trivial,mul_comm]

@[simp] theorem covariance_zero {d : ℕ} (u : Space d) : covariance u 0=0 := by
  simp [covariance]

theorem covariance_smul {d : ℕ} (u : Space d) (v : TorusL2 d) (t : ℝ) :
    covariance u ((t:ℂ) • v)=t^2*covariance u v := by
  have he : (t:ℂ) • v=t • v := by ext1; rfl
  rw [he]
  simp only [covariance,map_smul,real_inner_smul_left,real_inner_smul_right]
  ring

theorem realValue_normalizedEnergy {d : ℕ} (hd : 0<d) (v : TorusL2 d) (hv : Admissible v) :
    normalizedPotentialEnergy (realValue v)=criticalEnergy v := by
  rw [normalizedPotentialEnergy,realValue_energy hd v hv]
  exact mul_div_cancel_left₀ _ (pow_ne_zero _ (by positivity : (2*Real.pi:ℝ)≠0))

theorem secondVariation_realValue {d : ℕ} (hd : 0<d) (β : ℝ) (u : Space d)
    (v : TorusL2 d) (hv : Admissible v) :
    secondVariation β u (realValue v)=covariance u v-spectralThreshold d/β*criticalEnergy v := by
  rw [secondVariation,covariance_eq_integrals,realValue_normalizedEnergy hd v hv]

def pairing {d : ℕ} (h : Torus d → ℝ) (hh : MemLp h 2 (torusMeasure d)) (v : TorusL2 d) : ℝ :=
  inner ℝ (hh.toLp h) (realPart d v)

theorem pairing_continuous {d : ℕ} (h : Torus d → ℝ) (hh : MemLp h 2 (torusMeasure d)) :
    Continuous (pairing h hh) := continuous_const.inner (realPart d).continuous

theorem pairing_eq_integral {d : ℕ} (h : Torus d → ℝ) (hh : MemLp h 2 (torusMeasure d)) (v : TorusL2 d) :
    pairing h hh v=∫ x, realValue v x*h x ∂torusMeasure d := by
  rw [pairing,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hh.coeFn_toLp,realPart_ae v] with x hh hr
  simp only [hh,hr,RCLike.inner_apply,conj_trivial]

@[simp] theorem pairing_zero {d : ℕ} (h : Torus d → ℝ) (hh : MemLp h 2 (torusMeasure d)) :
    pairing h hh 0=0 := by simp [pairing]

theorem pairing_smul {d : ℕ} (h : Torus d → ℝ) (hh : MemLp h 2 (torusMeasure d))
    (v : TorusL2 d) (t : ℝ) : pairing h hh ((t:ℂ) • v)=t*pairing h hh v := by
  have he : (t:ℂ) • v=t • v := by ext1; rfl
  simp only [he,pairing,map_smul,real_inner_smul_right]

/-- A vector in the actual tangent span, orthogonal to every spanning tangent,
vanishes in L²; no linear independence assumption is needed. -/
theorem covariance_zero_of_tangent_orthogonal {d : ℕ} (u : Space d)
    (ht : ∀ j : Fin d, MemLp (coordinateDerivative u j) 2 (torusMeasure d))
    (v : TorusL2 d) (horth : ∀ j, pairing (coordinateDerivative u j) (ht j) v=0)
    (hspan : ∃ a : Fin d → ℝ, realValue v =ᵐ[torusMeasure d] tangentCombination u a) :
    covariance u v=0 := by
  obtain ⟨a,ha⟩ := hspan
  have he : realPart d v=∑ j : Fin d, a j • (ht j).toLp (coordinateDerivative u j) := by
    apply Lp.ext
    filter_upwards [realPart_ae v,ha,Lp.coeFn_fun_finsetSum Finset.univ (fun j : Fin d => a j • (ht j).toLp (coordinateDerivative u j)),
      Filter.eventually_all.mpr (fun j : Fin d => Lp.coeFn_smul (a j) ((ht j).toLp (coordinateDerivative u j))),
      Filter.eventually_all.mpr (fun j : Fin d => (ht j).coeFn_toLp)] with x hr ha hs hsm hj
    rw [hr,ha,hs]
    simp only [tangentCombination,hsm,Pi.smul_apply,smul_eq_mul,hj]
  have hz : realPart d v=0 := by
    apply (inner_self_eq_zero (𝕜 := ℝ)).mp
    have hh (j : Fin d) : inner ℝ ((ht j).toLp (coordinateDerivative u j)) (realPart d v)=0 := horth j
    calc
      inner ℝ (realPart d v) (realPart d v) =
        inner ℝ (∑ j : Fin d, a j • (ht j).toLp (coordinateDerivative u j)) (realPart d v) := by rw [← he]
      _ = 0 := by simp only [sum_inner,real_inner_smul_left,hh,mul_zero,Finset.sum_const_zero]
  simp [covariance,hz]

#print axioms covariance_zero_of_tangent_orthogonal
end BecknerOnofri.HighDim.NormalHessianCoercivity
