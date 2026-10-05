import BecknerOnofri.TwelveExitReduction
import BecknerOnofri.CommonEnclosure
import BecknerOnofri.GinibreNormMonotonicity
import BecknerOnofri.IterationOmittedTail

/-! The numerical iteration is applied to the actual selected endpoint
maximizer: its nonnegative summable Fourier coefficients reconstruct its
continuous potential, and Gibbs expectations are its genuine density modes. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped Topology BigOperators
namespace BecknerOnofri.HighDim.SelectedNumericalModel
open Legacy.TorusEndpoint Legacy.BecknerOnofri
open TorusSobolev SubcriticalAttainment SubcriticalEuler SmoothFourier SteinerSelection
open GinibreCovariance

/-- Precisely the optimizer class used in the dimension-twelve reduction. -/
abbrev Selected (u : TorusL2 12) : Prop :=
  Admissible u ∧
  (∀ v : TorusL2 12, Admissible v → functional (1/2) v≤functional (1/2) u) ∧
  Steiner (smoothGibbsValue u) ∧ Steiner (fun x => (WienerFourier.representative u x).re)

def amplitude (u : TorusL2 12) (k : Frequency 12) : ℝ := (fourierIsometry 12 u k).re

def potential (u : TorusL2 12) : ContinuousGibbs.Space 12 := cosineSeries (amplitude u) id

theorem rough :
    RoughExponentialBound 12 (endpointConstant 12/2)
      (GreenRoughEnergy.partition 12 (endpointConstant 12/2)) := by
  have hC : 0<endpointConstant 12 := div_pos (by norm_num) (endpointSigma_pos (by norm_num))
  exact GenericAttainment.rough_bound (by norm_num) (by positivity) (by linarith)

theorem amplitude_nonneg {u : TorusL2 12} (hu : Selected u) (k : Frequency 12) :
    0≤amplitude u k :=
  (twelve_selected_fourier_nonnegative u hu.1 hu.2.1 hu.2.2.1 hu.2.2.2 k).2

theorem fourier_eq_amplitude {u : TorusL2 12} (hu : Selected u) (k : Frequency 12) :
    fourierIsometry 12 u k=(amplitude u k : ℂ) :=
  (twelve_selected_fourier_nonnegative u hu.1 hu.2.1 hu.2.2.1 hu.2.2.2 k).1

theorem fourier_norm_summable {u : TorusL2 12} (hu : Selected u) :
    Summable (fun k => ‖fourierIsometry 12 u k‖) :=
  maximizer_fourier_summable (by norm_num) rough (by norm_num : (0:ℝ)<1/2) hu.1 hu.2.1

theorem amplitude_summable {u : TorusL2 12} (hu : Selected u) : Summable (amplitude u) := by
  apply (fourier_norm_summable hu).congr
  intro k
  rw [fourier_eq_amplitude hu,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (amplitude_nonneg hu k)]

theorem potential_apply {u : TorusL2 12} (hu : Selected u) (x : Torus 12) :
    potential u x=(WienerFourier.representative u x).re := by
  have hs := cosineSeries_summable (amplitude u) id (amplitude_nonneg hu) (amplitude_summable hu)
  have hx : Summable (fun k => fourierIsometry 12 u k*UnitAddTorus.mFourier k x) := by
    apply (fourier_norm_summable hu).of_norm_bounded
    intro k
    simp only [norm_mul,mFourier_norm_apply,mul_one,le_refl]
  trans ∑' k, amplitude u k*cosine k x
  · convert! (ContinuousMap.evalCLM ℝ x).map_tsum hs using 1
  change (∑' k, amplitude u k*cosine k x)=(∑' k, fourierIsometry 12 u k*UnitAddTorus.mFourier k x).re
  rw [Complex.re_tsum hx]
  apply tsum_congr
  intro k
  rw [fourier_eq_amplitude hu]
  simp [cosine_apply,Complex.mul_re]

theorem potential_partition {u : TorusL2 12} (hu : Selected u) :
    ContinuousGibbs.partition (potential u)=SubcriticalAttainment.partition u := by
  simp only [ContinuousGibbs.partition,ContinuousGibbs.mean_apply,
    ContinuousGibbs.exponential_apply,SubcriticalAttainment.partition]
  apply integral_congr_ae
  filter_upwards [WienerFourier.representative_ae_eq u (fourier_norm_summable hu)] with x hx
  rw [potential_apply hu,hx]

theorem potential_normalized {u : TorusL2 12} (hu : Selected u) (x : Torus 12) :
    ContinuousGibbs.normalized (potential u) x=smoothGibbsValue u x := by
  change (ContinuousGibbs.partition (potential u))⁻¹*ContinuousGibbs.exponential (potential u) x=_
  rw [potential_partition hu,ContinuousGibbs.exponential_apply,potential_apply hu]
  simp only [smoothGibbsValue,div_eq_mul_inv,mul_comm]

theorem density_expectation {u : TorusL2 12} (hu : Selected u) (k : Frequency 12) :
    (densityFourier (gibbsValue u) k).re=ContinuousGibbs.weightedMean (potential u) (cosine k) := by
  rw [ContinuousGibbs.weightedMean_apply,← GridGibbsComparison.coefficient_re,
    ContinuousFirstShell.coefficient_integral]
  have he := smoothGibbsDensity_fourier rough hu.1 (fourier_norm_summable hu) k
  rw [← he]
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall (fun x => by
    change UnitAddTorus.mFourier (-k) x * (smoothGibbsValue u x : ℂ)=
      UnitAddTorus.mFourier (-k) x * (ContinuousGibbs.normalized (potential u) x : ℂ)
    rw [potential_normalized hu])

theorem amplitude_euler {u : TorusL2 12} (hu : Selected u) {k : Frequency 12} (hk : k≠0) :
    amplitude u k=(frequencyRadius k^12)⁻¹*ContinuousGibbs.weightedMean (potential u) (cosine k) := by
  have he := congrArg Complex.re (maximizer_fourier_formula rough
    (by norm_num : (0:ℝ)<1/2) hu.1 hu.2.1 hk)
  simpa only [amplitude,show 1/(2*(1/2:ℝ))=1 by norm_num,one_mul,
    Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,density_expectation hu] using he

theorem potential_coefficient {u : TorusL2 12} (hu : Selected u) (k : Frequency 12) :
    ContinuousFirstShell.coefficient k (potential u)=fourierIsometry 12 u k := by
  rw [ContinuousFirstShell.coefficient_integral]
  calc
    _ = UnitAddTorus.mFourierCoeff (WienerFourier.representative u) k := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun x => by
        change UnitAddTorus.mFourier (-k) x*(potential u x : ℂ)=
          UnitAddTorus.mFourier (-k) x*WienerFourier.representative u x
        rw [potential_apply hu]
        congr 1
        apply Complex.ext
        · rfl
        · exact (WienerFourier.representative_real u (fourier_norm_summable hu) hu.1.1 x).symm)
    _ = _ := WienerFourier.representative_coefficient u (fourier_norm_summable hu) k

theorem density_coefficient {u : TorusL2 12} (hu : Selected u) (k : Frequency 12) :
    ContinuousFirstShell.coefficient k (ContinuousGibbs.normalized (potential u))=
      densityFourier (gibbsValue u) k := by
  rw [← smoothGibbsDensity_fourier rough hu.1 (fourier_norm_summable hu) k,
    ContinuousFirstShell.coefficient_integral]
  apply integral_congr_ae
  exact Eventually.of_forall (fun x => by
    change UnitAddTorus.mFourier (-k) x*(ContinuousGibbs.normalized (potential u) x : ℂ)=
      UnitAddTorus.mFourier (-k) x*(smoothGibbsValue u x : ℂ)
    rw [potential_normalized hu])

/-- The selected maximizer solves the actual full Green equation. -/
theorem potential_green {u : TorusL2 12} (hu : Selected u) :
    potential u=greenContinuous 12 (ContinuousGibbs.normalized (potential u)) := by
  apply ContinuousFirstShell.coefficient_ext
  intro k
  rw [potential_coefficient hu,coefficient_green (by norm_num),density_coefficient hu]
  by_cases hk : k=0
  · subst k
    simp [hu.1.2.1]
  · rw [if_neg hk,maximizer_fourier_formula rough (by norm_num : (0:ℝ)<1/2) hu.1 hu.2.1 hk]
    congr 1
    norm_num [Bridge.frequencyLength_eq,one_div]

theorem amplitude_zero {u : TorusL2 12} (hu : Selected u) : amplitude u 0=0 := by
  simp [amplitude,hu.1.2.1]

theorem amplitude_euler_raw {u : TorusL2 12} (hu : Selected u) {k : Frequency 12} (hk : k≠0) :
    amplitude u k=(1/frequencyLength k^12)*
      (fourierCoeff (ContinuousGibbs.normalized (potential u)) k).re := by
  rw [← ContinuousFirstShell.coefficient_eq_fourierCoeff,density_coefficient hu,density_expectation hu]
  simpa only [Bridge.frequencyLength_eq,one_div] using amplitude_euler hu hk

theorem omitted_mass_bound {u : TorusL2 12} (hu : Selected u) (A : Finset (Frequency 12)) :
    (∑' k, CommonEnclosure.omitted A (amplitude u) k)≤
      IterationOmittedTail.tailConstant A*gibbsL2Norm (potential u) := by
  classical
  have he : (∑' k, CommonEnclosure.omitted A (amplitude u) k)=
      ∑' k : IterationOmittedTail.OmittedFrequency A, amplitude u k.val := by
    rw [show (∑' k : IterationOmittedTail.OmittedFrequency A, amplitude u k.val)=
      ∑' k, ({k : Frequency 12 | k≠0 ∧ k∉A}.indicator (amplitude u)) k from
        tsum_subtype {k : Frequency 12 | k≠0 ∧ k∉A} (amplitude u)]
    apply tsum_congr
    intro k
    by_cases hk : k∈A
    · simp [CommonEnclosure.omitted,Set.indicator,hk]
    · by_cases hz : k=0
      · subst k; simp [CommonEnclosure.omitted,Set.indicator,hk,amplitude_zero hu]
      · simp [CommonEnclosure.omitted,Set.indicator,hk,hz]
  rw [he]
  have heuler (k : IterationOmittedTail.OmittedFrequency A) := amplitude_euler_raw hu k.property.1
  simp_rw [heuler]
  have hh := IterationOmittedTail.omitted_real_bound (by norm_num : 0<12) A
    (ContinuousGibbs.normalized (potential u))
    ((ContinuousGibbs.normalized (potential u)).continuous.memLp_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
  simpa only [gibbsL2Norm,ContinuousGibbs.normalized_apply] using hh

#print axioms potential_apply
#print axioms potential_normalized
#print axioms amplitude_euler
#print axioms potential_green
#print axioms omitted_mass_bound
end BecknerOnofri.HighDim.SelectedNumericalModel
