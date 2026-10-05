module

public import BecknerOnofri.OrderParameterDefinitions
public import BecknerOnofri.PhysicalBranchProperties
public import BecknerOnofri.GlobalOptimizerClassification

@[expose] public section

/-! Density first-shell order parameter, uniformly over every global optimizer.
The proof uses the exact Euler multiplier and the diagonal amplitude estimate. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter Asymptotics
open scoped BigOperators Topology ComplexConjugate
namespace BecknerOnofri.HighDim.OrderParameterOnset
open ContinuousGibbs ContinuousFirstShell DiagonalScalarBranch PhysicalBranchProperties

lemma orderParameter_congr {d : ℕ} {f g : Torus d → ℝ}
    (h : f =ᵐ[torusMeasure d] g) : firstShellOrderParameter f = firstShellOrderParameter g := by
  have he (k : Frequency d) : fourierCoeff f k = fourierCoeff g k := by
    apply integral_congr_ae
    filter_upwards [h] with x hx
    rw [hx]
  simp only [firstShellOrderParameter, he]

lemma orderParameter_translate {d : ℕ} (f : Torus d → ℝ) (a : Torus d) :
    firstShellOrderParameter (translate f a) = firstShellOrderParameter f := by
  simp only [firstShellOrderParameter, norm_fourierCoeff_translate]

lemma orderParameter_continuous {d : ℕ} (f : Space d) :
    firstShellOrderParameter f = Real.sqrt (2*∑ i : Fin d, ‖coefficient (axisFrequency i) f‖^2) := by
  simp only [firstShellOrderParameter, ← coefficient_eq_fourierCoeff, coefficient_neg,
    Complex.norm_conj, Finset.sum_add_distrib, two_mul]

lemma branch_density_axis {d : ℕ} (hd : 12 ≤ d) :
    ∀ᶠ β in 𝓝[>] (spectralThreshold d), ∀ i : Fin d,
      fourierCoeff (normalizedGibbs (physicalPotential hd β)) (axisFrequency i) =
        ((amplitude hd (β/spectralThreshold d)/(β/spectralThreshold d) : ℝ) : ℂ) := by
  filter_upwards [physical_branch_properties hd, self_mem_nhdsWithin] with β hb hβ
  have hσ := spectralThreshold_pos (by omega : 0<d)
  have hμ : 0 < β/spectralThreshold d := div_pos (hσ.trans hβ) hσ
  intro i
  have he := hb.stationary ⟨axisFrequency i,axisFrequency_ne_zero i⟩
  simp only [← Complex.ofReal_pow,frequencyLength_pow_eq,latticeSquare_axis,Nat.cast_one,Real.one_rpow,
    Complex.ofReal_one,one_mul,physical_axis_coefficient] at he
  rw [Complex.ofReal_div]
  apply (eq_div_iff (Complex.ofReal_ne_zero.mpr hμ.ne')).mpr
  simpa only [Complex.ofReal_div,mul_comm] using he.symm

lemma branch_orderParameter {d : ℕ} (hd : 12 ≤ d) :
    ∀ᶠ β in 𝓝[>] (spectralThreshold d),
      firstShellOrderParameter (normalizedGibbs (physicalPotential hd β)) =
        Real.sqrt (2*(d:ℝ)) * amplitude hd (β/spectralThreshold d)/(β/spectralThreshold d) := by
  filter_upwards [branch_density_axis hd,self_mem_nhdsWithin] with β hc hβ
  have hσ := spectralThreshold_pos (by omega : 0<d)
  have hμ : 0 < β/spectralThreshold d := div_pos (hσ.trans hβ) hσ
  have he : (normalized (physicalPotential hd β) : Torus d → ℝ) =
      normalizedGibbs (physicalPotential hd β) := funext (normalized_apply _)
  rw [← he,orderParameter_continuous]
  simp only [coefficient_eq_fourierCoeff,he,hc,Complex.norm_real,Real.norm_eq_abs,sq_abs,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  rw [← mul_assoc,Real.sqrt_mul (by positivity : 0 ≤ 2*(d:ℝ)),Real.sqrt_sq_eq_abs,
    abs_of_nonneg (div_nonneg (amplitude_nonneg hd _) hμ.le)]
  ring

/-- The explicit leading term and an O(delta) error for the actual density branch. -/
theorem branch_orderParameter_bound {d : ℕ} (hd : 12 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ β in 𝓝[>] (spectralThreshold d),
      |firstShellOrderParameter (normalizedGibbs (physicalPotential hd β)) -
        Real.sqrt (2*(d:ℝ)/kappa d)*Real.sqrt (onsetDelta d β)| ≤ C*onsetDelta d β := by
  obtain ⟨C,hC,hbound⟩ := (amplitude_sqrt_bound hd).exists_pos
  have hsmall : ∀ᶠ μ in 𝓝[>] (1:ℝ), amplitude hd μ < 1 :=
    (amplitude_tendsto hd).eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))
  refine ⟨Real.sqrt (2*(d:ℝ))*(C+1),by positivity,?_⟩
  filter_upwards [branch_orderParameter hd,
    (normalized_parameter_tendsto hd).eventually hbound.bound,
    (normalized_parameter_tendsto hd).eventually hsmall,
    (normalized_parameter_tendsto hd).eventually self_mem_nhdsWithin] with β he hb ha hμ
  let μ := β/spectralThreshold d
  have hμ1 : 1 < μ := hμ
  have hμ0 : 0 < μ := by linarith
  have hδ := onset_pos hμ1
  have hδeq := physical_onset_eq hd β
  have hk := kappa_pos d hd
  have hid : amplitude hd μ/μ - amplitude hd μ = -onset μ*amplitude hd μ := by
    unfold onset
    ring
  have hdiff : |amplitude hd μ/μ-amplitude hd μ| ≤ onset μ := by
    rw [hid,abs_mul,abs_neg,abs_of_pos hδ,abs_of_nonneg (amplitude_nonneg hd μ)]
    exact mul_le_of_le_one_right hδ.le ha.le
  have hb' : |amplitude hd μ-Real.sqrt (onset μ/kappa d)| ≤ C*onset μ := by
    change ‖amplitude hd μ-Real.sqrt (onset μ/kappa d)‖ ≤ C*‖onset μ‖ at hb
    simpa only [Real.norm_eq_abs,abs_of_pos hδ] using hb
  have herr : |amplitude hd μ/μ-Real.sqrt (onset μ/kappa d)| ≤ (C+1)*onset μ := by
    calc
      _ ≤ |amplitude hd μ/μ-amplitude hd μ| + |amplitude hd μ-Real.sqrt (onset μ/kappa d)| :=
        abs_sub_le _ _ _
      _ ≤ onset μ + C*onset μ := add_le_add hdiff hb'
      _ = _ := by ring
  have hsqrt : Real.sqrt (2*(d:ℝ)/kappa d)*Real.sqrt (onsetDelta d β) =
      Real.sqrt (2*(d:ℝ))*Real.sqrt (onset μ/kappa d) := by
    rw [Real.sqrt_div (by positivity),Real.sqrt_div hδ.le,hδeq]
    ring
  rw [he,hsqrt]
  calc
    _ = Real.sqrt (2*(d:ℝ))*|amplitude hd μ/μ-Real.sqrt (onset μ/kappa d)| := by
      change |Real.sqrt (2*(d:ℝ))*amplitude hd μ/μ-
        Real.sqrt (2*(d:ℝ))*Real.sqrt (onset μ/kappa d)| = _
      rw [show Real.sqrt (2*(d:ℝ))*amplitude hd μ/μ-
        Real.sqrt (2*(d:ℝ))*Real.sqrt (onset μ/kappa d) =
        Real.sqrt (2*(d:ℝ))*(amplitude hd μ/μ-Real.sqrt (onset μ/kappa d)) by ring,
        abs_mul,abs_of_nonneg (Real.sqrt_nonneg _)]
    _ ≤ Real.sqrt (2*(d:ℝ))*((C+1)*onset μ) :=
      mul_le_mul_of_nonneg_left herr (Real.sqrt_nonneg _)
    _ = _ := by change _ = _; rw [show onset μ = onsetDelta d β from hδeq]; ring

/-- One constant works for all global minimizing densities and all translations. -/
theorem all_minimizers_bound {d : ℕ} (hd : 12 ≤ d)
    (hEndpoint : BecknerOnofri.EndpointRigidity.CoefficientEndpoint d (1/2))
    (hRigidity : BecknerOnofri.OnsetCompactness.DensityRigidity d) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ β in 𝓝[>] (spectralThreshold d),
      ∀ ρ : ProbabilityDensity d, IsGlobalMinimizer β ρ →
        |firstShellOrderParameter ρ.value -
          Real.sqrt (2*(d:ℝ)/kappa d)*Real.sqrt (onsetDelta d β)| ≤ C*onsetDelta d β := by
  obtain ⟨C,hC,hbound⟩ := branch_orderParameter_bound hd
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound,GlobalOptimizerClassification.physical_density_classification hd hEndpoint hRigidity]
    with β hb hc
  intro ρ hρ
  obtain ⟨a,ha⟩ := (hc.2 ρ).mp hρ
  rw [orderParameter_congr ha,normalizedGibbs_translate,orderParameter_translate]
  exact hb

#print axioms branch_orderParameter_bound
#print axioms all_minimizers_bound
end BecknerOnofri.HighDim.OrderParameterOnset
