import BecknerOnofri.GibbsPerturbation
import BecknerOnofri.GridGibbsComparison
import BecknerOnofri.LocalBesselFourier

/-! Actual Gibbs trial lower bounds and the product von Mises denominator.
The Bessel factors are the convergent series already identified with their
circle Haar integrals. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace BecknerOnofri.HighDim.GibbsTrialLower
open ContinuousGibbs ContinuousFirstShell GinibreCovariance GibbsPerturbation GridGibbsComparison

theorem weighted_exp_jensen {d : ℕ} (b f : Space d) :
    Real.exp (weightedMean b f)≤weightedMean b (exponential f) := by
  let m := weightedMean b f
  have hh : weightedMean b (Real.exp m • (1+f-m • (1:Space d)))≤
      weightedMean b (exponential f) := by
    apply weightedMean_mono
    intro x
    simp only [ContinuousMap.smul_apply,ContinuousMap.sub_apply,ContinuousMap.add_apply,ContinuousMap.one_apply,smul_eq_mul,exponential_apply]
    change Real.exp m*(1+f x-m*1)≤Real.exp (f x)
    have he := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (f x-m)) (Real.exp_pos m).le
    have hmul : Real.exp m*Real.exp (f x-m)=Real.exp (f x) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hmul] at he
    linarith
  simpa only [map_smul,map_sub,map_add,weightedMean_one,smul_eq_mul,mul_one,m,
    add_sub_cancel_right] using hh

theorem weighted_exp_difference {d : ℕ} (b q : Space d) :
    weightedMean b (exponential (q-b))=partition q/partition b := by
  rw [weightedMean_apply]
  have he : normalized b*exponential (q-b)=(partition b)⁻¹ • exponential q := by
    ext x
    simp only [normalized,ContinuousMap.mul_apply,ContinuousMap.smul_apply,
      ContinuousMap.sub_apply,smul_eq_mul,exponential_apply]
    rw [mul_assoc,← Real.exp_add]
    congr 2
    ring
  rw [he,map_smul]
  change (partition b)⁻¹*partition q=partition q/partition b
  ring

/-- A positive, concrete denominator lower bound from any continuous trial potential. -/
theorem trial_lower {d : ℕ} (b q : Space d) :
    Real.exp (logPartitionReal b+weightedMean b (q-b))≤partition q := by
  have hh := weighted_exp_jensen b (q-b)
  rw [weighted_exp_difference] at hh
  rw [Real.exp_add,logPartitionReal,Real.exp_log (partition_pos b)]
  exact (mul_le_mul_of_nonneg_left hh (partition_pos b).le).trans_eq (by
    field_simp [(partition_pos b).ne'])

theorem trial_log_lower {d : ℕ} (b q : Space d) :
    logPartitionReal b+weightedMean b (q-b)≤logPartitionReal q := by
  have hh := Real.log_le_log (Real.exp_pos _) (trial_lower b q)
  simpa only [Real.log_exp,logPartitionReal] using hh

def besselRatio (h : ℝ) (m : ℕ) : ℝ :=
  (∑' n, besselOrderTerm h m n)/besselI0Two h

theorem circleTiltFourier_eq_ratio (h : ℝ) (m : ℤ) :
    circleTiltFourier h m=(besselRatio h m.natAbs : ℂ) := by
  rcases m with n | n
  · exact circleTiltFourier_nat_eq h n
  · change circleTiltFourier h (-((n+1 : ℕ) : ℤ))=(besselRatio h (n+1) : ℂ)
    rw [circleTiltFourier_neg,circleTiltFourier_nat_eq,Complex.conj_ofReal]
    rfl

theorem besselRatio_zero (h : ℝ) : besselRatio h 0=1 := by
  have hh := circleTiltFourier_nat_eq h 0
  simp only [Nat.cast_zero,circleTiltFourier,neg_zero,fourier_zero,ContinuousMap.one_apply,
    one_mul] at hh
  rw [integral_complex_ofReal,circleTiltDensity_integral] at hh
  exact Complex.ofReal_injective hh.symm

def trialPotential (d : ℕ) (h : ℝ) : Space d :=
  cosinePotential (fun _ : Fin d => 2*h) axisFrequency

theorem trialPotential_apply (d : ℕ) (h : ℝ) (x : Torus d) :
    trialPotential d h x=firstShellPotential (fun _ => h) x := by
  simp only [trialPotential,cosinePotential,ContinuousMap.sum_apply,ContinuousMap.smul_apply,
    smul_eq_mul,cosine_apply,mFourier_axisFrequency,firstShellPotential,circleCosine]

theorem trial_partition (d : ℕ) (h : ℝ) :
    partition (trialPotential d h)=(besselI0Two h)^d := by
  simp only [partition,mean_apply,exponential_apply]
  simp_rw [trialPotential_apply]
  rw [firstShell_partition]
  simp

theorem trial_logPartition (d : ℕ) (h : ℝ) :
    logPartitionReal (trialPotential d h)=(d:ℝ)*Real.log (besselI0Two h) := by
  rw [logPartitionReal,trial_partition,Real.log_pow]

theorem trial_normalized (d : ℕ) (h : ℝ) (x : Torus d) :
    normalized (trialPotential d h) x=firstShellTilt (fun _ => h) x := by
  rw [normalized_apply,firstShellTilt_eq_exp]
  unfold normalizedGibbs
  simp_rw [trialPotential_apply]

theorem trial_cosine_expectation (d : ℕ) (h : ℝ) (k : Frequency d) :
    weightedMean (trialPotential d h) (cosine k)=∏ i, besselRatio h (k i).natAbs := by
  rw [weightedMean_apply,← coefficient_re,coefficient_eq_fourierCoeff]
  have he : (normalized (trialPotential d h) : Torus d → ℝ)=firstShellTilt (fun _ => h) :=
    funext (trial_normalized d h)
  rw [he,firstShellTilt_fourier]
  simp only [circleTiltFourier_eq_ratio,← Complex.ofReal_prod,Complex.ofReal_re]

theorem trial_self_expectation (d : ℕ) (h : ℝ) :
    weightedMean (trialPotential d h) (trialPotential d h)=2*(d:ℝ)*h*besselRatio h 1 := by
  rw [show trialPotential d h=cosinePotential (fun _ : Fin d => 2*h) axisFrequency from rfl]
  conv_rhs => rw [show 2*(d:ℝ)*h*besselRatio h 1=(d:ℝ)*(2*h*besselRatio h 1) by ring]
  simp only [cosinePotential,map_sum,map_smul,smul_eq_mul]
  have he (j : Fin d) : weightedMean (trialPotential d h) (cosine (axisFrequency j))=besselRatio h 1 := by
    rw [trial_cosine_expectation]
    classical
    simp only [axisFrequency,apply_ite,Int.natAbs_one,Int.natAbs_zero,besselRatio_zero]
    simp
  change (∑ j : Fin d, 2*h*weightedMean (trialPotential d h) (cosine (axisFrequency j)))=_
  simp only [he,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]

/-- Source denominator lower bound, with its full linear correction. -/
theorem vonMises_log_lower {d : ℕ} {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (k : ι → Frequency d) (h : ℝ) :
    (d:ℝ)*Real.log (besselI0Two h)+
      (∑ j, a j*∏ i, besselRatio h (k j i).natAbs)-2*(d:ℝ)*h*besselRatio h 1≤
        logPartitionReal (cosinePotential a k) := by
  have hh := trial_log_lower (trialPotential d h) (cosinePotential a k)
  rw [map_sub,trial_logPartition,trial_self_expectation] at hh
  simp only [cosinePotential,map_sum,map_smul,smul_eq_mul,trial_cosine_expectation] at hh
  unfold cosinePotential
  linarith

theorem vonMises_lower {d : ℕ} {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (k : ι → Frequency d) (h : ℝ) :
    Real.exp ((d:ℝ)*Real.log (besselI0Two h)+
      (∑ j, a j*∏ i, besselRatio h (k j i).natAbs)-2*(d:ℝ)*h*besselRatio h 1)≤
        partition (cosinePotential a k) := by
  have hh := Real.exp_le_exp.mpr (vonMises_log_lower a k h)
  simpa only [logPartitionReal,Real.exp_log (partition_pos _)] using hh

#print axioms trial_lower
#print axioms vonMises_lower
end BecknerOnofri.HighDim.GibbsTrialLower
