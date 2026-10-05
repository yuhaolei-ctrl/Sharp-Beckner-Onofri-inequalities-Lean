module

public import BecknerOnofri.GibbsTrialLower
public import BecknerOnofri.GinibreStrictCovariance

@[expose] public section

/-! Derivatives of the actual Bessel ratios, obtained from the already
proved Gibbs integral representation and covariance derivative. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
namespace BecknerOnofri.HighDim.CircleScalar
open ContinuousGibbs GinibreCovariance GibbsTrialLower GibbsPerturbation

def circleFrequency (k : ℤ) : Frequency 1 := fun _ => k

theorem trial_one_mean (h : ℝ) (k : ℤ) :
    weightedMean (trialPotential 1 h) (cosine (circleFrequency k))=besselRatio h k.natAbs := by
  rw [trial_cosine_expectation]
  simp [circleFrequency]

theorem trial_one_line (h : ℝ) : trialPotential 1 h=h • ((2:ℝ) • cosine (circleFrequency 1)) := by
  unfold trialPotential cosinePotential
  simp only [Fin.sum_univ_one,smul_smul]
  congr 1
  · ring

/-- The signed order formulation includes the zero-order ratio without
an artificial boundary convention for m_{-1}. -/
theorem besselRatio_derivative (h : ℝ) (k : ℤ) :
    HasDerivAt (fun a : ℝ => besselRatio a k.natAbs)
      (besselRatio h (k-1).natAbs+besselRatio h (k+1).natAbs-
        2*besselRatio h k.natAbs*besselRatio h 1) h := by
  have hd := expectation_line_hasDerivAt (0:Space 1) ((2:ℝ) • cosine (circleFrequency 1))
    (cosine (circleFrequency k)) h
  simp only [zero_add,← trial_one_line,trial_one_mean] at hd
  have he : logPartitionHessian (trialPotential 1 h) ((2:ℝ) • cosine (circleFrequency 1))
      (cosine (circleFrequency k))=
      besselRatio h (k-1).natAbs+besselRatio h (k+1).natAbs-
        2*besselRatio h k.natAbs*besselRatio h 1 := by
    rw [logPartitionHessian_symmetric,logPartitionHessian_apply,mul_smul_comm,cosine_mul_cosine]
    simp only [map_smul,map_add,smul_eq_mul]
    have hf1 : circleFrequency k-circleFrequency 1=circleFrequency (k-1) := rfl
    have hf2 : circleFrequency k+circleFrequency 1=circleFrequency (k+1) := rfl
    rw [hf1,hf2,trial_one_mean,trial_one_mean,trial_one_mean,trial_one_mean]
    norm_num
    ring
  rw [he] at hd
  exact hd

theorem besselRatio_covariance_derivative (h : ℝ) (k : ℤ) :
    HasDerivAt (fun a : ℝ => besselRatio a k.natAbs)
      (2*logPartitionHessian (trialPotential 1 h) (cosine (circleFrequency 1))
        (cosine (circleFrequency k))) h := by
  have hd := expectation_line_hasDerivAt (0:Space 1) ((2:ℝ) • cosine (circleFrequency 1))
    (cosine (circleFrequency k)) h
  simpa only [zero_add,← trial_one_line,trial_one_mean,map_smul,
    ContinuousLinearMap.smul_apply,smul_eq_mul] using hd

theorem besselRatio_mono (k : ℤ) :
    MonotoneOn (fun h : ℝ => besselRatio h k.natAbs) (Set.Ici 0) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
    (f':=fun h => 2*logPartitionHessian (trialPotential 1 h) (cosine (circleFrequency 1))
      (cosine (circleFrequency k)))
  · exact (continuous_iff_continuousAt.mpr (fun h =>
      (besselRatio_covariance_derivative h k).continuousAt)).continuousOn
  · intro h _
    exact (besselRatio_covariance_derivative h k).hasDerivWithinAt
  · intro h hh
    have hh0 : 0≤h := Set.mem_Ici.mp (interior_subset hh)
    have hc := cosine_covariance_nonneg (fun _ : Fin 1 => 2*h)
      axisFrequency (fun _ => by positivity)
      (circleFrequency 1) (circleFrequency k)
    exact mul_nonneg (by norm_num) hc

theorem first_cosine_variance_pos (h : ℝ) :
    0<logPartitionHessian (trialPotential 1 h) (cosine (circleFrequency 1))
      (cosine (circleFrequency 1)) := by
  have hn := logPartitionHessian_nonneg (trialPotential 1 h) (cosine (circleFrequency 1))
  by_contra hh
  have hz := le_antisymm (le_of_not_gt hh) hn
  obtain ⟨c,hc⟩ := (logPartitionHessian_nullspace _ _).mp hz
  have hf : circleFrequency 1≠0 := by
    intro he
    have hi := congrFun he 0
    norm_num [circleFrequency] at hi
  have hm := congrArg (mean 1) hc
  rw [cosine_mean_eq,if_neg hf] at hm
  have hc0 : c=0 := by simpa [mean_apply] using hm.symm
  have hp := congrArg (fun f : Space 1 => f 0) hc
  simp [cosine_apply,hc0,UnitAddTorus.mFourier] at hp

theorem besselRatio_first_strictMono : StrictMono (fun h : ℝ => besselRatio h 1) := by
  apply strictMono_of_hasDerivAt_pos (fun h => besselRatio_covariance_derivative h 1)
  intro h
  exact mul_pos (by norm_num) (first_cosine_variance_pos h)

#print axioms besselRatio_first_strictMono
#print axioms besselRatio_derivative
#print axioms besselRatio_mono
end BecknerOnofri.HighDim.CircleScalar
