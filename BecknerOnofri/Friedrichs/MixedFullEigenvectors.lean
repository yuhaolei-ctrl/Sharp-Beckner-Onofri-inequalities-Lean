import BecknerOnofri.Friedrichs.MixedProfileOperator
import BecknerOnofri.Friedrichs.MixedChebyshevEigenvectors
import BecknerOnofri.Friedrichs.PeriodicEigenprofiles

/-! Full mixed Dirichlet/periodic eigenfunctions. Inactive coordinates include
both sine and cosine modes on the actual full circle. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Polynomial
open scoped ContDiff BigOperators
namespace BecknerOnofri.Friedrichs.MixedSpatial
open Legacy.BecknerOnofri.JacobiAngular

def fullEigenprofile (m n : ℕ) (odd : Bool) : ℝ → ℝ :=
  if m=0 then periodicMode odd n else
    angular m (fun z => (derivative^[m] (Chebyshev.T ℝ (n:ℤ))).eval z)

lemma fullEigenprofile_smooth (m n : ℕ) (odd : Bool) : ContDiff ℝ ∞ (fullEigenprofile m n odd) := by
  by_cases hm : m=0
  · simpa only [fullEigenprofile,if_pos hm] using periodicMode_smooth odd n
  · simpa only [fullEigenprofile,if_neg hm] using angular_smooth m (polynomial_contDiff (derivative^[m] (Chebyshev.T ℝ (n:ℤ))))

lemma fullEigenprofile_periodic (n : ℕ) (odd : Bool) :
    Function.Periodic (fullEigenprofile 0 n odd) (2*Real.pi) := by
  simpa [fullEigenprofile] using periodicMode_periodic odd n

lemma fullEigenprofile_endpoints (m n : ℕ) (odd : Bool) (hm : m≠0) :
    fullEigenprofile m n odd 0=0 ∧ fullEigenprofile m n odd Real.pi=0 := by
  simp [fullEigenprofile,hm,angular,zero_pow hm]

lemma fullEigenprofile_potential (m n : ℕ) (odd : Bool) :
    Integrable (fun t => (SpatialForm.potentialFactor m t*fullEigenprofile m n odd t)^2) (coordinateMeasure m) := by
  by_cases hm : m=0
  · subst m
    simp only [SpatialForm.potentialFactor,Nat.cast_zero,zero_mul,Real.sqrt_zero,zero_div,
      zero_pow (by decide : (2:ℕ)≠0)]
    exact integrable_zero ℝ ℝ (coordinateMeasure 0)
  · simpa only [fullEigenprofile,if_neg hm] using angular_coordinate_potential_integrable m
      (polynomial_contDiff (derivative^[m] (Chebyshev.T ℝ (n:ℤ))))

lemma fullEigenprofile_weak (m n : ℕ) (odd : Bool) {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hend : m≠0 → φ 0=0 ∧ φ Real.pi=0)
    (hp : m=0 → φ (2*Real.pi)=φ 0) :
    (∫ t,deriv (fullEigenprofile m n odd) t*deriv φ t+
      ((m:ℝ)*((m:ℝ)-1)/(Real.sin t)^2)*fullEigenprofile m n odd t*φ t ∂coordinateMeasure m)=
      ∫ t,(n:ℝ)^2*fullEigenprofile m n odd t*φ t ∂coordinateMeasure m := by
  by_cases hm : m=0
  · subst m
    simpa [fullEigenprofile,coordinateMeasure] using periodicMode_weak odd n hφ (hp rfl)
  · have h := coordinate_angular_weak m
      (polynomial_contDiff (derivative^[m] (Chebyshev.T ℝ (n:ℤ)))) hφ hend
    simpa only [fullEigenprofile,if_neg hm,angularImage_chebyshev] using h

def fullEigenprofiles {d : ℕ} (α n : MultiIndex d) (odd : Fin d → Bool) (i : Fin d) : ℝ → ℝ :=
  fullEigenprofile (α i) (n i) (odd i)

lemma fullEigenprofiles_smooth {d : ℕ} (α n : MultiIndex d) (odd : Fin d → Bool) (i : Fin d) :
    ContDiff ℝ ∞ (fullEigenprofiles α n odd i) := fullEigenprofile_smooth (α i) (n i) (odd i)

lemma fullEigenprofiles_potential {d : ℕ} (α n : MultiIndex d) (odd : Fin d → Bool) :
    ProfilePotentialIntegrable α (fullEigenprofiles α n odd) := by
  intro i
  exact weighted_product_square_integrable α (fullEigenprofiles α n odd)
    (fun j => (fullEigenprofiles_smooth α n odd j).continuous) i _
    (fullEigenprofile_potential (α i) (n i) (odd i))

lemma fullEigenprofiles_weak {d : ℕ} (α n : MultiIndex d) (odd : Fin d → Bool) :
    ProfileWeakImage α (fullEigenprofiles α n odd)
      (fun i t => (n i:ℝ)^2*fullEigenprofiles α n odd i t) := by
  intro i φ hφ hend hp
  exact fullEigenprofile_weak (α i) (n i) (odd i) hφ hend hp

lemma fullEigenprofiles_image {d : ℕ} (α n : MultiIndex d) (odd : Fin d → Bool) (x : Space d) :
    profileOperatorImage (fullEigenprofiles α n odd)
      (fun i t => (n i:ℝ)^2*fullEigenprofiles α n odd i t) x=
      (∑ i,(n i:ℝ)^2)*productProfile (fullEigenprofiles α n odd) x := by
  unfold profileOperatorImage
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  unfold profileCoordinateImage
  rw [← mul_left_comm, Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  rfl

def fullEigenvector {d : ℕ} (α n : MultiIndex d) (odd : Fin d → Bool) : H α :=
  (profileLift α (fullEigenprofiles α n odd) (fullEigenprofiles_smooth α n odd)
    (fullEigenprofiles_potential α n odd)).1

theorem fullEigenvector_operatorGraph {d : ℕ} (α n : MultiIndex d) (odd : Fin d → Bool) :
    operatorGraph α (fullEigenvector α n odd) ((∑ i,(n i:ℝ)^2) • fullEigenvector α n odd) := by
  have hg : ∀ i,Continuous (fun t => (n i:ℝ)^2*fullEigenprofiles α n odd i t) :=
    fun i => continuous_const.mul (fullEigenprofiles_smooth α n odd i).continuous
  have h := profile_operatorGraph α (fullEigenprofiles α n odd)
    (fun i t => (n i:ℝ)^2*fullEigenprofiles α n odd i t) (fullEigenprofiles_smooth α n odd) hg
    (fullEigenprofiles_potential α n odd) (fullEigenprofiles_weak α n odd)
    (fun i hi => by simpa only [fullEigenprofiles,hi] using fullEigenprofile_periodic (n i) (odd i))
    (fun i hi => fullEigenprofile_endpoints (α i) (n i) (odd i) hi)
  have he : profileOperatorImageLp α (fullEigenprofiles α n odd)
      (fun i t => (n i:ℝ)^2*fullEigenprofiles α n odd i t) (fullEigenprofiles_smooth α n odd) hg=
      (∑ i,(n i:ℝ)^2) • fullEigenvector α n odd := by
    apply Lp.ext
    filter_upwards [(continuous_memLp α (profileOperatorImage_continuous _ _
      (fullEigenprofiles_smooth α n odd) hg)).coeFn_toLp,
      Lp.coeFn_smul (∑ i,(n i:ℝ)^2) (fullEigenvector α n odd),
      (profile_memLp α (fullEigenprofiles α n odd) (fullEigenprofiles_smooth α n odd)).coeFn_toLp] with x hx hs hv
    change profileOperatorImageLp α (fullEigenprofiles α n odd)
      (fun i t => (n i:ℝ)^2*fullEigenprofiles α n odd i t) (fullEigenprofiles_smooth α n odd) hg x=_ at hx
    change fullEigenvector α n odd x=productProfile (fullEigenprofiles α n odd) x at hv
    rw [hx,hs]
    simpa only [Pi.smul_apply,smul_eq_mul,hv] using fullEigenprofiles_image α n odd x
  rw [he] at h
  exact h

#print axioms fullEigenvector_operatorGraph
end BecknerOnofri.Friedrichs.MixedSpatial
