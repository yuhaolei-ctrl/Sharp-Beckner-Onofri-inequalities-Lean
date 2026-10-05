import BecknerOnofri.SelectedCubicSymmetry
import BecknerOnofri.SelectedEnclosureStep

/-! Disjoint-coordinate correlation for the actual selected maximizer.
This is the Ginibre step in the source marginal bounds, with reflection
symmetry supplied by the genuine positive cosine representation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped BigOperators
namespace BecknerOnofri.HighDim.SelectedNumericalModel
open Legacy.TorusEndpoint Legacy.BecknerOnofri
open TorusSobolev SubcriticalAttainment SubcriticalEuler
open GinibreCovariance ContinuousGibbs CosineCoefficientLattice

/-- Actual Gibbs modes are real and nonnegative. -/
theorem densityFourier_eq_mode {u : TorusL2 12} (hu : Selected u) (k : Frequency 12) :
    densityFourier (gibbsValue u) k=(densityMode u k : ℂ) := by
  rw [PositiveFourierSupport.selected_density_exponential hu]
  unfold densityMode
  rw [PositiveFourierSupport.selected_density_exponential hu]
  simp

theorem densityMode_nonneg {u : TorusL2 12} (hu : Selected u) (k : Frequency 12) :
    0≤densityMode u k := by
  unfold densityMode
  rw [PositiveFourierSupport.selected_density_exponential hu]
  simpa using div_nonneg (fourierExponential_nonneg _ (amplitude_nonneg hu) k)
    (ContinuousGibbs.partition_pos (potential u)).le
      |>.trans_eq (by rw [potential_partition hu])

@[simp] theorem densityMode_zero {u : TorusL2 12} (hu : Selected u) : densityMode u 0=1 := by
  unfold densityMode
  have h := densityFourier_zero (gibbsDensity rough hu.1)
  change (densityFourier (gibbsValue u) 0).re=1
  change densityFourier (gibbsValue u) 0=1 at h
  rw [h]
  rfl

theorem densityMode_same_abs {u : TorusL2 12} (hu : Selected u) (k l : Frequency 12)
    (habs : ∀ i,(k i).natAbs=(l i).natAbs) : densityMode u k=densityMode u l :=
  congrArg Complex.re (selected_densityFourier_same_abs hu k l habs)

theorem densityMode_permutation {u : TorusL2 12} (hu : Selected u)
    (σ : Equiv.Perm (Fin 12)) (k : Frequency 12) :
    densityMode u (ContinuousSymmetry.frequencyPermutation σ k)=densityMode u k :=
  congrArg Complex.re (selected_permutation_densityFourier hu σ k)

/-- Disjoint coordinate supports turn the cosine covariance into the
multiplicative Fourier bound appearing in the source proof. -/
theorem densityMode_disjoint_product {u : TorusL2 12} (hu : Selected u)
    (k l : Frequency 12) (hdis : ∀ i,k i=0 ∨ l i=0) :
    densityMode u k*densityMode u l≤densityMode u (k+l) := by
  have habs : ∀ i,((k-l) i).natAbs=((k+l) i).natAbs := by
    intro i
    rcases hdis i with hi | hi <;> simp [hi]
  have he := densityMode_same_abs hu (k-l) (k+l) habs
  have h := cosineSeries_covariance_nonneg (amplitude u) id (amplitude_nonneg hu)
    (amplitude_summable hu) k l
  change 0≤logPartitionHessian (potential u) (cosine k) (cosine l) at h
  rw [logPartitionHessian_apply,cosine_mul_cosine,map_smul,map_add] at h
  simp only [smul_eq_mul,← density_expectation hu] at h
  change 0≤(1/2:ℝ)*(densityMode u (k-l)+densityMode u (k+l))-
    densityMode u k*densityMode u l at h
  rw [he] at h
  linarith

/-- Each full mode dominates the product of its actual axis modes. -/
theorem densityMode_coordinate_product {u : TorusL2 12} (hu : Selected u)
    (k : Frequency 12) :
    (∏ i,densityMode u (Pi.single i (k i)))≤densityMode u k := by
  classical
  have h (S : Finset (Fin 12)) :
      (∏ i∈S,densityMode u (Pi.single i (k i)))≤densityMode u (∑ i∈S,Pi.single i (k i)) := by
    induction S using Finset.induction_on with
    | empty => simp [densityMode_zero hu]
    | @insert i S hi ih =>
      simp only [Finset.prod_insert hi,Finset.sum_insert hi]
      apply (mul_le_mul_of_nonneg_left ih (densityMode_nonneg hu _)).trans
      apply densityMode_disjoint_product hu
      intro j
      by_cases hj : j=i
      · subst j
        right
        simp only [Finset.sum_apply]
        apply Finset.sum_eq_zero
        intro a ha
        exact Pi.single_eq_of_ne (by intro he; exact hi (he ▸ ha)) _
      · exact Or.inl (Pi.single_eq_of_ne hj _)
  simpa only [Finset.univ_sum_single] using h Finset.univ

#print axioms densityMode_disjoint_product
#print axioms densityMode_coordinate_product
end BecknerOnofri.HighDim.SelectedNumericalModel
