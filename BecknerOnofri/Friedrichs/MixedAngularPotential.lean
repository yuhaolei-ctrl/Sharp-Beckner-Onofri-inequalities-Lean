module

public import BecknerOnofri.Friedrichs.MixedWeightedCutoff
public import BecknerOnofri.Friedrichs.AngularCutoffApproximation
public import BecknerOnofri.Friedrichs.FormNormIdentity

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators
namespace BecknerOnofri.Friedrichs.MixedSpatial
open Legacy.BecknerOnofri.JacobiAngular

lemma weighted_product_square_integrable {d : ℕ} (α : MultiIndex d) (f : Fin d → ℝ → ℝ)
    (hf : ∀ j,Continuous (f j)) (i : Fin d) (W : ℝ → ℝ)
    (hi : Integrable (fun t => (W t*f i t)^2) (coordinateMeasure (α i))) :
    Integrable (fun x => (W (x i)*productProfile f x)^2) (spatialMeasure α) := by
  let q (j : Fin d) (t : ℝ) := if j=i then (W t*f i t)^2 else (f j t)^2
  have hq (j : Fin d) : Integrable (q j) (coordinateMeasure (α j)) := by
    by_cases h : j=i
    · subst j
      simpa only [q,if_true] using hi
    · simpa only [q,if_neg h] using coordinate_square_integrable (α j) (hf j)
  have hp := Integrable.fintype_prod hq
  have he : (fun x : Space d => ∏ j,q j (x j))=(fun x => (W (x i)*productProfile f x)^2) := by
    funext x
    rw [← Finset.mul_prod_erase Finset.univ (fun j => q j (x j)) (Finset.mem_univ i)]
    have hprod : (∏ j∈Finset.univ.erase i,q j (x j))=
        ∏ j∈Finset.univ.erase i,(f j (x j))^2 := by
      apply Finset.prod_congr rfl
      intro j hj
      exact if_neg (Finset.ne_of_mem_erase hj)
    rw [hprod]
    simp only [q,if_true,productProfile]
    rw [← Finset.mul_prod_erase Finset.univ (fun j => f j (x j)) (Finset.mem_univ i)]
    rw [Finset.prod_pow]
    ring
  rw [he] at hp
  exact hp

def angularProfiles {d : ℕ} (α : MultiIndex d) (f : Fin d → ℝ → ℝ) (i : Fin d) : ℝ → ℝ :=
  angular (α i) (f i)

lemma angularProfiles_smooth {d : ℕ} (α : MultiIndex d) (f : Fin d → ℝ → ℝ)
    (hf : ∀ i,ContDiff ℝ ∞ (f i)) (i : Fin d) : ContDiff ℝ ∞ (angularProfiles α f i) :=
  angular_smooth (α i) (hf i)

lemma angularProfiles_periodic {d : ℕ} (α : MultiIndex d) (f : Fin d → ℝ → ℝ) (i : Fin d) :
    Function.Periodic (angularProfiles α f i) (2*Real.pi) := by
  intro t
  simp only [angularProfiles,angular,Real.sin_add_two_pi,Real.cos_add_two_pi]

lemma angular_coordinate_potential_integrable (m : ℕ) {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) :
    Integrable (fun t => (SpatialForm.potentialFactor m t*angular m f t)^2) (coordinateMeasure m) := by
  by_cases hm : m=0
  · subst m
    simp only [SpatialForm.potentialFactor,Nat.cast_zero,zero_mul,Real.sqrt_zero,zero_div,
      zero_pow (by decide : (2:ℕ)≠0)]
    exact integrable_zero ℝ ℝ (coordinateMeasure 0)
  · have hi := (angular_potential_integrable (Nat.pos_of_ne_zero hm) hf).const_mul
      ((m:ℝ)*((m:ℝ)-1))
    simp_rw [SpatialForm.potential_sq]
    simpa only [coordinateMeasure,if_neg hm] using hi

lemma angular_product_potential_integrable {d : ℕ} (α : MultiIndex d) (f : Fin d → ℝ → ℝ)
    (hf : ∀ j,ContDiff ℝ ∞ (f j)) (i : Fin d) :
    Integrable (fun x => (SpatialForm.potentialFactor (α i) (x i)*
      productProfile (angularProfiles α f) x)^2) (spatialMeasure α) :=
  weighted_product_square_integrable α (angularProfiles α f)
    (fun j => (angularProfiles_smooth α f hf j).continuous) i _
    (angular_coordinate_potential_integrable (α i) (hf i))

theorem angular_product_potential_error_tendsto_zero {d : ℕ} (α : MultiIndex d)
    (f : Fin d → ℝ → ℝ) (hf : ∀ j,ContDiff ℝ ∞ (f j)) (i : Fin d) :
    Tendsto (fun δ : ℝ => ∫ x,(SpatialForm.potentialFactor (α i) (x i)*
      (cutoffProfile α (angularProfiles α f) δ x-productProfile (angularProfiles α f) x))^2 ∂spatialMeasure α)
      (𝓝[>] 0) (𝓝 (0:ℝ)) :=
  weighted_profile_error_tendsto_zero α _ _ (angular_product_potential_integrable α f hf i)

#print axioms angular_product_potential_error_tendsto_zero
end BecknerOnofri.Friedrichs.MixedSpatial
