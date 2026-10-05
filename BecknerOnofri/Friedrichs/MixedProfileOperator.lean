import BecknerOnofri.Friedrichs.MixedProfileFormDomain
import BecknerOnofri.Friedrichs.MixedAngularOperator
import BecknerOnofri.Friedrichs.PeriodicWeakEquation

/-! Tensor weak equations for arbitrary smooth one-dimensional profiles.
The inactive factors may be odd periodic functions. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped ContDiff BigOperators
namespace BecknerOnofri.Friedrichs.MixedSpatial

def ProfileWeakImage {d : ℕ} (α : MultiIndex d) (f g : Fin d → ℝ → ℝ) : Prop :=
  ∀ i, ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ →
    (α i≠0 → φ 0=0 ∧ φ Real.pi=0) →
    (α i=0 → φ (2*Real.pi)=φ 0) →
    (∫ t, deriv (f i) t*deriv φ t+
      ((α i:ℝ)*((α i:ℝ)-1)/(Real.sin t)^2)*f i t*φ t ∂coordinateMeasure (α i))=
      ∫ t, g i t*φ t ∂coordinateMeasure (α i)

def profileCoordinateImage {d : ℕ} (f g : Fin d → ℝ → ℝ) (i : Fin d) (x : Space d) : ℝ :=
  (∏ j∈Finset.univ.erase i,f j (x j))*g i (x i)

def profileOperatorImage {d : ℕ} (f g : Fin d → ℝ → ℝ) (x : Space d) : ℝ :=
  ∑ i, profileCoordinateImage f g i x

lemma profileCoordinateImage_continuous {d : ℕ} (f g : Fin d → ℝ → ℝ)
    (hf : ∀ j,ContDiff ℝ ∞ (f j)) (hg : ∀ j,Continuous (g j)) (i : Fin d) :
    Continuous (profileCoordinateImage f g i) :=
  (continuous_finsetProd _ (fun j _ => (hf j).continuous.comp (continuous_apply j))).mul
    ((hg i).comp (continuous_apply i))

lemma profileOperatorImage_continuous {d : ℕ} (f g : Fin d → ℝ → ℝ)
    (hf : ∀ j,ContDiff ℝ ∞ (f j)) (hg : ∀ j,Continuous (g j)) :
    Continuous (profileOperatorImage f g) :=
  continuous_finsetSum _ (fun i _ => profileCoordinateImage_continuous f g hf hg i)

lemma core_fiber_periodic_endpoint {d : ℕ} {α : MultiIndex d} {φ : Space d → ℝ}
    (hφ : inactivePeriodic α φ) (x : Space d) (i : Fin d) (hi : α i=0) :
    φ (Function.update x i (2*Real.pi))=φ (Function.update x i 0) := by
  simpa only [Function.update_self,zero_add,Function.update_idem] using hφ i hi (Function.update x i 0)

lemma profile_fiber_weak {d : ℕ} (α : MultiIndex d) (f g : Fin d → ℝ → ℝ)
    (hf : ∀ j,ContDiff ℝ ∞ (f j)) (hW : ProfileWeakImage α f g) {φ : Space d → ℝ}
    (hφ : smoothCoreProfile α φ) (i : Fin d) (x : Space d) :
    (∫ t,partialDerivative i (productProfile f) (Function.update x i t)*
        partialDerivative i φ (Function.update x i t)+
      ((α i:ℝ)*((α i:ℝ)-1)/(Real.sin t)^2)*
        productProfile f (Function.update x i t)*φ (Function.update x i t)
        ∂coordinateMeasure (α i))=
      ∫ t,profileCoordinateImage f g i (Function.update x i t)*φ (Function.update x i t)
        ∂coordinateMeasure (α i) := by
  have he := hW i _ (fiber_smooth hφ.1 x i) (core_fiber_endpoints hφ.2.2 x i)
    (core_fiber_periodic_endpoint hφ.2.1 x i)
  have hd (t : ℝ) : partialDerivative i (productProfile f) (Function.update x i t)=
      (∏ j∈Finset.univ.erase i,f j (x j))*deriv (f i) t := by
    rw [partialDerivative_productProfile _ (fun j => (hf j).differentiable (by simp)),product_except_update]
    simp
  simp_rw [hd,← fiber_deriv hφ.1 x i,productProfile_update,
    profileCoordinateImage,product_except_update,Function.update_self]
  have hl (t : ℝ) :
      (∏ j∈Finset.univ.erase i,f j (x j))*deriv (f i) t*deriv (fun s => φ (Function.update x i s)) t+
        ((α i:ℝ)*((α i:ℝ)-1)/(Real.sin t)^2)*
          ((∏ j∈Finset.univ.erase i,f j (x j))*f i t)*φ (Function.update x i t)=
      (∏ j∈Finset.univ.erase i,f j (x j))*
        (deriv (f i) t*deriv (fun s => φ (Function.update x i s)) t+
          ((α i:ℝ)*((α i:ℝ)-1)/(Real.sin t)^2)*f i t*φ (Function.update x i t)) := by ring
  simp_rw [hl,mul_assoc]
  simp only [mul_assoc] at he
  rw [integral_const_mul,integral_const_mul,he]

lemma profile_coordinate_weak {d : ℕ} (α : MultiIndex d) (f g : Fin d → ℝ → ℝ)
    (hf : ∀ j,ContDiff ℝ ∞ (f j)) (hg : ∀ j,Continuous (g j))
    (hW : ProfileWeakImage α f g) {φ : Space d → ℝ} (hφ : smoothCoreProfile α φ) (i : Fin d)
    (hI : Integrable (fun x => partialDerivative i (productProfile f) x*partialDerivative i φ x+
      ((α i:ℝ)*((α i:ℝ)-1)/(Real.sin (x i))^2)*productProfile f x*φ x) (spatialMeasure α)) :
    (∫ x,partialDerivative i (productProfile f) x*partialDerivative i φ x+
      ((α i:ℝ)*((α i:ℝ)-1)/(Real.sin (x i))^2)*productProfile f x*φ x ∂spatialMeasure α)=
      ∫ x,profileCoordinateImage f g i x*φ x ∂spatialMeasure α := by
  apply integral_eq_of_fiber_eq α i hI
    ((continuous_memLp α ((profileCoordinateImage_continuous f g hf hg i).mul hφ.1.continuous)).integrable (by norm_num))
  intro x
  simpa only [Function.update_self,Pi.mul_apply] using profile_fiber_weak α f g hf hW hφ i x

def profileOperatorImageLp {d : ℕ} (α : MultiIndex d) (f g : Fin d → ℝ → ℝ)
    (hf : ∀ j,ContDiff ℝ ∞ (f j)) (hg : ∀ j,Continuous (g j)) : H α :=
  (continuous_memLp α (profileOperatorImage_continuous f g hf hg)).toLp (profileOperatorImage f g)

lemma profile_core_equation {d : ℕ} (α : MultiIndex d) (f g : Fin d → ℝ → ℝ)
    (hf : ∀ j,ContDiff ℝ ∞ (f j)) (hg : ∀ j,Continuous (g j))
    (hV : ProfilePotentialIntegrable α f) (hW : ProfileWeakImage α f g) :
    ∀ w∈core α,formPairing (profileLift α f hf hV) w=inner ℝ (profileOperatorImageLp α f g hf hg) w.1 := by
  rintro w ⟨φ,hφ,hw0,hw1,hwV⟩
  have hu1 (i : Fin d) : ((profileLift α f hf hV).2.1 i : Space d → ℝ)=ᵐ[spatialMeasure α]
      partialDerivative i (productProfile f) := (profile_partial_memLp α f hf i).coeFn_toLp
  have huV (i : Fin d) : ((profileLift α f hf hV).2.2 i : Space d → ℝ)=ᵐ[spatialMeasure α]
      (fun x => SpatialForm.potentialFactor (α i) (x i)*productProfile f x) :=
    (profile_potential_memLp α f hf hV i).coeFn_toLp
  have hgAE : (profileOperatorImageLp α f g hf hg : Space d → ℝ)=ᵐ[spatialMeasure α]
      profileOperatorImage f g :=
    (continuous_memLp α (profileOperatorImage_continuous f g hf hg)).coeFn_toLp
  have he (i : Fin d) : inner ℝ ((profileLift α f hf hV).2.1 i) (w.2.1 i)+
      inner ℝ ((profileLift α f hf hV).2.2 i) (w.2.2 i)=
      ∫ x,profileCoordinateImage f g i x*φ x ∂spatialMeasure α := by
    have hi1 := integrable_mul_of_ae (hu1 i) (hw1 i)
    have hiV := integrable_mul_of_ae (huV i) (hwV i)
    have hp (x : Space d) :
        (SpatialForm.potentialFactor (α i) (x i)*productProfile f x)*
          (SpatialForm.potentialFactor (α i) (x i)*φ x)=
        ((α i:ℝ)*((α i:ℝ)-1)/(Real.sin (x i))^2)*productProfile f x*φ x :=
      SpatialForm.potential_product (α i) (fun _ => productProfile f x) (fun _ => φ x) (x i)
    have hi : Integrable (fun x => partialDerivative i (productProfile f) x*partialDerivative i φ x+
        ((α i:ℝ)*((α i:ℝ)-1)/(Real.sin (x i))^2)*productProfile f x*φ x) (spatialMeasure α) := by
      apply (hi1.add hiV).congr
      exact ae_of_all _ (fun x => by simp only [Pi.add_apply,hp])
    rw [inner_eq_integral_of_ae (hu1 i) (hw1 i),inner_eq_integral_of_ae (huV i) (hwV i),
      ← integral_add hi1 hiV]
    simp_rw [hp]
    exact profile_coordinate_weak α f g hf hg hW hφ i hi
  rw [inner_eq_integral_of_ae hgAE hw0]
  unfold formPairing
  simp_rw [he]
  rw [← integral_finset_sum]
  · apply integral_congr_ae
    apply ae_of_all
    intro x
    simp [profileOperatorImage,Finset.sum_mul]
  · intro i hi
    exact (continuous_memLp α ((profileCoordinateImage_continuous f g hf hg i).mul hφ.1.continuous)).integrable (by norm_num)

theorem profile_operatorGraph {d : ℕ} (α : MultiIndex d) (f g : Fin d → ℝ → ℝ)
    (hf : ∀ j,ContDiff ℝ ∞ (f j)) (hg : ∀ j,Continuous (g j))
    (hV : ProfilePotentialIntegrable α f) (hW : ProfileWeakImage α f g)
    (hp : ∀ i,α i=0 → Function.Periodic (f i) (2*Real.pi))
    (hend : ∀ j,α j≠0 → f j 0=0 ∧ f j Real.pi=0) :
    operatorGraph α (profileLift α f hf hV).1 (profileOperatorImageLp α f g hf hg) := by
  exact ⟨profileLift α f hf hV,rfl,profile_mem_formClosure α f hf hV hp hend,
    core_test_extends (profile_core_equation α f g hf hg hV hW)⟩


#print axioms profile_operatorGraph
end BecknerOnofri.Friedrichs.MixedSpatial
