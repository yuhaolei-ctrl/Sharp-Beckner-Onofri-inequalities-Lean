module

public import BecknerOnofri.Friedrichs.MixedCoordinateWeak
public import BecknerOnofri.Friedrichs.MixedAngularVectors

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped ContDiff BigOperators
namespace BecknerOnofri.Friedrichs.MixedSpatial
open Legacy.BecknerOnofri.JacobiAngular

def angularCoordinateImage {d : ℕ} (α : MultiIndex d) (f : Fin d → ℝ → ℝ)
    (i : Fin d) (x : Space d) : ℝ :=
  (∏ j∈Finset.univ.erase i,angularProfiles α f j (x j))*angularImage (α i) (f i) (x i)

lemma productProfile_update {d : ℕ} (f : Fin d → ℝ → ℝ) (x : Space d) (i : Fin d) (t : ℝ) :
    productProfile f (Function.update x i t)=
      (∏ j∈Finset.univ.erase i,f j (x j))*f i t := by
  unfold productProfile
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  congr 1
  · apply Finset.prod_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  · simp

lemma product_except_update {d : ℕ} (f : Fin d → ℝ → ℝ) (x : Space d) (i : Fin d) (t : ℝ) :
    (∏ j∈Finset.univ.erase i,f j (Function.update x i t j))=
      ∏ j∈Finset.univ.erase i,f j (x j) := by
  apply Finset.prod_congr rfl
  intro j hj
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

lemma angular_fiber_weak {d : ℕ} (α : MultiIndex d) (f : Fin d → ℝ → ℝ)
    (hf : ∀ j,ContDiff ℝ ∞ (f j)) {φ : Space d → ℝ}
    (hφ : smoothCoreProfile α φ) (i : Fin d) (x : Space d) :
    (∫ t,partialDerivative i (angularFunction α f) (Function.update x i t)*
        partialDerivative i φ (Function.update x i t)+
      ((α i:ℝ)*((α i:ℝ)-1)/(Real.sin t)^2)*
        angularFunction α f (Function.update x i t)*φ (Function.update x i t)
        ∂coordinateMeasure (α i))=
      ∫ t,angularCoordinateImage α f i (Function.update x i t)*φ (Function.update x i t)
        ∂coordinateMeasure (α i) := by
  have he := coordinate_angular_weak (α i) (hf i) (fiber_smooth hφ.1 x i)
    (core_fiber_endpoints hφ.2.2 x i)
  have hd (t : ℝ) : partialDerivative i (angularFunction α f) (Function.update x i t)=
      (∏ j∈Finset.univ.erase i,angularProfiles α f j (x j))*
        deriv (angular (α i) (f i)) t := by
    rw [angularFunction,partialDerivative_productProfile _
      (fun j => (angularProfiles_smooth α f hf j).differentiable (by simp)),product_except_update]
    simp [angularProfiles]
  simp_rw [hd,← fiber_deriv hφ.1 x i,angularFunction,productProfile_update,
    angularCoordinateImage,product_except_update,Function.update_self]
  have hl (t : ℝ) :
      (∏ j∈Finset.univ.erase i,angularProfiles α f j (x j))*
          deriv (angular (α i) (f i)) t*deriv (fun s => φ (Function.update x i s)) t+
        ((α i:ℝ)*((α i:ℝ)-1)/(Real.sin t)^2)*
          ((∏ j∈Finset.univ.erase i,angularProfiles α f j (x j))*angularProfiles α f i t)*
          φ (Function.update x i t)=
      (∏ j∈Finset.univ.erase i,angularProfiles α f j (x j))*
        (deriv (angular (α i) (f i)) t*deriv (fun s => φ (Function.update x i s)) t+
          ((α i:ℝ)*((α i:ℝ)-1)/(Real.sin t)^2)*angular (α i) (f i) t*φ (Function.update x i t)) := by
    dsimp [angularProfiles]
    ring
  simp_rw [hl,mul_assoc]
  simp only [mul_assoc] at he
  rw [integral_const_mul,integral_const_mul,he]

#print axioms angular_fiber_weak
end BecknerOnofri.Friedrichs.MixedSpatial
