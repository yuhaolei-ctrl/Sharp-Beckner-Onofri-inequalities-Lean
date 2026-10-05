module

public import BecknerOnofri.Friedrichs.MixedAngularWeak
public import BecknerOnofri.Friedrichs.MixedAngularFormDomain
public import BecknerOnofri.Friedrichs.MixedClosedFormTests
public import BecknerOnofri.Friedrichs.AngularOperatorGraph

@[expose] public section

/-! The actual mixed spatial weak operator equation, obtained by coordinate
integration by parts and extension to all closed-form tests. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped ContDiff BigOperators
namespace BecknerOnofri.Friedrichs.MixedSpatial

def angularOperatorImageLp {d : ℕ} (α : MultiIndex d) (f : Fin d → ℝ → ℝ)
    (hf : ∀ j,ContDiff ℝ ∞ (f j)) : H α :=
  (continuous_memLp α (angularOperatorImage_continuous α f hf)).toLp (angularOperatorImage α f)

lemma angular_core_equation {d : ℕ} (α : MultiIndex d) (f : Fin d → ℝ → ℝ)
    (hf : ∀ j,ContDiff ℝ ∞ (f j)) :
    ∀ w∈core α,formPairing (angularLift α f hf) w=inner ℝ (angularOperatorImageLp α f hf) w.1 := by
  rintro w ⟨φ,hφ,hw0,hw1,hwV⟩
  have hu1 (i : Fin d) : ((angularLift α f hf).2.1 i : Space d → ℝ)=ᵐ[spatialMeasure α]
      partialDerivative i (angularFunction α f) := (angular_partial_memLp α f hf i).coeFn_toLp
  have huV (i : Fin d) : ((angularLift α f hf).2.2 i : Space d → ℝ)=ᵐ[spatialMeasure α]
      (fun x => SpatialForm.potentialFactor (α i) (x i)*angularFunction α f x) :=
    (angular_potential_memLp α f hf i).coeFn_toLp
  have hg : (angularOperatorImageLp α f hf : Space d → ℝ)=ᵐ[spatialMeasure α]
      angularOperatorImage α f :=
    (continuous_memLp α (angularOperatorImage_continuous α f hf)).coeFn_toLp
  have he (i : Fin d) : inner ℝ ((angularLift α f hf).2.1 i) (w.2.1 i)+
      inner ℝ ((angularLift α f hf).2.2 i) (w.2.2 i)=
      ∫ x,angularCoordinateImage α f i x*φ x ∂spatialMeasure α := by
    have hi1 := integrable_mul_of_ae (hu1 i) (hw1 i)
    have hiV := integrable_mul_of_ae (huV i) (hwV i)
    have hp (x : Space d) :
        (SpatialForm.potentialFactor (α i) (x i)*angularFunction α f x)*
          (SpatialForm.potentialFactor (α i) (x i)*φ x)=
        ((α i:ℝ)*((α i:ℝ)-1)/(Real.sin (x i))^2)*angularFunction α f x*φ x :=
      SpatialForm.potential_product (α i) (fun _ => angularFunction α f x) (fun _ => φ x) (x i)
    have hi : Integrable (fun x => partialDerivative i (angularFunction α f) x*partialDerivative i φ x+
        ((α i:ℝ)*((α i:ℝ)-1)/(Real.sin (x i))^2)*angularFunction α f x*φ x) (spatialMeasure α) := by
      apply (hi1.add hiV).congr
      exact ae_of_all _ (fun x => by simp only [Pi.add_apply,hp])
    rw [inner_eq_integral_of_ae (hu1 i) (hw1 i),inner_eq_integral_of_ae (huV i) (hwV i),
      ← integral_add hi1 hiV]
    simp_rw [hp]
    exact angular_coordinate_weak α f hf hφ i hi
  rw [inner_eq_integral_of_ae hg hw0]
  unfold formPairing
  simp_rw [he]
  rw [← integral_finset_sum]
  · apply integral_congr_ae
    apply ae_of_all
    intro x
    simp [angularOperatorImage,Finset.sum_mul]
  · intro i hi
    exact (continuous_memLp α ((angularCoordinateImage_continuous α f hf i).mul hφ.1.continuous)).integrable (by norm_num)

theorem angular_operatorGraph {d : ℕ} (α : MultiIndex d) (f : Fin d → ℝ → ℝ)
    (hf : ∀ j,ContDiff ℝ ∞ (f j)) :
    operatorGraph α (angularLift α f hf).1 (angularOperatorImageLp α f hf) := by
  exact ⟨angularLift α f hf,rfl,angular_mem_formClosure α f hf,
    core_test_extends (angular_core_equation α f hf)⟩

#print axioms angular_operatorGraph
end BecknerOnofri.Friedrichs.MixedSpatial
