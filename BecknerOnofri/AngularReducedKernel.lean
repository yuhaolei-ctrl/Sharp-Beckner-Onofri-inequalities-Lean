module

public import BecknerOnofri.GraphTranslationTangents
public import BecknerOnofri.RealDiagonalReduction

@[expose] public section

/-! Exact translation directions lie in the actual reduced derivative kernel.
These are differentiated torus symmetries, not zeros of a model polynomial. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter
open scoped Topology BigOperators
namespace BecknerOnofri.HighDim.AngularReducedKernel
open ContinuousGibbs ContinuousFirstShell ContinuousSymmetry ReducedEquation
open GraphTranslationTangents

theorem angular_kernel {d : ℕ} (hd : 12 ≤ d) :
    ∀ᶠ x in 𝓝 (1,(0:Coordinates d)), reduced hd x = 0 → ∀ j : Fin d,
      fderiv ℝ (fun z => reduced hd (x.1,z)) x.2 (angularDirection x.2 j) = 0 := by
  filter_upwards [(reduced_analytic hd).eventually_analyticAt,reduced_translation hd] with x ha ht hs j
  have hf : DifferentiableAt ℝ (fun z => reduced hd (x.1,z)) x.2 := by
    have hp : HasFDerivAt (fun z : Coordinates d => (x.1,z))
        ((0 : Coordinates d →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (Coordinates d))) x.2 :=
      (hasFDerivAt_const x.1 x.2).prodMk (hasFDerivAt_id x.2)
    convert! ha.differentiableAt.comp x.2 hp.differentiableAt using 1
  have hder := hf.hasFDerivAt.comp_hasDerivAt_of_eq (0:ℝ)
    (hasDerivAt_phase_axisTranslation j x.2) (phase_axisTranslation_zero j x.2).symm
  have hz : HasDerivAt (fun t : ℝ => reduced hd (x.1,phaseCoordinates (-axisTranslation j t) x.2))
      (0 : Coordinates d) 0 := by
    apply (hasDerivAt_const (x := (0:ℝ)) (c := (0:Coordinates d))).congr_of_eventuallyEq
    exact Eventually.of_forall (fun t => by
      dsimp only
      rw [ht (-axisTranslation j t), hs]
      exact (coordinateTranslation (-axisTranslation j t)).map_zero)
  exact hder.unique hz

/-- Pure imaginary first-shell directions, as a real linear map. -/
def imaginaryCoordinates (d : ℕ) (b : Fin d → ℝ) : Coordinates d := fun i => (b i:ℂ)*Complex.I

theorem imaginary_as_angles {d : ℕ} {t : ℝ} (ht : t≠0) (b : Fin d → ℝ) :
    imaginaryCoordinates d b = ∑ j : Fin d, (b j/(2*Real.pi*t)) •
      angularDirection (ReducedCubicExpansion.realDiagonal d t) j := by
  classical
  funext i
  simp only [imaginaryCoordinates,Finset.sum_apply,Pi.smul_apply,angularDirection]
  rw [Finset.sum_eq_single i]
  · rw [Pi.single_eq_same]
    change (b i:ℂ)*Complex.I = (b i/(2*Real.pi*t)) • ((2*Real.pi*Complex.I)*(t:ℂ))
    rw [Complex.real_smul]
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr ht]
    <;> ring
  · intro j _ hji
    rw [Pi.single_eq_of_ne (Ne.symm hji),smul_zero]
  · simp

theorem imaginary_kernel {d : ℕ} (hd : 12 ≤ d) :
    ∀ᶠ x : ℝ × ℝ in 𝓝 (1,0), x.2≠0 →
      reduced hd (x.1,ReducedCubicExpansion.realDiagonal d x.2)=0 →
      ∀ b : Fin d → ℝ,
        fderiv ℝ (fun z => reduced hd (x.1,z)) (ReducedCubicExpansion.realDiagonal d x.2)
          (imaginaryCoordinates d b)=0 := by
  have ht : Tendsto (fun x : ℝ × ℝ => (x.1,ReducedCubicExpansion.realDiagonal d x.2))
      (𝓝 (1,0)) (𝓝 (1,(0:Coordinates d))) := by
    have hc : Continuous (fun x : ℝ × ℝ => (x.1,ReducedCubicExpansion.realDiagonal d x.2)) := by
      unfold ReducedCubicExpansion.realDiagonal
      fun_prop
    convert! hc.tendsto ((1:ℝ),(0:ℝ)) using 1
  filter_upwards [ht.eventually (angular_kernel hd)] with x hx ht0 hs b
  rw [imaginary_as_angles ht0 b,map_sum]
  simp only [map_smul,hx hs,smul_zero,Finset.sum_const_zero]

#print axioms angular_kernel
#print axioms imaginary_kernel
end BecknerOnofri.HighDim.AngularReducedKernel
