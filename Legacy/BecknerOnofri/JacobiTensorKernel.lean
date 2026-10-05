module

public import Legacy.BecknerOnofri.JacobiTensorSpectrum
public import Legacy.BecknerOnofri.SpectralKernelRepresentation

@[expose] public section

/-! The actual L2 kernel of the critical inverse Jacobi tensor operator.
All square summability needed by the kernel reconstruction has been proved
for the concrete lattice spectrum; no kernel representation is assumed. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology BigOperators
namespace Legacy.BecknerOnofri.JacobiTensorSpectrum
open JacobiTensor
variable {d : ℕ}

def criticalKernel (a : Index d) : Lp ℝ 2 ((JacobiTensor.measure d).prod (JacobiTensor.measure d)) :=
  SpectralKernel.spectralKernel (JacobiTensor.measure d) (hilbertBasis a)
    (fun n => (tensorEigenvalue a n)^(-((d:ℝ)/2)))

theorem criticalKernel_hasSum (a : Index d) (ha : a ≠ 0) :
    HasSum (fun n : Index d => (tensorEigenvalue a n)^(-((d:ℝ)/2)) •
      SpectralKernel.tensor (JacobiTensor.measure d) (tensorVector a n) (tensorVector a n))
      (criticalKernel a) := by
  have h := SpectralKernel.spectralKernel_hasSum (JacobiTensor.measure d) (hilbertBasis a)
    (fun n => (tensorEigenvalue a n)^(-((d:ℝ)/2))) (criticalSymbol_sq_summable a ha)
  simpa only [hilbertBasis_apply, criticalKernel] using h

/-- Every actual L2 input has almost everywhere integrable slices and the correct inverse action. -/
theorem criticalKernel_representation (a : Index d) (ha : a ≠ 0) (u : TensorL2 d) :
    ∀ᵐ x ∂JacobiTensor.measure d,
      Integrable (fun y => criticalKernel a (x,y)*u y) (JacobiTensor.measure d) ∧
        (∫ y, criticalKernel a (x,y)*u y ∂JacobiTensor.measure d) = criticalInverse a ha u x :=
  SpectralKernel.inversePower_kernel_representation (JacobiTensor.measure d) (hilbertBasis a)
    (positiveSpectrum a ha) ((d:ℝ)/2) (criticalExponent_pos a ha)
    (criticalSymbol_sq_summable a ha) u

theorem criticalKernel_pairing (a : Index d) (ha : a ≠ 0) (u v : TensorL2 d) :
    @inner ℝ (SpectralKernel.KernelL2 (JacobiTensor.measure d)) _
      (SpectralKernel.tensor (JacobiTensor.measure d) v u) (criticalKernel a) =
        @inner ℝ (TensorL2 d) _ v (criticalInverse a ha u) :=
  SpectralKernel.spectralKernel_pairing (JacobiTensor.measure d) (hilbertBasis a)
    (criticalSymbol a ha) (criticalSymbol_sq_summable a ha) u v

#print axioms criticalKernel_hasSum
#print axioms criticalKernel_representation
#print axioms criticalKernel_pairing
end Legacy.BecknerOnofri.JacobiTensorSpectrum
