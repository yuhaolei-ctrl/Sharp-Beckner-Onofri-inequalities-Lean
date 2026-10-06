module

public import BecknerOnofri.LocalQuarticStatementDefinitions
public import BecknerOnofri.SupportedEnergyStatementDefinitions
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

@[expose] public section

/-! Trusted statement of the active squared-amplitude Hessian assertion.
The Hessian below is the second Frechet derivative of the physical functional
on the actual complementary graph; no Taylor matrix is substituted for it. -/
noncomputable section
open Filter Asymptotics
open scoped Topology
namespace BecknerOnofri.HighDim.LocalReductionStatement.ActiveSquaredHessian
open ContinuousGibbs ContinuousFirstShell ContinuousComplement

def extend {d : ℕ} (I : Finset (Fin d)) : (I → ℝ) →L[ℝ] (Fin d → ℝ) :=
  ContinuousLinearMap.pi (fun i => if hi : i∈I then ContinuousLinearMap.proj ⟨i,hi⟩ else 0)

def squaredDiagonal {d : ℕ} (I : Finset (Fin d)) (r : ℝ) : Fin d → ℝ :=
  fun i => if i∈I then r else 0

def coordinates {d : ℕ} (I : Finset (Fin d)) (r : Fin d → ℝ) : Coordinates d :=
  fun i => if i∈I then (Real.sqrt (r i) : ℂ) else 0

def potential {d : ℕ} (ψ : ℝ × Coordinates d → complement d) (I : Finset (Fin d))
    (μ : ℝ) (r : Fin d → ℝ) : Space d :=
  reconstruction d (coordinates I r,ψ (μ,coordinates I r))

def energy {d : ℕ} (ψ : ℝ × Coordinates d → complement d) (I : Finset (Fin d))
    (μ : ℝ) (r : Fin d → ℝ) : ℝ :=
  (dualFunctional (μ*spectralThreshold d) (potential ψ I μ r)).toReal

/-- Restrict both arguments of the genuine second derivative to the active
coordinates, represented in their standard real orthonormal basis. -/
def hessian {d : ℕ} (ψ : ℝ × Coordinates d → complement d) (I : Finset (Fin d))
    (μ : ℝ) (r : Fin d → ℝ) : Module.End ℝ (I → ℝ) :=
  LinearMap.pi (fun i : I =>
    ((ContinuousLinearMap.apply ℝ ℝ (Pi.single i.val (1:ℝ))).comp
      ((fderiv ℝ (fun r => fderiv ℝ (energy ψ I μ) r) r).comp (extend I))).toLinearMap)

def Spectrum {d : ℕ} (ψ : ℝ × Coordinates d → complement d) (I : Finset (Fin d))
    (r R T : ℝ → ℝ) : Prop :=
  ((fun δ => R δ-(2*quarticA d+quarticB d*((I.card:ℝ)-1)))
    =O[𝓝[>] (0:ℝ)] (fun δ => ‖δ‖)) ∧
  ((fun δ => T δ-(2*quarticA d-quarticB d))
    =O[𝓝[>] (0:ℝ)] (fun δ => ‖δ‖)) ∧
  ∀ᶠ δ in 𝓝[>] (0:ℝ),R δ<0 ∧ T δ<0 ∧ R δ≠T δ ∧
    (∀ v : I → ℝ,∀ i : I,
      hessian ψ I (1/(1-δ)) (squaredDiagonal I (r δ)) v i=
        T δ*v i+((R δ-T δ)/(I.card:ℝ))*∑ k,v k) ∧
    Module.finrank ℝ ((hessian ψ I (1/(1-δ)) (squaredDiagonal I (r δ))).eigenspace (R δ))=1 ∧
    Module.finrank ℝ ((hessian ψ I (1/(1-δ)) (squaredDiagonal I (r δ))).eigenspace (T δ))=I.card-1

def Family (d : ℕ) : Prop :=
  ∃ ψ : ℝ × Coordinates d → complement d,
    AnalyticAt ℝ ψ (1,0) ∧ ψ (1,0)=0 ∧ HasFDerivAt (𝕜 := ℝ) ψ 0 (1,0) ∧
    (∀ᶠ x in 𝓝 (1,(0 : Coordinates d)),
      projectedEquation (greenContinuous d) (x,ψ x)=0) ∧
    (∀ᶠ x in 𝓝 ((1,(0 : Coordinates d)),(0 : complement d)),
      projectedEquation (greenContinuous d) x=0 ↔ ψ x.1=x.2) ∧
    (∀ᶠ x in 𝓝 (1,(0 : Coordinates d)),
      InCriticalSobolev (reconstruction d (x.2,ψ x)) ∧
      SmoothOnTorus (reconstruction d (x.2,ψ x)) ∧
      ∀ s : ℝ,InSobolev s (reconstruction d (x.2,ψ x))) ∧
    ∀ n : ℕ,0<n → n≤d → ∃ r : ℝ → ℝ,
      AnalyticAt ℝ r 0 ∧ r 0=0 ∧ HasDerivAt r (supportCoefficient d n)⁻¹ 0 ∧
      ((fun δ => r δ-δ/supportCoefficient d n) =O[𝓝 (0:ℝ)] (fun δ => ‖δ‖^2)) ∧
      ∀ I : Finset (Fin d),I.card=n → ∃ U : ℝ → Space d,∃ R T : ℝ → ℝ,
        SupportedProfile d I r U ∧
        (∀ᶠ δ in 𝓝[>] (0:ℝ),U δ=potential ψ I (1/(1-δ)) (squaredDiagonal I (r δ))) ∧
        Spectrum ψ I r R T

end BecknerOnofri.HighDim.LocalReductionStatement.ActiveSquaredHessian
