module

public import BecknerOnofri.WienerGraphGibbs
public import BecknerOnofri.WienerGraphInverse

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter
open scoped Topology
namespace BecknerOnofri.HighDim.WienerGraph
open ContinuousFirstShell

/-- The actual normalized Gibbs remainder after Green preconditioning and
projection, now in the complete weighted complement. -/
def nonlinearPart {d : ℕ} (hd : 0<d) (m : ℕ)
    (x : Coordinates d × complementSpace d m) : complementSpace d m :=
  projectComplement d m (green hd m (Gibbs.nonlinearRemainder (reconstruct d m x)))

lemma nonlinearPart_analytic {d : ℕ} (hd : 0<d) (m : ℕ)
    (x : Coordinates d × complementSpace d m) : AnalyticAt ℝ (nonlinearPart hd m) x := by
  have hi := (Gibbs.remainder_analytic (reconstruct d m x)).comp ((reconstruct d m).analyticAt x)
  have ho := (((projectComplement d m).comp (green hd m)).analyticAt
    (Gibbs.nonlinearRemainder (reconstruct d m x))).comp
      (f := fun y => Gibbs.nonlinearRemainder (reconstruct d m y)) hi
  exact ho

@[simp] lemma nonlinearPart_zero {d : ℕ} (hd : 0<d) (m : ℕ) :
    nonlinearPart hd m 0=0 := by simp [nonlinearPart]

lemma nonlinearPart_derivative_zero {d : ℕ} (hd : 0<d) (m : ℕ) :
    HasFDerivAt (𝕜 := ℝ) (nonlinearPart hd m) 0 (0 : Coordinates d × complementSpace d m) := by
  have h0 : HasFDerivAt (𝕜 := ℝ) Gibbs.nonlinearRemainder 0
      (reconstruct d m (0 : Coordinates d × complementSpace d m)) := by
    simpa only [map_zero] using Gibbs.hasFDerivAt_remainder_zero d m
  have hi := h0.comp (0 : Coordinates d × complementSpace d m) (reconstruct d m).hasFDerivAt
  have ho := (((projectComplement d m).comp (green hd m)).hasFDerivAt).comp
    (0 : Coordinates d × complementSpace d m) hi
  convert! ho using 1 <;> simp [nonlinearPart]

/-- Analytic implicit-function construction in the complete weighted Banach
space; no stronger-topology analytic regularity is presumed. -/
theorem exists_analytic_graph {d : ℕ} (hd : 11≤d) (m : ℕ) :
    ∃ ψ : ℝ × Coordinates d → complementSpace d m,
      AnalyticAt ℝ ψ (1,0) ∧ ψ (1,0)=0 ∧ HasFDerivAt (𝕜 := ℝ) ψ 0 (1,0) ∧
      (∀ᶠ x in 𝓝 (1,(0 : Coordinates d)),
        ComplementImplicit.equation (greenComplement (d := d) (by omega) m) (nonlinearPart (d := d) (by omega) m)
          (x,ψ x)=0) ∧
      (∀ᶠ x in 𝓝 ((1,(0 : Coordinates d)),(0 : complementSpace d m)),
        ComplementImplicit.equation (greenComplement (d := d) (by omega) m) (nonlinearPart (d := d) (by omega) m) x=0 ↔
          ψ x.1=x.2) :=
  ComplementImplicit.exists_analytic_complement (greenComplement (d := d) (by omega) m)
    (nonlinearPart (d := d) (by omega) m) (nonlinearPart_analytic (d := d) (by omega) m 0)
    (nonlinearPart_zero (d := d) (by omega) m) (nonlinearPart_derivative_zero (d := d) (by omega) m)
    (complementEquiv hd m) (complementEquiv_toCLM hd m)

#print axioms exists_analytic_graph
end BecknerOnofri.HighDim.WienerGraph
