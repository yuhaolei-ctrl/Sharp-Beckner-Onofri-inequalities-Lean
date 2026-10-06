module

public import BecknerOnofri.WienerGraphImplicit
public import BecknerOnofri.WienerGraphSobolev

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter
open scoped Topology
namespace BecknerOnofri.HighDim.WienerGraph
open ContinuousFirstShell

@[simp] lemma toComplement_greenComplement {d : ℕ} (hd : 0<d) (m : ℕ)
    (x : complementSpace d m) : toComplement d m (greenComplement hd m x)=
      continuousComplementGreen hd (toComplement d m x) := rfl

lemma toComplement_nonlinearPart {d : ℕ} (hd : 0<d) (m : ℕ)
    (x : Coordinates d × complementSpace d m) :
    toComplement d m (nonlinearPart hd m x)=
      ContinuousComplement.remainder (greenContinuous d) (x.1,toComplement d m x.2) := by
  rw [nonlinearPart,toComplement_project,toContinuous_green,Gibbs.toContinuous_remainder,
    toContinuous_reconstruct]
  rfl

lemma toComplement_equation {d : ℕ} (hd : 0<d) (m : ℕ)
    (x : (ℝ × Coordinates d) × complementSpace d m) :
    toComplement d m (ComplementImplicit.equation (greenComplement hd m) (nonlinearPart hd m) x)=
      ContinuousComplement.projectedEquation (greenContinuous d) (x.1,toComplement d m x.2) := by
  rw [ContinuousComplement.projectedEquation_eq (greenContinuous d)
    (LocalEleven.GreenLocalBranch.green_first_complement_zero hd),
    LocalEleven.GreenLocalBranch.linearPart_eq hd]
  simp only [ComplementImplicit.equation,map_sub,map_smul,map_add,
    toComplement_greenComplement,toComplement_nonlinearPart]

/-- Uniqueness identifies the stronger-topology IFT graph with the same
continuous-space graph used throughout the local branch construction. -/
theorem exists_identified_analytic_graph {d : ℕ} (hd : 11≤d) (m : ℕ) :
    ∃ ψ : ℝ × Coordinates d → complementSpace d m,
      AnalyticAt ℝ ψ (1,0) ∧ ψ (1,0)=0 ∧ HasFDerivAt (𝕜 := ℝ) ψ 0 (1,0) ∧
      ∀ᶠ x in 𝓝 (1,(0 : Coordinates d)),
        toComplement d m (ψ x)=LocalEleven.GreenLocalBranch.correction hd x := by
  obtain ⟨ψ,ha,h0,hdψ,hsolve,_⟩ := exists_analytic_graph hd m
  refine ⟨ψ,ha,h0,hdψ,?_⟩
  have ht : Tendsto (fun x => (x,toComplement d m (ψ x)))
      (𝓝 (1,(0 : Coordinates d))) (𝓝 ((1,0),(0 : complement d))) := by
    have hh : ContinuousAt (fun x : ℝ × Coordinates d => (x,toComplement d m (ψ x))) (1,0) :=
      continuousAt_id.prodMk ((toComplement d m).continuous.continuousAt.comp ha.continuousAt)
    simpa only [h0,map_zero] using hh.tendsto
  filter_upwards [hsolve,ht.eventually (LocalEleven.GreenLocalBranch.correction_unique hd)] with x hx hu
  apply Eq.symm
  apply hu.mp
  rw [← toComplement_equation (by omega) m (x,ψ x),hx,map_zero]

/-- Analyticity in the exact physical H^s Fourier Hilbert norm, for every
fixed real s, of the previously constructed graph. -/
theorem exists_analytic_sobolev_lift {d : ℕ} (hd : 11≤d) (s : ℝ) :
    ∃ F : ℝ × Coordinates d → FourierL2 d, AnalyticAt ℝ F (1,0) ∧
      F (1,0)=0 ∧ HasFDerivAt (𝕜 := ℝ) F 0 (1,0) ∧
      ∀ᶠ x in 𝓝 (1,(0 : Coordinates d)), ∀ k : Frequency d,
        F x k=(sobolevScale s k : ℂ)*
          fourierCoeff (LocalEleven.GreenLocalBranch.correction hd x).val k := by
  obtain ⟨m,hm⟩ := exists_nat_ge s
  obtain ⟨ψ,hψ,hψ0,hψd,he⟩ := exists_identified_analytic_graph hd m
  let L : complementSpace d m →L[ℝ] FourierL2 d :=
    (toSobolev hm).comp (complementSpace d m).subtypeL
  refine ⟨fun x => L (ψ x),(L.analyticAt _).comp hψ,by change L (ψ (1,0))=0; rw [hψ0,map_zero],?_,?_⟩
  · convert! L.hasFDerivAt.comp (1,0) hψd using 1
    simp
  · filter_upwards [he] with x hx
    intro k
    change toSobolev hm (ψ x).val k=_
    rw [toSobolev_apply]
    have hv := congrArg Subtype.val hx
    change toContinuous d m (ψ x).val=(LocalEleven.GreenLocalBranch.correction hd x).val at hv
    rw [hv]

#print axioms exists_analytic_sobolev_lift
end BecknerOnofri.HighDim.WienerGraph
