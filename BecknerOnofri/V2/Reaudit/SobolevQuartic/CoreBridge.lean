module

public import BecknerOnofri.V2.Reaudit.SobolevQuartic.Final
public import BecknerOnofri.V2.Reaudit.Sobolev.Branch
public import BecknerOnofri.LocalElevenCore.ReducedEnergyDeltaRemainder

@[expose] public section

/-! # The reduced quartic expansion of the Core branch, from the native `H^s` reduction (S054)

`physicalReducedEnergy_quartic_paper_native` has exactly the statement of
`UniformComplementBounds.physicalReducedEnergy_quartic_paper` (the two-parameter quartic expansion
of the physical reduced energy along the solved graph), but it is proved from
`SobolevQuartic.section5_quartic_reduction_native` (the third assertion of
`lem:section5-quartic-reduction`, native in `H^s`, `s = d`) and not from the sup-norm expansion
`physicalReducedEnergy_joint_quartic`.  The identification of the `H^s` graph with the Core
correction is `Sobolev.reconstructionH_graph` (for `s = d` the Core correction is the Sobolev graph). -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter Asymptotics
open scoped Topology

namespace BecknerOnofri.HighDim.LocalEleven.UniformComplementBounds
open ContinuousFirstShell ReducedEnergyGradient ReducedQuarticExpansion

/-- **Reduced quartic expansion, native route.**  Same statement as
`physicalReducedEnergy_quartic_paper`; proved from `section5_quartic_reduction_native` with
`s = d`. -/
theorem physicalReducedEnergy_quartic_paper_native {d : ℕ} (hd : 11 ≤ d) :
    (fun x : ℝ × Coordinates d => physicalReducedEnergy hd x -
      (1-1/x.1)*squaredAmplitude x.2 - quarticValue x.2)
      =O[𝓝 (1,0)] (fun x => (squaredAmplitude x.2)^3+
        |1-1/x.1| *(squaredAmplitude x.2)^2) := by
  have := BecknerOnofri.V2.Reaudit.Sobolev.sobolevIndex_self (d := d) (by omega)
  have h := (BecknerOnofri.V2.Reaudit.SobolevQuartic.section5_quartic_reduction_native
    (d := d) (s := (d : ℝ)) hd).2.2
  refine h.congr' ?_ (Eventually.of_forall fun _ => rfl)
  filter_upwards [BecknerOnofri.V2.Reaudit.Sobolev.reconstructionH_graph (d := d) (s := (d : ℝ)) hd]
    with x hx
  rw [hx]
  rfl

#print axioms physicalReducedEnergy_quartic_paper_native

end BecknerOnofri.HighDim.LocalEleven.UniformComplementBounds
